//! Content-keyed registration with rule progress independent of named bindings.

use super::*;
use std::ops::Range;

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) enum Site {
    Binding(usize),
    Selection(Vec<u32>, usize),
}

// Fail wrappers are path transparent; loop bodies add a list coordinate.
pub(super) fn collections(program: &pb::Program) -> impl Iterator<Item = (Site, &pb::Ruleset)> {
    let bindings = program
        .rulesets
        .iter()
        .enumerate()
        .filter_map(|(index, binding)| {
            binding
                .value
                .as_ref()
                .map(|value| (Site::Binding(index), value))
        });
    let mut pending = program
        .commands
        .iter()
        .enumerate()
        .rev()
        .map(|(index, command)| (vec![index as u32], command))
        .collect::<Vec<_>>();
    let mut literals = vec![];
    while let Some((path, command)) = pending.pop() {
        match &command.kind {
            Some(pb::command::Kind::Run(run)) => {
                for (index, selection) in run.rulesets.iter().enumerate() {
                    if let Some(pb::ruleset_selection::Kind::Ruleset(value)) = &selection.kind {
                        literals.push((Site::Selection(path.clone(), index), value));
                    }
                }
            }
            Some(pb::command::Kind::Fail(child)) => pending.push((path, child)),
            Some(pb::command::Kind::Loop(body)) => {
                pending.extend(body.body.iter().enumerate().rev().map(|(index, command)| {
                    let mut path = path.clone();
                    path.push(index as u32);
                    (path, command)
                }));
            }
            _ => (),
        }
    }
    bindings.chain(literals)
}

#[derive(Clone)]
pub(super) struct Candidate {
    pub record: Arc<graph::RuleRecord>,
    pub key: Vec<u8>,
    pub name: String,
    pub commands: Vec<Command>,
}

#[derive(Clone)]
pub(super) struct Registered {
    pub candidate: Candidate,
    completed: usize,
}

#[derive(Clone, Default)]
pub(super) struct Registry {
    pub rules: Vec<Registered>,
    pub keys: HashMap<Vec<u8>, usize>,
    pub groups: HashMap<String, Vec<usize>>,
    selections: HashMap<Vec<usize>, String>,
}

impl Registry {
    pub(super) fn intern(&mut self, candidate: &Candidate) -> usize {
        if let Some(index) = self.keys.get(&candidate.key) {
            return *index;
        }
        let index = self.rules.len();
        self.keys.insert(candidate.key.clone(), index);
        self.rules.push(Registered {
            candidate: candidate.clone(),
            completed: 0,
        });
        index
    }

    pub(super) fn ordered_union(&self, groups: &[String]) -> Vec<usize> {
        let mut seen = HashSet::new();
        groups
            .iter()
            .filter_map(|group| self.groups.get(group))
            .flatten()
            .copied()
            .filter(|index| seen.insert(*index))
            .collect()
    }

    pub(super) fn resolve(
        &self,
        selections: &[pb::RulesetSelection],
        path: &[u32],
        context: &RequestOccurrences,
    ) -> Vec<usize> {
        let mut seen = HashSet::new();
        let mut result = vec![];
        for (index, selection) in selections.iter().enumerate() {
            let indices: &[usize] = match selection.kind.as_ref().expect("validated selection") {
                pb::ruleset_selection::Kind::Name(name) => {
                    self.groups.get(name).map_or(&[], Vec::as_slice)
                }
                pb::ruleset_selection::Kind::Ruleset(_) => {
                    &context.literal_rules[&Site::Selection(path.to_vec(), index)]
                }
            };
            result.extend(indices.iter().copied().filter(|index| seen.insert(*index)));
        }
        result
    }

    // Registration may partially succeed in the native backend. Retain each
    // completed step so a later request resumes its installation safely.
    pub(super) fn install(
        &mut self,
        candidates: &[Candidate],
        ranges: &[(Site, Range<usize>)],
        bindings: &[pb::RulesetBinding],
        executor: &mut NativeExecutor<'_>,
        context: &mut RequestOccurrences,
        response: &mut pb::RunProgramOutput,
    ) -> Result<(), egglog::Error> {
        let mut replacements = vec![];
        for (site, range) in ranges {
            let mut indices = vec![];
            let mut seen = HashSet::new();
            for candidate in &candidates[range.clone()] {
                let index = self.intern(candidate);
                let rule = &mut self.rules[index];
                while rule.completed < rule.candidate.commands.len() {
                    let (result, registered, _) = executor.run_observed(
                        vec![rule.candidate.commands[rule.completed].clone()],
                        None,
                        context,
                        response,
                        None,
                    );
                    if registered {
                        rule.completed += 1;
                    }
                    result?;
                    debug_assert!(registered);
                }
                if seen.insert(index) {
                    indices.push(index);
                }
            }
            match site {
                Site::Binding(index) => replacements.push((bindings[*index].name.clone(), indices)),
                Site::Selection(..) => {
                    context.literal_rules.insert(site.clone(), indices);
                }
            }
        }
        self.groups.extend(replacements);
        Ok(())
    }

    pub(super) fn selection(
        &mut self,
        indices: Vec<usize>,
        executor: &mut NativeExecutor<'_>,
        context: &mut RequestOccurrences,
        response: &mut pb::RunProgramOutput,
    ) -> Result<String, egglog::Error> {
        if let Some(name) = self.selections.get(&indices) {
            return Ok(name.clone());
        }
        let name = format!(
            "__protobuf_selection_{}_{}",
            context.request,
            self.selections.len()
        );
        let holders = indices
            .iter()
            .map(|index| format!("{}_holder", self.rules[*index].candidate.name))
            .collect();
        let (result, registered, _) = executor.run_observed(
            vec![Command::UnstableCombinedRuleset(
                ast::Span::Panic,
                name.clone(),
                holders,
            )],
            None,
            context,
            response,
            None,
        );
        if registered {
            self.selections.insert(indices, name.clone());
        }
        result?;
        Ok(name)
    }

    pub(super) fn reconstruct(&self, destination: &mut pb::Program) -> Result<(), String> {
        let mut mapping: HashMap<usize, pb::Rule> = HashMap::new();
        let mut groups: Vec<_> = self.groups.iter().collect();
        groups.sort_unstable_by(|a, b| a.0.cmp(b.0));
        for (group, rules) in groups {
            let mut selected = vec![];
            for &index in rules {
                let rule = if let Some(rule) = mapping.get(&index) {
                    rule.clone()
                } else {
                    let rule =
                        graph::append_rule(destination, &self.rules[index].candidate.record)?;
                    mapping.insert(index, rule.clone());
                    rule
                };
                selected.push(rule);
            }
            destination.rulesets.push(pb::RulesetBinding {
                name: group.clone(),
                value: Some(pb::Ruleset { rules: selected }),
            });
        }
        Ok(())
    }
}
