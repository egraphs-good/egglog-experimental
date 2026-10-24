//! Content-keyed registration with one native rule state shared by all groups.

use super::*;

// Request-local provenance for each inline addition. Fail wrappers are path
// transparent, matching CommandLocation; loop bodies add one list coordinate.
pub(super) fn additions(
    commands: &[pb::Command],
) -> impl Iterator<Item = (Vec<u32>, &pb::AddRules)> {
    let mut pending = commands
        .iter()
        .enumerate()
        .rev()
        .map(|(index, command)| (vec![index as u32], command))
        .collect::<Vec<_>>();
    std::iter::from_fn(move || {
        loop {
            let (path, command) = pending.pop()?;
            match &command.kind {
                Some(pb::command::Kind::AddRules(add)) => return Some((path, add)),
                Some(pb::command::Kind::Fail(child)) => pending.push((path, child)),
                Some(pb::command::Kind::Loop(body)) => {
                    pending.extend(body.body.iter().enumerate().rev().map(|(index, command)| {
                        let mut path = path.clone();
                        path.push(index as u32);
                        (path, command)
                    }))
                }
                _ => (),
            }
        }
    })
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
    membership: HashSet<(String, usize)>,
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
        let mut indices = vec![];
        for group in groups {
            if let Some(rules) = self.groups.get(group) {
                indices.extend(rules.iter().copied().filter(|index| seen.insert(*index)));
            }
        }
        indices
    }

    pub(super) fn add(
        &mut self,
        path: &[u32],
        add: &pb::AddRules,
        candidates: &[Candidate],
        executor: &mut NativeExecutor<'_>,
        context: &mut RequestOccurrences,
        response: &mut pb::RunProgramOutput,
    ) -> Result<(), egglog::Error> {
        let start = *context
            .candidate_offsets
            .get(path)
            .ok_or_else(|| egglog::Error::BackendError("unprepared inline addition".into()))?;
        for local in 0..add.rules.len() {
            let candidate = candidates.get(start + local).ok_or_else(|| {
                egglog::Error::BackendError("unprepared inline rule occurrence".into())
            })?;
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
                // A completed registration survives a later maintenance error.
                if registered {
                    rule.completed += 1;
                }
                result?;
                debug_assert!(registered);
            }
            if self.membership.insert((add.group.clone(), index)) {
                self.groups
                    .entry(add.group.clone())
                    .or_default()
                    .push(index);
            }
        }
        Ok(())
    }

    pub(super) fn selection(
        &mut self,
        groups: &[String],
        executor: &mut NativeExecutor<'_>,
        context: &mut RequestOccurrences,
        response: &mut pb::RunProgramOutput,
    ) -> Result<String, egglog::Error> {
        let indices = self.ordered_union(groups);
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
        let mut file_offsets = HashMap::new();
        let mut groups: Vec<_> = self.groups.iter().collect();
        groups.sort_unstable_by(|a, b| a.0.cmp(b.0));
        for (group, rules) in groups {
            let mut selected = vec![];
            for &index in rules {
                let rule = if let Some(rule) = mapping.get(&index) {
                    rule.clone()
                } else {
                    let rule = graph::append_rule(
                        destination,
                        &self.rules[index].candidate.record,
                        &mut file_offsets,
                    )?;
                    mapping.insert(index, rule.clone());
                    rule
                };
                selected.push(rule);
            }
            destination.commands.push(pb::Command {
                kind: Some(pb::command::Kind::AddRules(pb::AddRules {
                    group: group.clone(),
                    rules: selected,
                })),
                ..Default::default()
            });
        }
        Ok(())
    }
}
