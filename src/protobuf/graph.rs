//! Arena relocation shared by accumulated inputs and owned rule diagnostics.

use super::{pb, source};
use prost::Message;
use std::collections::HashMap;
use std::sync::Arc;

/// Visit setup bindings, then literal selections in command-tree order.
pub(crate) fn rules(program: &pb::Program) -> impl Iterator<Item = &pb::Rule> {
    super::rules::collections(program).flat_map(|(_, ruleset)| ruleset.rules.iter())
}

/// Mutable traversal matching the immutable rule order.
pub(crate) fn rules_mut(program: &mut pb::Program) -> Vec<&mut pb::Rule> {
    let mut result = vec![];
    for binding in &mut program.rulesets {
        if let Some(value) = &mut binding.value {
            result.extend(&mut value.rules);
        }
    }
    let mut pending: Vec<_> = program.commands.iter_mut().rev().collect();
    while let Some(command) = pending.pop() {
        match &mut command.kind {
            Some(pb::command::Kind::Run(run)) => {
                for selection in &mut run.rulesets {
                    if let Some(pb::ruleset_selection::Kind::Ruleset(value)) = &mut selection.kind {
                        result.extend(&mut value.rules);
                    }
                }
            }
            Some(pb::command::Kind::Fail(child)) => pending.push(child),
            Some(pb::command::Kind::Loop(body)) => pending.extend(body.body.iter_mut().rev()),
            _ => (),
        }
    }
    result
}

/// Append prepared rule/command arenas without identifying their node locations
/// with another input's locations. Named declarations are reconciled separately,
/// keeping cumulative command data out of declaration reconciliation.
pub(super) fn append(
    destination: &mut pb::Program,
    source: &pb::Program,
    files: u32,
) -> Result<(), String> {
    let mut source = source.clone();
    source.declarations.clear();
    let nodes = u32::try_from(destination.nodes.len()).map_err(|_| "too many nodes")?;
    let sorts = u32::try_from(destination.sorts.len()).map_err(|_| "too many sorts")?;
    source::source_phase_refs(&mut source, |index| {
        *index = index.checked_add(nodes).ok_or("too many nodes")?;
        Ok(())
    })?;
    for node in &mut source.nodes {
        node.sort_id = node.sort_id.checked_add(sorts).ok_or("too many sorts")?;
        relocate_span(&mut node.span, files)?;
        source::source_node_refs(node, |index| {
            *index = index.checked_add(nodes).ok_or("too many nodes")?;
            Ok(())
        })?;
    }
    for sort in &mut source.sorts {
        relocate_span(&mut sort.span, files)?;
        sort_refs(sort, |index| {
            *index = index.checked_add(sorts).ok_or("too many sorts")?;
            Ok(())
        })?;
    }
    for rule in rules_mut(&mut source) {
        crate::builtin::definitions::rule_refs(
            rule,
            |_| Ok(()),
            |span| relocate_span(span, files),
        )?;
    }
    let mut pending: Vec<_> = source.commands.iter_mut().collect();
    while let Some(command) = pending.pop() {
        relocate_span(&mut command.span, files)?;
        match &mut command.kind {
            Some(pb::command::Kind::Action(action)) => relocate_span(&mut action.span, files)?,
            Some(pb::command::Kind::Fail(child)) => pending.push(child),
            Some(pb::command::Kind::Loop(body)) => pending.extend(&mut body.body),
            _ => (),
        }
    }
    destination.sorts.append(&mut source.sorts);
    destination.nodes.append(&mut source.nodes);
    destination.files.append(&mut source.files);
    destination.rulesets.append(&mut source.rulesets);
    destination.commands.append(&mut source.commands);
    Ok(())
}

/// Rule syntax owns only its reachable graph. Source blobs are shared by all
/// rules from one submission; spans address this shared provenance arena.
pub(super) struct RuleRecord {
    pub program: pb::Program,
    pub files: Arc<Vec<pb::SourceFile>>,
}

/// Import one rule's graph and its submission provenance once per output.
/// File identity is presentation only, so distinct submissions may keep equal
/// file records. No source blob is copied once per rule in the same submission.
pub(super) fn append_rule(
    destination: &mut pb::Program,
    record: &RuleRecord,
    file_offsets: &mut HashMap<usize, u32>,
) -> Result<pb::Rule, String> {
    let identity = Arc::as_ptr(&record.files) as usize;
    let offset = if let Some(offset) = file_offsets.get(&identity) {
        *offset
    } else {
        let offset = u32::try_from(destination.files.len()).map_err(|_| "too many files")?;
        destination.files.extend(record.files.iter().cloned());
        file_offsets.insert(identity, offset);
        offset
    };
    append(destination, &record.program, offset)?;
    let binding = destination
        .rulesets
        .pop()
        .ok_or("missing owned rule binding")?;
    binding
        .value
        .and_then(|mut value| value.rules.pop())
        .ok_or_else(|| "missing owned rule".into())
}

fn relocate_span(span: &mut Option<pb::Span>, offset: u32) -> Result<(), String> {
    if let Some(span) = span {
        span.file = span.file.checked_add(offset).ok_or("too many files")?;
    }
    Ok(())
}

fn sort_refs(
    sort: &mut pb::Sort,
    mut visit: impl FnMut(&mut u32) -> Result<(), String>,
) -> Result<(), String> {
    match &mut sort.kind {
        Some(pb::sort::Kind::Application(family)) => {
            for index in &mut family.args {
                visit(index)?;
            }
        }
        Some(pb::sort::Kind::Func(function)) => {
            for index in function.params.iter_mut().chain([&mut function.result]) {
                visit(index)?;
            }
        }
        Some(pb::sort::Kind::Eq(_) | pb::sort::Kind::Var(_)) => (),
        None => return Err("missing sort kind".into()),
    }
    Ok(())
}

/// Copy exactly one rooted rule graph. Numbering follows ordered roots/edges,
/// independent of source arena allocation, and allocates before following edges
/// so both shared locations and Union cycles survive.
pub(super) fn rule(source: &pb::Program, rule: &pb::Rule) -> Result<pb::Program, String> {
    let mut result = pb::Program::default();
    let mut indices = HashMap::new();
    let mut import = |index: &mut u32, nodes: &mut Vec<pb::Node>| -> Result<(), String> {
        let next = u32::try_from(nodes.len()).map_err(|_| "too many rule nodes")?;
        let local = match indices.entry(*index) {
            std::collections::hash_map::Entry::Occupied(entry) => *entry.get(),
            std::collections::hash_map::Entry::Vacant(entry) => {
                let node = source
                    .nodes
                    .get(*index as usize)
                    .ok_or("rule node out of bounds")?;
                nodes.push(node.clone());
                entry.insert(next);
                next
            }
        };
        *index = local;
        Ok(())
    };
    let mut rule = rule.clone();
    crate::builtin::definitions::rule_refs(
        &mut rule,
        |index| import(index, &mut result.nodes),
        |_| Ok(()),
    )?;
    let mut cursor = 0;
    while cursor < result.nodes.len() {
        let mut node = std::mem::take(&mut result.nodes[cursor]);
        source::source_node_refs(&mut node, |index| import(index, &mut result.nodes))?;
        result.nodes[cursor] = node;
        cursor += 1;
    }
    // Sorts are structural, not identity-bearing locations. Intern normalized
    // kinds once instead of embedding recursively expanded type strings.
    fn sort(
        source: &[pb::Sort],
        index: u32,
        result: &mut Vec<pb::Sort>,
        mapping: &mut HashMap<u32, u32>,
        interned: &mut HashMap<Vec<u8>, u32>,
    ) -> Result<u32, String> {
        if let Some(index) = mapping.get(&index) {
            return Ok(*index);
        }
        let mut value = source
            .get(index as usize)
            .ok_or("rule sort out of bounds")?
            .clone();
        sort_refs(&mut value, |child| {
            *child = sort(source, *child, result, mapping, interned)?;
            Ok(())
        })?;
        let mut semantic = value.clone();
        semantic.span = None;
        let key = semantic.encode_to_vec();
        let next = u32::try_from(result.len()).map_err(|_| "too many rule sorts")?;
        let local = *interned.entry(key).or_insert_with(|| {
            result.push(value);
            next
        });
        mapping.insert(index, local);
        Ok(local)
    }
    let mut mapping = HashMap::new();
    let mut interned = HashMap::new();
    for node in &mut result.nodes {
        node.sort_id = sort(
            &source.sorts,
            node.sort_id,
            &mut result.sorts,
            &mut mapping,
            &mut interned,
        )?;
    }
    result.rulesets.push(pb::RulesetBinding {
        name: String::new(),
        value: Some(pb::Ruleset { rules: vec![rule] }),
    });
    Ok(result)
}

/// A linear rooted syntax key: metadata does not establish identity and every
/// represented node-sharing edge remains observable in the canonical bytes.
pub(super) fn rule_key(rule: &pb::Program) -> Result<Vec<u8>, String> {
    let mut key = rule.clone();
    key.files.clear();
    // Saved-code bodies own positional binders. Conservatively retain spelling
    // for every node reachable inside one, including a node also shared with
    // the surrounding rule. Outside those bodies, _0 is an ordinary rule
    // variable and must normalize like any other spelling.
    let mut bodies = std::collections::HashSet::new();
    let mut pending: Vec<_> = key
        .nodes
        .iter()
        .filter_map(|node| match &node.kind {
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Lambda(lambda)),
            })) => Some(lambda.body),
            _ => None,
        })
        .collect();
    while let Some(index) = pending.pop() {
        if bodies.insert(index) {
            let mut node = key.nodes[index as usize].clone();
            source::source_node_refs(&mut node, |index| {
                pending.push(*index);
                Ok(())
            })?;
        }
    }
    let mut outer = std::collections::HashSet::new();
    let mut roots = rules(&key).next().ok_or("missing owned rule")?.clone();
    let mut pending = vec![];
    crate::builtin::definitions::rule_refs(
        &mut roots,
        |index| {
            pending.push(*index);
            Ok(())
        },
        |_| Ok(()),
    )?;
    while let Some(index) = pending.pop() {
        if outer.insert(index) {
            let mut node = key.nodes[index as usize].clone();
            if let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Lambda(lambda)),
            })) = &mut node.kind
            {
                pending.extend(&lambda.captures);
            } else {
                source::source_node_refs(&mut node, |index| {
                    pending.push(*index);
                    Ok(())
                })?;
            }
        }
    }
    // If one raw variable location is used in both binders, its spelling links
    // the outer binding to the fixed positional parameter. Preserve that outer
    // name consistently at all its locations, rather than merging two binders.
    let fixed: std::collections::HashSet<_> = outer
        .intersection(&bodies)
        .filter_map(|index| match &key.nodes[*index as usize].kind {
            Some(pb::node::Kind::Var(name)) => Some(name.clone()),
            _ => None,
        })
        .collect();
    let mut variables = HashMap::new();
    for (index, node) in key.nodes.iter_mut().enumerate() {
        node.span = None;
        if let Some(pb::node::Kind::Var(name)) = &mut node.kind
            && !bodies.contains(&(index as u32))
            && !fixed.contains(name)
        {
            let next = variables.len();
            *name = variables
                .entry(name.clone())
                .or_insert_with(|| format!("v{next}"))
                .clone();
        }
    }
    for sort in &mut key.sorts {
        sort.span = None;
    }
    for rule in rules_mut(&mut key) {
        rule.name = None;
        rule.doc.clear();
        crate::builtin::definitions::rule_refs(
            rule,
            |_| Ok(()),
            |span| {
                *span = None;
                Ok(())
            },
        )?;
    }
    // Separate Var syntax locations in the same ordinary binder denote one
    // binding. Preserve all nonvariable graph-sharing edges, but quotient these
    // variable copies before numbering the rooted key graph again.
    let nodes = std::mem::take(&mut key.nodes);
    let mut mapping = HashMap::new();
    let mut bindings = HashMap::new();
    let mut import = |index: &mut u32, destination: &mut Vec<pb::Node>| -> Result<(), String> {
        if let Some(local) = mapping.get(index) {
            *index = *local;
            return Ok(());
        }
        let source = *index;
        let node = &nodes[source as usize];
        let binding = match &node.kind {
            Some(pb::node::Kind::Var(name))
                if !bodies.contains(&source) && !fixed.contains(name) =>
            {
                Some((node.sort_id, name.clone()))
            }
            _ => None,
        };
        let local = binding
            .as_ref()
            .and_then(|binding| bindings.get(binding))
            .copied()
            .unwrap_or_else(|| {
                let local = destination.len() as u32;
                destination.push(node.clone());
                if let Some(binding) = binding {
                    bindings.insert(binding, local);
                }
                local
            });
        mapping.insert(source, local);
        *index = local;
        Ok(())
    };
    let mut roots = rules(&key).next().ok_or("missing owned rule")?.clone();
    crate::builtin::definitions::rule_refs(
        &mut roots,
        |index| import(index, &mut key.nodes),
        |span| {
            *span = None;
            Ok(())
        },
    )?;
    *rules_mut(&mut key)
        .into_iter()
        .next()
        .ok_or("missing owned rule")? = roots;
    let mut cursor = 0;
    while cursor < key.nodes.len() {
        let mut node = std::mem::take(&mut key.nodes[cursor]);
        source::source_node_refs(&mut node, |index| import(index, &mut key.nodes))?;
        key.nodes[cursor] = node;
        cursor += 1;
    }
    Ok(key.encode_to_vec())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture(name: &str) -> pb::Program {
        pb::Program {
            rulesets: vec![pb::RulesetBinding {
                name: String::new(),
                value: Some(pb::Ruleset {
                    rules: vec![pb::Rule {
                        eval_mode: pb::RuleEvalMode::Seminaive.into(),
                        kind: Some(pb::rule::Kind::Rule(pb::RuleBody {
                            query: vec![0],
                            head: vec![pb::Action {
                                kind: Some(pb::action::Kind::Term(1)),
                                ..Default::default()
                            }],
                        })),
                        ..Default::default()
                    }],
                }),
            }],

            sorts: vec![pb::Sort {
                kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                    name: "i64".into(),
                    args: vec![],
                })),
                ..Default::default()
            }],
            nodes: vec![
                pb::Node {
                    kind: Some(pb::node::Kind::Var(name.into())),
                    ..Default::default()
                },
                pb::Node {
                    kind: Some(pb::node::Kind::Call(pb::Call {
                        func: "output".into(),
                        args: vec![0, 0],
                    })),
                    ..Default::default()
                },
            ],
            commands: vec![],
            ..Default::default()
        }
    }

    #[test]
    fn content_key_ignores_metadata_allocation_and_outer_binder_spelling() {
        let source = fixture("_0");
        let expected = rule_key(&rule(&source, rules(&source).next().unwrap()).unwrap()).unwrap();
        let mut changed = fixture("x");
        rules_mut(&mut changed).into_iter().next().unwrap().name = Some("diagnostic".into());
        rules_mut(&mut changed).into_iter().next().unwrap().doc = "documentation".into();
        rules_mut(&mut changed).into_iter().next().unwrap().span = Some(pb::Span {
            file: 0,
            start: 0,
            end: 1,
        });
        changed.files.push(pb::SourceFile {
            name: "rule.egg".into(),
            contents: Some("x".into()),
        });
        changed.nodes.insert(0, pb::Node::default());
        let mut body = rules(&changed).next().unwrap().clone();
        crate::builtin::definitions::rule_refs(
            &mut body,
            |index| {
                *index += 1;
                Ok(())
            },
            |_| Ok(()),
        )
        .unwrap();
        *rules_mut(&mut changed).into_iter().next().unwrap() = body;
        changed.nodes[2].kind = Some(pb::node::Kind::Call(pb::Call {
            func: "output".into(),
            args: vec![1, 1],
        }));
        assert_eq!(
            expected,
            rule_key(&rule(&changed, rules(&changed).next().unwrap()).unwrap()).unwrap()
        );
        rules_mut(&mut changed)
            .into_iter()
            .next()
            .unwrap()
            .no_decomp = true;
        assert_ne!(
            expected,
            rule_key(&rule(&changed, rules(&changed).next().unwrap()).unwrap()).unwrap()
        );
    }

    #[test]
    fn content_key_preserves_sharing_and_lambda_positional_binding() {
        let source = fixture("_0");
        let expected = rule_key(&rule(&source, rules(&source).next().unwrap()).unwrap()).unwrap();
        let mut changed = source.clone();
        changed.nodes.push(changed.nodes[0].clone());
        let Some(pb::node::Kind::Call(call)) = &mut changed.nodes[1].kind else {
            unreachable!()
        };
        call.args[1] = 2;
        assert_eq!(
            expected,
            rule_key(&rule(&changed, rules(&changed).next().unwrap()).unwrap()).unwrap()
        );
        let mut changed = source.clone();
        changed.nodes.push(changed.nodes[1].clone());
        let Some(pb::rule::Kind::Rule(body)) =
            &mut rules_mut(&mut changed).into_iter().next().unwrap().kind
        else {
            unreachable!()
        };
        body.head.push(pb::Action {
            kind: Some(pb::action::Kind::Term(2)),
            ..Default::default()
        });
        let separate_calls =
            rule_key(&rule(&changed, rules(&changed).next().unwrap()).unwrap()).unwrap();
        let Some(pb::rule::Kind::Rule(body)) =
            &mut rules_mut(&mut changed).into_iter().next().unwrap().kind
        else {
            unreachable!()
        };
        body.head[1].kind = Some(pb::action::Kind::Term(1));
        assert_ne!(
            separate_calls,
            rule_key(&rule(&changed, rules(&changed).next().unwrap()).unwrap()).unwrap()
        );

        let mut shared = source.clone();
        shared.nodes.push(pb::Node {
            kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Lambda(pb::Lambda {
                    captures: vec![],
                    body: 0,
                })),
            })),
            ..Default::default()
        });
        let Some(pb::rule::Kind::Rule(body)) =
            &mut rules_mut(&mut shared).into_iter().next().unwrap().kind
        else {
            unreachable!()
        };
        body.head.push(pb::Action {
            kind: Some(pb::action::Kind::Term(2)),
            ..Default::default()
        });
        let shared_key = rule_key(&rule(&shared, rules(&shared).next().unwrap()).unwrap()).unwrap();
        shared.nodes[0].kind = Some(pb::node::Kind::Var("_1".into()));
        assert_ne!(
            shared_key,
            rule_key(&rule(&shared, rules(&shared).next().unwrap()).unwrap()).unwrap()
        );

        // Equal positional spellings in distinct locations do not bind an
        // unrelated ordinary query variable to the lambda's parameter.
        let mut separate = source.clone();
        separate.nodes.push(source.nodes[0].clone());
        separate.nodes.push(pb::Node {
            kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Lambda(pb::Lambda {
                    captures: vec![],
                    body: 2,
                })),
            })),
            ..Default::default()
        });
        let Some(pb::rule::Kind::Rule(body)) =
            &mut rules_mut(&mut separate).into_iter().next().unwrap().kind
        else {
            unreachable!()
        };
        body.head.push(pb::Action {
            kind: Some(pb::action::Kind::Term(3)),
            ..Default::default()
        });
        let separate_key =
            rule_key(&rule(&separate, rules(&separate).next().unwrap()).unwrap()).unwrap();
        separate.nodes[0].kind = Some(pb::node::Kind::Var("x".into()));
        assert_eq!(
            separate_key,
            rule_key(&rule(&separate, rules(&separate).next().unwrap()).unwrap()).unwrap()
        );
    }
}
