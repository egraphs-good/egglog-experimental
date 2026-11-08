//! Arena relocation shared by accumulated inputs and owned rule diagnostics.

use super::{Declaration, DeclarationMut, declarations, declarations_mut, pb, source};
use prost::Message;
use std::collections::{HashMap, HashSet};
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
pub(super) fn append(destination: &mut pb::Program, source: &pb::Program) -> Result<(), String> {
    let mut source = source.clone();
    source.constructors.clear();
    source.functions.clear();
    source.relations.clear();
    source.user_defined_primitives.clear();
    let mut source = relocate(
        source,
        u32::try_from(destination.nodes.len()).map_err(|_| "too many nodes")?,
        u32::try_from(destination.sorts.len()).map_err(|_| "too many sorts")?,
    )?;
    destination.sorts.append(&mut source.sorts);
    destination.nodes.append(&mut source.nodes);
    destination.rulesets.append(&mut source.rulesets);
    destination.commands.append(&mut source.commands);
    Ok(())
}

/// Relocate a graph once, including declaration signature and deferred-body
/// references. Named identity is unchanged; this operation never executes code.
fn relocate(mut source: pb::Program, nodes: u32, sorts: u32) -> Result<pb::Program, String> {
    source::source_phase_refs(&mut source, |index| {
        *index = index.checked_add(nodes).ok_or("too many nodes")?;
        Ok(())
    })?;
    for node in &mut source.nodes {
        node.sort_id = node.sort_id.checked_add(sorts).ok_or("too many sorts")?;
        source::source_node_refs(node, |index| {
            *index = index.checked_add(nodes).ok_or("too many nodes")?;
            Ok(())
        })?;
    }
    for sort in &mut source.sorts {
        sort_refs(sort, |index| {
            *index = index.checked_add(sorts).ok_or("too many sorts")?;
            Ok(())
        })?;
    }
    for declaration in declarations_mut(&mut source) {
        let (inputs, output) = match declaration {
            DeclarationMut::Constructor(d) => (&mut d.inputs, Some(&mut d.output)),
            DeclarationMut::Function(d) => (&mut d.inputs, Some(&mut d.output)),
            DeclarationMut::Relation(d) => (&mut d.inputs, None),
            DeclarationMut::UserDefinedPrimitive(d) => (&mut d.inputs, Some(&mut d.output)),
        };
        for input in inputs {
            *input = input.checked_add(sorts).ok_or("too many sorts")?;
        }
        if let Some(output) = output {
            *output = output.checked_add(sorts).ok_or("too many sorts")?;
        }
    }
    Ok(source)
}

/// An installed rule owns its compact authored graph across requests.
pub(super) struct RuleRecord {
    pub program: Arc<pb::Program>,
}

/// Proven correspondence to one immutable authored recipe, not structural CSE.
pub(super) type RuleAliases = HashMap<u32, (Arc<RuleRecord>, u32)>;

fn code_body_nodes(program: &pb::Program) -> Result<HashSet<u32>, String> {
    let mut bodies = HashSet::new();
    let mut pending: Vec<_> = program
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
            let mut node = program
                .nodes
                .get(index as usize)
                .ok_or("code body node out of bounds")?
                .clone();
            source::source_node_refs(&mut node, |child| {
                pending.push(*child);
                Ok(())
            })?;
        }
    }
    Ok(bodies)
}

/// Context compaction may identify same-kind sort aliases. Recording can reuse
/// its node correspondence only when every referenced sort retains all metadata.
pub(super) fn preserves_sort_metadata(
    source: &pb::Program,
    owned: &pb::Program,
    nodes: &HashMap<u32, u32>,
) -> Result<bool, String> {
    let mut pending: Vec<_> = nodes
        .iter()
        .map(|(source_index, owned_index)| {
            (
                source.nodes[*source_index as usize].sort_id,
                owned.nodes[*owned_index as usize].sort_id,
            )
        })
        .collect();
    let mut seen = HashSet::new();
    while let Some((left, right)) = pending.pop() {
        if !seen.insert((left, right)) {
            continue;
        }
        let mut left = source
            .sorts
            .get(left as usize)
            .ok_or("source recipe sort out of bounds")?
            .clone();
        let mut right = owned
            .sorts
            .get(right as usize)
            .ok_or("owned recipe sort out of bounds")?
            .clone();
        let mut left_children = vec![];
        let mut right_children = vec![];
        sort_refs(&mut left, |child| {
            left_children.push(*child);
            *child = 0;
            Ok(())
        })?;
        sort_refs(&mut right, |child| {
            right_children.push(*child);
            *child = 0;
            Ok(())
        })?;
        if left != right || left_children.len() != right_children.len() {
            return Ok(false);
        }
        pending.extend(left_children.into_iter().zip(right_children));
    }
    Ok(true)
}

/// Indices shared by one recording export, never rescanning its growing prefix.
pub(super) struct RecordedStorage {
    recipes: HashMap<(usize, u32), u32>,
    sorts: HashMap<Vec<u8>, u32>,
    bindings: HashMap<(String, u32), u32>,
}

impl RecordedStorage {
    pub(super) fn new(destination: &pb::Program) -> Self {
        Self {
            recipes: HashMap::new(),
            sorts: destination
                .sorts
                .iter()
                .enumerate()
                .map(|(index, sort)| (sort.encode_to_vec(), index as u32))
                .collect(),
            bindings: destination
                .nodes
                .iter()
                .enumerate()
                .filter_map(|(index, node)| {
                    if let Some(pb::node::Kind::Binding(name)) = &node.kind {
                        Some(((name.clone(), node.sort_id), index as u32))
                    } else {
                        None
                    }
                })
                .collect(),
        }
    }

    /// Share sorts, named leaves and proven private recipe copies. Calls and Eq
    /// locations otherwise remain positional.
    pub(super) fn append(
        &mut self,
        destination: &mut pb::Program,
        source: &pb::Program,
        aliases: &RuleAliases,
    ) -> Result<(), String> {
        fn import_sort(
            source: &[pb::Sort],
            index: u32,
            destination: &mut Vec<pb::Sort>,
            mapping: &mut HashMap<u32, u32>,
            active: &mut HashSet<u32>,
            shared: &mut HashMap<Vec<u8>, u32>,
        ) -> Result<u32, String> {
            if let Some(local) = mapping.get(&index) {
                return Ok(*local);
            }
            if !active.insert(index) {
                return Err("cyclic recorded sort".into());
            }
            let mut sort = source
                .get(index as usize)
                .ok_or("recorded sort out of bounds")?
                .clone();
            sort_refs(&mut sort, |child| {
                *child = import_sort(source, *child, destination, mapping, active, shared)?;
                Ok(())
            })?;
            active.remove(&index);
            // Documentation is retained too: differing metadata is not discarded.
            let key = sort.encode_to_vec();
            let local = if let Some(local) = shared.get(&key) {
                *local
            } else {
                let local =
                    u32::try_from(destination.len()).map_err(|_| "too many recorded sorts")?;
                destination.push(sort);
                shared.insert(key, local);
                local
            };
            mapping.insert(index, local);
            Ok(local)
        }
        let mut sorts = HashMap::new();
        for index in 0..source.sorts.len() {
            import_sort(
                &source.sorts,
                index as u32,
                &mut destination.sorts,
                &mut sorts,
                &mut HashSet::new(),
                &mut self.sorts,
            )?;
        }
        // A raw Var location can be used in more than one ordinary binder. Include
        // its full membership set, and never enter a lambda's positional body.
        let mut binders: HashMap<u32, Vec<usize>> = HashMap::new();
        for (binder, rule) in rules(source).enumerate() {
            let mut rule = rule.clone();
            let mut pending = vec![];
            crate::builtin::definitions::rule_refs(&mut rule, |index| {
                pending.push(*index);
                Ok(())
            })?;
            let mut seen = HashSet::new();
            while let Some(index) = pending.pop() {
                if !seen.insert(index) {
                    continue;
                }
                let mut node = source
                    .nodes
                    .get(index as usize)
                    .ok_or("recorded rule node out of bounds")?
                    .clone();
                if matches!(node.kind, Some(pb::node::Kind::Var(_))) {
                    binders.entry(index).or_default().push(binder);
                }
                if let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Lambda(lambda)),
                })) = &node.kind
                {
                    pending.extend(&lambda.captures);
                } else {
                    source::source_node_refs(&mut node, |child| {
                        pending.push(*child);
                        Ok(())
                    })?;
                }
            }
        }
        // A raw Var may link an ordinary binder to positional saved code. Keep
        // that link and same-name ordinary copies distinct, as rule_key does.
        let bodies = code_body_nodes(source)?;
        let mut fixed: HashMap<usize, HashSet<String>> = HashMap::new();
        for (index, binders) in &binders {
            if bodies.contains(index)
                && let Some(pb::node::Kind::Var(name)) = &source.nodes[*index as usize].kind
            {
                for binder in binders {
                    fixed.entry(*binder).or_default().insert(name.clone());
                }
            }
        }
        let mut variables = HashMap::new();
        let mut nodes = HashMap::new();
        let mut allocated = vec![];
        for (index, node) in source.nodes.iter().enumerate() {
            let index = index as u32;
            let sort = sorts[&node.sort_id];
            let recipe = aliases
                .get(&index)
                .map(|(owner, index)| (Arc::as_ptr(owner) as usize, *index));
            let binding = match &node.kind {
                Some(pb::node::Kind::Binding(name)) => Some((name.clone(), sort)),
                _ => None,
            };
            let variable = match (&node.kind, binders.get(&index)) {
                (Some(pb::node::Kind::Var(name)), Some(binders))
                    if !binders.iter().any(|binder| {
                        fixed.get(binder).is_some_and(|names| names.contains(name))
                    }) =>
                {
                    Some((binders.clone(), name.clone(), sort))
                }
                _ => None,
            };
            let existing = recipe
                .and_then(|key| self.recipes.get(&key).copied())
                .or_else(|| {
                    binding
                        .as_ref()
                        .and_then(|key| self.bindings.get(key).copied())
                })
                .or_else(|| {
                    variable
                        .as_ref()
                        .and_then(|key| variables.get(key).copied())
                });
            let local = if let Some(local) = existing {
                local
            } else {
                let local = u32::try_from(destination.nodes.len())
                    .map_err(|_| "too many recorded nodes")?;
                destination.nodes.push(pb::Node::default());
                allocated.push((index, local));
                local
            };
            nodes.insert(index, local);
            if let Some(key) = recipe {
                self.recipes.insert(key, local);
            }
            if let Some(key) = binding {
                self.bindings.insert(key, local);
            }
            if let Some(key) = variable {
                variables.insert(key, local);
            }
        }
        for (index, local) in allocated {
            let mut node = source.nodes[index as usize].clone();
            node.sort_id = sorts[&node.sort_id];
            source::source_node_refs(&mut node, |child| {
                *child = *nodes
                    .get(child)
                    .ok_or("recorded node reference out of bounds")?;
                Ok(())
            })?;
            destination.nodes[local as usize] = node;
        }
        let mut source = source.clone();
        source.nodes.clear();
        source.sorts.clear();
        source.constructors.clear();
        source.functions.clear();
        source.relations.clear();
        source.user_defined_primitives.clear();
        source::source_phase_refs(&mut source, |index| {
            *index = *nodes.get(index).ok_or("recorded root out of bounds")?;
            Ok(())
        })?;
        destination.rulesets.extend(source.rulesets);
        destination.commands.extend(source.commands);
        Ok(())
    }
}

/// Import one rule's arenas, retaining their shared node identities.
pub(super) fn append_rule(
    destination: &mut pb::Program,
    record: &RuleRecord,
) -> Result<pb::Rule, String> {
    append(destination, &record.program)?;
    destination
        .rulesets
        .pop()
        .and_then(|binding| binding.value)
        .and_then(|mut value| value.rules.pop())
        .ok_or_else(|| "missing owned rule".into())
}

fn sort_refs(
    sort: &mut pb::Sort,
    mut visit: impl FnMut(&mut u32) -> Result<(), String>,
) -> Result<(), String> {
    match &mut sort.kind {
        Some(pb::sort::Kind::Primitive(family)) => {
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

/// Copy one rule without changing identity-bearing graph sharing.
pub(super) fn rule(source: &pb::Program, rule: &pb::Rule) -> Result<pb::Program, String> {
    let fragment = pb::Program {
        rulesets: vec![pb::RulesetBinding {
            name: String::new(),
            value: Some(pb::Ruleset {
                rules: vec![rule.clone()],
            }),
        }],
        ..Default::default()
    };
    compact(source, fragment).map(|(program, _)| program)
}

/// Build the response only after a failure escapes. The native token owns
/// just its authored fragment; live immutable definitions supply named callees.
pub(super) fn error_context(
    owner: &pb::Program,
    definitions: &pb::Program,
) -> Result<(pb::Program, HashMap<u32, u32>), String> {
    let mut source = owner.clone();
    let mut installed = relocate(
        definitions.clone(),
        u32::try_from(source.nodes.len()).map_err(|_| "too many nodes")?,
        u32::try_from(source.sorts.len()).map_err(|_| "too many sorts")?,
    )?;
    source.nodes.append(&mut installed.nodes);
    source.sorts.append(&mut installed.sorts);
    source.constructors.append(&mut installed.constructors);
    source.functions.append(&mut installed.functions);
    source.relations.append(&mut installed.relations);
    source
        .user_defined_primitives
        .append(&mut installed.user_defined_primitives);
    let mut fragment = owner.clone();
    fragment.nodes.clear();
    fragment.sorts.clear();
    context(&source, fragment)
}

/// Traverse each node and named declaration once, then retain selected
/// declarations in source order. Recursive calls need no recursive traversal.
fn context(
    source: &pb::Program,
    mut fragment: pb::Program,
) -> Result<(pb::Program, HashMap<u32, u32>), String> {
    enum Pending {
        Node(u32),
        Callable(String),
    }
    let mut declarations_by_name = HashMap::new();
    for declaration in declarations(source) {
        let name = match declaration {
            Declaration::Constructor(d) => &d.name,
            Declaration::Function(d) => &d.name,
            Declaration::Relation(d) => &d.name,
            Declaration::UserDefinedPrimitive(d) => &d.name,
        };
        // The authored owner precedes compatible installed copies.
        declarations_by_name
            .entry(name.as_str())
            .or_insert(declaration);
    }
    let included: HashSet<String> = declarations(&fragment)
        .map(|d| match d {
            Declaration::Constructor(d) => d.name.clone(),
            Declaration::Function(d) => d.name.clone(),
            Declaration::Relation(d) => d.name.clone(),
            Declaration::UserDefinedPrimitive(d) => d.name.clone(),
        })
        .collect();
    let mut selected = HashSet::new();
    let mut pending = vec![];
    source::source_phase_refs(&mut fragment, |index| {
        pending.push(Pending::Node(*index));
        Ok(())
    })?;
    let mut names = HashSet::new();
    for rule in rules(&fragment) {
        if let Some(pb::rule::Kind::Rule(body)) = &rule.kind {
            for action in &body.actions {
                action_names(action, &mut names);
            }
        }
    }
    let mut commands: Vec<_> = fragment.commands.iter().collect();
    while let Some(command) = commands.pop() {
        match &command.kind {
            Some(pb::command::Kind::Action(action)) => action_names(action, &mut names),
            Some(pb::command::Kind::Loop(body)) => commands.extend(&body.body),
            Some(pb::command::Kind::Fail(child)) => commands.push(child),
            Some(pb::command::Kind::TableSizes(request)) => {
                names.extend(request.tables.iter().cloned())
            }
            Some(pb::command::Kind::TableRows(request)) => {
                names.insert(request.table.clone());
            }
            Some(pb::command::Kind::TableStats(request)) => {
                names.extend(request.tables.iter().cloned())
            }
            Some(pb::command::Kind::ProveExists(request)) => {
                names.insert(request.constructor.clone());
            }
            Some(pb::command::Kind::KeepBest(request)) => {
                names.extend(request.tables.iter().cloned())
            }
            _ => (),
        }
    }
    pending.extend(names.into_iter().map(Pending::Callable));
    let mut visited = HashSet::new();
    while let Some(next) = pending.pop() {
        match next {
            Pending::Node(index) => {
                if !visited.insert(index) {
                    continue;
                }
                let mut node = source
                    .nodes
                    .get(index as usize)
                    .ok_or("context node out of bounds")?
                    .clone();
                match &node.kind {
                    Some(pb::node::Kind::Call(call) | pb::node::Kind::GetCost(call)) => {
                        pending.push(Pending::Callable(call.func.clone()))
                    }
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::PartialCall(call)),
                    })) => pending.push(Pending::Callable(call.func.clone())),
                    _ => (),
                }
                source::source_node_refs(&mut node, |index| {
                    pending.push(Pending::Node(*index));
                    Ok(())
                })?;
            }
            Pending::Callable(name) => {
                if included.contains(&name) || !selected.insert(name.clone()) {
                    continue;
                }
                if let Some(declaration) = declarations_by_name.get(name.as_str()) {
                    let root = match declaration {
                        Declaration::Constructor(d) => d.cost,
                        Declaration::Function(d) => d.merge,
                        Declaration::Relation(_) => None,
                        Declaration::UserDefinedPrimitive(d) => d.body,
                    };
                    pending.extend(root.map(Pending::Node));
                }
            }
        }
    }
    for declaration in declarations(source) {
        let name = match declaration {
            Declaration::Constructor(d) => &d.name,
            Declaration::Function(d) => &d.name,
            Declaration::Relation(d) => &d.name,
            Declaration::UserDefinedPrimitive(d) => &d.name,
        };
        if !selected.remove(name) {
            continue;
        }
        match declaration {
            Declaration::Constructor(d) => fragment.constructors.push(d.clone()),
            Declaration::Function(d) => fragment.functions.push(d.clone()),
            Declaration::Relation(d) => fragment.relations.push(d.clone()),
            Declaration::UserDefinedPrimitive(d) => {
                fragment.user_defined_primitives.push(d.clone())
            }
        }
    }
    compact(source, fragment)
}

fn action_names(action: &pb::Action, names: &mut HashSet<String>) {
    let call = match &action.kind {
        Some(pb::action::Kind::Set(set)) => set.target.as_ref(),
        Some(pb::action::Kind::SetCost(set)) => set.target.as_ref(),
        Some(pb::action::Kind::Delete(call) | pb::action::Kind::Subsume(call)) => Some(call),
        _ => None,
    };
    if let Some(call) = call {
        names.insert(call.func.clone());
    }
}

/// Allocate before following node edges, preserving shared locations and Eq
/// cycles. The returned correspondence belongs only to this owned fragment.
pub(super) fn compact(
    source: &pb::Program,
    mut result: pb::Program,
) -> Result<(pb::Program, HashMap<u32, u32>), String> {
    let mut indices = HashMap::new();
    let mut nodes = vec![];
    let mut import = |index: &mut u32, nodes: &mut Vec<pb::Node>| -> Result<(), String> {
        let next = u32::try_from(nodes.len()).map_err(|_| "too many context nodes")?;
        let local = match indices.entry(*index) {
            std::collections::hash_map::Entry::Occupied(entry) => *entry.get(),
            std::collections::hash_map::Entry::Vacant(entry) => {
                nodes.push(
                    source
                        .nodes
                        .get(*index as usize)
                        .ok_or("context node out of bounds")?
                        .clone(),
                );
                entry.insert(next);
                next
            }
        };
        *index = local;
        Ok(())
    };
    source::source_phase_refs(&mut result, |index| import(index, &mut nodes))?;
    let mut cursor = 0;
    while cursor < nodes.len() {
        let mut node = std::mem::take(&mut nodes[cursor]);
        source::source_node_refs(&mut node, |index| import(index, &mut nodes))?;
        nodes[cursor] = node;
        cursor += 1;
    }
    result.nodes = nodes;
    let mut sorts = HashMap::new();
    for node in &mut result.nodes {
        node.sort_id =
            import_context_sort(&source.sorts, node.sort_id, &mut result.sorts, &mut sorts)?;
    }
    let mut context_sorts = std::mem::take(&mut result.sorts);
    for declaration in declarations_mut(&mut result) {
        let (inputs, output) = match declaration {
            DeclarationMut::Constructor(d) => (&mut d.inputs, Some(&mut d.output)),
            DeclarationMut::Function(d) => (&mut d.inputs, Some(&mut d.output)),
            DeclarationMut::Relation(d) => (&mut d.inputs, None),
            DeclarationMut::UserDefinedPrimitive(d) => (&mut d.inputs, Some(&mut d.output)),
        };
        for input in inputs {
            *input = import_context_sort(&source.sorts, *input, &mut context_sorts, &mut sorts)?;
        }
        if let Some(output) = output {
            *output = import_context_sort(&source.sorts, *output, &mut context_sorts, &mut sorts)?;
        }
    }
    result.sorts = context_sorts;
    Ok((result, indices))
}

fn import_context_sort(
    source: &[pb::Sort],
    index: u32,
    destination: &mut Vec<pb::Sort>,
    mapping: &mut HashMap<u32, u32>,
) -> Result<u32, String> {
    if let Some(local) = mapping.get(&index) {
        return Ok(*local);
    }
    // Sort arenas are validated as acyclic before authored runtime contexts exist.
    let mut sort = source
        .get(index as usize)
        .ok_or("context sort out of bounds")?
        .clone();
    sort_refs(&mut sort, |index| {
        *index = import_context_sort(source, *index, destination, mapping)?;
        Ok(())
    })?;
    if let Some(local) = destination.iter().position(|other| other.kind == sort.kind) {
        mapping.insert(index, local as u32);
        return Ok(local as u32);
    }
    let local = u32::try_from(destination.len()).map_err(|_| "too many context sorts")?;
    destination.push(sort);
    mapping.insert(index, local);
    Ok(local)
}

/// A linear rooted syntax key: metadata does not establish identity and every
/// represented node-sharing edge remains observable in the canonical bytes.
pub(super) fn rule_key(rule: &pb::Program) -> Result<Vec<u8>, String> {
    let mut key = rule.clone();
    // Saved-code bodies own positional binders. Conservatively retain spelling
    // for every node reachable inside one, including a node also shared with
    // the surrounding rule. Outside those bodies, _0 is an ordinary rule
    // variable and must normalize like any other spelling.
    let bodies = code_body_nodes(&key)?;
    let mut outer = std::collections::HashSet::new();
    let mut roots = rules(&key).next().ok_or("missing owned rule")?.clone();
    let mut pending = vec![];
    crate::builtin::definitions::rule_refs(&mut roots, |index| {
        pending.push(*index);
        Ok(())
    })?;
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
        sort.doc = None;
    }
    for rule in rules_mut(&mut key) {
        rule.name = None;
        rule.doc.clear();
        crate::builtin::definitions::rule_refs(rule, |_| Ok(()))?;
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
    crate::builtin::definitions::rule_refs(&mut roots, |index| import(index, &mut key.nodes))?;
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
                            actions: vec![pb::Action {
                                kind: Some(pb::action::Kind::Term(1)),
                            }],
                        })),
                        ..Default::default()
                    }],
                }),
            }],

            sorts: vec![pb::Sort {
                kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
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
    fn recorded_variables_keep_mixed_positional_body_aliases() {
        let source = pb::Program {
            sorts: vec![
                pb::Sort {
                    kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
                        name: "i64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Func(pb::FuncSort {
                        params: vec![0],
                        result: 0,
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
                        name: "Unit".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
            ],
            nodes: vec![
                pb::Node {
                    kind: Some(pb::node::Kind::Var("_0".into())),
                    ..Default::default()
                },
                pb::Node {
                    kind: Some(pb::node::Kind::Var("_0".into())),
                    ..Default::default()
                },
                pb::Node {
                    sort_id: 2,
                    kind: Some(pb::node::Kind::Call(pb::Call {
                        func: "source".into(),
                        args: vec![0, 1],
                    })),
                },
                pb::Node {
                    sort_id: 1,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Lambda(pb::Lambda {
                            captures: vec![],
                            body: 0,
                        })),
                    })),
                },
                pb::Node {
                    sort_id: 2,
                    kind: Some(pb::node::Kind::Call(pb::Call {
                        func: "sink".into(),
                        args: vec![3],
                    })),
                },
            ],
            relations: vec![
                pb::Relation {
                    name: "source".into(),
                    inputs: vec![0, 0],
                    ..Default::default()
                },
                pb::Relation {
                    name: "sink".into(),
                    inputs: vec![1],
                    ..Default::default()
                },
            ],
            rulesets: vec![pb::RulesetBinding {
                value: Some(pb::Ruleset {
                    rules: vec![pb::Rule {
                        kind: Some(pb::rule::Kind::Rule(pb::RuleBody {
                            query: vec![2],
                            actions: vec![pb::Action {
                                kind: Some(pb::action::Kind::Term(4)),
                            }],
                        })),
                        ..Default::default()
                    }],
                }),
                ..Default::default()
            }],
            ..Default::default()
        };
        let expected_key =
            rule_key(&rule(&source, rules(&source).next().unwrap()).unwrap()).unwrap();
        let mut exported = source.clone();
        exported.nodes.clear();
        exported.rulesets.clear();
        let mut storage = RecordedStorage::new(&exported);
        storage
            .append(&mut exported, &source, &RuleAliases::new())
            .unwrap();
        let saved = rules(&exported).next().unwrap();
        let Some(pb::rule::Kind::Rule(body)) = &saved.kind else {
            panic!("rule")
        };
        let Some(pb::node::Kind::Call(query)) = &exported.nodes[body.query[0] as usize].kind else {
            panic!("source")
        };
        assert_ne!(query.args[0], query.args[1]);
        let Some(pb::action::Kind::Term(head)) = body.actions[0].kind else {
            panic!("term")
        };
        let Some(pb::node::Kind::Call(sink)) = &exported.nodes[head as usize].kind else {
            panic!("sink")
        };
        let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Lambda(lambda)),
        })) = &exported.nodes[sink.args[0] as usize].kind
        else {
            panic!("lambda")
        };
        assert_eq!(lambda.body, query.args[0]);
        assert_ne!(lambda.body, query.args[1]);
        assert_eq!(
            rule_key(&rule(&exported, saved).unwrap()).unwrap(),
            expected_key
        );
    }

    #[test]
    fn content_key_ignores_metadata_allocation_and_outer_binder_spelling() {
        let source = fixture("_0");
        let expected = rule_key(&rule(&source, rules(&source).next().unwrap()).unwrap()).unwrap();
        let mut changed = fixture("x");
        rules_mut(&mut changed).into_iter().next().unwrap().name = Some("diagnostic".into());
        rules_mut(&mut changed).into_iter().next().unwrap().doc = "documentation".into();
        changed.nodes.insert(0, pb::Node::default());
        let mut body = rules(&changed).next().unwrap().clone();
        crate::builtin::definitions::rule_refs(&mut body, |index| {
            *index += 1;
            Ok(())
        })
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
        body.actions.push(pb::Action {
            kind: Some(pb::action::Kind::Term(2)),
        });
        let separate_calls =
            rule_key(&rule(&changed, rules(&changed).next().unwrap()).unwrap()).unwrap();
        let Some(pb::rule::Kind::Rule(body)) =
            &mut rules_mut(&mut changed).into_iter().next().unwrap().kind
        else {
            unreachable!()
        };
        body.actions[1].kind = Some(pb::action::Kind::Term(1));
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
        body.actions.push(pb::Action {
            kind: Some(pb::action::Kind::Term(2)),
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
        body.actions.push(pb::Action {
            kind: Some(pb::action::Kind::Term(3)),
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
