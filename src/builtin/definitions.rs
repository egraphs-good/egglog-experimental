//! Structural relocation and compatibility for canonical definition records.
//! No native values, executable bodies, or second signature model live here.

type HashMap<K, V> = std::collections::HashMap<K, V>;
type HashSet<T> = std::collections::HashSet<T>;
use crate::proto as pb;

/// A borrowed cross-kind view keeps one callable namespace and dependency graph
/// without introducing an owned declaration record beside the wire messages.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum Declaration<'a> {
    Constructor(&'a pb::Constructor),
    Function(&'a pb::Function),
    Relation(&'a pb::Relation),
    UserDefinedPrimitive(&'a pb::UserDefinedPrimitive),
}

pub(crate) enum DeclarationMut<'a> {
    Constructor(&'a mut pb::Constructor),
    Function(&'a mut pb::Function),
    Relation(&'a mut pb::Relation),
    UserDefinedPrimitive(&'a mut pb::UserDefinedPrimitive),
}

/// Locations remain stable when a later request appends a different kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum DeclarationIndex {
    Constructor(usize),
    Function(usize),
    Relation(usize),
    UserDefinedPrimitive(usize),
}

pub(crate) fn declarations(p: &pb::Program) -> impl Iterator<Item = Declaration<'_>> {
    p.constructors
        .iter()
        .map(Declaration::Constructor)
        .chain(p.functions.iter().map(Declaration::Function))
        .chain(p.relations.iter().map(Declaration::Relation))
        .chain(
            p.user_defined_primitives
                .iter()
                .map(Declaration::UserDefinedPrimitive),
        )
}

pub(crate) fn declarations_mut(p: &mut pb::Program) -> impl Iterator<Item = DeclarationMut<'_>> {
    p.constructors
        .iter_mut()
        .map(DeclarationMut::Constructor)
        .chain(p.functions.iter_mut().map(DeclarationMut::Function))
        .chain(p.relations.iter_mut().map(DeclarationMut::Relation))
        .chain(
            p.user_defined_primitives
                .iter_mut()
                .map(DeclarationMut::UserDefinedPrimitive),
        )
}

/// Keep membership against original kind-local indices while compacting each list.
pub(crate) fn retain_declarations(
    p: &mut pb::Program,
    mut keep: impl FnMut(DeclarationIndex) -> bool,
) {
    macro_rules! retain {
        ($field:ident, $kind:ident) => {{
            let mut index = 0;
            p.$field.retain(|_| {
                let retain = keep(DeclarationIndex::$kind(index));
                index += 1;
                retain
            });
        }};
    }
    retain!(constructors, Constructor);
    retain!(functions, Function);
    retain!(relations, Relation);
    retain!(user_defined_primitives, UserDefinedPrimitive);
}

/// Callable spellings share one namespace; sorts and bindings are separate.
fn declaration_identity(d: Declaration<'_>) -> Result<&str, String> {
    let name = match d {
        Declaration::Constructor(c) => &c.name,
        Declaration::Function(f) => &f.name,
        Declaration::Relation(r) => &r.name,
        Declaration::UserDefinedPrimitive(p) => &p.name,
    };
    if name.is_empty() {
        return Err("empty declaration name".into());
    }
    Ok(name)
}

/// Visits every node edge in the admitted saved-code/value shapes. Unknown
/// forms fail, rather than retaining an unrelocated or unchecked reference.
fn node_edges(
    kind: &mut pb::node::Kind,
    mut f: impl FnMut(&mut u32) -> Result<(), String>,
) -> Result<(), String> {
    use pb::{node::Kind as N, primitive_value::Value as V};
    match kind {
        N::Apply(apply) => {
            if let Some(function) = &mut apply.function {
                f(function)?;
            }
            for argument in &mut apply.args {
                f(argument)?;
            }
        }
        N::Call(c) | N::GetCost(c) => {
            for i in &mut c.args {
                f(i)?;
            }
        }
        N::Eq(u) => {
            for i in &mut u.members {
                f(i)?;
            }
        }
        N::Var(_) | N::Binding(_) => (),
        N::PrimitiveValue(p) => match p.value.as_mut().ok_or("missing primitive value")? {
            V::Vec(v) | V::Set(v) | V::Multiset(v) => {
                for i in &mut v.items {
                    f(i)?;
                }
            }
            V::Map(v) => {
                for pair in &mut v.entries {
                    f(pair.key.as_mut().ok_or("missing map key")?)?;
                    f(pair.value.as_mut().ok_or("missing map value")?)?;
                }
            }
            V::Pair(v) => {
                f(v.first.as_mut().ok_or("missing pair first")?)?;
                f(v.second.as_mut().ok_or("missing pair second")?)?;
            }
            V::Maybe(v) => {
                if let Some(i) = &mut v.value {
                    f(i)?;
                }
            }
            V::Custom(v) => {
                for i in &mut v.args {
                    f(i)?;
                }
            }
            V::PartialCall(c) => {
                for i in &mut c.args {
                    f(i)?;
                }
            }
            V::Lambda(_) => return Err("lambda declaration templates are not supported yet".into()),
            _ => (),
        },
    }
    Ok(())
}

fn declaration_refs(
    d: DeclarationMut<'_>,
    mut sort: impl FnMut(&mut u32) -> Result<(), String>,
    mut node: impl FnMut(&mut u32) -> Result<(), String>,
) -> Result<(), String> {
    let (inputs, output) = match d {
        DeclarationMut::Constructor(c) => {
            if let Some(i) = &mut c.cost {
                node(i)?;
            }
            (&mut c.inputs, Some(&mut c.output))
        }
        DeclarationMut::Function(c) => {
            if let Some(i) = &mut c.merge {
                node(i)?;
            }
            (&mut c.inputs, Some(&mut c.output))
        }
        DeclarationMut::Relation(r) => (&mut r.inputs, None),
        DeclarationMut::UserDefinedPrimitive(p) => {
            node(p.body.as_mut().ok_or("missing primitive body")?)?;
            (&mut p.inputs, Some(&mut p.output))
        }
    };
    for a in inputs {
        sort(a)?;
    }
    if let Some(output) = output {
        sort(output)?;
    }
    Ok(())
}

// Declaration bodies/costs and rules use the same canonical arenas.
fn import_arenas(source: &pb::Program, destination: &mut pb::Program) -> Result<Vec<u32>, String> {
    let mut input_sorts = source.sorts.clone();
    for sort in &mut input_sorts {
        if matches!(&sort.kind, Some(pb::sort::Kind::Eq(name)) if name.is_empty()) {
            return Err("equality sort name must not be empty".into());
        }
        if sort.doc.is_some() && !matches!(sort.kind, Some(pb::sort::Kind::Eq(_))) {
            return Err("sort docs require an equality sort".into());
        }
    }
    let mut sorts = Vec::new();
    for index in 0..input_sorts.len() {
        sorts.push(super::import_sort(
            &input_sorts,
            index as u32,
            &mut destination.sorts,
        )?);
    }
    Ok(sorts)
}

// One reference visitor serves import, structural comparison and retention.
pub(crate) fn rule_refs(
    rule: &mut pb::Rule,
    mut node: impl FnMut(&mut u32) -> Result<(), String>,
) -> Result<(), String> {
    match rule.kind.as_mut().ok_or("missing rule kind")? {
        pb::rule::Kind::Rule(rule) => {
            for root in &mut rule.query {
                node(root)?;
            }
            for action in &mut rule.actions {
                let call = match action.kind.as_mut().ok_or("missing action kind")? {
                    pb::action::Kind::Term(root) => {
                        node(root)?;
                        None
                    }
                    pb::action::Kind::Set(set) => {
                        node(set.value.as_mut().ok_or("missing set value")?)?;
                        Some(set.target.as_mut().ok_or("missing set target")?)
                    }
                    pb::action::Kind::SetCost(set) => {
                        node(set.cost.as_mut().ok_or("missing set-cost value")?)?;
                        Some(set.target.as_mut().ok_or("missing set-cost target")?)
                    }
                    pb::action::Kind::Delete(call) | pb::action::Kind::Subsume(call) => Some(call),
                    pb::action::Kind::Panic(_) => None,
                };
                if let Some(call) = call {
                    for arg in &mut call.args {
                        node(arg)?;
                    }
                }
            }
        }
        pb::rule::Kind::Rewrite(rule) => {
            node(&mut rule.lhs)?;
            node(&mut rule.rhs)?;
            for root in &mut rule.conditions {
                node(root)?;
            }
        }
        pb::rule::Kind::Birewrite(rule) => {
            node(&mut rule.lhs)?;
            node(&mut rule.rhs)?;
            for root in &mut rule.conditions {
                node(root)?;
            }
        }
    }
    Ok(())
}

struct NodeImport<'a> {
    source: &'a pb::Program,
    sorts: &'a [u32],
    nodes: &'a mut Vec<pb::Node>,
    imported: HashMap<u32, u32>,
    active: HashSet<u32>,
}

impl NodeImport<'_> {
    fn import(&mut self, index: u32) -> Result<u32, String> {
        enum Visit {
            Enter(u32),
            Finish(u32, pb::Node),
        }
        let mut pending = vec![Visit::Enter(index)];
        while let Some(visit) = pending.pop() {
            match visit {
                Visit::Enter(index) => {
                    if self.imported.contains_key(&index) {
                        continue;
                    }
                    if !self.active.insert(index) {
                        return Err("cyclic declaration template".into());
                    }
                    let mut node = self
                        .source
                        .nodes
                        .get(index as usize)
                        .ok_or("declaration node out of bounds")?
                        .clone();
                    node.sort_id = *self
                        .sorts
                        .get(node.sort_id as usize)
                        .ok_or("node sort out of bounds")?;
                    let mut children = Vec::new();
                    node_edges(node.kind.as_mut().ok_or("missing node kind")?, |child| {
                        children.push(*child);
                        Ok(())
                    })?;
                    pending.push(Visit::Finish(index, node));
                    pending.extend(children.into_iter().rev().map(Visit::Enter));
                }
                Visit::Finish(index, mut node) => {
                    node_edges(node.kind.as_mut().unwrap(), |child| {
                        *child = self.imported[child];
                        Ok(())
                    })?;
                    self.active.remove(&index);
                    let result = self
                        .nodes
                        .len()
                        .try_into()
                        .map_err(|_| "too many declaration nodes")?;
                    self.nodes.push(node);
                    self.imported.insert(index, result);
                }
            }
        }
        Ok(self.imported[&index])
    }
}

#[derive(Default)]
struct NodeComparison {
    pairs: HashSet<(u32, u32)>,
    unions: HashMap<u32, u32>,
    reverse: HashMap<u32, u32>,
}

impl NodeComparison {
    fn equal(&mut self, p: &pb::Program, a: u32, b: u32) -> Result<bool, String> {
        let left = p
            .nodes
            .get(a as usize)
            .ok_or("comparison node out of bounds")?;
        let right = p
            .nodes
            .get(b as usize)
            .ok_or("comparison node out of bounds")?;
        if left.sort_id != right.sort_id {
            return Ok(false);
        }
        if matches!(left.kind, Some(pb::node::Kind::Eq(_))) {
            if self.unions.get(&a).is_some_and(|old| *old != b)
                || self.reverse.get(&b).is_some_and(|old| *old != a)
            {
                return Ok(false);
            }
            self.unions.insert(a, b);
            self.reverse.insert(b, a);
        }
        if !self.pairs.insert((a, b)) {
            return Ok(true);
        }
        let mut left = left.kind.clone().ok_or("missing comparison node")?;
        let mut right = right.kind.clone().ok_or("missing comparison node")?;
        let mut lc = vec![];
        let mut rc = vec![];
        node_edges(&mut left, |i| {
            lc.push(*i);
            *i = 0;
            Ok(())
        })?;
        node_edges(&mut right, |i| {
            rc.push(*i);
            *i = 0;
            Ok(())
        })?;
        if left != right || lc.len() != rc.len() {
            return Ok(false);
        }
        for (a, b) in lc.into_iter().zip(rc) {
            if !self.equal(p, a, b)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

fn compatible_semantics(
    p: &pb::Program,
    a: Declaration<'_>,
    b: Declaration<'_>,
) -> Result<bool, String> {
    let mut roots = [vec![], vec![]];
    macro_rules! compare {
        ($a:expr, $b:expr, $kind:ident, $table:ident) => {{
            let mut records = [$a.clone(), $b.clone()];
            for (d, roots) in records.iter_mut().zip(&mut roots) {
                if let Some(pb::$table::TableName::DefaultName(name)) = &d.table_name
                    && d.name == *name
                {
                    d.table_name = None;
                }
                d.doc = None;
                declaration_refs(
                    DeclarationMut::$kind(d),
                    |_| Ok(()),
                    |i| {
                        roots.push(*i);
                        *i = 0;
                        Ok(())
                    },
                )?;
            }
            records[0] == records[1]
        }};
    }
    let equal = match (a, b) {
        (Declaration::Constructor(a), Declaration::Constructor(b)) => {
            compare!(a, b, Constructor, constructor)
        }
        (Declaration::Function(a), Declaration::Function(b)) => compare!(a, b, Function, function),
        (Declaration::Relation(a), Declaration::Relation(b)) => compare!(a, b, Relation, relation),
        (Declaration::UserDefinedPrimitive(a), Declaration::UserDefinedPrimitive(b)) => {
            let mut records = [a.clone(), b.clone()];
            for (d, roots) in records.iter_mut().zip(&mut roots) {
                d.doc = None;
                declaration_refs(
                    DeclarationMut::UserDefinedPrimitive(d),
                    |_| Ok(()),
                    |i| {
                        roots.push(*i);
                        *i = 0;
                        Ok(())
                    },
                )?;
            }
            records[0] == records[1]
        }
        _ => false,
    };
    if !equal || roots[0].len() != roots[1].len() {
        return Ok(false);
    }
    let mut comparison = NodeComparison::default();
    for (a, b) in roots[0].iter().zip(&roots[1]) {
        if !comparison.equal(p, *a, *b)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Transactionally imports and reconciles semantic declaration closures. The returned flags identify newly installed definitions
/// in source order; compatible resupplies never ask a native engine to redeclare.
pub fn reconcile_declarations(
    source: &pb::Program,
    destination: &mut pb::Program,
) -> Result<Vec<bool>, String> {
    let mut staged = destination.clone();
    let sorts = import_arenas(source, &mut staged)?;
    let mut importer = NodeImport {
        source,
        sorts: &sorts,
        nodes: &mut staged.nodes,
        imported: HashMap::default(),
        active: HashSet::default(),
    };
    // Typed binding leaves are setup metadata, including unused/unset slots.
    let mut bindings: HashMap<_, _> = importer
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(i, node)| {
            if let Some(pb::node::Kind::Binding(name)) = &node.kind {
                Some((name.clone(), (i as u32, node.sort_id)))
            } else {
                None
            }
        })
        .collect();
    for (index, node) in source.nodes.iter().enumerate() {
        let Some(pb::node::Kind::Binding(name)) = &node.kind else {
            continue;
        };
        let sort = *sorts
            .get(node.sort_id as usize)
            .ok_or("binding sort out of bounds")?;
        if let Some((old_index, old_sort)) = bindings.get(name) {
            if *old_sort != sort {
                return Err(format!("conflicting binding sort for {name}"));
            }
            importer.imported.insert(index as u32, *old_index);
        } else {
            let imported = importer.import(index as u32)?;
            bindings.insert(name.clone(), (imported, sort));
        }
    }
    let mut incoming = pb::Program {
        constructors: source.constructors.clone(),
        functions: source.functions.clone(),
        relations: source.relations.clone(),
        user_defined_primitives: source.user_defined_primitives.clone(),
        ..Default::default()
    };
    for d in declarations(&incoming) {
        declaration_identity(d)?;
    }
    for d in declarations_mut(&mut incoming) {
        declaration_refs(
            d,
            |i| {
                *i = *sorts
                    .get(*i as usize)
                    .ok_or("declaration sort out of bounds")?;
                Ok(())
            },
            |i| {
                *i = importer.import(*i)?;
                Ok(())
            },
        )?;
    }
    let mut added = vec![];
    for d in declarations(&incoming) {
        let identity = declaration_identity(d)?;
        let existing = declarations(&staged)
            .find(|old| declaration_identity(*old).ok() == Some(identity))
            .map(|old| compatible_semantics(&staged, old, d))
            .transpose()?;
        if let Some(compatible) = existing {
            if !compatible {
                return Err(format!("conflicting declaration {}", identity));
            }
            added.push(false);
        } else {
            match d {
                Declaration::Constructor(d) => staged.constructors.push(d.clone()),
                Declaration::Function(d) => staged.functions.push(d.clone()),
                Declaration::Relation(d) => staged.relations.push(d.clone()),
                Declaration::UserDefinedPrimitive(d) => {
                    staged.user_defined_primitives.push(d.clone())
                }
            }
            added.push(true);
        }
    }
    validate_semantics(&staged)?;
    retain_imported_closures(&mut staged, destination)?;
    *destination = staged;
    Ok(added)
}

// Reconciliation can retain old roots instead of the newly imported compatible
// copies. Drop only unreachable NEW arena entries; preexisting indices may also
// be addressed by a caller's in-progress commands and must remain stable.
fn retain_imported_closures(p: &mut pb::Program, previous: &pb::Program) -> Result<(), String> {
    let mut nodes = (0..previous.nodes.len() as u32).collect::<HashSet<_>>();
    let mut sorts = (0..previous.sorts.len() as u32).collect::<HashSet<_>>();
    let mut pending = nodes.iter().copied().collect::<Vec<_>>();
    pending.extend(p.nodes.iter().enumerate().filter_map(|(i, n)| {
        matches!(n.kind, Some(pb::node::Kind::Binding(_))).then_some(i as u32)
    }));
    sorts.extend(
        p.sorts
            .iter()
            .enumerate()
            .filter_map(|(i, s)| matches!(s.kind, Some(pb::sort::Kind::Eq(_))).then_some(i as u32)),
    );
    for d in declarations_mut(p) {
        declaration_refs(
            d,
            |i| {
                sorts.insert(*i);
                Ok(())
            },
            |i| {
                pending.push(*i);
                Ok(())
            },
        )?;
    }
    for rule in crate::protobuf::graph::rules_mut(p) {
        rule_refs(rule, |root| {
            pending.push(*root);
            Ok(())
        })?;
    }
    let mut walked = HashSet::default();
    while let Some(i) = pending.pop() {
        if !walked.insert(i) {
            continue;
        }
        nodes.insert(i);
        let n = &mut p.nodes[i as usize];
        sorts.insert(n.sort_id);
        node_edges(n.kind.as_mut().ok_or("missing retained node kind")?, |i| {
            pending.push(*i);
            Ok(())
        })?;
    }
    let mut pending = sorts.iter().copied().collect::<Vec<_>>();
    let mut walked = HashSet::default();
    while let Some(i) = pending.pop() {
        if !walked.insert(i) {
            continue;
        }
        sorts.insert(i);
        let s = &p.sorts[i as usize];
        if let Some(pb::sort::Kind::Primitive(f)) = &s.kind {
            pending.extend(&f.args);
        } else if let Some(pb::sort::Kind::Func(f)) = &s.kind {
            pending.extend(&f.params);
            pending.push(f.result);
        }
    }
    let mut node_map = vec![None; p.nodes.len()];
    let mut sort_map = vec![None; p.sorts.len()];
    for (keep, map) in [(&nodes, &mut node_map), (&sorts, &mut sort_map)] {
        let mut next = 0;
        for (i, slot) in map.iter_mut().enumerate() {
            if keep.contains(&(i as u32)) {
                *slot = Some(next);
                next += 1;
            }
        }
    }
    p.nodes = std::mem::take(&mut p.nodes)
        .into_iter()
        .enumerate()
        .filter_map(|(i, n)| nodes.contains(&(i as u32)).then_some(n))
        .collect();
    p.sorts = std::mem::take(&mut p.sorts)
        .into_iter()
        .enumerate()
        .filter_map(|(i, s)| sorts.contains(&(i as u32)).then_some(s))
        .collect();
    for n in &mut p.nodes {
        n.sort_id = sort_map[n.sort_id as usize].unwrap();
        node_edges(n.kind.as_mut().unwrap(), |i| {
            *i = node_map[*i as usize].unwrap();
            Ok(())
        })?;
    }
    for s in &mut p.sorts {
        if let Some(pb::sort::Kind::Primitive(f)) = &mut s.kind {
            for i in &mut f.args {
                *i = sort_map[*i as usize].unwrap();
            }
        } else if let Some(pb::sort::Kind::Func(f)) = &mut s.kind {
            for i in f.params.iter_mut().chain([&mut f.result]) {
                *i = sort_map[*i as usize].unwrap();
            }
        }
    }
    for d in declarations_mut(p) {
        declaration_refs(
            d,
            |i| {
                *i = sort_map[*i as usize].unwrap();
                Ok(())
            },
            |i| {
                *i = node_map[*i as usize].unwrap();
                Ok(())
            },
        )?;
    }
    for rule in crate::protobuf::graph::rules_mut(p) {
        rule_refs(rule, |root| {
            *root = node_map[*root as usize].unwrap();
            Ok(())
        })?;
    }
    Ok(())
}

fn pattern_scope(p: &pb::Program, index: u32, parameters: usize) -> Result<(), String> {
    let mut pending = vec![index];
    let mut seen = HashSet::default();
    while let Some(i) = pending.pop() {
        if !seen.insert(i) {
            continue;
        }
        match p
            .sorts
            .get(i as usize)
            .and_then(|s| s.kind.as_ref())
            .ok_or("signature sort out of bounds")?
        {
            pb::sort::Kind::Var(i) if *i as usize >= parameters => {
                return Err("unbound signature sort parameter".into());
            }
            pb::sort::Kind::Primitive(f) => {
                pending.extend(&f.args);
            }
            pb::sort::Kind::Eq(_) | pb::sort::Kind::Var(_) => (),
            pb::sort::Kind::Func(f) => {
                pending.extend(&f.params);
                pending.push(f.result);
            }
        }
    }
    Ok(())
}

/// Validate semantic signature scopes and authored primitive bodies without execution.
fn validate_semantics(p: &pb::Program) -> Result<(), String> {
    for d in declarations(p) {
        let (inputs, output) = match d {
            Declaration::Constructor(c) => (&c.inputs, Some(c.output)),
            Declaration::Function(f) => (&f.inputs, Some(f.output)),
            Declaration::Relation(r) => (&r.inputs, None),
            Declaration::UserDefinedPrimitive(primitive) => {
                let root = primitive.body.ok_or("missing primitive body")?;
                if p.nodes
                    .get(root as usize)
                    .ok_or("primitive body out of bounds")?
                    .sort_id
                    != primitive.output
                {
                    return Err("primitive body result sort mismatch".into());
                }
                // Scope belongs to this declaration, even when another
                // declaration shares the same imported body nodes.
                let mut pending = vec![root];
                let mut seen = HashSet::default();
                while let Some(i) = pending.pop() {
                    if !seen.insert(i) {
                        continue;
                    }
                    let node = p
                        .nodes
                        .get(i as usize)
                        .ok_or("primitive body node out of bounds")?;
                    pattern_scope(p, node.sort_id, 0)?;
                    let mut kind = node.kind.clone().ok_or("missing primitive body node")?;
                    if let pb::node::Kind::Var(name) = &kind {
                        let index = name
                            .strip_prefix('_')
                            .and_then(|s| s.parse::<usize>().ok())
                            .filter(|index| name == &format!("_{index}"));
                        if index
                            .and_then(|index| primitive.inputs.get(index))
                            .is_none_or(|arg| *arg != node.sort_id)
                        {
                            return Err(format!(
                                "unbound or inconsistently typed primitive variable {name}"
                            ));
                        }
                    }
                    node_edges(&mut kind, |child| {
                        pending.push(*child);
                        Ok(())
                    })?;
                }
                (&primitive.inputs, Some(primitive.output))
            }
        };
        for i in inputs.iter().copied().chain(output) {
            pattern_scope(p, i, 0)?;
        }
    }
    Ok(())
}
