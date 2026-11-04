//! Structural relocation and compatibility for canonical definition records.
//! No native values, executable bodies, or second signature model live here.

type HashMap<K, V> = std::collections::HashMap<K, V>;
type HashSet<T> = std::collections::HashSet<T>;
use crate::proto as pb;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Namespace {
    EqSort,
    Callable,
}

/// Existing declaration tags select two namespaces; spellings may coincide.
fn declaration_identity(d: &pb::Declaration) -> Result<(Namespace, &str), String> {
    if d.table_name.is_some()
        && !matches!(
            d.kind,
            Some(
                pb::declaration::Kind::Constructor(_)
                    | pb::declaration::Kind::Function(_)
                    | pb::declaration::Kind::Relation(_)
            )
        )
    {
        return Err("only table declarations may have a reflective table prefix".into());
    }
    let identity = match d.kind.as_ref().ok_or("missing declaration kind")? {
        pb::declaration::Kind::EqSort(s) => (Namespace::EqSort, s.name.as_str()),
        pb::declaration::Kind::Constructor(c) => (Namespace::Callable, c.name.as_str()),
        pb::declaration::Kind::Function(f) => (Namespace::Callable, f.name.as_str()),
        pb::declaration::Kind::Relation(r) => (Namespace::Callable, r.name.as_str()),
        pb::declaration::Kind::UserDefinedPrimitive(p) => (Namespace::Callable, p.name.as_str()),
    };
    if identity.1.is_empty() {
        return Err("empty declaration name".into());
    }
    Ok(identity)
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
        N::Union(u) => {
            for i in &mut u.members {
                f(i)?;
            }
        }
        N::Var(_) => (),
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
    d: &mut pb::Declaration,
    mut sort: impl FnMut(&mut u32) -> Result<(), String>,
    mut node: impl FnMut(&mut u32) -> Result<(), String>,
) -> Result<(), String> {
    match d.kind.as_mut().ok_or("missing declaration kind")? {
        pb::declaration::Kind::Constructor(c) => {
            for a in &mut c.inputs {
                sort(&mut a.sort)?;
            }
            sort(&mut c.output)?;
            if let Some(i) = &mut c.cost {
                node(i)?;
            }
        }
        pb::declaration::Kind::Function(c) => {
            for a in &mut c.inputs {
                sort(&mut a.sort)?;
            }
            sort(&mut c.output)?;
            if let Some(i) = &mut c.merge {
                node(i)?;
            }
        }
        pb::declaration::Kind::Relation(r) => {
            for a in &mut r.inputs {
                sort(&mut a.sort)?;
            }
        }
        pb::declaration::Kind::UserDefinedPrimitive(p) => {
            for a in &mut p.inputs {
                sort(&mut a.sort)?;
            }
            sort(&mut p.output)?;
            node(p.body.as_mut().ok_or("missing primitive body")?)?;
        }
        pb::declaration::Kind::EqSort(_) => (),
    }
    Ok(())
}

fn relocate_span(
    span: &mut Option<pb::Span>,
    source: &pb::Program,
    files: &[u32],
) -> Result<(), String> {
    if let Some(span) = span {
        let file = source
            .files
            .get(span.file as usize)
            .ok_or("span file out of bounds")?;
        if span.start > span.end
            || file.contents.as_ref().is_some_and(|s| {
                !s.is_char_boundary(span.start as usize) || !s.is_char_boundary(span.end as usize)
            })
        {
            return Err("invalid span range".into());
        }
        span.file = files[span.file as usize];
    }
    Ok(())
}

// Declaration bodies/costs and rules use the same canonical arenas.
fn import_arenas(
    source: &pb::Program,
    destination: &mut pb::Program,
) -> Result<(Vec<u32>, Vec<u32>), String> {
    let mut files = Vec::new();
    for file in &source.files {
        let index = if let Some(index) = destination.files.iter().position(|old| old == file) {
            index
        } else {
            destination.files.push(file.clone());
            destination.files.len() - 1
        };
        files.push(u32::try_from(index).map_err(|_| "too many source files")?);
    }
    let mut input_sorts = source.sorts.clone();
    for sort in &mut input_sorts {
        relocate_span(&mut sort.span, source, &files)?;
    }
    let mut sorts = Vec::new();
    for index in 0..input_sorts.len() {
        sorts.push(super::import_sort(
            &input_sorts,
            index as u32,
            &mut destination.sorts,
        )?);
    }
    Ok((sorts, files))
}

// One reference visitor serves import, structural comparison and retention.
pub(crate) fn rule_refs(
    rule: &mut pb::Rule,
    mut node: impl FnMut(&mut u32) -> Result<(), String>,
    mut span: impl FnMut(&mut Option<pb::Span>) -> Result<(), String>,
) -> Result<(), String> {
    span(&mut rule.span)?;
    match rule.kind.as_mut().ok_or("missing rule kind")? {
        pb::rule::Kind::Rule(rule) => {
            for root in &mut rule.query {
                node(root)?;
            }
            for action in &mut rule.head {
                span(&mut action.span)?;
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
    files: &'a [u32],
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
                    relocate_span(&mut node.span, self.source, self.files)?;
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
        if matches!(left.kind, Some(pb::node::Kind::Union(_))) {
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
    a: &pb::Declaration,
    b: &pb::Declaration,
) -> Result<bool, String> {
    let mut roots = [vec![], vec![]];
    let mut declarations = [a.clone(), b.clone()];
    for (d, roots) in declarations.iter_mut().zip(&mut roots) {
        if let Some(pb::declaration::TableName::DefaultName(name)) = &d.table_name
            && declaration_identity(d)?.1 == name
        {
            d.table_name = None;
        }
        d.span = None;
        d.doc = None;
        match d.kind.as_mut().unwrap() {
            pb::declaration::Kind::EqSort(_) => (),
            pb::declaration::Kind::Constructor(c) => {
                for a in &mut c.inputs {
                    a.name.clear();
                }
            }
            pb::declaration::Kind::Function(c) => {
                for a in &mut c.inputs {
                    a.name.clear();
                }
            }
            pb::declaration::Kind::Relation(r) => {
                for a in &mut r.inputs {
                    a.name.clear();
                }
            }
            pb::declaration::Kind::UserDefinedPrimitive(c) => {
                for a in &mut c.inputs {
                    a.name.clear();
                }
            }
        }
        declaration_refs(
            d,
            |_| Ok(()),
            |i| {
                roots.push(*i);
                *i = 0;
                Ok(())
            },
        )?;
    }
    if declarations[0] != declarations[1] || roots[0].len() != roots[1].len() {
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
    let (sorts, files) = import_arenas(source, &mut staged)?;
    let mut importer = NodeImport {
        source,
        sorts: &sorts,
        files: &files,
        nodes: &mut staged.nodes,
        imported: HashMap::default(),
        active: HashSet::default(),
    };
    let mut incoming = source.declarations.clone();
    for d in &mut incoming {
        declaration_identity(d)?;
        relocate_span(&mut d.span, source, &files)?;
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
    for d in incoming {
        let identity = declaration_identity(&d)?;
        let existing = staged
            .declarations
            .iter()
            .position(|old| declaration_identity(old).ok() == Some(identity));
        if let Some(i) = existing {
            let old = staged.declarations[i].clone();
            if !compatible_semantics(&staged, &old, &d)? {
                return Err(format!("conflicting declaration {}", identity.1));
            }
            added.push(false);
        } else {
            staged.declarations.push(d);
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
    let mut files = (0..previous.files.len() as u32).collect::<HashSet<_>>();
    let mut pending = nodes.iter().copied().collect::<Vec<_>>();
    for d in &mut p.declarations {
        if let Some(s) = d.span {
            files.insert(s.file);
        }
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
        rule_refs(
            rule,
            |root| {
                pending.push(*root);
                Ok(())
            },
            |span| {
                if let Some(span) = span {
                    files.insert(span.file);
                }
                Ok(())
            },
        )?;
    }
    let mut walked = HashSet::default();
    while let Some(i) = pending.pop() {
        if !walked.insert(i) {
            continue;
        }
        nodes.insert(i);
        let n = &mut p.nodes[i as usize];
        sorts.insert(n.sort_id);
        if let Some(s) = n.span {
            files.insert(s.file);
        }
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
        if let Some(s) = s.span {
            files.insert(s.file);
        }
        if let Some(pb::sort::Kind::Primitive(f)) = &s.kind {
            pending.extend(&f.args);
        } else if let Some(pb::sort::Kind::Func(f)) = &s.kind {
            pending.extend(&f.params);
            pending.push(f.result);
        }
    }
    let mut node_map = vec![None; p.nodes.len()];
    let mut sort_map = vec![None; p.sorts.len()];
    let mut file_map = vec![None; p.files.len()];
    for (keep, map) in [
        (&nodes, &mut node_map),
        (&sorts, &mut sort_map),
        (&files, &mut file_map),
    ] {
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
    p.files = std::mem::take(&mut p.files)
        .into_iter()
        .enumerate()
        .filter_map(|(i, f)| files.contains(&(i as u32)).then_some(f))
        .collect();
    for n in &mut p.nodes {
        n.sort_id = sort_map[n.sort_id as usize].unwrap();
        if let Some(s) = &mut n.span {
            s.file = file_map[s.file as usize].unwrap();
        }
        node_edges(n.kind.as_mut().unwrap(), |i| {
            *i = node_map[*i as usize].unwrap();
            Ok(())
        })?;
    }
    for s in &mut p.sorts {
        if let Some(span) = &mut s.span {
            span.file = file_map[span.file as usize].unwrap();
        }
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
    for d in &mut p.declarations {
        if let Some(s) = &mut d.span {
            s.file = file_map[s.file as usize].unwrap();
        }
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
        rule_refs(
            rule,
            |root| {
                *root = node_map[*root as usize].unwrap();
                Ok(())
            },
            |span| {
                if let Some(span) = span {
                    span.file = file_map[span.file as usize].unwrap();
                }
                Ok(())
            },
        )?;
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
    for d in &p.declarations {
        let (inputs, output) = match d.kind.as_ref().ok_or("missing declaration kind")? {
            pb::declaration::Kind::EqSort(_) => {
                continue;
            }
            pb::declaration::Kind::Constructor(c) => (&c.inputs, Some(c.output)),
            pb::declaration::Kind::Function(f) => (&f.inputs, Some(f.output)),
            pb::declaration::Kind::Relation(r) => (&r.inputs, None),
            pb::declaration::Kind::UserDefinedPrimitive(primitive) => {
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
                            .is_none_or(|arg| arg.sort != node.sort_id)
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
        for i in inputs.iter().map(|a| a.sort).chain(output) {
            pattern_scope(p, i, 0)?;
        }
    }
    Ok(())
}
