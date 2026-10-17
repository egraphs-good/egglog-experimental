//! Immutable protobuf records and location-only imports. No semantic shadow IR.
use super::{TypedError, pb};
use prost::Message;
use std::{
    collections::HashMap,
    sync::{
        Arc, OnceLock,
        atomic::{AtomicUsize, Ordering},
    },
};

static NEXT_OWNER: AtomicUsize = AtomicUsize::new(0);

// Keep support items outside the authored builtins namespace, so valid type
// names cannot capture them. The owner still retains exactly the generated
// catalog records, without native discovery or copied semantic signatures.
pub(super) fn builtin_catalog() -> &'static Record {
    static CATALOG: OnceLock<Record> = OnceLock::new();
    CATALOG.get_or_init(|| {
        let program = pb::Program::decode(include_bytes!("builtins/catalog.pb").as_slice())
            .expect("generated catalog is valid protobuf");
        assert!(
            program.nodes.is_empty() && program.rules.is_empty() && program.rulesets.is_empty()
        );
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Sort as usize] = (0..program.sorts.len() as u32).map(Slot::Local).collect();
        slots[Arena::Declaration as usize] = (0..program.declarations.len() as u32)
            .map(Slot::Local)
            .collect();
        publish(program, slots, vec![], Arena::Sort, 0)
            .expect("unsupported generated catalog shape")
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum Arena {
    Node,
    Sort,
    Declaration,
    Rule,
    Ruleset,
    Command,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum DeclarationKind {
    EqSort,
    HostSortFamily,
    Callable,
}

#[derive(Clone)]
pub(super) struct Record {
    pub owner: Option<Arc<Owner>>,
    pub arena: Arena,
    pub index: u32,
}

pub(super) enum Slot {
    Local(u32),
    External(Record),
}

pub(super) struct Owner {
    pub id: usize,
    pub program: pb::Program,
    pub slots: [Vec<Slot>; 6],
    // Candidate declaration locations, not names/signatures copied from them.
    pub declarations: Vec<Record>,
    // Locations in this owner's generated records, never an initializer copy.
    pub capture: Option<(u32, u32)>,
    // Function declaration and its two exact parameter locations in Node slots.
    pub merge_parameters: Option<(u32, [u32; 2])>,
}

// A validated, temporary view of the generated Function/Call/Set linkage.
pub(super) struct CaptureRecipe {
    pub name: String,
    pub declaration: Record,
    pub initializer: Record,
    pub initialization: Record,
}

impl Drop for Record {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        if let Some(owner) = self.owner.take() {
            pending.push(owner);
        }
        while let Some(owner) = pending.pop() {
            if let Some(mut owner) = Arc::into_inner(owner) {
                for slots in &mut owner.slots {
                    for slot in slots {
                        if let Slot::External(record) = slot
                            && let Some(child) = record.owner.take()
                        {
                            pending.push(child);
                        }
                    }
                }
                for record in &mut owner.declarations {
                    if let Some(child) = record.owner.take() {
                        pending.push(child);
                    }
                }
            }
        }
    }
}

impl Record {
    pub fn capture(&self) -> Result<Option<CaptureRecipe>, TypedError> {
        let owner = self.owner.as_ref().unwrap();
        let Some((read, initialization)) = owner.capture else {
            return Ok(None);
        };
        let invalid = || TypedError::Invalid("invalid canonical capture recipe".into());
        let node = owner.program.nodes.get(read as usize).ok_or_else(invalid)?;
        let command = owner
            .program
            .commands
            .get(initialization as usize)
            .ok_or_else(invalid)?;
        if self.arena != Arena::Node || self.index != read {
            return Ok(None);
        }
        let Some(pb::node::Kind::Call(call)) = &node.kind else {
            return Err(invalid());
        };
        let Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Set(set)),
            ..
        })) = &command.kind
        else {
            return Err(invalid());
        };
        let target = set.target.as_ref().ok_or_else(invalid)?;
        let value = set.value.ok_or_else(invalid)?;
        let Some(Slot::External(initializer)) =
            owner.slots[Arena::Node as usize].get(value as usize)
        else {
            return Err(invalid());
        };
        let declaration = self.declaration(&call.func, DeclarationKind::Callable)?;
        let Some(pb::declaration::Kind::Function(function)) =
            &declaration.owner.as_ref().unwrap().program.declarations[declaration.index as usize]
                .kind
        else {
            return Err(invalid());
        };
        let hex = call
            .func
            .strip_prefix("__typed_capture_recipe_")
            .ok_or_else(invalid)?;
        if !call.args.is_empty()
            || target != call
            || !function.inputs.is_empty()
            || function.merge.is_some()
            || hex.len() % 2 != 0
            || !hex
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        {
            return Err(invalid());
        }
        let bytes = (0..hex.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).map_err(|_| invalid()))
            .collect::<Result<Vec<_>, _>>()?;
        String::from_utf8(bytes).map_err(|_| invalid())?;
        let rhs = initializer
            .owner
            .as_ref()
            .unwrap()
            .program
            .nodes
            .get(initializer.index as usize)
            .ok_or_else(invalid)?;
        let sort = super::SortRef(self.resolve(Arena::Sort, node.sort_id)?);
        if sort != super::SortRef(declaration.resolve(Arena::Sort, function.output)?)
            || sort != super::SortRef(initializer.resolve(Arena::Sort, rhs.sort_id)?)
        {
            return Err(invalid());
        }
        Ok(Some(CaptureRecipe {
            name: call.func.clone(),
            declaration,
            initializer: initializer.clone(),
            initialization: Record {
                owner: self.owner.clone(),
                arena: Arena::Command,
                index: initialization,
            },
        }))
    }

    pub fn resolve(&self, arena: Arena, slot: u32) -> Result<Self, TypedError> {
        let owner = self.owner.as_ref().unwrap();
        match owner.slots[arena as usize].get(slot as usize) {
            Some(Slot::Local(index)) => Ok(Self {
                owner: self.owner.clone(),
                arena,
                index: *index,
            }),
            Some(Slot::External(record)) if record.arena == arena => Ok(record.clone()),
            _ => Err(TypedError::Invalid(
                "invalid protobuf relocation slot".into(),
            )),
        }
    }

    pub fn declaration(&self, name: &str, kind: DeclarationKind) -> Result<Self, TypedError> {
        let owner = self.owner.as_ref().unwrap();
        let matches = |d: &pb::Declaration| match &d.kind {
            Some(pb::declaration::Kind::EqSort(d)) => {
                kind == DeclarationKind::EqSort && d.name == name
            }
            Some(pb::declaration::Kind::HostSortFamily(d)) => {
                kind == DeclarationKind::HostSortFamily && d.name == name
            }
            Some(pb::declaration::Kind::Constructor(d)) => {
                kind == DeclarationKind::Callable && d.name == name
            }
            Some(pb::declaration::Kind::Function(d)) => {
                kind == DeclarationKind::Callable && d.name == name
            }
            Some(pb::declaration::Kind::Relation(d)) => {
                kind == DeclarationKind::Callable && d.name == name
            }
            Some(pb::declaration::Kind::HostPrimitive(d)) => {
                kind == DeclarationKind::Callable && d.name == name
            }
            Some(pb::declaration::Kind::Primitive(d)) => {
                kind == DeclarationKind::Callable && d.name == name
            }
            _ => false,
        };
        if let Some(index) = owner.program.declarations.iter().position(matches) {
            return Ok(Self {
                owner: self.owner.clone(),
                arena: Arena::Declaration,
                index: index as u32,
            });
        }
        owner
            .declarations
            .iter()
            .find(|r| matches(&r.owner.as_ref().unwrap().program.declarations[r.index as usize]))
            .cloned()
            .ok_or_else(|| TypedError::Invalid(format!("{kind:?} declaration unavailable: {name}")))
    }
}

pub(super) type Key = (usize, Arena, u32);

/// Inspect the reachable canonical closure before packing can erase provenance.
/// Capture initializer edges belong to authoring, not the nullary wire Call.
pub(super) fn closure(roots: &[Record]) -> Result<Vec<Record>, TypedError> {
    let mut pending = roots.to_vec();
    let mut seen = std::collections::HashSet::new();
    let mut result = vec![];
    while let Some(record) = pending.pop() {
        let owner = record.owner.as_ref().unwrap();
        if !seen.insert((owner.id, record.arena, record.index)) {
            continue;
        }
        let mut one = pb::Program::default();
        match record.arena {
            Arena::Node => {
                let node = owner
                    .program
                    .nodes
                    .get(record.index as usize)
                    .ok_or_else(|| TypedError::Invalid("invalid node location".into()))?;
                if let Some(capture) = record.capture()? {
                    pending.push(capture.initializer);
                }
                if let Some(pb::node::Kind::Call(call)) = &node.kind {
                    pending.push(record.declaration(&call.func, DeclarationKind::Callable)?);
                } else if let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::PartialCall(call)),
                })) = &node.kind
                {
                    pending.push(record.declaration(&call.func, DeclarationKind::Callable)?);
                }
                one.nodes.push(node.clone());
            }
            Arena::Sort => {
                let sort = &owner.program.sorts[record.index as usize];
                match &sort.kind {
                    Some(pb::sort::Kind::Eq(name)) => {
                        pending.push(record.declaration(name, DeclarationKind::EqSort)?)
                    }
                    Some(pb::sort::Kind::Family(f)) => {
                        pending.push(record.declaration(&f.name, DeclarationKind::HostSortFamily)?)
                    }
                    _ => (),
                }
                one.sorts.push(sort.clone());
            }
            Arena::Declaration => one
                .declarations
                .push(owner.program.declarations[record.index as usize].clone()),
            Arena::Rule => {
                one.rules
                    .push(owner.program.rules[record.index as usize].clone());
                pending.extend(owner.declarations.iter().cloned());
            }
            Arena::Ruleset => one
                .rulesets
                .push(owner.program.rulesets[record.index as usize].clone()),
            Arena::Command => {
                one.commands
                    .push(owner.program.commands[record.index as usize].clone());
                pending.extend(owner.declarations.iter().cloned());
            }
        }
        visit(&mut one, record.arena, 0, |arena, index| {
            pending.push(record.resolve(arena, index)?);
            Ok(index)
        })?;
        result.push(record);
    }
    Ok(result)
}

/// One operand-order/validation algorithm for owned actions and inline heads.
pub(super) fn visit_action(
    action: &mut pb::Action,
    mut node: impl FnMut(u32) -> Result<u32, TypedError>,
) -> Result<(), TypedError> {
    let invalid = || TypedError::Invalid("unsupported protobuf action in typed subset".into());
    if action.span.is_some() {
        return Err(invalid());
    }
    match action.kind.as_mut().ok_or_else(invalid)? {
        pb::action::Kind::Term(index) => *index = node(*index)?,
        pb::action::Kind::Set(set) => {
            for arg in &mut set.target.as_mut().ok_or_else(invalid)?.args {
                *arg = node(*arg)?;
            }
            let value = set.value.as_mut().ok_or_else(invalid)?;
            *value = node(*value)?;
        }
        pb::action::Kind::Delete(call) | pb::action::Kind::Subsume(call) => {
            for arg in &mut call.args {
                *arg = node(*arg)?;
            }
        }
        _ => return Err(invalid()),
    }
    Ok(())
}

/// Relocate only admitted shapes. Both publication and packing use this visitor.
pub(super) fn visit(
    program: &mut pb::Program,
    arena: Arena,
    index: u32,
    mut map: impl FnMut(Arena, u32) -> Result<u32, TypedError>,
) -> Result<(), TypedError> {
    let invalid = || TypedError::Invalid("unsupported protobuf shape in typed subset".into());
    match arena {
        Arena::Node => {
            let n = &mut program.nodes[index as usize];
            if n.span.is_some() {
                return Err(invalid());
            }
            n.sort_id = map(Arena::Sort, n.sort_id)?;
            match n.kind.as_mut().ok_or_else(invalid)? {
                pb::node::Kind::Call(c) => {
                    for a in &mut c.args {
                        *a = map(Arena::Node, *a)?;
                    }
                }
                pb::node::Kind::Union(u) => {
                    for a in &mut u.members {
                        *a = map(Arena::Node, *a)?;
                    }
                }
                pb::node::Kind::Var(_) => {}
                pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Maybe(maybe)),
                }) => {
                    if let Some(child) = &mut maybe.value {
                        *child = map(Arena::Node, *child)?;
                    }
                }
                pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Map(values)),
                }) => {
                    for entry in &mut values.entries {
                        for child in [&mut entry.key, &mut entry.value] {
                            let child = child.as_mut().ok_or_else(invalid)?;
                            *child = map(Arena::Node, *child)?;
                        }
                    }
                }
                pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Pair(pair)),
                }) => {
                    for child in [&mut pair.first, &mut pair.second] {
                        let child = child.as_mut().ok_or_else(invalid)?;
                        *child = map(Arena::Node, *child)?;
                    }
                }
                pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value:
                        Some(
                            pb::primitive_value::Value::Vec(values)
                            | pb::primitive_value::Value::Set(values)
                            | pb::primitive_value::Value::Multiset(values),
                        ),
                }) => {
                    for child in &mut values.items {
                        *child = map(Arena::Node, *child)?;
                    }
                }
                pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::PartialCall(call)),
                }) => {
                    for child in &mut call.args {
                        *child = map(Arena::Node, *child)?;
                    }
                }
                pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value:
                        Some(
                            pb::primitive_value::Value::I64(_)
                            | pb::primitive_value::Value::F64Bits(_)
                            | pb::primitive_value::Value::String(_)
                            | pb::primitive_value::Value::Bool(_)
                            | pb::primitive_value::Value::Unit(_)
                            | pb::primitive_value::Value::BigInt(_)
                            | pb::primitive_value::Value::BigRat(_)
                            | pb::primitive_value::Value::Rational(_),
                        ),
                }) => {}
                _ => return Err(invalid()),
            }
        }
        Arena::Sort => {
            let s = &mut program.sorts[index as usize];
            if s.span.is_some() {
                return Err(invalid());
            }
            match s.kind.as_mut().ok_or_else(invalid)? {
                pb::sort::Kind::Eq(_) | pb::sort::Kind::Var(_) => {}
                pb::sort::Kind::Family(f) => {
                    for arg in &mut f.args {
                        *arg = map(Arena::Sort, *arg)?;
                    }
                }
                pb::sort::Kind::Func(f) => {
                    for arg in &mut f.params {
                        *arg = map(Arena::Sort, *arg)?;
                    }
                    f.result = map(Arena::Sort, f.result)?;
                }
            }
        }
        Arena::Declaration => {
            let d = &mut program.declarations[index as usize];
            if d.span.is_some() {
                return Err(invalid());
            }
            match d.kind.as_mut().ok_or_else(invalid)? {
                pb::declaration::Kind::EqSort(_) | pb::declaration::Kind::HostSortFamily(_) => {}
                pb::declaration::Kind::Constructor(c) if c.cost.is_none() => {
                    for a in &mut c.inputs {
                        a.sort = map(Arena::Sort, a.sort)?;
                    }
                    c.output = map(Arena::Sort, c.output)?;
                }
                pb::declaration::Kind::Function(f) => {
                    for arg in &mut f.inputs {
                        arg.sort = map(Arena::Sort, arg.sort)?;
                    }
                    f.output = map(Arena::Sort, f.output)?;
                    if let Some(merge) = &mut f.merge {
                        *merge = map(Arena::Node, *merge)?;
                    }
                }
                pb::declaration::Kind::Relation(relation) => {
                    for arg in &mut relation.inputs {
                        arg.sort = map(Arena::Sort, arg.sort)?;
                    }
                }
                pb::declaration::Kind::Primitive(primitive) => {
                    for arg in &mut primitive.inputs {
                        arg.sort = map(Arena::Sort, arg.sort)?;
                    }
                    primitive.output = map(Arena::Sort, primitive.output)?;
                    let body = primitive.body.as_mut().ok_or_else(invalid)?;
                    *body = map(Arena::Node, *body)?;
                }
                pb::declaration::Kind::HostPrimitive(p) => {
                    match p.typing.as_mut().ok_or_else(invalid)? {
                        pb::host_primitive::Typing::Signature(signature) => {
                            for arg in signature
                                .inputs
                                .iter_mut()
                                .chain(signature.varargs.iter_mut())
                            {
                                arg.sort = map(Arena::Sort, arg.sort)?;
                            }
                            let output = signature.output.as_mut().ok_or_else(invalid)?;
                            *output = map(Arena::Sort, *output)?;
                        }
                        // This marker contains no arena references to relocate.
                        pb::host_primitive::Typing::Application(_) => {}
                    }
                }
                _ => return Err(invalid()),
            }
            let application = matches!(
                &d.kind,
                Some(pb::declaration::Kind::HostPrimitive(pb::HostPrimitive {
                    typing: Some(pb::host_primitive::Typing::Application(_)),
                    ..
                }))
            );
            if let Some(bindings) = &mut d.bindings {
                if let Some(python) = &mut bindings.python {
                    for view in &mut python.views {
                        if let Some(owner) = &mut view.owner {
                            match owner.kind.as_mut().ok_or_else(invalid)? {
                                pb::binding_owner::Kind::Sort(sort) => {
                                    *sort = map(Arena::Sort, *sort)?
                                }
                                pb::binding_owner::Kind::Function(_) if application => {}
                                _ => return Err(invalid()),
                            }
                        }
                        // Saved defaults need their own binder closure support;
                        // the scalar catalog contains none.
                        if view.params.iter().any(|p| p.default_expr.is_some()) {
                            return Err(invalid());
                        }
                    }
                }
                if let Some(rust) = &mut bindings.rust {
                    for view in &mut rust.views {
                        if let Some(owner) = &mut view.owner {
                            match owner.kind.as_mut().ok_or_else(invalid)? {
                                pb::binding_owner::Kind::Sort(sort) => {
                                    *sort = map(Arena::Sort, *sort)?
                                }
                                pb::binding_owner::Kind::Function(_) if application => {}
                                _ => return Err(invalid()),
                            }
                        }
                        if let Some(trait_impl) = &mut view.trait_impl {
                            for arg in &mut trait_impl.args {
                                let sort = arg.sort.as_mut().ok_or_else(invalid)?;
                                *sort = map(Arena::Sort, *sort)?;
                            }
                        }
                    }
                }
            }
        }
        Arena::Rule => {
            let rule = &mut program.rules[index as usize];
            if rule.span.is_some() {
                return Err(invalid());
            }
            match rule.kind.as_mut().ok_or_else(invalid)? {
                pb::rule_decl::Kind::Rule(r) => {
                    for fact in &mut r.query {
                        *fact = map(Arena::Node, *fact)?;
                    }
                    for action in &mut r.head {
                        visit_action(action, |index| map(Arena::Node, index))?;
                    }
                }
                pb::rule_decl::Kind::Rewrite(r) => {
                    r.lhs = map(Arena::Node, r.lhs)?;
                    for c in &mut r.conditions {
                        *c = map(Arena::Node, *c)?;
                    }
                    r.rhs = map(Arena::Node, r.rhs)?;
                }
                _ => return Err(invalid()),
            }
        }
        Arena::Ruleset => {
            let ruleset = &mut program.rulesets[index as usize];
            if ruleset.span.is_some() {
                return Err(invalid());
            }
            match ruleset.kind.as_mut().ok_or_else(invalid)? {
                pb::ruleset::Kind::Rules(r) => {
                    for i in &mut r.rules {
                        *i = map(Arena::Rule, *i)?;
                    }
                }
                pb::ruleset::Kind::Combined(r) => {
                    for reference in &mut r.rulesets {
                        let Some(pb::ruleset_ref::Kind::Index(index)) = &mut reference.kind else {
                            return Err(invalid());
                        };
                        *index = map(Arena::Ruleset, *index)?;
                    }
                }
            }
        }
        Arena::Command => {
            let command = &mut program.commands[index as usize];
            if command.span.is_some() {
                return Err(invalid());
            }
            let Some(pb::command::Kind::Action(action)) = &mut command.kind else {
                return Err(invalid());
            };
            visit_action(action, |index| map(Arena::Node, index))?;
        }
    }
    Ok(())
}

pub(super) fn publish(
    mut program: pb::Program,
    slots: [Vec<Slot>; 6],
    declarations: Vec<Record>,
    arena: Arena,
    index: u32,
) -> Result<Record, TypedError> {
    if program.ir_version != 1
        || !program.files.is_empty()
        || program
            .commands
            .iter()
            .any(|c| !matches!(c.kind, Some(pb::command::Kind::Action(_))))
    {
        return Err(TypedError::Invalid(
            "unsupported typed fragment sections".into(),
        ));
    }
    let lengths = [
        program.nodes.len(),
        program.sorts.len(),
        program.declarations.len(),
        program.rules.len(),
        program.rulesets.len(),
        program.commands.len(),
    ];
    if index as usize >= lengths[arena as usize] {
        return Err(TypedError::Invalid("invalid fragment root".into()));
    }
    for (category, table) in slots.iter().enumerate() {
        for slot in table {
            let valid = match slot {
                Slot::Local(i) => (*i as usize) < lengths[category],
                Slot::External(r) => r.arena as usize == category,
            };
            if !valid {
                return Err(TypedError::Invalid("invalid fragment import".into()));
            }
        }
    }
    for (arena, len) in [
        Arena::Node,
        Arena::Sort,
        Arena::Declaration,
        Arena::Rule,
        Arena::Ruleset,
        Arena::Command,
    ]
    .into_iter()
    .zip(lengths)
    {
        for index in 0..len {
            visit(&mut program, arena, index as u32, |a, i| {
                if (i as usize) < slots[a as usize].len() {
                    Ok(i)
                } else {
                    Err(TypedError::Invalid(
                        "protobuf reference out of bounds".into(),
                    ))
                }
            })?;
        }
    }
    let id = NEXT_OWNER
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |i| i.checked_add(1))
        .expect("owner identity exhausted");
    // Only already-published owners can be imported. Flat local backedges create
    // no strong ownership edge, so ownership cycles cannot be published.
    for r in slots
        .iter()
        .flatten()
        .filter_map(|s| {
            if let Slot::External(r) = s {
                Some(r)
            } else {
                None
            }
        })
        .chain(&declarations)
    {
        assert!(r.owner.as_ref().unwrap().id < id);
    }
    Ok(Record {
        owner: Some(Arc::new(Owner {
            id,
            program,
            slots,
            declarations,
            capture: None,
            merge_parameters: None,
        })),
        arena,
        index,
    })
}

pub(super) struct Packer {
    pub program: pb::Program,
    // Source locations parallel to the packed arena, for request-scoped receipts.
    pub rulesets: Vec<Record>,
    ids: HashMap<(Key, usize), u32>,
    pending: Vec<(Record, usize, u32)>,
    cursor: usize,
    pub binders: Vec<HashMap<String, String>>,
    pub declarations: HashMap<String, Record>,
    // Request-local renaming of proven recipe locations, never string aliases.
    pub captures: HashMap<Key, String>,
    pub initializations: Vec<(u32, Record, String)>,
    pub ordinary_callables: std::collections::HashSet<String>,
    pub capture_counter: Option<u64>,
}

impl Default for Packer {
    fn default() -> Self {
        Self {
            program: pb::Program {
                ir_version: 1,
                ..Default::default()
            },
            rulesets: vec![],
            ids: HashMap::new(),
            pending: vec![],
            cursor: 0,
            binders: vec![HashMap::new()],
            declarations: HashMap::new(),
            captures: HashMap::new(),
            initializations: vec![],
            ordinary_callables: std::collections::HashSet::new(),
            capture_counter: None,
        }
    }
}

impl Packer {
    pub fn intern(&mut self, record: Record, binder: usize) -> u32 {
        let owner = record.owner.as_ref().unwrap();
        let context = if matches!(record.arena, Arena::Node | Arena::Command) {
            binder
        } else {
            0
        };
        let key = ((owner.id, record.arena, record.index), context);
        if let Some(index) = self.ids.get(&key) {
            return *index;
        }
        let index = match record.arena {
            Arena::Node => {
                self.program.nodes.push(pb::Node::default());
                self.program.nodes.len() - 1
            }
            Arena::Sort => {
                self.program.sorts.push(pb::Sort::default());
                self.program.sorts.len() - 1
            }
            Arena::Declaration => {
                self.program.declarations.push(pb::Declaration::default());
                self.program.declarations.len() - 1
            }
            Arena::Rule => {
                self.program.rules.push(pb::RuleDecl::default());
                self.program.rules.len() - 1
            }
            Arena::Ruleset => {
                self.program.rulesets.push(pb::Ruleset::default());
                self.rulesets.push(record.clone());
                self.program.rulesets.len() - 1
            }
            Arena::Command => {
                self.program.commands.push(pb::Command::default());
                self.program.commands.len() - 1
            }
        };
        let index = u32::try_from(index).expect("protobuf arena exceeds u32");
        self.ids.insert(key, index);
        self.pending.push((record, binder, index));
        index
    }

    pub fn finish(&mut self) -> Result<(), TypedError> {
        while self.cursor < self.pending.len() {
            let (record, mut binder, index) = self.pending[self.cursor].clone();
            let owner = record.owner.as_ref().unwrap();
            // Inline row targets have no Node.Call, including nullary targets.
            // Their actual declaration imports must still enter this packet.
            if matches!(record.arena, Arena::Rule | Arena::Command) {
                for declaration in &owner.declarations {
                    self.intern(declaration.clone(), 0);
                }
            }
            // Copy exactly one generated record, never the previous fragment.
            let mut one = pb::Program::default();
            match record.arena {
                Arena::Node => {
                    let mut n = owner.program.nodes[record.index as usize].clone();
                    if record.capture()?.is_some()
                        && !self
                            .captures
                            .contains_key(&(owner.id, record.arena, record.index))
                    {
                        return Err(TypedError::Invalid("capture requires session materialization; captures are forbidden in rules".into()));
                    }
                    match &mut n.kind {
                        Some(pb::node::Kind::Var(token)) => {
                            *token = self.binders[binder].get(token).cloned().ok_or_else(|| {
                                TypedError::Invalid("free variable in evaluated input".into())
                            })?;
                        }
                        Some(pb::node::Kind::Call(call)) => {
                            self.intern(
                                record.declaration(&call.func, DeclarationKind::Callable)?,
                                0,
                            );
                            if let Some(name) =
                                self.captures.get(&(owner.id, record.arena, record.index))
                            {
                                call.func = name.clone();
                            } else {
                                self.ordinary_callables.insert(call.func.clone());
                            }
                        }
                        Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                            value: Some(pb::primitive_value::Value::PartialCall(call)),
                        })) => {
                            self.intern(
                                record.declaration(&call.func, DeclarationKind::Callable)?,
                                0,
                            );
                        }
                        _ => {}
                    }
                    one.nodes.push(n);
                }
                Arena::Sort => {
                    let s = owner.program.sorts[record.index as usize].clone();
                    match &s.kind {
                        Some(pb::sort::Kind::Eq(name)) => {
                            self.intern(record.declaration(name, DeclarationKind::EqSort)?, 0);
                        }
                        Some(pb::sort::Kind::Family(f)) => {
                            self.intern(
                                record.declaration(&f.name, DeclarationKind::HostSortFamily)?,
                                0,
                            );
                        }
                        _ => {}
                    }
                    one.sorts.push(s);
                }
                Arena::Declaration => {
                    let mut declaration = owner.program.declarations[record.index as usize].clone();
                    match &mut declaration.kind {
                        Some(pb::declaration::Kind::Function(f)) => {
                            if let Some(merge) = f.merge {
                                let output = super::SortRef(record.resolve(Arena::Sort, f.output)?);
                                let Some((declaration, parameter_slots)) = owner.merge_parameters
                                else {
                                    return Err(TypedError::Invalid(
                                        "function merge parameter locations unavailable".into(),
                                    ));
                                };
                                if declaration != record.index {
                                    return Err(TypedError::Invalid(
                                        "function merge parameter declaration mismatch".into(),
                                    ));
                                }
                                let parameters = [
                                    (record.resolve(Arena::Node, parameter_slots[0])?, "old"),
                                    (record.resolve(Arena::Node, parameter_slots[1])?, "new"),
                                ];
                                for (parameter, label) in &parameters {
                                    let node = &parameter.owner.as_ref().unwrap().program.nodes
                                        [parameter.index as usize];
                                    if !matches!(
                                        &node.kind,
                                        Some(pb::node::Kind::Var(name)) if name.as_str() == *label
                                    ) || super::SortRef(
                                        parameter.resolve(Arena::Sort, node.sort_id)?,
                                    ) != output
                                    {
                                        return Err(TypedError::Invalid(
                                            "invalid canonical function merge parameter".into(),
                                        ));
                                    }
                                }
                                let parameters = parameters.map(|(parameter, label)| {
                                    (
                                        (
                                            parameter.owner.as_ref().unwrap().id,
                                            parameter.arena,
                                            parameter.index,
                                        ),
                                        label,
                                    )
                                });
                                let root = record.resolve(Arena::Node, merge)?;
                                let node = &root.owner.as_ref().unwrap().program.nodes
                                    [root.index as usize];
                                if super::SortRef(root.resolve(Arena::Sort, node.sort_id)?)
                                    != output
                                {
                                    return Err(TypedError::Invalid(
                                        "merge output sort mismatch".into(),
                                    ));
                                }
                                // A merge starts its own binder. Walk only this
                                // body's value edges; called declarations close
                                // their own bodies when they are packed.
                                let mut pending = vec![root];
                                let mut seen = std::collections::HashSet::new();
                                while let Some(child) = pending.pop() {
                                    let owner = child.owner.as_ref().unwrap();
                                    let key = (owner.id, child.arena, child.index);
                                    if !seen.insert(key) {
                                        continue;
                                    }
                                    if child.capture()?.is_some() {
                                        return Err(TypedError::Invalid(
                                            "captures are forbidden in function merges".into(),
                                        ));
                                    }
                                    let node = &owner.program.nodes[child.index as usize];
                                    if let Some(pb::node::Kind::Var(name)) = &node.kind
                                        && (!parameters.iter().any(|(parameter, label)| {
                                            *parameter == key && name.as_str() == *label
                                        }) || super::SortRef(
                                            child.resolve(Arena::Sort, node.sort_id)?,
                                        ) != output)
                                    {
                                        return Err(TypedError::Invalid(
                                            "function merge variables must be owned old or new of the output sort".into(),
                                        ));
                                    }
                                    visit(
                                        &mut pb::Program {
                                            nodes: vec![node.clone()],
                                            ..Default::default()
                                        },
                                        Arena::Node,
                                        0,
                                        |arena, index| {
                                            if arena == Arena::Node {
                                                pending.push(child.resolve(arena, index)?);
                                            }
                                            Ok(index)
                                        },
                                    )?;
                                }
                                binder = self.binders.len();
                                self.binders.push(HashMap::from([
                                    ("old".into(), "old".into()),
                                    ("new".into(), "new".into()),
                                ]));
                            }
                            if let Some(name) =
                                self.captures.get(&(owner.id, record.arena, record.index))
                            {
                                f.name = name.clone();
                            } else {
                                self.ordinary_callables.insert(f.name.clone());
                            }
                        }
                        Some(pb::declaration::Kind::Constructor(c)) => {
                            self.ordinary_callables.insert(c.name.clone());
                        }
                        Some(pb::declaration::Kind::Relation(r)) => {
                            self.ordinary_callables.insert(r.name.clone());
                        }
                        Some(pb::declaration::Kind::HostPrimitive(p)) => {
                            self.ordinary_callables.insert(p.name.clone());
                        }
                        Some(pb::declaration::Kind::Primitive(p)) => {
                            self.ordinary_callables.insert(p.name.clone());
                            binder = self.binders.len();
                            self.binders.push(
                                (0..p.inputs.len())
                                    .map(|i| {
                                        let name = format!("_{i}");
                                        (name.clone(), name)
                                    })
                                    .collect(),
                            );
                        }
                        _ => (),
                    }
                    one.declarations.push(declaration);
                }
                Arena::Rule => {
                    one.rules
                        .push(owner.program.rules[record.index as usize].clone());
                    let mut roots = vec![];
                    visit(&mut one, Arena::Rule, 0, |arena, index| {
                        roots.push(record.resolve(arena, index)?);
                        Ok(index)
                    })?;
                    for root in closure(&roots)? {
                        if root.capture()?.is_some() {
                            return Err(TypedError::Invalid(
                                "captures are forbidden in rules, rewrites and conditions".into(),
                            ));
                        }
                    }
                    binder = self.binders.len();
                    self.binders.push(super::close::binder(&roots)?);
                }
                Arena::Ruleset => one
                    .rulesets
                    .push(owner.program.rulesets[record.index as usize].clone()),
                Arena::Command => {
                    let mut command = owner.program.commands[record.index as usize].clone();
                    if let Some(name) = self.captures.get(&(owner.id, record.arena, record.index)) {
                        let Some(pb::command::Kind::Action(pb::Action {
                            kind: Some(pb::action::Kind::Set(set)),
                            ..
                        })) = &mut command.kind
                        else {
                            return Err(TypedError::Invalid(
                                "invalid capture initialization".into(),
                            ));
                        };
                        set.target.as_mut().unwrap().func = name.clone();
                    }
                    one.commands.push(command);
                }
            }
            visit(&mut one, record.arena, 0, |a, i| {
                Ok(self.intern(record.resolve(a, i)?, binder))
            })?;
            match record.arena {
                Arena::Node => self.program.nodes[index as usize] = one.nodes.pop().unwrap(),
                Arena::Sort => self.program.sorts[index as usize] = one.sorts.pop().unwrap(),
                Arena::Declaration => {
                    let d = one.declarations.pop().unwrap();
                    // Keep authoritative callable closures for finite data and
                    // extracted function values, including deferred bodies.
                    let name = match &d.kind {
                        Some(pb::declaration::Kind::Constructor(c)) => Some(&c.name),
                        Some(pb::declaration::Kind::Function(f)) => Some(&f.name),
                        Some(pb::declaration::Kind::Primitive(p)) => Some(&p.name),
                        Some(pb::declaration::Kind::HostPrimitive(p)) => Some(&p.name),
                        _ => None,
                    };
                    if let Some(name) = name {
                        self.declarations.insert(name.clone(), record.clone());
                    }
                    self.program.declarations[index as usize] = d;
                }
                Arena::Rule => self.program.rules[index as usize] = one.rules.pop().unwrap(),
                Arena::Ruleset => {
                    self.program.rulesets[index as usize] = one.rulesets.pop().unwrap()
                }
                Arena::Command => {
                    self.program.commands[index as usize] = one.commands.pop().unwrap()
                }
            }
            self.cursor += 1;
        }
        // Independent compatible declarations can have distinct owners. Compare
        // complete node bodies, but keep the original arena references below.
        let mut seen = HashMap::new();
        let mut kept = vec![];
        for d in &self.program.declarations {
            let (kind, name) = match &d.kind {
                Some(pb::declaration::Kind::EqSort(d)) => (DeclarationKind::EqSort, &d.name),
                Some(pb::declaration::Kind::HostSortFamily(d)) => {
                    (DeclarationKind::HostSortFamily, &d.name)
                }
                Some(pb::declaration::Kind::Constructor(d)) => (DeclarationKind::Callable, &d.name),
                Some(pb::declaration::Kind::Function(d)) => (DeclarationKind::Callable, &d.name),
                Some(pb::declaration::Kind::Relation(d)) => (DeclarationKind::Callable, &d.name),
                Some(pb::declaration::Kind::HostPrimitive(d)) => {
                    (DeclarationKind::Callable, &d.name)
                }
                Some(pb::declaration::Kind::Primitive(d)) => (DeclarationKind::Callable, &d.name),
                _ => unreachable!(),
            };
            if seen.insert((kind, name), d).is_none() {
                kept.push(d.clone());
            }
        }
        if kept.len() != self.program.declarations.len() {
            egglog::builtin::definitions::reconcile_declarations(
                &self.program,
                &mut pb::Program {
                    ir_version: 1,
                    ..Default::default()
                },
            )
            .map_err(TypedError::Invalid)?;
        }
        self.program.declarations = kept;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn function_merges_keep_owned_nodes_and_compare_complete_bodies() {
        use crate::typed::{EgglogValue, builtins::I64, decl::Callable};
        use std::cell::Cell;

        let evaluations = Cell::new(0);
        let function = Callable::function(
            "OwnedMerge",
            vec![],
            I64::sort_ref(),
            Some(|_, new| {
                evaluations.set(evaluations.get() + 1);
                new
            }),
        );
        let retained = function.clone();
        drop(function);
        let compatible =
            Callable::function("OwnedMerge", vec![], I64::sort_ref(), Some(|_, new| new));
        let mut packer = Packer::default();
        packer.intern(retained.0.clone(), 0);
        packer.intern(compatible.0, 0);
        packer.finish().unwrap();
        assert_eq!(evaluations.get(), 1);
        let functions = packer
            .program
            .declarations
            .iter()
            .filter_map(|declaration| match &declaration.kind {
                Some(pb::declaration::Kind::Function(function)) => Some(function),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(functions.len(), 1);
        let merge = functions[0].merge.unwrap();
        assert!(matches!(
            &packer.program.nodes[merge as usize].kind,
            Some(pb::node::Kind::Var(name)) if name == "new"
        ));

        let conflicting =
            Callable::function("OwnedMerge", vec![], I64::sort_ref(), Some(|old, _| old));
        let mut packer = Packer::default();
        packer.intern(retained.0, 0);
        packer.intern(conflicting.0, 0);
        assert!(matches!(
            packer.finish(),
            Err(TypedError::Invalid(message)) if message.contains("conflicting declaration OwnedMerge")
        ));
    }

    #[test]
    fn function_merge_binder_is_separate_from_query_and_evaluated_uses() {
        use crate::typed::{EgglogValue, builtins::I64, decl::Callable};

        let mut shared = None;
        let function = Callable::function(
            "SeparateMergeBinder",
            vec![],
            I64::sort_ref(),
            Some(|old: crate::typed::expr::Expr, _| {
                shared = Some(old.clone());
                old
            }),
        );
        let shared = shared.unwrap();
        let mut packer = Packer::default();
        let declaration = packer.intern(function.0, 0);
        packer
            .binders
            .push(HashMap::from([("old".into(), "query_old".into())]));
        let query = packer.intern(shared.0.clone(), 1);
        packer.finish().unwrap();
        let Some(pb::declaration::Kind::Function(function)) =
            &packer.program.declarations[declaration as usize].kind
        else {
            panic!("function declaration")
        };
        let merge = function.merge.unwrap();
        assert_ne!(merge, query);
        assert!(matches!(
            &packer.program.nodes[merge as usize].kind,
            Some(pb::node::Kind::Var(name)) if name == "old"
        ));
        assert!(matches!(
            &packer.program.nodes[query as usize].kind,
            Some(pb::node::Kind::Var(name)) if name == "query_old"
        ));
        let mut packer = Packer::default();
        packer.intern(shared.0, 0);
        assert!(matches!(
            packer.finish(),
            Err(TypedError::Invalid(message)) if message == "free variable in evaluated input"
        ));
    }

    #[test]
    fn function_merge_packing_rejects_foreign_variables_captures_and_sorts() {
        use crate::typed::{EgglogValue, builtins::F64, builtins::I64, decl::Callable, let_, var};

        let capture = let_("merge-capture", I64::from(4));
        for body in [
            var::<I64>("old").expression().clone(),
            capture.expression().clone(),
            F64::from(1.0).expression().clone(),
        ] {
            let function =
                Callable::function("InvalidMerge", vec![], I64::sort_ref(), Some(|_, _| body));
            let mut packer = Packer::default();
            let record = &capture.expression().0;
            packer.captures.insert(
                (
                    record.owner.as_ref().unwrap().id,
                    record.arena,
                    record.index,
                ),
                "already-planned".into(),
            );
            packer.intern(function.0, 0);
            assert!(matches!(packer.finish(), Err(TypedError::Invalid(_))));
        }
    }

    #[test]
    fn subsume_checked_publication() {
        use crate::typed::{EgglogValue, SortRef, builtins::I64, decl::Callable};
        let argument = I64::from(17);
        let constructor = Callable::constructor(
            "Subsumed",
            vec![I64::sort_ref()],
            SortRef::equality("SubsumedSort"),
        );
        let program = pb::Program {
            ir_version: 1,
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Subsume(pb::Call {
                        func: "Subsumed".into(),
                        args: vec![0],
                    })),
                    ..Default::default()
                })),
                ..Default::default()
            }],
            ..Default::default()
        };
        for case in 0..5 {
            let mut program = program.clone();
            let Some(pb::command::Kind::Action(action)) = &mut program.commands[0].kind else {
                panic!()
            };
            match case {
                0 => {}
                1 => action.kind = None,
                2 => {
                    let Some(pb::action::Kind::Subsume(call)) = &mut action.kind else {
                        panic!()
                    };
                    call.args[0] = 1;
                }
                3 => action.kind = Some(pb::action::Kind::Panic("unsupported".into())),
                4 => action.kind = Some(pb::action::Kind::Set(pb::Set::default())),
                _ => unreachable!(),
            }
            let bytes = program.encode_to_vec();
            let mut slots = std::array::from_fn(|_| vec![]);
            slots[Arena::Node as usize] = vec![Slot::External(argument.expression().0.clone())];
            let result = publish(
                program,
                slots,
                vec![constructor.0.clone()],
                Arena::Command,
                0,
            );
            if case == 0 {
                assert_eq!(
                    result
                        .unwrap()
                        .owner
                        .as_ref()
                        .unwrap()
                        .program
                        .encode_to_vec(),
                    bytes
                );
            } else {
                assert!(matches!(result, Err(TypedError::Invalid(_))), "case={case}");
            }
        }
    }

    use super::*;

    #[test]
    fn actual_catalog_retains_application_metadata_and_checks_authoring_signature() {
        use crate::typed::{EgglogValue, builtins::Unit, decl::Callable, expr::Expr};
        let original =
            pb::Program::decode(include_bytes!("builtins/catalog.pb").as_slice()).unwrap();
        for reverse in [false, true] {
            let mut program = original.clone();
            if reverse {
                program.declarations.reverse();
            }
            let index = program.declarations.iter().position(|d| matches!(&d.kind,
                Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.core.fn.apply"
            )).unwrap() as u32;
            let bytes = program.encode_to_vec();
            let application = program.declarations[index as usize].clone();
            let mut slots = std::array::from_fn(|_| vec![]);
            slots[Arena::Sort as usize] =
                (0..program.sorts.len() as u32).map(Slot::Local).collect();
            slots[Arena::Declaration as usize] = (0..program.declarations.len() as u32)
                .map(Slot::Local)
                .collect();
            let record = publish(program, slots, vec![], Arena::Declaration, index)
                .expect("the actual complete catalog must retain its descriptors");
            assert_eq!(
                record.owner.as_ref().unwrap().program.encode_to_vec(),
                bytes
            );
            let mut packer = Packer::default();
            packer.intern(record.clone(), 0);
            packer.finish().unwrap();
            assert!(packer.program.sorts.is_empty() && packer.program.nodes.is_empty());
            assert_eq!(packer.program.declarations, [application]);
            assert!(
                matches!(Expr::call_with_result(&Callable(record), vec![], Unit::sort_ref()),
                Err(TypedError::Invalid(message)) if message == "application requires a function")
            );
        }
    }

    #[test]
    fn retained_application_markers_keep_checked_publication_boundaries() {
        let original =
            pb::Program::decode(include_bytes!("builtins/catalog.pb").as_slice()).unwrap();
        let apply = original.declarations.iter().position(|d| matches!(&d.kind,
            Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.core.fn.apply"
        )).unwrap();
        let ne = original
            .declarations
            .iter()
            .position(|d| {
                matches!(&d.kind,
                    Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.core.ne"
                )
            })
            .unwrap();
        let function_owner = original.declarations[apply]
            .bindings
            .as_ref()
            .unwrap()
            .python
            .as_ref()
            .unwrap()
            .views[0]
            .owner;
        for rust in [false, true] {
            // The Rust marker is an emitter-only variation; no wrapper or call
            // is produced. Both language branches must enforce the same rule.
            for case in 0..7 {
                let mut program = original.clone();
                if rust {
                    program.declarations[apply].bindings.as_mut().unwrap().rust =
                        Some(pb::RustBindings {
                            views: vec![pb::RustCallable {
                                path: vec!["call".into()],
                                owner: function_owner,
                                receiver: Some(pb::RustReceiver {
                                    core_input: Some(0),
                                    borrowed: false,
                                }),
                                params: vec![pb::RustParameter {
                                    name: "args".into(),
                                    core_input: Some(1),
                                    borrowed: false,
                                }],
                                ..Default::default()
                            }],
                        });
                }
                let target = if case == 3 { ne } else { apply };
                if case == 3 {
                    if rust {
                        program.declarations[ne].bindings.as_mut().unwrap().rust = program
                            .declarations[apply]
                            .bindings
                            .as_ref()
                            .unwrap()
                            .rust
                            .clone();
                    } else {
                        program.declarations[ne].bindings.as_mut().unwrap().python = program
                            .declarations[apply]
                            .bindings
                            .as_ref()
                            .unwrap()
                            .python
                            .clone();
                    }
                }
                let declaration = &mut program.declarations[target];
                match case {
                    0 | 3 => {} // unchanged positive, or Function owner on Signature
                    1 => {
                        let Some(pb::declaration::Kind::HostPrimitive(p)) = &mut declaration.kind
                        else {
                            panic!()
                        };
                        p.typing = None;
                    }
                    2 | 4 => {
                        let bindings = declaration.bindings.as_mut().unwrap();
                        let owner = if rust {
                            bindings.rust.as_mut().unwrap().views[0]
                                .owner
                                .as_mut()
                                .unwrap()
                        } else {
                            bindings.python.as_mut().unwrap().views[0]
                                .owner
                                .as_mut()
                                .unwrap()
                        };
                        owner.kind = (case == 4).then_some(pb::binding_owner::Kind::Sort(u32::MAX));
                    }
                    5 => {
                        // Defaults and Rust trait arguments must not be skipped
                        // when the declaration itself has no arena references.
                        let bindings = declaration.bindings.as_mut().unwrap();
                        if rust {
                            bindings.rust.as_mut().unwrap().views[0].trait_impl =
                                Some(pb::RustTrait {
                                    path: vec!["Test".into()],
                                    args: vec![pb::RustType {
                                        sort: Some(u32::MAX),
                                        borrowed: false,
                                    }],
                                    ..Default::default()
                                });
                        } else {
                            bindings.python.as_mut().unwrap().views[0].params[0].default_expr =
                                Some(0);
                        }
                    }
                    6 => {
                        let Some(pb::declaration::Kind::HostPrimitive(p)) =
                            &mut program.declarations[ne].kind
                        else {
                            panic!()
                        };
                        let Some(pb::host_primitive::Typing::Signature(s)) = &mut p.typing else {
                            panic!()
                        };
                        s.inputs[0].sort = u32::MAX;
                    }
                    _ => unreachable!(),
                }
                let bytes = program.encode_to_vec();
                let mut slots = std::array::from_fn(|_| vec![]);
                slots[Arena::Sort as usize] =
                    (0..program.sorts.len() as u32).map(Slot::Local).collect();
                slots[Arena::Declaration as usize] = (0..program.declarations.len() as u32)
                    .map(Slot::Local)
                    .collect();
                let result = publish(program, slots, vec![], Arena::Declaration, apply as u32);
                if case == 0 {
                    assert_eq!(
                        result
                            .unwrap()
                            .owner
                            .as_ref()
                            .unwrap()
                            .program
                            .encode_to_vec(),
                        bytes
                    );
                } else {
                    assert!(
                        matches!(result, Err(TypedError::Invalid(_))),
                        "rust={rust}, case={case}"
                    );
                }
            }
        }
        // Ordinary Signature references still visit every input and output.
        let mut relocated = original.clone();
        visit(
            &mut relocated,
            Arena::Declaration,
            ne as u32,
            |arena, index| {
                assert_eq!(arena, Arena::Sort);
                Ok(index + 1)
            },
        )
        .unwrap();
        let Some(pb::declaration::Kind::HostPrimitive(before)) = &original.declarations[ne].kind
        else {
            panic!()
        };
        let Some(pb::host_primitive::Typing::Signature(before)) = &before.typing else {
            panic!()
        };
        let Some(pb::declaration::Kind::HostPrimitive(after)) = &relocated.declarations[ne].kind
        else {
            panic!()
        };
        let Some(pb::host_primitive::Typing::Signature(after)) = &after.typing else {
            panic!()
        };
        assert_eq!(
            after.inputs.iter().map(|a| a.sort).collect::<Vec<_>>(),
            before.inputs.iter().map(|a| a.sort + 1).collect::<Vec<_>>()
        );
        assert_eq!(after.output, before.output.map(|s| s + 1));
    }
}
