//! Immutable protobuf records and location-only imports. No semantic shadow IR.
use super::{TypedError, pb};
use std::{
    collections::HashMap,
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
};

static NEXT_OWNER: AtomicUsize = AtomicUsize::new(0);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum Arena {
    Node,
    Sort,
    Declaration,
    Rule,
    Ruleset,
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
    pub slots: [Vec<Slot>; 5],
    // Candidate declaration locations, not names/signatures copied from them.
    pub declarations: Vec<Record>,
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

    pub fn declaration(&self, name: &str, sort: bool) -> Result<Self, TypedError> {
        let owner = self.owner.as_ref().unwrap();
        let matches = |d: &pb::Declaration| match &d.kind {
            Some(pb::declaration::Kind::EqSort(d)) => sort && d.name == name,
            Some(pb::declaration::Kind::Constructor(d)) => !sort && d.name == name,
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
            .ok_or_else(|| TypedError::Invalid(format!("declaration unavailable: {name}")))
    }
}

pub(super) type Key = (usize, Arena, u32);

/// Relocate only admitted shapes. Both publication and packing use this visitor.
fn visit(
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
                _ => return Err(invalid()),
            }
        }
        Arena::Sort => {
            let s = &program.sorts[index as usize];
            if s.span.is_some() || !matches!(s.kind, Some(pb::sort::Kind::Eq(_))) {
                return Err(invalid());
            }
        }
        Arena::Declaration => {
            let d = &mut program.declarations[index as usize];
            if d.span.is_some() || d.bindings.is_some() {
                return Err(invalid());
            }
            match d.kind.as_mut().ok_or_else(invalid)? {
                pb::declaration::Kind::EqSort(_) => {}
                pb::declaration::Kind::Constructor(c) if c.cost.is_none() => {
                    for a in &mut c.inputs {
                        a.sort = map(Arena::Sort, a.sort)?;
                    }
                    c.output = map(Arena::Sort, c.output)?;
                }
                _ => return Err(invalid()),
            }
        }
        Arena::Rule => {
            let rule = &mut program.rules[index as usize];
            if rule.span.is_some() {
                return Err(invalid());
            }
            match rule.kind.as_mut().ok_or_else(invalid)? {
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
                _ => return Err(invalid()),
            }
        }
    }
    Ok(())
}

pub(super) fn publish(
    mut program: pb::Program,
    slots: [Vec<Slot>; 5],
    declarations: Vec<Record>,
    arena: Arena,
    index: u32,
) -> Result<Record, TypedError> {
    if program.ir_version != 1 || !program.commands.is_empty() || !program.files.is_empty() {
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
        })),
        arena,
        index,
    })
}

pub(super) struct Packer {
    pub program: pb::Program,
    ids: HashMap<(Key, usize), u32>,
    pending: Vec<(Record, usize, u32)>,
    cursor: usize,
    pub binders: Vec<HashMap<String, String>>,
    pub declarations: HashMap<String, Record>,
}

impl Default for Packer {
    fn default() -> Self {
        Self {
            program: pb::Program {
                ir_version: 1,
                ..Default::default()
            },
            ids: HashMap::new(),
            pending: vec![],
            cursor: 0,
            binders: vec![HashMap::new()],
            declarations: HashMap::new(),
        }
    }
}

impl Packer {
    pub fn intern(&mut self, record: Record, binder: usize) -> u32 {
        let owner = record.owner.as_ref().unwrap();
        let context = if record.arena == Arena::Node {
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
                self.program.rulesets.len() - 1
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
            // Copy exactly one generated record, never the previous fragment.
            let mut one = pb::Program::default();
            match record.arena {
                Arena::Node => {
                    let mut n = owner.program.nodes[record.index as usize].clone();
                    match &mut n.kind {
                        Some(pb::node::Kind::Var(token)) => {
                            *token = self.binders[binder].get(token).cloned().ok_or_else(|| {
                                TypedError::Invalid("free variable in evaluated input".into())
                            })?;
                        }
                        Some(pb::node::Kind::Call(call)) => {
                            self.intern(record.declaration(&call.func, false)?, 0);
                        }
                        _ => {}
                    }
                    one.nodes.push(n);
                }
                Arena::Sort => {
                    let s = owner.program.sorts[record.index as usize].clone();
                    if let Some(pb::sort::Kind::Eq(name)) = &s.kind {
                        self.intern(record.declaration(name, true)?, 0);
                    }
                    one.sorts.push(s);
                }
                Arena::Declaration => one
                    .declarations
                    .push(owner.program.declarations[record.index as usize].clone()),
                Arena::Rule => {
                    let r = owner.program.rules[record.index as usize].clone();
                    let Some(pb::rule_decl::Kind::Rewrite(body)) = &r.kind else {
                        unreachable!()
                    };
                    let roots = std::iter::once(body.lhs)
                        .chain(body.conditions.iter().copied())
                        .chain(std::iter::once(body.rhs))
                        .map(|i| record.resolve(Arena::Node, i))
                        .collect::<Result<Vec<_>, _>>()?;
                    binder = self.binders.len();
                    self.binders.push(super::close::binder(&roots)?);
                    one.rules.push(r);
                }
                Arena::Ruleset => one
                    .rulesets
                    .push(owner.program.rulesets[record.index as usize].clone()),
            }
            visit(&mut one, record.arena, 0, |a, i| {
                Ok(self.intern(record.resolve(a, i)?, binder))
            })?;
            match record.arena {
                Arena::Node => self.program.nodes[index as usize] = one.nodes.pop().unwrap(),
                Arena::Sort => self.program.sorts[index as usize] = one.sorts.pop().unwrap(),
                Arena::Declaration => {
                    let d = one.declarations.pop().unwrap();
                    if let Some(pb::declaration::Kind::Constructor(c)) = &d.kind {
                        self.declarations.insert(c.name.clone(), record.clone());
                    }
                    self.program.declarations[index as usize] = d;
                }
                Arena::Rule => self.program.rules[index as usize] = one.rules.pop().unwrap(),
                Arena::Ruleset => {
                    self.program.rulesets[index as usize] = one.rulesets.pop().unwrap()
                }
            }
            self.cursor += 1;
        }
        // Independent compatible declarations can have distinct owners. Let the
        // engine compare actual signatures, but avoid identical local names twice.
        let mut seen = HashMap::new();
        let mut kept = vec![];
        for d in &self.program.declarations {
            let (sort, name) = match &d.kind {
                Some(pb::declaration::Kind::EqSort(d)) => (true, &d.name),
                Some(pb::declaration::Kind::Constructor(d)) => (false, &d.name),
                _ => unreachable!(),
            };
            if let Some(previous) = seen.insert((sort, name), d) {
                if !super::decl::compatible(&self.program, previous, d) {
                    return Err(TypedError::Invalid(format!(
                        "conflicting declaration {name}"
                    )));
                }
            } else {
                kept.push(d.clone());
            }
        }
        self.program.declarations = kept;
        Ok(())
    }
}
