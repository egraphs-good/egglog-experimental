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
        let catalog = pb::BuiltinCatalog::decode(include_bytes!("builtins/catalog.pb").as_slice())
            .expect("generated catalog is valid protobuf");
        publish_catalog(catalog).expect("unsupported generated catalog shape")
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum Arena {
    Node,
    Sort,
    Declaration,
    Rule,
    Command,
    PrimitiveSort,
    Primitive,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum DeclarationKind {
    NominalSort,
    PrimitiveSort,
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

type Definitions = hashbrown::HashMap<(DeclarationKind, String), (Arena, u32)>;
type Bindings = hashbrown::HashMap<(DeclarationKind, String), DefinitionLink>;

#[derive(Hash)]
struct DefinitionName<'a>(DeclarationKind, &'a str);

impl hashbrown::Equivalent<(DeclarationKind, String)> for DefinitionName<'_> {
    fn equivalent(&self, key: &(DeclarationKind, String)) -> bool {
        self.0 == key.0 && self.1 == key.1
    }
}

enum DefinitionLink {
    Imported(usize, Arena, u32),
    Ambient(Arena, u32),
    External(Record),
}

#[cfg(test)]
thread_local! {
    // Local definition records, named records/imports, dependency owners,
    // cold name probes, and public lookup probes. No wall-clock thresholds.
    pub(super) static LINK_WORK: std::cell::Cell<[usize; 5]> = const { std::cell::Cell::new([0; 5]) };
}

pub(super) struct Owner {
    pub id: usize,
    pub graph: OwnedGraph,
    // Reusable authored protobuf rules live privately, outside the wire Program.
    pub rules: Vec<pb::Rule>,
    pub slots: [Vec<Slot>; 7],
    // Candidate declaration locations, not names/signatures copied from them.
    pub declarations: Vec<Record>,
    pub ambient: Option<Arc<Owner>>,
    // Locations in this owner's generated records, never an initializer copy.
    pub capture: Option<(u32, u32)>,
    // Function declaration and its two exact parameter locations in Node slots.
    pub merge_parameters: Option<(u32, [u32; 2])>,
    // Snapshot data are inspectable records, never live authoring inputs.
    pub observed: bool,
    // Diagnostic presentations share their underlying authored rule record.
    pub rule_origin: Option<Record>,
    // First access seals names after the fresh owner has received capture,
    // merge, origin and ambient metadata. Links retain locations, not signatures
    // or copied transitive environments. Ordinary direct imports need no new Arc.
    definitions: OnceLock<Definitions>,
    bindings: OnceLock<Bindings>,
}

pub(super) enum OwnedGraph {
    Program(pb::Program),
    BuiltinCatalog(pb::BuiltinCatalog),
}

impl Owner {
    #[cfg(test)]
    pub(super) fn retained_definition_links(&self) -> [usize; 3] {
        let bindings = self.bindings.get().expect("bindings already resolved");
        [
            self.declarations.len(),
            bindings.len(),
            bindings
                .values()
                .filter(|link| matches!(link, DefinitionLink::External(_)))
                .count(),
        ]
    }

    fn definitions(&self) -> &Definitions {
        self.definitions.get_or_init(|| {
            let mut definitions = Definitions::default();
            match &self.graph {
                OwnedGraph::Program(program) => {
                    for (index, sort) in program.sorts.iter().enumerate() {
                        if let Some(pb::sort::Kind::Eq(name)) = &sort.kind {
                            definitions
                                .entry((DeclarationKind::NominalSort, name.clone()))
                                .or_insert((Arena::Sort, index as u32));
                        }
                    }
                    for (index, declaration) in program.declarations.iter().enumerate() {
                        if let Some(key) = declaration.kind.as_ref().map(declaration_name) {
                            definitions
                                .entry((key.0, key.1.to_owned()))
                                .or_insert((Arena::Declaration, index as u32));
                        }
                    }
                    #[cfg(test)]
                    LINK_WORK.with(|work| {
                        let mut n = work.get();
                        n[0] += program.declarations.len();
                        work.set(n);
                    });
                }
                OwnedGraph::BuiltinCatalog(catalog) => {
                    for (index, family) in catalog.primitive_sorts.iter().enumerate() {
                        definitions.insert(
                            (DeclarationKind::PrimitiveSort, family.name.clone()),
                            (Arena::PrimitiveSort, index as u32),
                        );
                    }
                    for (index, primitive) in catalog.primitives.iter().enumerate() {
                        definitions.insert(
                            (DeclarationKind::Callable, primitive.name.clone()),
                            (Arena::Primitive, index as u32),
                        );
                    }
                    #[cfg(test)]
                    LINK_WORK.with(|work| {
                        let mut n = work.get();
                        n[0] += catalog.primitive_sorts.len() + catalog.primitives.len();
                        work.set(n);
                    });
                }
            }
            definitions
        })
    }

    fn bindings(&self) -> &Bindings {
        self.bindings.get_or_init(|| {
            let mut wanted = hashbrown::HashSet::new();
            if let OwnedGraph::Program(program) = &self.graph {
                for node in &program.nodes {
                    let call = match &node.kind {
                        Some(pb::node::Kind::Call(call) | pb::node::Kind::GetCost(call)) => {
                            Some(call)
                        }
                        Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                            value: Some(pb::primitive_value::Value::PartialCall(call)),
                        })) => Some(call),
                        _ => None,
                    };
                    if let Some(call) = call {
                        wanted.insert((DeclarationKind::Callable, call.func.clone()));
                    }
                }
                for sort in &program.sorts {
                    match &sort.kind {
                        Some(pb::sort::Kind::Eq(name)) => {
                            wanted.insert((DeclarationKind::NominalSort, name.clone()));
                        }
                        Some(pb::sort::Kind::Primitive(family)) => {
                            wanted.insert((DeclarationKind::PrimitiveSort, family.name.clone()));
                        }
                        _ => (),
                    }
                }
                #[cfg(test)]
                LINK_WORK.with(|work| {
                    let mut n = work.get();
                    n[1] += program.nodes.len() + program.sorts.len();
                    work.set(n);
                });
            }
            let mut direct = HashMap::new();
            for (index, record) in self.declarations.iter().enumerate() {
                let owner = record.owner.as_ref().unwrap();
                direct.entry(owner.id).or_insert(index);
                let key = match record.arena {
                    Arena::Sort => match &owner.graph {
                        OwnedGraph::Program(program) => {
                            match &program.sorts[record.index as usize].kind {
                                Some(pb::sort::Kind::Eq(name)) => {
                                    Some((DeclarationKind::NominalSort, name.as_str()))
                                }
                                _ => None,
                            }
                        }
                        OwnedGraph::BuiltinCatalog(_) => None,
                    },
                    Arena::Declaration => owner.program().unwrap().declarations
                        [record.index as usize]
                        .kind
                        .as_ref()
                        .map(declaration_name),
                    Arena::Primitive => Some((
                        DeclarationKind::Callable,
                        record.primitive().unwrap().name.as_str(),
                    )),
                    Arena::PrimitiveSort => Some((
                        DeclarationKind::PrimitiveSort,
                        record.primitive_sort().unwrap().name.as_str(),
                    )),
                    _ => None,
                };
                if let Some((kind, name)) = key {
                    wanted.insert((kind, name.to_owned()));
                }
            }
            #[cfg(test)]
            LINK_WORK.with(|work| {
                let mut n = work.get();
                n[1] += self.declarations.len();
                work.set(n);
            });
            wanted.retain(|key| !self.definitions().contains_key(key));
            let mut result = Bindings::default();
            let mut pending = self.declarations.iter().rev().cloned().collect::<Vec<_>>();
            if let Some(ambient) = &self.ambient {
                pending.push(Record {
                    owner: Some(ambient.clone()),
                    arena: Arena::PrimitiveSort,
                    index: 0,
                });
            }
            let mut seen = std::collections::HashSet::new();
            while !wanted.is_empty() {
                let Some(context) = pending.pop() else {
                    break;
                };
                let owner = context.owner.as_ref().unwrap();
                if !seen.insert(owner.id) {
                    continue;
                }
                #[cfg(test)]
                LINK_WORK.with(|work| {
                    let mut n = work.get();
                    n[2] += 1;
                    work.set(n);
                });
                let definitions = owner.definitions();
                // Probe the smaller set: a single call never scans the whole
                // catalog, and a declaration-rich Program visits each small
                // imported definition table once rather than once per use.
                let candidates = if wanted.len() < definitions.len() {
                    wanted
                        .iter()
                        .filter_map(|key| {
                            definitions
                                .get(key)
                                .map(|location| (key.clone(), *location))
                        })
                        .collect::<Vec<_>>()
                } else {
                    definitions
                        .iter()
                        .filter(|(key, _)| wanted.contains(*key))
                        .map(|(key, location)| (key.clone(), *location))
                        .collect()
                };
                #[cfg(test)]
                LINK_WORK.with(|work| {
                    let mut n = work.get();
                    n[3] += wanted.len().min(definitions.len());
                    work.set(n);
                });
                for (key, (arena, index)) in candidates {
                    wanted.remove(&key);
                    let location = if self
                        .ambient
                        .as_ref()
                        .is_some_and(|ambient| ambient.id == owner.id)
                    {
                        DefinitionLink::Ambient(arena, index)
                    } else if let Some(import) = direct.get(&owner.id) {
                        DefinitionLink::Imported(*import, arena, index)
                    } else {
                        DefinitionLink::External(Record {
                            owner: Some(owner.clone()),
                            arena,
                            index,
                        })
                    };
                    result.insert(key, location);
                }
                pending.extend(owner.declarations.iter().rev().cloned());
                if let Some(ambient) = &owner.ambient {
                    pending.push(Record {
                        owner: Some(ambient.clone()),
                        arena: Arena::PrimitiveSort,
                        index: 0,
                    });
                }
            }
            result
        })
    }

    // A catalog is never implicitly converted to a user Program. Callers that
    // require executable/user arenas cross this checked ownership boundary.
    pub fn program(&self) -> Result<&pb::Program, TypedError> {
        match &self.graph {
            OwnedGraph::Program(program) => Ok(program),
            OwnedGraph::BuiltinCatalog(_) => Err(TypedError::Invalid(
                "builtin catalog is not a user Program".into(),
            )),
        }
    }

    #[cfg(test)]
    pub fn program_mut(&mut self) -> Result<&mut pb::Program, TypedError> {
        self.definitions.take();
        self.bindings.take();
        match &mut self.graph {
            OwnedGraph::Program(program) => Ok(program),
            OwnedGraph::BuiltinCatalog(_) => Err(TypedError::Invalid(
                "builtin catalog is not a user Program".into(),
            )),
        }
    }
}

fn declaration_name(kind: &pb::declaration::Kind) -> (DeclarationKind, &str) {
    match kind {
        pb::declaration::Kind::Constructor(d) => (DeclarationKind::Callable, &d.name),
        pb::declaration::Kind::Function(d) => (DeclarationKind::Callable, &d.name),
        pb::declaration::Kind::Relation(d) => (DeclarationKind::Callable, &d.name),
        pb::declaration::Kind::UserDefinedPrimitive(d) => (DeclarationKind::Callable, &d.name),
    }
}

// A validated, temporary view of a Binding node and its Let initialization.
pub(super) struct CaptureRecipe {
    pub name: String,
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
                if let Some(bindings) = owner.bindings.get_mut() {
                    for location in bindings.values_mut() {
                        if let DefinitionLink::External(record) = location
                            && let Some(child) = record.owner.take()
                        {
                            pending.push(child);
                        }
                    }
                }
                if let Some(ambient) = owner.ambient.take() {
                    pending.push(ambient);
                }
                if let Some(mut origin) = owner.rule_origin.take()
                    && let Some(parent) = origin.owner.take()
                {
                    pending.push(parent);
                }
            }
        }
    }
}

impl Record {
    pub fn sort(&self) -> Result<&pb::Sort, TypedError> {
        if self.arena != Arena::Sort {
            return Err(TypedError::Invalid("expected an owned sort".into()));
        }
        let sorts = match &self.owner.as_ref().unwrap().graph {
            OwnedGraph::Program(program) => &program.sorts,
            OwnedGraph::BuiltinCatalog(catalog) => &catalog.sorts,
        };
        sorts
            .get(self.index as usize)
            .ok_or_else(|| TypedError::Invalid("owned sort out of bounds".into()))
    }

    pub fn primitive_sort(&self) -> Result<&pb::PrimitiveSort, TypedError> {
        match (&self.owner.as_ref().unwrap().graph, self.arena) {
            (OwnedGraph::BuiltinCatalog(catalog), Arena::PrimitiveSort) => {
                catalog.primitive_sorts.get(self.index as usize)
            }
            _ => None,
        }
        .ok_or_else(|| TypedError::Invalid("expected an owned primitive sort descriptor".into()))
    }

    pub fn primitive(&self) -> Result<&pb::Primitive, TypedError> {
        match (&self.owner.as_ref().unwrap().graph, self.arena) {
            (OwnedGraph::BuiltinCatalog(catalog), Arena::Primitive) => {
                catalog.primitives.get(self.index as usize)
            }
            _ => None,
        }
        .ok_or_else(|| TypedError::Invalid("expected an owned primitive descriptor".into()))
    }

    pub fn key(&self) -> Key {
        let mut record = self;
        while record.arena == Arena::Rule {
            let Some(origin) = &record.owner.as_ref().unwrap().rule_origin else {
                break;
            };
            record = origin;
        }
        (
            record.owner.as_ref().unwrap().id,
            record.arena,
            record.index,
        )
    }

    pub fn capture(&self) -> Result<Option<CaptureRecipe>, TypedError> {
        let owner = self.owner.as_ref().unwrap();
        let Some((read, initialization)) = owner.capture else {
            return Ok(None);
        };
        let invalid = || TypedError::Invalid("invalid canonical capture recipe".into());
        let program = owner.program()?;
        let node = program.nodes.get(read as usize).ok_or_else(invalid)?;
        if self.arena != Arena::Node || self.index != read {
            return Ok(None);
        }
        let Some(pb::node::Kind::Binding(name)) = &node.kind else {
            return Err(invalid());
        };
        let command = program
            .commands
            .get(initialization as usize)
            .ok_or_else(invalid)?;
        let Some(pb::command::Kind::Let(value)) = &command.kind else {
            return Err(invalid());
        };
        let target = self.resolve(Arena::Node, value.binding.ok_or_else(invalid)?)?;
        if target.key() != self.key() {
            return Err(invalid());
        }
        let initializer = self.resolve(Arena::Node, value.value.ok_or_else(invalid)?)?;
        let rhs = &initializer.owner.as_ref().unwrap().program()?.nodes[initializer.index as usize];
        if super::SortRef(self.resolve(Arena::Sort, node.sort_id)?)
            != super::SortRef(initializer.resolve(Arena::Sort, rhs.sort_id)?)
        {
            return Err(invalid());
        }
        Ok(Some(CaptureRecipe {
            name: name.clone(),
            initializer,
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
        // Resolve local/recorded/direct dependencies, not arbitrary unused
        // transitive siblings: sealing never copies a transitive environment.
        #[cfg(test)]
        LINK_WORK.with(|work| {
            let mut n = work.get();
            n[4] += 1;
            work.set(n);
        });
        let owner = self.owner.as_ref().unwrap();
        let key = DefinitionName(kind, name);
        if let Some((arena, index)) = owner.definitions().get(&key) {
            return Ok(Self {
                owner: self.owner.clone(),
                arena: *arena,
                index: *index,
            });
        }
        if let Some(location) = owner.bindings().get(&key) {
            let (owner, arena, index) = match location {
                DefinitionLink::Imported(import, arena, index) => {
                    (&owner.declarations[*import].owner, *arena, *index)
                }
                DefinitionLink::Ambient(arena, index) => (&owner.ambient, *arena, *index),
                DefinitionLink::External(record) => return Ok(record.clone()),
            };
            return Ok(Self {
                owner: owner.clone(),
                arena,
                index,
            });
        }
        Err(TypedError::Invalid(format!(
            "{kind:?} definition unavailable: {name}"
        )))
    }
}

pub(super) type Key = (usize, Arena, u32);

pub(super) fn publish_catalog(catalog: pb::BuiltinCatalog) -> Result<Record, TypedError> {
    let mut sorts = pb::Program {
        sorts: catalog.sorts.clone(),
        ..Default::default()
    };
    for index in 0..sorts.sorts.len() as u32 {
        visit(&mut sorts, Arena::Sort, index, |arena, index| {
            if arena == Arena::Sort && (index as usize) < catalog.sorts.len() {
                Ok(index)
            } else {
                Err(TypedError::Invalid(
                    "builtin sort reference out of bounds".into(),
                ))
            }
        })?;
    }
    let mut names = std::collections::HashSet::new();
    for primitive in &catalog.primitive_sorts {
        if primitive.name.is_empty() || !names.insert((false, &primitive.name)) {
            return Err(TypedError::Invalid("invalid builtin sort identity".into()));
        }
    }
    for primitive in &catalog.primitives {
        if primitive.name.is_empty() || !names.insert((true, &primitive.name)) {
            return Err(TypedError::Invalid(
                "invalid builtin primitive identity".into(),
            ));
        }
        match &primitive.signature {
            Some(signature) => {
                let output = signature
                    .output
                    .ok_or_else(|| TypedError::Invalid("missing builtin output sort".into()))?;
                if signature
                    .inputs
                    .iter()
                    .chain(&signature.varargs)
                    .map(|arg| arg.sort)
                    .chain([output])
                    .any(|i| i as usize >= catalog.sorts.len())
                {
                    return Err(TypedError::Invalid(
                        "builtin signature reference out of bounds".into(),
                    ));
                }
            }
            None => return Err(TypedError::Invalid("missing builtin typing".into())),
        }
    }
    let mut slots = std::array::from_fn(|_| vec![]);
    slots[Arena::Sort as usize] = (0..catalog.sorts.len() as u32).map(Slot::Local).collect();
    slots[Arena::PrimitiveSort as usize] = (0..catalog.primitive_sorts.len() as u32)
        .map(Slot::Local)
        .collect();
    slots[Arena::Primitive as usize] = (0..catalog.primitives.len() as u32)
        .map(Slot::Local)
        .collect();
    let id = NEXT_OWNER
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |i| i.checked_add(1))
        .expect("owner identity exhausted");
    Ok(Record {
        owner: Some(Arc::new(Owner {
            id,
            graph: OwnedGraph::BuiltinCatalog(catalog),
            rules: vec![],
            slots,
            declarations: vec![],
            ambient: None,
            capture: None,
            merge_parameters: None,
            observed: false,
            rule_origin: None,
            definitions: OnceLock::new(),
            bindings: OnceLock::new(),
        })),
        arena: Arena::Sort,
        index: 0,
    })
}

// Freeze is an already-checked, complete reconstruction Program. Keep its
// arenas intact: saved code is not a typed authoring fragment and must not be
// traversed as though it were stored data.
pub(super) fn observe(
    program: pb::Program,
    root_sort: u32,
    builtins: &Record,
) -> Result<Record, TypedError> {
    if root_sort as usize >= program.sorts.len() {
        return Err(TypedError::Decode("invalid snapshot Program".into()));
    }
    let lengths = [
        program.nodes.len(),
        program.sorts.len(),
        program.declarations.len(),
        0,
        program.commands.len(),
        0,
        0,
    ];
    let slots = lengths.map(|len| (0..len as u32).map(Slot::Local).collect());
    let id = NEXT_OWNER
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
        .expect("owner identity exhausted");
    Ok(Record {
        owner: Some(Arc::new(Owner {
            id,
            graph: OwnedGraph::Program(program),
            rules: vec![],
            slots,
            declarations: vec![],
            ambient: builtins.owner.clone(),
            capture: None,
            merge_parameters: None,
            observed: true,
            rule_origin: None,
            definitions: OnceLock::new(),
            bindings: OnceLock::new(),
        })),
        arena: Arena::Sort,
        index: root_sort,
    })
}

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
        let mut one_rules = vec![];
        match record.arena {
            Arena::PrimitiveSort => {
                record.primitive_sort()?;
                result.push(record);
                continue;
            }
            Arena::Primitive => {
                let primitive = record.primitive()?;
                if let Some(signature) = &primitive.signature {
                    let output = signature
                        .output
                        .ok_or_else(|| TypedError::Invalid("missing builtin output".into()))?;
                    for sort in signature
                        .inputs
                        .iter()
                        .chain(&signature.varargs)
                        .map(|arg| arg.sort)
                        .chain([output])
                    {
                        pending.push(record.resolve(Arena::Sort, sort)?);
                    }
                }
                result.push(record);
                continue;
            }
            Arena::Node => {
                let node = owner
                    .program()
                    .unwrap()
                    .nodes
                    .get(record.index as usize)
                    .ok_or_else(|| TypedError::Invalid("invalid node location".into()))?;
                if let Some(capture) = record.capture()? {
                    pending.push(capture.initializer);
                }
                if let Some(pb::node::Kind::Call(call) | pb::node::Kind::GetCost(call)) = &node.kind
                {
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
                let sort = record.sort()?;
                match &sort.kind {
                    Some(pb::sort::Kind::Eq(name)) => {
                        pending.push(record.declaration(name, DeclarationKind::NominalSort)?)
                    }
                    Some(pb::sort::Kind::Primitive(f)) => {
                        pending.push(record.declaration(&f.name, DeclarationKind::PrimitiveSort)?)
                    }
                    _ => (),
                }
                one.sorts.push(sort.clone());
            }
            Arena::Declaration => one
                .declarations
                .push(owner.program().unwrap().declarations[record.index as usize].clone()),
            Arena::Rule => {
                one_rules.push(owner.rules[record.index as usize].clone());
                pending.extend(owner.declarations.iter().cloned());
            }
            Arena::Command => {
                one.commands
                    .push(owner.program().unwrap().commands[record.index as usize].clone());
                pending.extend(owner.declarations.iter().cloned());
            }
        }
        let relocate = |arena, index| {
            pending.push(record.resolve(arena, index)?);
            Ok(index)
        };
        if record.arena == Arena::Rule {
            visit_rule(&mut one_rules[0], relocate)?;
        } else {
            visit(&mut one, record.arena, 0, relocate)?;
        }
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

/// Relocate the evaluated operands and binding addresses of an authored command.
pub(super) fn visit_command(
    command: &mut pb::Command,
    mut node: impl FnMut(u32) -> Result<u32, TypedError>,
) -> Result<(), TypedError> {
    let invalid = || TypedError::Invalid("unsupported protobuf command in typed subset".into());
    if command.span.is_some() {
        return Err(invalid());
    }
    match command.kind.as_mut().ok_or_else(invalid)? {
        pb::command::Kind::Action(action) => visit_action(action, node),
        pb::command::Kind::Let(value) => {
            let binding = value.binding.as_mut().ok_or_else(invalid)?;
            *binding = node(*binding)?;
            let value = value.value.as_mut().ok_or_else(invalid)?;
            *value = node(*value)?;
            Ok(())
        }
        _ => Err(invalid()),
    }
}

pub(super) fn visit_rule(
    rule: &mut pb::Rule,
    mut map: impl FnMut(Arena, u32) -> Result<u32, TypedError>,
) -> Result<(), TypedError> {
    let invalid = || TypedError::Invalid("unsupported protobuf rule in typed subset".into());
    if rule.span.is_some() {
        return Err(invalid());
    }
    match rule.kind.as_mut().ok_or_else(invalid)? {
        pb::rule::Kind::Rule(r) => {
            for fact in &mut r.query {
                *fact = map(Arena::Node, *fact)?;
            }
            for action in &mut r.head {
                visit_action(action, |index| map(Arena::Node, index))?;
            }
        }
        pb::rule::Kind::Rewrite(r) => {
            r.lhs = map(Arena::Node, r.lhs)?;
            for c in &mut r.conditions {
                *c = map(Arena::Node, *c)?;
            }
            r.rhs = map(Arena::Node, r.rhs)?;
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
                pb::node::Kind::Call(c) | pb::node::Kind::GetCost(c) => {
                    for a in &mut c.args {
                        *a = map(Arena::Node, *a)?;
                    }
                }
                pb::node::Kind::Apply(apply) => {
                    let function = apply.function.as_mut().ok_or_else(invalid)?;
                    *function = map(Arena::Node, *function)?;
                    for argument in &mut apply.args {
                        *argument = map(Arena::Node, *argument)?;
                    }
                }
                pb::node::Kind::Union(u) => {
                    for a in &mut u.members {
                        *a = map(Arena::Node, *a)?;
                    }
                }
                pb::node::Kind::Var(_) | pb::node::Kind::Binding(_) => {}
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
                    value: Some(pb::primitive_value::Value::Lambda(lambda)),
                }) => {
                    for capture in &mut lambda.captures {
                        *capture = map(Arena::Node, *capture)?;
                    }
                    lambda.body = map(Arena::Node, lambda.body)?;
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
                pb::sort::Kind::Primitive(f) => {
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
                pb::declaration::Kind::Constructor(c) => {
                    for a in &mut c.inputs {
                        a.sort = map(Arena::Sort, a.sort)?;
                    }
                    c.output = map(Arena::Sort, c.output)?;
                    if let Some(cost) = &mut c.cost {
                        *cost = map(Arena::Node, *cost)?;
                    }
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
                pb::declaration::Kind::UserDefinedPrimitive(primitive) => {
                    for arg in &mut primitive.inputs {
                        arg.sort = map(Arena::Sort, arg.sort)?;
                    }
                    primitive.output = map(Arena::Sort, primitive.output)?;
                    let body = primitive.body.as_mut().ok_or_else(invalid)?;
                    *body = map(Arena::Node, *body)?;
                }
            }
        }
        Arena::Rule => return Err(invalid()),
        Arena::Command => visit_command(&mut program.commands[index as usize], |index| {
            map(Arena::Node, index)
        })?,
        Arena::PrimitiveSort | Arena::Primitive => return Err(invalid()),
    }
    Ok(())
}

pub(super) fn publish(
    mut program: pb::Program,
    slots: [Vec<Slot>; 7],
    declarations: Vec<Record>,
    arena: Arena,
    index: u32,
    mut rules: Vec<pb::Rule>,
) -> Result<Record, TypedError> {
    if !program.files.is_empty()
        || !program.rulesets.is_empty()
        || program.commands.iter().any(|c| {
            !matches!(
                c.kind,
                Some(pb::command::Kind::Action(_) | pb::command::Kind::Let(_))
            )
        })
    {
        return Err(TypedError::Invalid(
            "unsupported typed fragment sections".into(),
        ));
    }
    let lengths = [
        program.nodes.len(),
        program.sorts.len(),
        program.declarations.len(),
        rules.len(),
        program.commands.len(),
        0,
        0,
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
        Arena::Command,
    ]
    .into_iter()
    .zip(lengths)
    {
        let mut relocate = |a: Arena, i: u32| {
            if (i as usize) < slots[a as usize].len() {
                Ok(i)
            } else {
                Err(TypedError::Invalid(
                    "protobuf reference out of bounds".into(),
                ))
            }
        };
        if arena == Arena::Rule {
            for rule in &mut rules {
                visit_rule(rule, &mut relocate)?;
            }
        } else {
            for index in 0..len {
                visit(&mut program, arena, index as u32, &mut relocate)?;
            }
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
            graph: OwnedGraph::Program(program),
            rules,
            slots,
            declarations,
            ambient: None,
            capture: None,
            merge_parameters: None,
            observed: false,
            rule_origin: None,
            definitions: OnceLock::new(),
            bindings: OnceLock::new(),
        })),
        arena,
        index,
    })
}

pub(super) struct Packer {
    pub program: pb::Program,
    pub(super) rules: Vec<pb::Rule>,
    ids: HashMap<(Key, usize), u32>,
    pending: Vec<(Record, usize, u32)>,
    cursor: usize,
    pub binders: Vec<HashMap<String, String>>,
    pub declarations: HashMap<String, Record>,
    pub builtin_demands: Vec<Record>,
    // Request-local renaming of proven recipe locations, never string aliases.
    pub initializations: Vec<(u32, Option<Record>, String)>,
    pub observed_data: bool,
}

impl Default for Packer {
    fn default() -> Self {
        Self {
            program: pb::Program {
                ..Default::default()
            },
            rules: vec![],
            ids: HashMap::new(),
            pending: vec![],
            cursor: 0,
            binders: vec![HashMap::new()],
            declarations: HashMap::new(),
            builtin_demands: vec![],
            initializations: vec![],
            observed_data: false,
        }
    }
}

impl Packer {
    pub fn intern(&mut self, record: Record, binder: usize) -> u32 {
        let owner = record.owner.as_ref().unwrap();
        self.observed_data |=
            owner.observed && matches!(record.arena, Arena::Node | Arena::Command);
        let context = if matches!(record.arena, Arena::Node | Arena::Command) {
            binder
        } else {
            0
        };
        let key = (record.key(), context);
        if let Some(index) = self.ids.get(&key) {
            return *index;
        }
        if matches!(record.arena, Arena::PrimitiveSort | Arena::Primitive) {
            let index = record.index;
            if record.arena == Arena::Primitive {
                self.declarations.insert(
                    record
                        .primitive()
                        .expect("owned primitive descriptor")
                        .name
                        .clone(),
                    record.clone(),
                );
            }
            self.builtin_demands.push(record);
            self.ids.insert(key, index);
            return index;
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
                self.rules.push(pb::Rule::default());
                self.rules.len() - 1
            }
            Arena::Command => {
                self.program.commands.push(pb::Command::default());
                self.program.commands.len() - 1
            }
            Arena::PrimitiveSort | Arena::Primitive => {
                unreachable!("builtin demand is not a Program record")
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
            let mut one_rules = vec![];
            match record.arena {
                Arena::Node => {
                    let mut n = owner.program().unwrap().nodes[record.index as usize].clone();
                    match &mut n.kind {
                        Some(pb::node::Kind::Var(token)) => {
                            *token = self.binders[binder].get(token).cloned().ok_or_else(|| {
                                TypedError::Invalid("free variable in evaluated input".into())
                            })?;
                        }
                        Some(pb::node::Kind::Call(call) | pb::node::Kind::GetCost(call)) => {
                            self.intern(
                                record.declaration(&call.func, DeclarationKind::Callable)?,
                                0,
                            );
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
                    let s = record.sort().unwrap().clone();
                    match &s.kind {
                        Some(pb::sort::Kind::Eq(name)) => {
                            self.intern(record.declaration(name, DeclarationKind::NominalSort)?, 0);
                        }
                        Some(pb::sort::Kind::Primitive(f)) => {
                            self.intern(
                                record.declaration(&f.name, DeclarationKind::PrimitiveSort)?,
                                0,
                            );
                        }
                        _ => {}
                    }
                    one.sorts.push(s);
                }
                Arena::Declaration => {
                    let mut declaration =
                        owner.program().unwrap().declarations[record.index as usize].clone();
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
                                    let node =
                                        &parameter.owner.as_ref().unwrap().program().unwrap().nodes
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
                                let node = &root.owner.as_ref().unwrap().program().unwrap().nodes
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
                                    let node =
                                        &owner.program().unwrap().nodes[child.index as usize];
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
                                    if let Some(pb::node::Kind::PrimitiveValue(
                                        pb::PrimitiveValue {
                                            value: Some(pb::primitive_value::Value::Lambda(lambda)),
                                        },
                                    )) = &node.kind
                                    {
                                        for capture in &lambda.captures {
                                            pending.push(child.resolve(Arena::Node, *capture)?);
                                        }
                                        continue;
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
                        }
                        Some(pb::declaration::Kind::Constructor(c)) => {
                            if let Some(index) = c.cost {
                                let cost = record.resolve(Arena::Node, index)?;
                                let node = &cost.owner.as_ref().unwrap().program().unwrap().nodes
                                    [cost.index as usize];
                                let sort = cost.resolve(Arena::Sort, node.sort_id)?;
                                if super::SortRef(sort)
                                    != <super::builtins::I64 as super::EgglogValue>::sort_ref()
                                    || !matches!(
                                        &node.kind,
                                        Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                                            value: Some(pb::primitive_value::Value::I64(value)),
                                        })) if *value >= 0
                                    )
                                {
                                    return Err(TypedError::Invalid(
                                        "constructor costs require a nonnegative inert i64".into(),
                                    ));
                                }
                            }
                        }
                        Some(pb::declaration::Kind::Relation(_)) => {}
                        Some(pb::declaration::Kind::UserDefinedPrimitive(p)) => {
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
                    one_rules.push(owner.rules[record.index as usize].clone());
                    let mut roots = vec![];
                    visit_rule(&mut one_rules[0], |arena, index| {
                        roots.push(record.resolve(arena, index)?);
                        Ok(index)
                    })?;
                    binder = self.binders.len();
                    self.binders.push(super::close::binder(&roots)?);
                }
                Arena::Command => {
                    let command = owner.program().unwrap().commands[record.index as usize].clone();
                    one.commands.push(command);
                }
                Arena::PrimitiveSort | Arena::Primitive => {
                    unreachable!("builtin descriptor cannot enter Program queue")
                }
            }
            if record.arena == Arena::Node
                && matches!(
                    &one.nodes[0].kind,
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Lambda(_)),
                    }))
                )
            {
                let node = &mut one.nodes[0];
                let sort = record.resolve(Arena::Sort, node.sort_id)?;
                let Some(pb::sort::Kind::Func(function)) = &sort.sort()?.kind else {
                    return Err(TypedError::Invalid(
                        "Lambda requires a function sort".into(),
                    ));
                };
                let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Lambda(lambda)),
                })) = &mut node.kind
                else {
                    unreachable!()
                };
                let body_binder = self.binders.len();
                self.binders.push(
                    (0..lambda.captures.len() + function.params.len())
                        .map(|i| {
                            let name = format!("_{i}");
                            (name.clone(), name)
                        })
                        .collect(),
                );
                node.sort_id = self.intern(sort, 0);
                for capture in &mut lambda.captures {
                    *capture = self.intern(record.resolve(Arena::Node, *capture)?, binder);
                }
                lambda.body = self.intern(record.resolve(Arena::Node, lambda.body)?, body_binder);
            } else {
                let mut relocate = |a, i| Ok(self.intern(record.resolve(a, i)?, binder));
                if record.arena == Arena::Rule {
                    visit_rule(&mut one_rules[0], relocate)?;
                } else {
                    visit(&mut one, record.arena, 0, &mut relocate)?;
                }
            }
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
                        Some(pb::declaration::Kind::UserDefinedPrimitive(p)) => Some(&p.name),
                        _ => None,
                    };
                    if let Some(name) = name {
                        self.declarations.insert(name.clone(), record.clone());
                    }
                    self.program.declarations[index as usize] = d;
                }
                Arena::Rule => self.rules[index as usize] = one_rules.pop().unwrap(),
                Arena::Command => {
                    self.program.commands[index as usize] = one.commands.pop().unwrap()
                }
                Arena::PrimitiveSort | Arena::Primitive => {
                    unreachable!("builtin descriptor cannot enter Program queue")
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
                Some(pb::declaration::Kind::Constructor(d)) => (DeclarationKind::Callable, &d.name),
                Some(pb::declaration::Kind::Function(d)) => (DeclarationKind::Callable, &d.name),
                Some(pb::declaration::Kind::Relation(d)) => (DeclarationKind::Callable, &d.name),
                Some(pb::declaration::Kind::UserDefinedPrimitive(d)) => {
                    (DeclarationKind::Callable, &d.name)
                }
                _ => unreachable!(),
            };
            if seen.insert((kind, name), d).is_none() {
                kept.push(d.clone());
            }
        }
        if kept.len() != self.program.declarations.len() {
            crate::builtin::definitions::reconcile_declarations(
                &self.program,
                &mut pb::Program {
                    ..Default::default()
                },
            )
            .map_err(TypedError::Invalid)?;
        }
        self.program.declarations = kept;
        let mut builtins: HashMap<(bool, String), &Record> = HashMap::new();
        for record in &self.builtin_demands {
            let key = if record.arena == Arena::PrimitiveSort {
                (false, record.primitive_sort()?.name.clone())
            } else {
                (true, record.primitive()?.name.clone())
            };
            if let Some(previous) = builtins.insert(key.clone(), record)
                && !super::decl::same_builtin(previous, record)?
            {
                return Err(TypedError::Invalid(format!(
                    "conflicting builtin descriptor: {}",
                    key.1
                )));
            }
        }
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
            None,
            false,
        );
        let program = pb::Program {
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
                vec![],
            );
            if case == 0 {
                assert_eq!(
                    result
                        .unwrap()
                        .owner
                        .as_ref()
                        .unwrap()
                        .program()
                        .unwrap()
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
    fn sealed_links_keep_local_then_ambient_then_import_precedence() {
        use crate::typed::{EgglogValue, builtins::I64, decl::Callable, expr::Expr};
        let key = "egglog.core.i64.add";
        let catalog =
            pb::BuiltinCatalog::decode(include_bytes!("builtins/catalog.pb").as_slice()).unwrap();
        let ambient = publish_catalog(catalog).unwrap();
        let imported = Callable::constructor(
            key,
            vec![I64::sort_ref(), I64::sort_ref()],
            I64::sort_ref(),
            None,
            false,
        );
        let mut call = Expr::call(
            &imported,
            vec![
                I64::from(1).expression().clone(),
                I64::from(2).expression().clone(),
            ],
        );
        Arc::get_mut(call.0.owner.as_mut().unwrap())
            .unwrap()
            .ambient = ambient.owner.clone();
        let selected = call.0.declaration(key, DeclarationKind::Callable).unwrap();
        assert_eq!(selected.arena, Arena::Primitive);
        assert!(Arc::ptr_eq(
            selected.owner.as_ref().unwrap(),
            ambient.owner.as_ref().unwrap()
        ));

        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Sort as usize].push(Slot::External(I64::sort_ref().0));
        let mut local = publish(
            pb::Program {
                declarations: vec![pb::Declaration {
                    kind: Some(pb::declaration::Kind::Constructor(pb::Constructor {
                        name: key.into(),
                        inputs: vec![],
                        output: 0,
                        ..Default::default()
                    })),
                    ..Default::default()
                }],
                ..Default::default()
            },
            slots,
            vec![imported.0],
            Arena::Declaration,
            0,
            vec![],
        )
        .unwrap();
        Arc::get_mut(local.owner.as_mut().unwrap()).unwrap().ambient = ambient.owner.clone();
        let selected = local.declaration(key, DeclarationKind::Callable).unwrap();
        assert_eq!(selected.arena, Arena::Declaration);
        assert!(Arc::ptr_eq(
            selected.owner.as_ref().unwrap(),
            local.owner.as_ref().unwrap()
        ));
    }

    #[test]
    fn actual_catalog_retains_signatures_without_a_public_application_primitive() {
        use crate::typed::{EgglogValue, builtins::Unit, decl::Callable, expr::Expr};
        let original =
            pb::BuiltinCatalog::decode(include_bytes!("builtins/catalog.pb").as_slice()).unwrap();
        for reverse in [false, true] {
            let mut catalog = original.clone();
            if reverse {
                catalog.primitives.reverse();
                catalog.primitive_sorts.reverse();
            }
            let bytes = catalog.encode_to_vec();
            let context =
                publish_catalog(catalog).expect("the actual catalog retains its descriptors");
            let OwnedGraph::BuiltinCatalog(catalog) = &context.owner.as_ref().unwrap().graph else {
                panic!()
            };
            assert_eq!(catalog.encode_to_vec(), bytes);
            assert!(context.owner.as_ref().unwrap().program().is_err());
            assert!(
                context
                    .declaration("egglog.core.fn.apply", DeclarationKind::Callable)
                    .is_err()
            );
            let record = context
                .declaration("egglog.core.ne", DeclarationKind::Callable)
                .unwrap();
            let primitive = record.primitive().unwrap().clone();
            let mut packer = Packer::default();
            packer.intern(record.clone(), 0);
            packer.finish().unwrap();
            assert!(packer.program.sorts.is_empty() && packer.program.nodes.is_empty());
            assert!(packer.program.declarations.is_empty());
            assert_eq!(packer.builtin_demands[0].primitive().unwrap(), &primitive);
            assert!(
                matches!(Expr::call_with_result(&Callable(record),vec![],Unit::sort_ref()),
                Err(TypedError::Invalid(message)) if message == "callable arity")
            );
        }
    }

    #[test]
    fn required_signatures_keep_checked_publication_boundaries() {
        let original =
            pb::BuiltinCatalog::decode(include_bytes!("builtins/catalog.pb").as_slice()).unwrap();
        let ne = original
            .primitives
            .iter()
            .position(|p| p.name == "egglog.core.ne")
            .unwrap();
        for case in 0..4 {
            let mut catalog = original.clone();
            if case == 1 {
                catalog.primitives[ne].signature = None;
            } else if case >= 2 {
                let Some(signature) = &mut catalog.primitives[ne].signature else {
                    panic!()
                };
                if case == 2 {
                    signature.inputs[0].sort = u32::MAX;
                } else {
                    signature.output = None;
                }
            }
            let bytes = catalog.encode_to_vec();
            let result = publish_catalog(catalog);
            if case == 0 {
                let context = result.unwrap();
                let OwnedGraph::BuiltinCatalog(catalog) = &context.owner.as_ref().unwrap().graph
                else {
                    panic!()
                };
                assert_eq!(catalog.encode_to_vec(), bytes);
            } else {
                assert!(matches!(result, Err(TypedError::Invalid(_))), "case={case}");
            }
        }
    }
}
