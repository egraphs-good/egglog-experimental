use super::{
    TypedError, pb,
    storage::{Arena, DeclarationKind, Packer, Record, Slot, publish},
};
use std::{
    collections::{HashMap, HashSet},
    hash::{DefaultHasher, Hash, Hasher},
};

/// A view of an owned generated Sort, not an independent sort description.
#[derive(Clone)]
pub struct SortRef(pub(super) Record);

impl SortRef {
    // Instantiate the actual catalog family, retaining only its record and
    // ordered parameter locations. No frontend family/signature table exists.
    pub(super) fn family(family: &Record, parameters: Vec<Self>) -> Result<Self, TypedError> {
        let owner = family.owner.as_ref().unwrap();
        let Some(pb::declaration::Kind::HostSortFamily(definition)) =
            &owner.program.declarations[family.index as usize].kind
        else {
            return Err(TypedError::Invalid(
                "expected a host family definition".into(),
            ));
        };
        if parameters.len() != definition.arity as usize {
            return Err(TypedError::Invalid("family parameter arity".into()));
        }
        for parameter in &parameters {
            parameter.validate_closed()?;
        }
        let mut slots = std::array::from_fn(|_| vec![]);
        let args = (0..parameters.len() as u32).collect();
        slots[Arena::Sort as usize] = parameters
            .into_iter()
            .map(|s| Slot::External(s.0))
            .collect();
        Ok(Self(publish(
            pb::Program {
                ir_version: 1,
                sorts: vec![pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: definition.name.clone(),
                        args,
                    })),
                    ..Default::default()
                }],
                ..Default::default()
            },
            slots,
            vec![family.clone()],
            Arena::Sort,
            0,
        )?))
    }

    pub(super) fn validate_closed(&self) -> Result<(), TypedError> {
        let mut colors = HashMap::new();
        let mut pending = vec![(self.0.clone(), false)];
        while let Some((record, finish)) = pending.pop() {
            let owner = record.owner.as_ref().unwrap();
            let key = (owner.id, record.index);
            if finish {
                colors.insert(key, 2);
                continue;
            }
            match colors.get(&key) {
                Some(2) => continue,
                Some(1) => return Err(TypedError::Invalid("cyclic concrete sort".into())),
                _ => {}
            }
            colors.insert(key, 1);
            pending.push((record.clone(), true));
            match &owner.program.sorts[record.index as usize].kind {
                Some(pb::sort::Kind::Eq(_)) => {}
                Some(pb::sort::Kind::Family(f)) => {
                    let declaration =
                        record.declaration(&f.name, DeclarationKind::HostSortFamily)?;
                    let Some(pb::declaration::Kind::HostSortFamily(d)) =
                        &declaration.owner.as_ref().unwrap().program.declarations
                            [declaration.index as usize]
                            .kind
                    else {
                        return Err(TypedError::Invalid("invalid family declaration".into()));
                    };
                    if d.arity as usize != f.args.len() {
                        return Err(TypedError::Invalid("family sort arity".into()));
                    }
                    for child in f.args.iter().rev() {
                        pending.push((record.resolve(Arena::Sort, *child)?, false));
                    }
                }
                _ => {
                    return Err(TypedError::Invalid(
                        "expected a closed concrete sort".into(),
                    ));
                }
            }
        }
        Ok(())
    }

    // A temporary substitution derived solely from protobuf patterns and
    // concrete sort records. Binder labels are diagnostic, not lookup keys.
    pub(super) fn match_pattern(
        &self,
        actual: &Self,
        bindings: &mut [Option<Self>],
    ) -> Result<(), TypedError> {
        actual.validate_closed()?;
        let mut pending = vec![(self.0.clone(), actual.0.clone())];
        let mut seen = HashSet::new();
        while let Some((pattern, actual)) = pending.pop() {
            let p = pattern.owner.as_ref().unwrap();
            let a = actual.owner.as_ref().unwrap();
            if !seen.insert((p.id, pattern.index, a.id, actual.index)) {
                continue;
            }
            match (
                &p.program.sorts[pattern.index as usize].kind,
                &a.program.sorts[actual.index as usize].kind,
            ) {
                (Some(pb::sort::Kind::Var(index)), _) => {
                    let slot = bindings
                        .get_mut(*index as usize)
                        .ok_or_else(|| TypedError::Invalid("unbound signature parameter".into()))?;
                    let actual = Self(actual);
                    if slot.as_ref().is_some_and(|old| old != &actual) {
                        return Err(TypedError::Invalid(
                            "inconsistent generic substitution".into(),
                        ));
                    }
                    *slot = Some(actual);
                }
                (Some(pb::sort::Kind::Eq(p)), Some(pb::sort::Kind::Eq(a))) if p == a => {}
                (Some(pb::sort::Kind::Family(p)), Some(pb::sort::Kind::Family(a)))
                    if p.name == a.name && p.args.len() == a.args.len() =>
                {
                    for (p, a) in p.args.iter().zip(&a.args) {
                        pending.push((
                            pattern.resolve(Arena::Sort, *p)?,
                            actual.resolve(Arena::Sort, *a)?,
                        ));
                    }
                }
                _ => return Err(TypedError::Invalid("callable argument/result sort".into())),
            }
        }
        Ok(())
    }

    #[doc(hidden)]
    pub fn equality(name: &str) -> Self {
        assert!(!name.is_empty(), "sort names must not be empty");
        let program = pb::Program {
            ir_version: 1,
            sorts: vec![pb::Sort {
                kind: Some(pb::sort::Kind::Eq(name.into())),
                ..Default::default()
            }],
            declarations: vec![pb::Declaration {
                kind: Some(pb::declaration::Kind::EqSort(pb::EqSort {
                    name: name.into(),
                    ..Default::default()
                })),
                ..Default::default()
            }],
            ..Default::default()
        };
        Self(
            publish(
                program,
                std::array::from_fn(|_| vec![]),
                vec![],
                Arena::Sort,
                0,
            )
            .unwrap(),
        )
    }
}

impl PartialEq for SortRef {
    fn eq(&self, other: &Self) -> bool {
        let mut pending = vec![(self.0.clone(), other.0.clone())];
        let mut seen = HashSet::new();
        while let Some((a, b)) = pending.pop() {
            let oa = a.owner.as_ref().unwrap();
            let ob = b.owner.as_ref().unwrap();
            if !seen.insert((oa.id, a.index, ob.id, b.index)) {
                continue;
            }
            match (
                &oa.program.sorts[a.index as usize].kind,
                &ob.program.sorts[b.index as usize].kind,
            ) {
                (Some(pb::sort::Kind::Eq(a)), Some(pb::sort::Kind::Eq(b))) if a == b => {}
                (Some(pb::sort::Kind::Var(a)), Some(pb::sort::Kind::Var(b))) if a == b => {}
                (Some(pb::sort::Kind::Family(fa)), Some(pb::sort::Kind::Family(fb)))
                    if fa.name == fb.name && fa.args.len() == fb.args.len() =>
                {
                    for (ia, ib) in fa.args.iter().zip(&fb.args) {
                        pending.push((
                            a.resolve(Arena::Sort, *ia).unwrap(),
                            b.resolve(Arena::Sort, *ib).unwrap(),
                        ));
                    }
                }
                _ => return false,
            }
        }
        true
    }
}
impl Eq for SortRef {}

impl Hash for SortRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut hashes: HashMap<(usize, u32), u64> = HashMap::new();
        let mut active = HashSet::new();
        let mut pending = vec![(self.0.clone(), false)];
        while let Some((record, finish)) = pending.pop() {
            let owner = record.owner.as_ref().unwrap();
            let key = (owner.id, record.index);
            if hashes.contains_key(&key) {
                continue;
            }
            let kind = owner.program.sorts[record.index as usize]
                .kind
                .as_ref()
                .unwrap();
            if !finish {
                assert!(active.insert(key), "cyclic sort");
                pending.push((record.clone(), true));
                if let pb::sort::Kind::Family(f) = kind {
                    for child in f.args.iter().rev() {
                        pending.push((record.resolve(Arena::Sort, *child).unwrap(), false));
                    }
                }
                continue;
            }
            let mut hash = DefaultHasher::new();
            match kind {
                pb::sort::Kind::Eq(name) => {
                    0u8.hash(&mut hash);
                    name.hash(&mut hash);
                }
                pb::sort::Kind::Var(index) => {
                    1u8.hash(&mut hash);
                    index.hash(&mut hash);
                }
                pb::sort::Kind::Family(f) => {
                    2u8.hash(&mut hash);
                    f.name.hash(&mut hash);
                    f.args.len().hash(&mut hash);
                    for child in &f.args {
                        let child = record.resolve(Arena::Sort, *child).unwrap();
                        hashes[&(child.owner.as_ref().unwrap().id, child.index)].hash(&mut hash);
                    }
                }
                _ => unreachable!("unsupported sort hash"),
            }
            active.remove(&key);
            hashes.insert(key, hash.finish());
        }
        hashes[&(self.0.owner.as_ref().unwrap().id, self.0.index)].hash(state);
    }
}

/// Cached generated declaration owned by a macro's definition factory.
#[doc(hidden)]
#[derive(Clone)]
pub struct Callable(pub(super) Record);

impl Callable {
    pub fn constructor(name: &str, inputs: Vec<SortRef>, output: SortRef) -> Self {
        assert!(!name.is_empty(), "constructor names must not be empty");
        let constructor = pb::Constructor {
            name: name.into(),
            inputs: inputs
                .iter()
                .enumerate()
                .map(|(i, _)| pb::Arg {
                    sort: i as u32,
                    name: String::new(),
                })
                .collect(),
            output: inputs.len() as u32,
            ..Default::default()
        };
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Sort as usize] = inputs
            .into_iter()
            .chain(std::iter::once(output))
            .map(|s| Slot::External(s.0))
            .collect();
        let program = pb::Program {
            ir_version: 1,
            declarations: vec![pb::Declaration {
                kind: Some(pb::declaration::Kind::Constructor(constructor)),
                ..Default::default()
            }],
            ..Default::default()
        };
        Self(publish(program, slots, vec![], Arena::Declaration, 0).unwrap())
    }
}

pub(super) fn compatible(program: &pb::Program, a: &pb::Declaration, b: &pb::Declaration) -> bool {
    // Reuse the shared generated-record comparison for this packet only.
    // Admitted declarations have no node-valued costs/defaults; no expression
    // graph is copied. Installed/provider compatibility remains the engine's.
    let incoming = pb::Program {
        ir_version: 1,
        sorts: program.sorts.clone(),
        declarations: vec![a.clone(), b.clone()],
        ..Default::default()
    };
    egglog::builtin::definitions::reconcile_declarations(
        &incoming,
        &mut pb::Program {
            ir_version: 1,
            ..Default::default()
        },
    )
    .is_ok()
}

pub(super) fn same_callable(a: &Record, b: &Record) -> Result<bool, TypedError> {
    let oa = a.owner.as_ref().unwrap();
    let ob = b.owner.as_ref().unwrap();
    if oa.id == ob.id && a.index == b.index {
        return Ok(true);
    }
    let name_a = match &oa.program.declarations[a.index as usize].kind {
        Some(pb::declaration::Kind::Constructor(c)) => &c.name,
        Some(pb::declaration::Kind::HostPrimitive(p)) => &p.name,
        _ => unreachable!(),
    };
    let name_b = match &ob.program.declarations[b.index as usize].kind {
        Some(pb::declaration::Kind::Constructor(c)) => &c.name,
        Some(pb::declaration::Kind::HostPrimitive(p)) => &p.name,
        _ => unreachable!(),
    };
    if name_a != name_b {
        return Ok(false);
    }
    let mut packer = Packer::default();
    packer.intern(a.clone(), 0);
    packer.intern(b.clone(), 0);
    packer.finish()?;
    Ok(true)
}
