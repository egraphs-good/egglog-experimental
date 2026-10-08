use super::{
    TypedError, pb,
    storage::{Arena, Packer, Record, Slot, publish},
};

/// A view of an owned generated Sort, not an independent sort description.
#[derive(Clone)]
pub struct SortRef(pub(super) Record);

impl SortRef {
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
        self.0.owner.as_ref().unwrap().program.sorts[self.0.index as usize].kind
            == other.0.owner.as_ref().unwrap().program.sorts[other.0.index as usize].kind
    }
}
impl Eq for SortRef {}

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
