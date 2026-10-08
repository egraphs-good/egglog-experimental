use super::{
    TypedError, pb,
    storage::{Arena, Record, Slot, publish},
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
    let mut a = a.clone();
    let mut b = b.clone();
    // Local packing compares declaration meaning, not first-use diagnostics.
    // This is not an installed-declaration resupply check; the engine owns it.
    a.doc.clear();
    b.doc.clear();
    a.span = None;
    b.span = None;
    match (&mut a.kind, &mut b.kind) {
        (
            Some(pb::declaration::Kind::Constructor(a)),
            Some(pb::declaration::Kind::Constructor(b)),
        ) => {
            if a.inputs.len() != b.inputs.len() {
                return false;
            }
            for (a, b) in a.inputs.iter_mut().zip(&mut b.inputs) {
                if program.sorts[a.sort as usize].kind != program.sorts[b.sort as usize].kind {
                    return false;
                }
                a.sort = 0;
                b.sort = 0;
                a.name.clear();
                b.name.clear();
            }
            if program.sorts[a.output as usize].kind != program.sorts[b.output as usize].kind {
                return false;
            }
            a.output = 0;
            b.output = 0;
        }
        (Some(pb::declaration::Kind::EqSort(_)), Some(pb::declaration::Kind::EqSort(_))) => {}
        _ => return false,
    }
    a == b
}

pub(super) fn same_callable(a: &Record, b: &Record) -> Result<bool, TypedError> {
    let pa = &a.owner.as_ref().unwrap().program;
    let pb = &b.owner.as_ref().unwrap().program;
    let Some(pb::declaration::Kind::Constructor(ca)) = &pa.declarations[a.index as usize].kind
    else {
        unreachable!()
    };
    let Some(pb::declaration::Kind::Constructor(cb)) = &pb.declarations[b.index as usize].kind
    else {
        unreachable!()
    };
    if ca.name != cb.name {
        return Ok(false);
    }
    let same = ca.inputs.len() == cb.inputs.len()
        && ca.cost == cb.cost
        && ca.unextractable == cb.unextractable
        && ca.inputs.iter().zip(&cb.inputs).all(|(sa, sb)| {
            SortRef(a.resolve(Arena::Sort, sa.sort).unwrap())
                == SortRef(b.resolve(Arena::Sort, sb.sort).unwrap())
        })
        && SortRef(a.resolve(Arena::Sort, ca.output)?)
            == SortRef(b.resolve(Arena::Sort, cb.output)?);
    if same {
        Ok(true)
    } else {
        Err(TypedError::Invalid(format!(
            "conflicting declaration {}",
            ca.name
        )))
    }
}
