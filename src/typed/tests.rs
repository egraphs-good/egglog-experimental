use super::{
    SortRef, close,
    decl::Callable,
    expr::Expr,
    pb,
    storage::{Arena, DeclarationKind, Packer, Record, Slot, publish},
};
use prost::Message;
use std::sync::Arc;

// The same spelling deliberately names a nominal sort, an applied family,
// and a constructor. Imports retain the original generated records.
fn namespace_fragment(imported: bool, reversed: bool, missing: Option<DeclarationKind>) -> Record {
    let mut declarations = vec![
        (
            DeclarationKind::EqSort,
            pb::declaration::Kind::EqSort(pb::EqSort {
                name: "Shared".into(),
                bindings: Some(pb::SortBindings {
                    rust: Some(pb::TypeBinding {
                        path: vec!["Original".into()],
                        type_params: vec![],
                    }),
                    ..Default::default()
                }),
            }),
        ),
        (
            DeclarationKind::HostSortFamily,
            pb::declaration::Kind::HostSortFamily(pb::HostSortFamily {
                name: "Shared".into(),
                arity: 1,
                ..Default::default()
            }),
        ),
        (
            DeclarationKind::Callable,
            pb::declaration::Kind::Constructor(pb::Constructor {
                name: "Shared".into(),
                output: 0,
                ..Default::default()
            }),
        ),
    ];
    if reversed {
        declarations.reverse();
    }
    let mut program = pb::Program {
        ir_version: 1,
        sorts: vec![
            pb::Sort {
                kind: Some(pb::sort::Kind::Eq("Shared".into())),
                ..Default::default()
            },
            pb::Sort {
                kind: Some(pb::sort::Kind::Family(pb::HostSort {
                    name: "Shared".into(),
                    args: vec![0],
                })),
                ..Default::default()
            },
        ],
        nodes: vec![pb::Node {
            sort_id: 0,
            kind: Some(pb::node::Kind::Call(pb::Call {
                func: "Shared".into(),
                args: vec![],
            })),
            ..Default::default()
        }],
        declarations: declarations
            .into_iter()
            .filter(|(kind, _)| Some(*kind) != missing)
            .map(|(_, kind)| pb::Declaration {
                kind: Some(kind),
                ..Default::default()
            })
            .collect(),
        ..Default::default()
    };
    let slots = || {
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Sort as usize] = vec![Slot::Local(0), Slot::Local(1)];
        slots
    };
    let imports = if imported {
        let source = publish(program.clone(), slots(), vec![], Arena::Node, 0).unwrap();
        let records = (0..program.declarations.len())
            .map(|index| Record {
                owner: source.owner.clone(),
                arena: Arena::Declaration,
                index: index as u32,
            })
            .collect();
        program.declarations.clear();
        records
    } else {
        vec![]
    };
    publish(program, slots(), imports, Arena::Node, 0).unwrap()
}

#[test]
fn nominal_family_and_callable_names_close_independently() {
    for imported in [false, true] {
        for reversed in [false, true] {
            let root = namespace_fragment(imported, reversed, None);
            let nominal = SortRef(root.resolve(Arena::Sort, 0).unwrap());
            let family = SortRef(root.resolve(Arena::Sort, 1).unwrap());
            family.validate_closed().unwrap();
            assert!(nominal != family);
            assert!(nominal == SortRef::equality("Shared"));
            for kind in [
                DeclarationKind::EqSort,
                DeclarationKind::HostSortFamily,
                DeclarationKind::Callable,
            ] {
                let declaration = root.declaration("Shared", kind).unwrap();
                let actual = &declaration.owner.as_ref().unwrap().program.declarations
                    [declaration.index as usize]
                    .kind;
                assert!(matches!(
                    (kind, actual),
                    (
                        DeclarationKind::EqSort,
                        Some(pb::declaration::Kind::EqSort(_))
                    ) | (
                        DeclarationKind::HostSortFamily,
                        Some(pb::declaration::Kind::HostSortFamily(_))
                    ) | (
                        DeclarationKind::Callable,
                        Some(pb::declaration::Kind::Constructor(_))
                    )
                ));
                if imported {
                    assert!(root.owner.as_ref().unwrap().declarations.iter().any(|r| {
                        Arc::ptr_eq(
                            r.owner.as_ref().unwrap(),
                            declaration.owner.as_ref().unwrap(),
                        ) && r.index == declaration.index
                    }));
                } else {
                    // Wrong-kind local records must not shadow the correct import.
                    let mut program = root.owner.as_ref().unwrap().program.clone();
                    program
                        .declarations
                        .retain(|d| d.kind.as_ref() != actual.as_ref());
                    let mut slots = std::array::from_fn(|_| vec![]);
                    slots[Arena::Sort as usize] = vec![Slot::Local(0), Slot::Local(1)];
                    let mixed =
                        publish(program, slots, vec![declaration.clone()], Arena::Node, 0).unwrap();
                    let selected = mixed.declaration("Shared", kind).unwrap();
                    assert!(Arc::ptr_eq(
                        selected.owner.as_ref().unwrap(),
                        declaration.owner.as_ref().unwrap()
                    ));
                    assert_eq!(selected.index, declaration.index);
                }
            }
            let definition = root
                .declaration("Shared", DeclarationKind::HostSortFamily)
                .unwrap();
            let applied = SortRef::family(&definition, vec![nominal]).unwrap();
            assert!(applied == family);
            assert!(SortRef::family(&definition, vec![]).is_err());
            let hash = |sort: &SortRef| {
                let mut h = std::hash::DefaultHasher::new();
                std::hash::Hash::hash(sort, &mut h);
                std::hash::Hasher::finish(&h)
            };
            assert_eq!(hash(&applied), hash(&family));
            for family_first in [false, true] {
                let mut roots = [root.clone(), family.0.clone()];
                if family_first {
                    roots.reverse();
                }
                let mut packer = Packer::default();
                for record in roots {
                    packer.intern(record, 0);
                }
                packer.finish().unwrap();
                assert_eq!(packer.program.declarations.len(), 3);
                assert!(packer.program.declarations.iter().any(|d| matches!(
                    &d.kind, Some(pb::declaration::Kind::EqSort(d)) if d.name == "Shared"
                )));
                assert!(packer.program.declarations.iter().any(|d| matches!(
                    &d.kind, Some(pb::declaration::Kind::HostSortFamily(d)) if d.name == "Shared"
                )));
                assert!(packer.program.declarations.iter().any(|d| matches!(
                    &d.kind, Some(pb::declaration::Kind::Constructor(d)) if d.name == "Shared"
                )));
                let bytes = packer.program.encode_to_vec();
                assert_eq!(
                    pb::Program::decode(bytes.as_slice()).unwrap(),
                    packer.program
                );
            }
        }
    }
}

#[test]
fn missing_declaration_kind_never_uses_a_same_named_other_kind() {
    for imported in [false, true] {
        for reversed in [false, true] {
            for missing in [
                DeclarationKind::EqSort,
                DeclarationKind::HostSortFamily,
                DeclarationKind::Callable,
            ] {
                let root = namespace_fragment(imported, reversed, Some(missing));
                assert!(root.declaration("Shared", missing).is_err());
                let required = match missing {
                    DeclarationKind::EqSort => root.resolve(Arena::Sort, 0).unwrap(),
                    DeclarationKind::HostSortFamily => {
                        let family = root.resolve(Arena::Sort, 1).unwrap();
                        assert!(SortRef(family.clone()).validate_closed().is_err());
                        family
                    }
                    DeclarationKind::Callable => root,
                };
                let mut packer = Packer::default();
                packer.intern(required, 0);
                assert!(packer.finish().is_err());
            }
        }
    }
}

#[test]
fn namespace_split_keeps_same_kind_and_callable_kind_conflicts() {
    for changed in 0..4 {
        let root = namespace_fragment(false, false, None);
        let mut program = root.owner.as_ref().unwrap().program.clone();
        match changed {
            0 => {
                let Some(pb::declaration::Kind::EqSort(d)) = &mut program.declarations[0].kind
                else {
                    unreachable!()
                };
                d.bindings = Some(pb::SortBindings {
                    rust: Some(pb::TypeBinding {
                        path: vec!["Changed".into()],
                        type_params: vec![],
                    }),
                    ..Default::default()
                });
            }
            1 => {
                let Some(pb::declaration::Kind::HostSortFamily(d)) =
                    &mut program.declarations[1].kind
                else {
                    unreachable!()
                };
                d.arity = 2;
            }
            2 => {
                let Some(pb::declaration::Kind::Constructor(d)) = &mut program.declarations[2].kind
                else {
                    unreachable!()
                };
                d.unextractable = true;
            }
            _ => {
                program.declarations[2].kind =
                    Some(pb::declaration::Kind::HostPrimitive(pb::HostPrimitive {
                        name: "Shared".into(),
                        typing: Some(pb::host_primitive::Typing::Signature(
                            pb::GenericSignature {
                                output: Some(0),
                                ..Default::default()
                            },
                        )),
                    }));
            }
        }
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Sort as usize] = vec![Slot::Local(0), Slot::Local(1)];
        let other = publish(program, slots, vec![], Arena::Node, 0).unwrap();
        let mut packer = Packer::default();
        for record in [root, other] {
            packer.intern(record.resolve(Arena::Sort, 1).unwrap(), 0);
            packer.intern(record, 0);
        }
        assert!(packer.finish().is_err(), "conflict case {changed}");
    }
}

#[test]
fn family_sort_comparison_resolves_slots_not_raw_indices() {
    use super::{EgglogValue, builtins::I64};
    let family = super::storage::builtin_catalog()
        .declaration("Vec", DeclarationKind::HostSortFamily)
        .unwrap();
    let integers = SortRef::family(&family, vec![I64::sort_ref()]).unwrap();
    let atoms = SortRef::family(&family, vec![SortRef::equality("Atom")]).unwrap();
    assert!(
        integers != atoms,
        "same local slot 0 must not hide different imported sorts"
    );
    let mut slots = std::array::from_fn(|_| vec![]);
    slots[Arena::Sort as usize] = vec![
        Slot::External(SortRef::equality("Unused").0),
        Slot::External(I64::sort_ref().0),
    ];
    let shifted = SortRef(
        publish(
            pb::Program {
                ir_version: 1,
                sorts: vec![pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "Vec".into(),
                        args: vec![1],
                    })),
                    ..Default::default()
                }],
                ..Default::default()
            },
            slots,
            vec![family],
            Arena::Sort,
            0,
        )
        .unwrap(),
    );
    assert!(
        integers == shifted,
        "equal sorts at different slots must agree"
    );
}

#[test]
fn generic_calls_infer_from_actual_arguments_and_result_records() {
    use super::{EgglogValue, builtins::I64};
    let catalog = super::storage::builtin_catalog();
    let family = catalog
        .declaration("Vec", DeclarationKind::HostSortFamily)
        .unwrap();
    let integers = SortRef::family(&family, vec![I64::sort_ref()]).unwrap();
    let atoms = SortRef::family(&family, vec![SortRef::equality("A")]).unwrap();
    let empty = Callable(
        catalog
            .declaration("egglog.core.vec.empty", DeclarationKind::Callable)
            .unwrap(),
    );
    let of = Callable(
        catalog
            .declaration("egglog.core.vec.of", DeclarationKind::Callable)
            .unwrap(),
    );
    let get = Callable(
        catalog
            .declaration("egglog.core.vec.get", DeclarationKind::Callable)
            .unwrap(),
    );
    assert!(Expr::call_with_result(&empty, vec![], integers.clone()).is_ok());
    assert!(Expr::call_with_result(&of, vec![], atoms.clone()).is_ok());
    assert!(Expr::call_with_result(&empty, vec![], I64::sort_ref()).is_err());
    let scalar = I64::from(7).expression().clone();
    assert!(Expr::call_with_result(&of, vec![scalar.clone()], atoms).is_err());
    let vector = Expr::call_with_result(&of, vec![scalar.clone()], integers).unwrap();
    assert!(
        Expr::call_with_result(&get, vec![vector.clone(), scalar.clone()], I64::sort_ref()).is_ok()
    );
    assert!(Expr::call_with_result(&get, vec![vector, scalar], SortRef::equality("A")).is_err());
}

#[test]
fn generic_tail_patterns_keep_group_width_and_share_every_binding() {
    use super::{
        EgglogValue,
        builtins::{F64, I64},
    };
    // Locations 0/1 are binder variables; 2/3 import concrete scalar sorts.
    let declaration = |inputs: &[u32], tail: &[u32], output, parameters| {
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Sort as usize] = vec![
            Slot::Local(0),
            Slot::Local(1),
            Slot::External(I64::sort_ref().0),
            Slot::External(F64::sort_ref().0),
        ];
        Callable(
            publish(
                pb::Program {
                    ir_version: 1,
                    sorts: (0..2)
                        .map(|i| pb::Sort {
                            kind: Some(pb::sort::Kind::Var(i)),
                            ..Default::default()
                        })
                        .collect(),
                    declarations: vec![pb::Declaration {
                        kind: Some(pb::declaration::Kind::HostPrimitive(pb::HostPrimitive {
                            name: "test.grouped".into(),
                            typing: Some(pb::host_primitive::Typing::Signature(
                                pb::GenericSignature {
                                    type_params: (0..parameters).map(|i| format!("T{i}")).collect(),
                                    inputs: inputs
                                        .iter()
                                        .map(|sort| pb::Arg {
                                            sort: *sort,
                                            ..Default::default()
                                        })
                                        .collect(),
                                    varargs: tail
                                        .iter()
                                        .map(|sort| pb::Arg {
                                            sort: *sort,
                                            ..Default::default()
                                        })
                                        .collect(),
                                    output: Some(output),
                                },
                            )),
                        })),
                        ..Default::default()
                    }],
                    ..Default::default()
                },
                slots,
                vec![],
                Arena::Declaration,
                0,
            )
            .unwrap(),
        )
    };
    let integer = I64::from(7).expression().clone();
    let float = F64::from(2.5).expression().clone();
    let fixed = declaration(&[0], &[], 0, 1);
    assert!(Expr::call_with_result(&fixed, vec![integer.clone()], I64::sort_ref()).is_ok());
    for arguments in [vec![], vec![integer.clone(), integer.clone()]] {
        assert!(Expr::call_with_result(&fixed, arguments, I64::sort_ref()).is_err());
    }
    let homogeneous = declaration(&[], &[0], 0, 1);
    assert!(Expr::call_with_result(&homogeneous, vec![], I64::sort_ref()).is_ok());
    assert!(
        Expr::call_with_result(&homogeneous, vec![integer.clone(); 3], I64::sort_ref()).is_ok()
    );
    let repeated = declaration(&[], &[0, 0], 0, 1);
    for count in [0, 2, 4] {
        assert!(
            Expr::call_with_result(&repeated, vec![integer.clone(); count], I64::sort_ref())
                .is_ok()
        );
    }
    for count in [1, 3] {
        assert!(
            Expr::call_with_result(&repeated, vec![integer.clone(); count], I64::sort_ref())
                .is_err(),
            "equal tail patterns must not collapse their group width"
        );
    }
    let pairs = declaration(&[1], &[0, 1], 0, 2);
    let valid = vec![
        float.clone(),
        integer.clone(),
        float.clone(),
        integer.clone(),
        float.clone(),
    ];
    assert!(Expr::call_with_result(&pairs, valid.clone(), I64::sort_ref()).is_ok());
    assert!(Expr::call_with_result(&pairs, vec![float.clone()], I64::sort_ref()).is_ok());
    assert!(Expr::call_with_result(&pairs, vec![], I64::sort_ref()).is_err());
    assert!(Expr::call_with_result(&pairs, valid[..4].to_vec(), I64::sort_ref()).is_err());
    assert!(Expr::call_with_result(&pairs, valid.clone(), F64::sort_ref()).is_err());
    let mut swapped = valid.clone();
    swapped.swap(1, 2);
    assert!(Expr::call_with_result(&pairs, swapped, I64::sort_ref()).is_err());
    for position in [0, 2, 4] {
        let mut invalid = valid.clone();
        invalid[position] = integer.clone();
        assert!(
            Expr::call_with_result(&pairs, invalid, I64::sort_ref()).is_err(),
            "fixed prefix and every group share the same substitution"
        );
    }
    let triples = declaration(&[], &[0, 1, 0], 0, 2);
    let mut arguments: Vec<_> = (0..3)
        .flat_map(|_| [integer.clone(), float.clone(), integer.clone()])
        .collect();
    assert!(Expr::call_with_result(&triples, arguments.clone(), I64::sort_ref()).is_ok());
    arguments[4] = integer.clone();
    assert!(
        Expr::call_with_result(&triples, arguments, I64::sort_ref()).is_err(),
        "a mismatch inside the middle group must be checked"
    );
    assert!(
        Expr::call_with_result(&declaration(&[], &[0, 1], 0, 2), vec![], I64::sort_ref()).is_err(),
        "result inference must not leave the other parameter undetermined"
    );
    assert!(
        Expr::call_with_result(&declaration(&[], &[0], 2, 1), vec![], I64::sort_ref()).is_err(),
        "a concrete result cannot determine an unused tail parameter"
    );
    assert!(
        Expr::call_with_result(
            &declaration(&[], &[2, 3], 2, 0),
            vec![integer.clone(), integer],
            I64::sort_ref()
        )
        .is_err(),
        "concrete tail positions are checked too"
    );
}

#[test]
fn grouped_declarations_relocate_every_tail_position() {
    use super::{
        EgglogValue,
        builtins::{F64, I64},
    };
    let declaration = |imports: Vec<SortRef>, tail: Vec<u32>| {
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Sort as usize] = imports.into_iter().map(|s| Slot::External(s.0)).collect();
        Callable(
            publish(
                pb::Program {
                    ir_version: 1,
                    declarations: vec![pb::Declaration {
                        kind: Some(pb::declaration::Kind::HostPrimitive(pb::HostPrimitive {
                            name: "test.relocated.group".into(),
                            typing: Some(pb::host_primitive::Typing::Signature(
                                pb::GenericSignature {
                                    inputs: vec![pb::Arg {
                                        sort: tail[0],
                                        name: "prefix".into(),
                                    }],
                                    output: Some(tail[0]),
                                    varargs: tail
                                        .into_iter()
                                        .enumerate()
                                        .map(|(i, sort)| pb::Arg {
                                            sort,
                                            name: format!("item{i}"),
                                        })
                                        .collect(),
                                    ..Default::default()
                                },
                            )),
                        })),
                        doc: Some("retain complete grouped record".into()),
                        ..Default::default()
                    }],
                    ..Default::default()
                },
                slots,
                vec![],
                Arena::Declaration,
                0,
            )
            .unwrap(),
        )
    };
    let original = declaration(vec![I64::sort_ref(), F64::sort_ref()], vec![0, 1, 0]);
    let relocated = declaration(vec![F64::sort_ref(), I64::sort_ref()], vec![1, 0, 1]);
    let changed = declaration(vec![I64::sort_ref(), I64::sort_ref()], vec![0, 1, 0]);
    assert!(super::decl::same_callable(&original.0, &relocated.0).unwrap());
    assert!(super::decl::same_callable(&original.0, &changed.0).is_err());
    let mut programs = vec![];
    for callable in [&original, &relocated] {
        let mut packer = Packer::default();
        packer.intern(callable.0.clone(), 0);
        packer.finish().unwrap();
        let declaration = &packer.program.declarations[0];
        assert_eq!(
            declaration.doc.as_deref(),
            Some("retain complete grouped record")
        );
        let Some(pb::declaration::Kind::HostPrimitive(primitive)) = &declaration.kind else {
            panic!()
        };
        let Some(pb::host_primitive::Typing::Signature(signature)) = &primitive.typing else {
            panic!()
        };
        assert_eq!(signature.varargs.len(), 3);
        for (position, (arg, family)) in signature
            .varargs
            .iter()
            .zip(["i64", "f64", "i64"])
            .enumerate()
        {
            assert_eq!(arg.name, format!("item{position}"));
            assert!(matches!(&packer.program.sorts[arg.sort as usize].kind,
                Some(pb::sort::Kind::Family(f)) if f.name == family));
        }
        programs.push(packer.program.encode_to_vec());
    }
    assert_eq!(programs[0], programs[1]);
}

#[test]
fn vec_calls_and_values_preserve_actual_ordered_child_records() {
    use super::{
        EgglogValue,
        builtins::{I64, Vec as EVec},
    };
    let leaf = I64::from(7);
    let vector = EVec::<I64>::of([leaf.clone(), I64::from(11), leaf.clone()]);
    let weak = Arc::downgrade(vector.expression().0.owner.as_ref().unwrap());
    let p = packed_query(&[vector.expression().0.clone()]);
    let Some(pb::node::Kind::Call(call)) = &p.nodes[0].kind else {
        panic!()
    };
    assert_eq!(call.func, "egglog.core.vec.of");
    assert_eq!(call.args.len(), 3);
    assert_eq!(call.args[0], call.args[2]);
    for (index, expected) in call.args.iter().zip([7, 11, 7]) {
        assert!(matches!(&p.nodes[*index as usize].kind,
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue { value: Some(pb::primitive_value::Value::I64(v)) })) if *v == expected));
    }
    let owner = vector.expression().0.owner.as_ref().unwrap();
    assert_eq!(owner.program.nodes.len(), 1);
    assert_eq!(owner.slots[Arena::Node as usize].len(), 3);
    drop(vector);
    assert!(
        weak.upgrade().is_none(),
        "retained leaf must not retain parent"
    );
    let sort = EVec::<I64>::sort_ref();
    let first = leaf.expression().0.clone();
    let second = I64::from(11).expression().0.clone();
    let value = |items, imports| {
        Expr(node(
            &sort,
            pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Vec(pb::ValueList { items })),
            }),
            imports,
            vec![],
        ))
    };
    let a = value(vec![0, 1, 0], vec![first.clone(), second.clone()]);
    let relocated = value(vec![1, 0, 1], vec![second.clone(), first.clone()]);
    let different = value(vec![0, 1, 0], vec![second, first]);
    assert_eq!(a, relocated);
    assert_ne!(
        a, different,
        "raw equal ValueList indices are not equal values"
    );
    let mut ah = std::hash::DefaultHasher::new();
    let mut bh = std::hash::DefaultHasher::new();
    std::hash::Hash::hash(&a, &mut ah);
    std::hash::Hash::hash(&relocated, &mut bh);
    assert_eq!(
        std::hash::Hasher::finish(&ah),
        std::hash::Hasher::finish(&bh)
    );

    let named = super::var::<I64>("__typed_v_0");
    let fresh = super::expr::variable::<I64>(super::expr::fresh_scope(), 0);
    let with_variables = value(
        vec![1, 0, 1],
        vec![named.expression().0.clone(), fresh.expression().0.clone()],
    );
    let p = packed_query(&[with_variables.0]);
    let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
        value: Some(pb::primitive_value::Value::Vec(items)),
    })) = &p.nodes[0].kind
    else {
        panic!()
    };
    assert_eq!(items.items[0], items.items[2]);
    assert!(matches!(&p.nodes[items.items[0] as usize].kind,
        Some(pb::node::Kind::Var(name)) if name == "__typed_v_1"));
    assert!(matches!(&p.nodes[items.items[1] as usize].kind,
        Some(pb::node::Kind::Var(name)) if name == "__typed_v_0"));

    let atom = SortRef::equality("VecOwnershipAtom");
    let family = super::storage::builtin_catalog()
        .declaration("Vec", DeclarationKind::HostSortFamily)
        .unwrap();
    let vector_sort = SortRef::family(&family, vec![atom.clone()]).unwrap();
    let of = Callable(
        super::storage::builtin_catalog()
            .declaration("egglog.core.vec.of", DeclarationKind::Callable)
            .unwrap(),
    );
    let leaf = Expr::call(&Callable::constructor("Leaf", vec![], atom.clone()), vec![]);
    let pack = Callable::constructor("Pack", vec![vector_sort.clone()], atom);
    for growing_first in [false, true] {
        let mut term = leaf.clone();
        for _ in 0..100_000 {
            let children = if growing_first {
                vec![term, leaf.clone()]
            } else {
                vec![leaf.clone(), term]
            };
            let vector = Expr::call_with_result(&of, children, vector_sort.clone()).unwrap();
            let owner = vector.0.owner.as_ref().unwrap();
            assert_eq!(owner.program.nodes.len(), 1);
            assert_eq!(owner.slots[Arena::Node as usize].len(), 2);
            assert_eq!(owner.declarations.len(), 1);
            term = Expr::call(&pack, vec![vector]);
        }
        let weak = Arc::downgrade(term.0.owner.as_ref().unwrap());
        std::thread::spawn(move || drop(term)).join().unwrap();
        assert!(weak.upgrade().is_none());
    }
}

#[test]
// Symbolic Add preserves ordered children; swapping operands also changes
// which operator implementation owns the growing input. It is not arithmetic.
#[allow(clippy::if_same_then_else)]
fn scalar_records_remain_authoritative_and_parents_are_reclaimed() {
    use super::{EgglogValue, builtins::I64};
    let leaf = I64::from(7);
    let a = &leaf + I64::from(11);
    let weak = Arc::downgrade(a.expression().0.owner.as_ref().unwrap());
    let packed = packed_query(&[a.expression().0.clone()]);
    let Some(pb::node::Kind::Call(call)) = &packed.nodes[0].kind else {
        panic!()
    };
    assert_eq!(call.func, "egglog.core.i64.add");
    assert_eq!(call.args.len(), 2);
    for (id, expected) in call.args.iter().zip([7, 11]) {
        assert!(matches!(&packed.nodes[*id as usize].kind,
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::I64(value))
            })) if *value == expected));
    }
    assert_eq!(
        packed.declarations.len(),
        2,
        "only reachable scalar family and primitive"
    );
    drop(a);
    assert!(
        weak.upgrade().is_none(),
        "retained leaf cannot retain parents"
    );
    for left in [false, true] {
        let mut value = leaf.clone();
        for _ in 0..100_000 {
            value = if left { value + &leaf } else { &leaf + value };
            let owner = value.expression().0.owner.as_ref().unwrap();
            assert_eq!(owner.program.nodes.len(), 1);
            assert_eq!(owner.slots[Arena::Node as usize].len(), 2);
            assert_eq!(owner.declarations.len(), 1);
        }
        let weak = Arc::downgrade(value.expression().0.owner.as_ref().unwrap());
        std::thread::spawn(move || drop(value)).join().unwrap();
        assert!(weak.upgrade().is_none());
    }
}

#[test]
fn host_calls_read_changed_generated_definitions_not_cached_signatures() {
    use super::{EgglogValue, builtins::I64};
    let mut program = super::storage::builtin_catalog()
        .owner
        .as_ref()
        .unwrap()
        .program
        .clone();
    let index = program
        .declarations
        .iter()
        .position(|d| {
            matches!(&d.kind,
        Some(pb::declaration::Kind::HostPrimitive(h)) if h.name == "egglog.core.i64.add")
        })
        .unwrap();
    let Some(pb::declaration::Kind::HostPrimitive(primitive)) =
        &mut program.declarations[index].kind
    else {
        panic!()
    };
    primitive.name = "test.changed.generated.key".into();
    let mut slots = std::array::from_fn(|_| vec![]);
    slots[Arena::Sort as usize] = (0..program.sorts.len() as u32).map(Slot::Local).collect();
    slots[Arena::Declaration as usize] = (0..program.declarations.len() as u32)
        .map(Slot::Local)
        .collect();
    let callable =
        Callable(publish(program, slots, vec![], Arena::Declaration, index as u32).unwrap());
    let call = Expr::call(
        &callable,
        vec![
            I64::from(7).expression().clone(),
            I64::from(11).expression().clone(),
        ],
    );
    let packed = packed_query(&[call.0]);
    assert!(
        matches!(&packed.nodes[0].kind, Some(pb::node::Kind::Call(c)) if c.func == "test.changed.generated.key")
    );
    assert!(packed.declarations.iter().any(|d| matches!(&d.kind,
        Some(pb::declaration::Kind::HostPrimitive(h)) if h.name == "test.changed.generated.key")));
    assert!(!packed.declarations.iter().any(|d| matches!(&d.kind,
        Some(pb::declaration::Kind::HostPrimitive(h)) if h.name == "egglog.core.i64.add")));
}

// A private raw-record builder lets tests mutate only generated fields before
// immutable publication, without an authoring-side semantic representation.
fn node(
    sort: &SortRef,
    kind: pb::node::Kind,
    imports: Vec<Record>,
    declarations: Vec<Record>,
) -> Record {
    let mut slots = std::array::from_fn(|_| vec![]);
    slots[Arena::Node as usize] = imports.into_iter().map(Slot::External).collect();
    slots[Arena::Sort as usize] = vec![Slot::External(sort.0.clone())];
    publish(
        pb::Program {
            ir_version: 1,
            nodes: vec![pb::Node {
                kind: Some(kind),
                ..Default::default()
            }],
            ..Default::default()
        },
        slots,
        declarations,
        Arena::Node,
        0,
    )
    .unwrap()
}

fn packed_query(roots: &[Record]) -> pb::Program {
    let mut packer = Packer::default();
    packer.binders.push(close::binder(roots).unwrap());
    let facts = roots.iter().map(|r| packer.intern(r.clone(), 1)).collect();
    packer.program.commands.push(pb::Command {
        kind: Some(pb::command::Kind::Check(pb::Check { facts })),
        ..Default::default()
    });
    packer.finish().unwrap();
    packer.program
}

#[test]
fn generated_var_authority_determinism_and_whole_binder_names() {
    let sort = SortRef::equality("M");
    let fresh = |n| {
        node(
            &sort,
            pb::node::Kind::Var(format!("@typed:f:{n}:0")),
            vec![],
            vec![],
        )
    };
    let named = node(
        &sort,
        pb::node::Kind::Var("@typed:n:5f5f74797065645f765f30".into()),
        vec![],
        vec![],
    ); // __typed_v_0
    let a = fresh(7);
    let b = fresh(8);
    let first = packed_query(&[a.clone(), b.clone(), a.clone(), named.clone()]);
    // Construction/allocation order and fresh-token magnitude are not ordering.
    let d = fresh(99);
    let c = fresh(100);
    let second = packed_query(&[c, d, a.clone(), named.clone()]);
    let repeated = packed_query(&[fresh(100), fresh(99), fresh(100), named.clone()]);
    // Different owner aliases versus equal fresh strings preserve the same
    // variable equivalence, though ordinary Node sharing need not match bytes.
    let Some(pb::node::Kind::Var(name)) = &first.nodes[0].kind else {
        panic!()
    };
    assert_eq!(name, "__typed_v_1");
    assert_ne!(first.encode_to_vec(), second.encode_to_vec());
    let aa = fresh(100);
    let bb = fresh(99);
    assert_eq!(
        first.encode_to_vec(),
        packed_query(&[aa.clone(), bb, aa, named]).encode_to_vec()
    );
    assert_eq!(repeated.nodes[0].kind, repeated.nodes[2].kind);
    let changed = node(
        &sort,
        pb::node::Kind::Var("@typed:n:78".into()),
        vec![],
        vec![],
    );
    assert_ne!(Expr(a.clone()), Expr(changed.clone()));
    assert_eq!(
        packed_query(&[changed]).nodes[0].kind,
        Some(pb::node::Kind::Var("x".into()))
    );
    assert!(
        close::binder(&[node(
            &sort,
            pb::node::Kind::Var("foreign".into()),
            vec![],
            vec![]
        )])
        .is_err()
    );
}

#[test]
fn context_sensitive_packing_and_slot_permutation() {
    let sort = SortRef::equality("M");
    let a = node(
        &sort,
        pb::node::Kind::Var("@typed:f:1:0".into()),
        vec![],
        vec![],
    );
    let b = node(
        &sort,
        pb::node::Kind::Var("@typed:f:2:0".into()),
        vec![],
        vec![],
    );
    let call = Callable::constructor("Pair", vec![sort.clone(), sort.clone()], sort.clone());
    let original = node(
        &sort,
        pb::node::Kind::Call(pb::Call {
            func: "Pair".into(),
            args: vec![0, 1],
        }),
        vec![a.clone(), b.clone()],
        vec![call.0.clone()],
    );
    let permuted = node(
        &sort,
        pb::node::Kind::Call(pb::Call {
            func: "Pair".into(),
            args: vec![1, 0],
        }),
        vec![b.clone(), a.clone()],
        vec![call.0.clone()],
    );
    assert_eq!(
        packed_query(std::slice::from_ref(&original)).encode_to_vec(),
        packed_query(&[permuted]).encode_to_vec()
    );
    let mut p = Packer::default();
    p.binders
        .push(close::binder(&[a.clone(), b.clone()]).unwrap());
    p.binders
        .push(close::binder(&[b.clone(), a.clone()]).unwrap());
    let first = p.intern(original.clone(), 1);
    let second = p.intern(original, 2);
    p.finish().unwrap();
    assert_ne!(first, second);
    let args = |i: u32| {
        let Some(pb::node::Kind::Call(c)) = &p.program.nodes[i as usize].kind else {
            panic!()
        };
        c.args.clone()
    };
    let one = args(first);
    let two = args(second);
    assert_ne!(
        p.program.nodes[one[0] as usize].kind,
        p.program.nodes[two[0] as usize].kind
    );
    assert_eq!(
        p.program.nodes[one[0] as usize].kind,
        p.program.nodes[two[1] as usize].kind
    );
    // Only the generated callee changes, and the descriptor selected changes.
    let other = Callable::constructor("Other", vec![sort.clone(), sort.clone()], sort.clone());
    let changed = node(
        &sort,
        pb::node::Kind::Call(pb::Call {
            func: "Other".into(),
            args: vec![1, 0],
        }),
        vec![a, b],
        vec![call.0, other.0],
    );
    let packed = packed_query(&[changed]);
    assert!(packed.declarations.iter().any(
        |d| matches!(&d.kind, Some(pb::declaration::Kind::Constructor(c)) if c.name == "Other")
    ));
    assert!(!packed.declarations.iter().any(
        |d| matches!(&d.kind, Some(pb::declaration::Kind::Constructor(c)) if c.name == "Pair")
    ));
}

#[test]
fn shared_union_identity_and_flat_cycle_reclamation() {
    let sort = SortRef::equality("M");
    let a = node(
        &sort,
        pb::node::Kind::Union(pb::Union { members: vec![] }),
        vec![],
        vec![],
    );
    let b = node(
        &sort,
        pb::node::Kind::Union(pb::Union { members: vec![] }),
        vec![],
        vec![],
    );
    assert_ne!(Expr(a.clone()), Expr(b.clone()));
    let mut p = Packer::default();
    assert_eq!(p.intern(a.clone(), 0), p.intern(a, 0));
    assert_ne!(p.intern(b, 0), 0);
    p.finish().unwrap();
    assert_eq!(p.program.nodes.len(), 2);
    let mut slots = std::array::from_fn(|_| vec![]);
    slots[Arena::Node as usize] = vec![Slot::Local(0)];
    slots[Arena::Sort as usize] = vec![Slot::External(sort.0)];
    let cycle = publish(
        pb::Program {
            ir_version: 1,
            nodes: vec![pb::Node {
                kind: Some(pb::node::Kind::Union(pb::Union { members: vec![0] })),
                ..Default::default()
            }],
            ..Default::default()
        },
        slots,
        vec![],
        Arena::Node,
        0,
    )
    .unwrap();
    let weak = Arc::downgrade(cycle.owner.as_ref().unwrap());
    let mut p = Packer::default();
    p.intern(cycle.clone(), 0);
    p.finish().unwrap();
    assert_eq!(
        p.program.nodes[0].kind,
        Some(pb::node::Kind::Union(pb::Union { members: vec![0] }))
    );
    drop((p, cycle));
    assert!(weak.upgrade().is_none());
}

#[test]
fn retained_leaf_releases_all_parents_with_bounded_immediate_imports() {
    let sort = SortRef::equality("M");
    let leaf_call = Callable::constructor("Leaf", vec![], sort.clone());
    let pair = Callable::constructor("Pair", vec![sort.clone(), sort.clone()], sort);
    let leaf = Expr::call(&leaf_call, vec![]);
    for left_growing in [false, true] {
        let mut root = leaf.clone();
        let mut parents = vec![];
        for _ in 0..100_000 {
            root = Expr::call(
                &pair,
                if left_growing {
                    vec![root, leaf.clone()]
                } else {
                    vec![leaf.clone(), root]
                },
            );
            let owner = root.0.owner.as_ref().unwrap();
            assert_eq!(owner.program.nodes.len(), 1);
            assert_eq!(owner.slots.iter().map(Vec::len).sum::<usize>(), 3);
            assert_eq!(owner.declarations.len(), 1);
            parents.push(Arc::downgrade(owner));
        }
        std::thread::spawn(move || drop(root)).join().unwrap();
        assert!(parents.iter().all(|w| w.upgrade().is_none()));
        assert_eq!(leaf, Expr::call(&leaf_call, vec![]));
    }
}

#[test]
fn generated_rule_fields_and_occurrence_locations_are_authoritative() {
    let sort = SortRef::equality("M");
    let x = node(
        &sort,
        pb::node::Kind::Var("@typed:n:78".into()),
        vec![],
        vec![],
    );
    let y = node(
        &sort,
        pb::node::Kind::Var("@typed:n:79".into()),
        vec![],
        vec![],
    );
    let make = |rhs, mode| {
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Node as usize] = vec![Slot::External(x.clone()), Slot::External(y.clone())];
        publish(
            pb::Program {
                ir_version: 1,
                rules: vec![pb::RuleDecl {
                    kind: Some(pb::rule_decl::Kind::Rewrite(pb::Rewrite {
                        lhs: 0,
                        rhs,
                        ..Default::default()
                    })),
                    eval_mode: mode,
                    name: Some("same diagnostic label".into()),
                    ..Default::default()
                }],
                ..Default::default()
            },
            slots,
            vec![],
            Arena::Rule,
            0,
        )
        .unwrap()
    };
    let a = make(1, pb::RuleEvalMode::Seminaive.into());
    let independent_equal = make(1, pb::RuleEvalMode::Seminaive.into());
    let changed = make(0, pb::RuleEvalMode::Naive.into());
    let mut slots = std::array::from_fn(|_| vec![]);
    slots[Arena::Rule as usize] = vec![
        Slot::External(a.clone()),
        Slot::External(a),
        Slot::External(independent_equal),
        Slot::External(changed),
    ];
    let group = publish(
        pb::Program {
            ir_version: 1,
            rulesets: vec![pb::Ruleset {
                kind: Some(pb::ruleset::Kind::Rules(pb::RuleList {
                    rules: vec![0, 1, 2, 3],
                })),
                ..Default::default()
            }],
            ..Default::default()
        },
        slots,
        vec![],
        Arena::Ruleset,
        0,
    )
    .unwrap();
    let mut packer = Packer::default();
    packer.intern(group, 0);
    packer.finish().unwrap();
    let Some(pb::ruleset::Kind::Rules(rules)) = &packer.program.rulesets[0].kind else {
        panic!()
    };
    assert_eq!(rules.rules, [0, 0, 1, 2]);
    assert_eq!(packer.program.rules.len(), 3);
    assert_eq!(
        packer.program.rules[2].eval_mode,
        pb::RuleEvalMode::Naive as i32
    );
    let Some(pb::rule_decl::Kind::Rewrite(rule)) = &packer.program.rules[2].kind else {
        panic!()
    };
    assert_eq!(rule.lhs, rule.rhs);
}

#[test]
fn declaration_diagnostics_do_not_change_local_compatibility() {
    let sort = SortRef::equality("M");
    let leaf = Expr::call(&Callable::constructor("Leaf", vec![], sort.clone()), vec![]);
    let declaration = |label: &str, doc: Option<&str>, unextractable: bool| {
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Sort as usize] = vec![Slot::External(sort.0.clone())];
        Callable(
            publish(
                pb::Program {
                    ir_version: 1,
                    declarations: vec![pb::Declaration {
                        kind: Some(pb::declaration::Kind::Constructor(pb::Constructor {
                            name: "Wrap".into(),
                            inputs: vec![pb::Arg {
                                sort: 0,
                                name: label.into(),
                            }],
                            output: 0,
                            unextractable,
                            ..Default::default()
                        })),
                        doc: doc.map(str::to_owned),
                        ..Default::default()
                    }],
                    ..Default::default()
                },
                slots,
                vec![],
                Arena::Declaration,
                0,
            )
            .unwrap(),
        )
    };
    for doc in [None, Some(""), Some("first docs")] {
        let first = declaration("old label", doc, false);
        let mut packed = Packer::default();
        packed.intern(Expr::call(&first, vec![leaf.clone()]).0, 0);
        for resupplied in [None, Some(""), Some("second docs")] {
            let second = declaration("new label", resupplied, false);
            assert!(super::decl::same_callable(&first.0, &second.0).unwrap());
            packed.intern(Expr::call(&second, vec![leaf.clone()]).0, 0);
        }
        packed
            .finish()
            .expect("diagnostic-only changes are compatible");
        let wraps: Vec<_> = packed
            .program
            .declarations
            .iter()
            .filter(
                |d| matches!(&d.kind, Some(pb::declaration::Kind::Constructor(c)) if c.name == "Wrap"),
            )
            .collect();
        assert_eq!(wraps.len(), 1);
        assert_eq!(
            *wraps[0],
            first.0.owner.as_ref().unwrap().program.declarations[0],
            "packing retains the complete first record, including documentation presence"
        );
        let encoded = packed.program.encode_to_vec();
        assert_eq!(
            pb::Program::decode(encoded.as_slice()).unwrap(),
            packed.program
        );

        let mut conflict = Packer::default();
        conflict.intern(Expr::call(&first, vec![leaf.clone()]).0, 0);
        conflict.intern(
            Expr::call(
                &declaration("ignored", Some("ignored"), true),
                vec![leaf.clone()],
            )
            .0,
            0,
        );
        assert!(
            conflict.finish().is_err(),
            "semantic constructor options still conflict"
        );
    }
}
