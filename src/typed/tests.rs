use super::{
    SortRef, close,
    decl::Callable,
    expr::Expr,
    pb,
    storage::{Arena, Packer, Record, Slot, publish},
};
use prost::Message;
use std::sync::Arc;

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
    let declaration = |label: &str, doc: &str, unextractable: bool| {
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
                        doc: doc.into(),
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
    let first = declaration("old label", "first docs", false);
    let second = declaration("new label", "second docs", false);
    assert!(super::decl::same_callable(&first.0, &second.0).unwrap());
    let mut packed = Packer::default();
    packed.intern(Expr::call(&first, vec![leaf.clone()]).0, 0);
    packed.intern(Expr::call(&second, vec![leaf.clone()]).0, 0);
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
        wraps[0].doc, "first docs",
        "packing retains first-use metadata"
    );

    let mut conflict = Packer::default();
    conflict.intern(Expr::call(&first, vec![leaf.clone()]).0, 0);
    conflict.intern(
        Expr::call(&declaration("ignored", "ignored", true), vec![leaf]).0,
        0,
    );
    assert!(
        conflict.finish().is_err(),
        "semantic constructor options still conflict"
    );
}
