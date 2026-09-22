#![cfg(feature = "typed")]

use std::collections::HashSet;

use egglog_experimental::typed::{
    FrozenEClass, FrozenScalar, FrozenValue, FrozenValueView, TypedError, builtins as egg,
    prelude::*,
};

#[sort(name = "freeze-test::Term")]
pub struct Term;
#[declarations]
impl Term {
    pub fn Leaf(value: egg::I64) -> Self;
    pub fn Pair(left: Term, right: Term) -> Self;
    pub fn Children(values: egg::Vec<Term>) -> Self;
}

#[function(no_merge)]
pub fn Stored(key: egg::I64) -> Term;

#[relation]
pub fn Seen(term: Term);

#[constructor]
pub fn Nested(values: egg::Vec<egg::Pair<egg::I64, Term>>) -> Term;

fn class(value: FrozenValue<'_>) -> FrozenEClass<'_> {
    let FrozenValueView::EClass(class) = value.view() else {
        panic!("expected an equality class")
    };
    class
}

#[test]
fn selected_constructor_bridge_checks_snapshot_sort_and_retains_fields() -> Result<(), TypedError> {
    #[sort]
    struct Other;
    let capture = let_("bridge", Term::Leaf(17));
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register(&capture)?;
    let frozen = graph.freeze()?;
    let root = class(frozen.as_view(&frozen.lookup(&capture)?)?);
    let node = root.nodes().next().unwrap();
    assert!(frozen.typed_node::<Other>(node).is_err());
    assert!(graph.freeze()?.typed_node::<Term>(node).is_err());
    let selected = frozen.typed_node::<Term>(node)?;
    assert!(
        frozen.nodes(&selected).is_err(),
        "the bridge must retain the constructor target"
    );
    assert!(
        get_args(&selected, |left: &Term, right: &Term| Term::Pair(
            left, right
        ))?
        .is_none()
    );
    let (value,) = get_args(&selected, |value: &egg::I64| Term::Leaf(value))?.unwrap();
    drop(graph);
    drop(frozen);
    assert_eq!(i64::try_from(&value).unwrap(), 17);
    assert!(
        get_args(&selected, |left: &Term, right: &Term| Term::Pair(
            right, left
        ))
        .is_err()
    );
    assert!(get_args(&selected, |value: &egg::I64| Term::Leaf(value + 1)).is_err());
    Ok(())
}

#[test]
fn rootless_forest_preserves_duplicates_cycles_and_snapshot_identity() -> Result<(), TypedError> {
    let leaf = Term::Leaf(7);
    let output = let_("output", Term::Pair(leaf.clone(), leaf.clone()));
    let outside = let_("outside", Term::Leaf(99));
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register((
        &output,
        &outside,
        Seen(output.clone()),
        set(Stored(0), output.clone()),
    ))?;
    let frozen = graph.freeze()?;
    let root = class(frozen.as_view(&frozen.lookup(&output)?)?);
    let other = class(frozen.as_view(&frozen.lookup(&outside)?)?);
    assert_eq!(frozen.eclasses().count(), 3);
    assert_eq!(
        frozen
            .eclasses()
            .map(|class| class.nodes().len())
            .sum::<usize>(),
        3
    );
    let node = root.nodes().next().unwrap();
    let selected = frozen.typed_node::<Term>(node)?;
    assert!(
        get_args(&selected, |left: &Term, right: &Term| Term::Pair(
            left, right
        ))?
        .is_some()
    );
    let children: Vec<_> = node.eclass_children().collect();
    assert_eq!(children.len(), 2);
    assert_eq!(children[0], children[1]);
    let roots = [root, other, root];
    assert_eq!(roots[0], roots[2]);
    assert_ne!(roots[0], roots[1]);
    let tables: Vec<_> = frozen.tables().collect();
    assert!(tables.iter().all(|t| !t.name().starts_with("$typed_")));
    assert!(
        tables
            .iter()
            .any(|t| t.name() == Stored(0).call_name().unwrap())
    );
    let relation = tables
        .iter()
        .find(|t| t.name() == Seen(var::<Term>("x")).call_name())
        .unwrap();
    assert_eq!(relation.inputs(), [Term::sort_ref()]);
    assert_eq!(relation.output(), egg::Unit::sort_ref());
    assert!(matches!(
        relation.rows().next().unwrap().output().view(),
        FrozenValueView::Scalar(FrozenScalar::Unit)
    ));

    graph.push()?;
    graph.register(union(output.clone(), leaf))?;
    let cyclic = graph.freeze()?;
    let cyclic_root = class(cyclic.as_view(&cyclic.lookup(&output)?)?);
    assert_ne!(root, cyclic_root);
    assert_eq!(HashSet::from([root, cyclic_root]).len(), 2);
    assert!(
        cyclic_root
            .nodes()
            .any(|node| node.eclass_children().any(|child| child == cyclic_root))
    );
    assert!(!frozen.contains(cyclic_root.value()));
    graph.pop()?;
    drop(graph);
    assert_eq!(class(frozen.as_view(&frozen.lookup(&output)?)?), root);
    assert_eq!(
        class(cyclic.as_view(&cyclic.lookup(&output)?)?),
        cyclic_root
    );
    assert_eq!(root.nodes().len(), 1);
    Ok(())
}

#[test]
fn lookup_uses_exact_copied_capture_identity_without_evaluation() -> Result<(), TypedError> {
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register(set(Stored(0), Term::Leaf(1)))?;
    let output = let_("read", Stored(0));
    graph.register(&output)?;
    let frozen = graph.freeze()?;
    let root = class(frozen.as_view(&frozen.lookup(&output)?)?);
    assert_eq!(
        root,
        class(frozen.as_view(&frozen.lookup(&let_("read", Stored(0,)))?)?)
    );
    assert!(matches!(
        frozen.lookup(&let_("read", Stored(1,))),
        Err(TypedError::UnresolvedRoot { .. })
    ));
    assert!(matches!(
        frozen.lookup(&Term::Leaf(1,)),
        Err(TypedError::UnresolvedRoot { .. })
    ));
    assert!(frozen.lookup(&let_("missing", Stored(99,))).is_err());
    assert!(frozen.lookup(&let_("read", egg::I64::from(1))).is_err());

    graph.push()?;
    // Updating the source does not rerun the explicit capture, nor alter an
    // already frozen graph. Use a fresh key to avoid no-merge conflicts.
    graph.register(set(Stored(1), Term::Leaf(2)))?;
    let later = let_("later", Stored(1));
    graph.register(&later)?;
    let after = graph.freeze()?;
    assert!(after.lookup(&later).is_ok());
    assert!(frozen.lookup(&later).is_err());
    graph.pop()?;
    assert!(graph.freeze()?.lookup(&later).is_err());
    drop(graph);
    assert_eq!(class(frozen.as_view(&frozen.lookup(&output)?)?), root);
    assert!(after.lookup(&later).is_ok());
    Ok(())
}

#[test]
fn container_fields_follow_equality_leaves_in_order() -> Result<(), TypedError> {
    let a = Term::Leaf(1);
    let b = Term::Leaf(2);
    let output = let_(
        "container",
        Term::Children(egg::Vec::of([a.clone(), b.clone(), a.clone()])),
    );
    let left = let_("a", a);
    let right = let_("b", b);
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register((&output, &left, &right))?;
    let frozen = graph.freeze()?;
    let root = class(frozen.as_view(&frozen.lookup(&output)?)?);
    let children: Vec<_> = root.nodes().next().unwrap().eclass_children().collect();
    assert_eq!(
        children,
        [
            class(frozen.as_view(&frozen.lookup(&left)?)?),
            class(frozen.as_view(&frozen.lookup(&right)?)?),
            class(frozen.as_view(&frozen.lookup(&left)?)?)
        ]
    );
    assert_eq!(
        class(frozen.as_view(&frozen.lookup(&left)?)?)
            .nodes()
            .next()
            .unwrap()
            .eclass_children()
            .count(),
        0
    );
    Ok(())
}

#[test]
fn subsumed_alternatives_remain_flagged() -> Result<(), TypedError> {
    let a = Term::Leaf(1);
    let b = Term::Leaf(2);
    let output = let_("subsumed", a.clone());
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register((&output, union(a, b), subsume(Term::Leaf(1))))?;
    let frozen = graph.freeze()?;
    let root = class(frozen.as_view(&frozen.lookup(&output)?)?);
    assert_eq!(root.nodes().count(), 2);
    assert_eq!(root.nodes().filter(|node| node.is_subsumed()).count(), 1);
    Ok(())
}

#[test]
fn limits_return_errors_without_poisoning_the_destination() -> Result<(), TypedError> {
    let options = EGraphOptions {
        freeze_limits: FreezeLimits {
            max_nodes: 1,
            max_edges: 1,
        },
        ..EGraphOptions::default()
    };
    let mut graph = EGraph::new(options);
    let a = let_("a", Term::Leaf(1));
    let b = let_("b", Term::Leaf(2));
    graph.register((&a, &b))?;
    assert!(matches!(graph.freeze(), Err(TypedError::LoweringLimit(_))));
    assert!(graph.check(&a)?);

    let options = EGraphOptions {
        freeze_limits: FreezeLimits {
            max_nodes: 100,
            max_edges: 0,
        },
        ..EGraphOptions::default()
    };
    let mut graph = EGraph::new(options);
    graph.register(Term::Leaf(1))?;
    assert!(matches!(graph.freeze(), Err(TypedError::LoweringLimit(_))));
    assert!(graph.check(())?);
    Ok(())
}

#[test]
fn empty_snapshot_has_no_roots_or_classes() -> Result<(), TypedError> {
    let graph = EGraph::new(EGraphOptions::default());
    let frozen = graph.freeze()?;
    assert_eq!(frozen.eclasses().count(), 0);
    assert_eq!(frozen.tables().count(), 0);
    Ok(())
}

#[test]
fn unhealthy_destination_requires_restoration_before_freezing() -> Result<(), TypedError> {
    let mut graph = EGraph::new(EGraphOptions::default());
    let output = let_("healthy", Term::Leaf(1));
    graph.register(&output)?;
    let before = graph.freeze()?;
    graph.push()?;
    assert!(
        graph
            .register(egg::I64::from(1) / egg::I64::from(0))
            .is_err()
    );
    assert!(matches!(graph.freeze(), Err(TypedError::NeedsRestore)));
    assert!(before.lookup(&output).is_ok());
    graph.pop()?;
    assert!(graph.freeze()?.lookup(&output).is_ok());
    Ok(())
}

#[test]
fn captures_decode_every_scalar_without_text_or_live_state() -> Result<(), TypedError> {
    let mut graph = EGraph::new(EGraphOptions::default());
    let i = let_("i", egg::I64::from(i64::MIN));
    let b = let_("b", egg::Bool::from(false));
    let u = let_("u", egg::Unit::from(()));
    let f = let_("f", egg::F64::from(f64::from_bits(0x8000_0000_0000_0000)));
    let s = let_("s", egg::String::from("a\"\\\n\tλ\0😀"));
    let z = let_(
        "z",
        egg::BigInt::from_string("123456789012345678901234567890123456789"),
    );
    let q = let_("q", egg::BigRat::new(3, 7));
    let r = let_("r", egg::Rational::new(-5, 9));
    graph.register((&i, &b, &u, &f, &s, &z, &q, &r))?;
    let frozen = graph.freeze()?;
    drop(graph);
    let values = [
        frozen.as_view(&frozen.lookup(&i)?)?,
        frozen.as_view(&frozen.lookup(&b)?)?,
        frozen.as_view(&frozen.lookup(&u)?)?,
        frozen.as_view(&frozen.lookup(&f)?)?,
        frozen.as_view(&frozen.lookup(&s)?)?,
        frozen.as_view(&frozen.lookup(&z)?)?,
        frozen.as_view(&frozen.lookup(&q)?)?,
        frozen.as_view(&frozen.lookup(&r)?)?,
    ];
    let scalars: Vec<_> = values
        .iter()
        .map(|v| match v.view() {
            FrozenValueView::Scalar(s) => s.clone(),
            _ => panic!("expected scalar"),
        })
        .collect();
    assert_eq!(
        scalars,
        [
            FrozenScalar::I64(i64::MIN),
            FrozenScalar::Bool(false),
            FrozenScalar::Unit,
            FrozenScalar::F64(0x8000_0000_0000_0000),
            FrozenScalar::String("a\"\\\n\tλ\0😀".into()),
            FrozenScalar::BigInt("123456789012345678901234567890123456789".parse().unwrap()),
            FrozenScalar::BigRat(num::BigRational::new(3.into(), 7.into())),
            FrozenScalar::Rational(num::rational::Rational64::new(-5, 9))
        ]
    );
    assert_eq!(values[0].sort(), egg::I64::sort_ref());
    assert_eq!(values[5].sort(), egg::BigInt::sort_ref());
    assert!(frozen.lookup(&let_("i", egg::I64::from(7))).is_err());
    assert!(
        frozen
            .lookup(&let_("i", egg::String::from("wrong sort")))
            .is_err()
    );
    assert!(frozen.lookup(&egg::I64::from(i64::MIN)).is_err());
    Ok(())
}

#[test]
fn structured_containers_preserve_fields_pairing_sharing_and_cycles() -> Result<(), TypedError> {
    let mut graph = EGraph::new(EGraphOptions::default());
    let leaf = let_("leaf", Term::Leaf(3));
    let vector = let_("vector", egg::Vec::<Term>::of([leaf.clone(), leaf.clone()]));
    let empty = let_("empty", egg::Vec::<Term>::empty());
    let set = let_("set", egg::Set::<Term>::of([leaf.clone(), leaf.clone()]));
    let bag = let_(
        "bag",
        egg::MultiSet::<Term>::of([leaf.clone(), leaf.clone()]),
    );
    let pair = let_("pair", egg::Pair::<egg::I64, Term>::new(7, &leaf));
    let map = let_(
        "map",
        egg::Map::<egg::String, egg::Pair<egg::I64, Term>>::of([
            ("left", pair.clone()),
            ("right", pair.clone()),
        ]),
    );
    graph.register((&leaf, &vector, &empty, &set, &bag, &pair, &map))?;
    let frozen = graph.freeze()?;
    let expected = frozen.as_view(&frozen.lookup(&leaf)?)?;
    let FrozenValueView::Vec(members) = frozen.as_view(&frozen.lookup(&vector)?)?.view() else {
        panic!("vector")
    };
    assert_eq!(members.collect::<Vec<_>>(), [expected, expected]);
    let FrozenValueView::Vec(members) = frozen.as_view(&frozen.lookup(&empty)?)?.view() else {
        panic!("empty vector")
    };
    assert_eq!(members.len(), 0);
    let FrozenValueView::Set(members) = frozen.as_view(&frozen.lookup(&set)?)?.view() else {
        panic!("set")
    };
    assert_eq!(members.collect::<Vec<_>>(), [expected]);
    let FrozenValueView::MultiSet(members) = frozen.as_view(&frozen.lookup(&bag)?)?.view() else {
        panic!("multiset")
    };
    assert_eq!(members.collect::<Vec<_>>(), [expected, expected]);
    let pair_value = frozen.as_view(&frozen.lookup(&pair)?)?;
    let FrozenValueView::Pair(first, second) = pair_value.view() else {
        panic!("pair")
    };
    assert!(matches!(
        first.view(),
        FrozenValueView::Scalar(FrozenScalar::I64(7))
    ));
    assert_eq!(second, expected);
    let map_value = frozen.as_view(&frozen.lookup(&map)?)?;
    assert_eq!(
        map_value.sort(),
        egg::Map::<egg::String, egg::Pair<egg::I64, Term>>::sort_ref()
    );
    let FrozenValueView::Map(entries) = map_value.view() else {
        panic!("map")
    };
    let mut labels = Vec::new();
    for (key, value) in entries {
        let FrozenValueView::Scalar(FrozenScalar::String(label)) = key.view() else {
            panic!("key")
        };
        labels.push(label.as_str());
        assert_eq!(value, pair_value);
    }
    labels.sort();
    assert_eq!(labels, ["left", "right"]);

    let container = Term::Children(egg::Vec::of([leaf.clone(), leaf.clone()]));
    graph.register(union(&leaf, container))?;
    let cyclic = graph.freeze()?;
    let root = class(cyclic.as_view(&cyclic.lookup(&leaf)?)?);
    let node = root
        .nodes()
        .find(|&n| {
            let selected = cyclic.typed_node::<Term>(n).unwrap();
            get_args(&selected, |values: &egg::Vec<Term>| Term::Children(values))
                .unwrap()
                .is_some()
        })
        .unwrap();
    let FrozenValueView::Vec(fields) = node.args().next().unwrap().view() else {
        panic!("vector field")
    };
    assert_eq!(fields.collect::<Vec<_>>(), [root.value(), root.value()]);
    assert!(!frozen.contains(root.value()));

    let pairs = egg::Vec::of([
        egg::Pair::<egg::I64, Term>::new(7, &leaf),
        egg::Pair::<egg::I64, Term>::new(7, &leaf),
    ]);
    graph.register(union(&leaf, Nested(pairs)))?;
    let nested = graph.freeze()?;
    let root = class(nested.as_view(&nested.lookup(&leaf)?)?);
    let node = root
        .nodes()
        .find(|&n| {
            let selected = nested.typed_node::<Term>(n).unwrap();
            get_args(&selected, |values: &egg::Vec<egg::Pair<egg::I64, Term>>| {
                Nested(values)
            })
            .unwrap()
            .is_some()
        })
        .unwrap();
    assert_eq!(node.eclass_children().collect::<Vec<_>>(), [root, root]);
    let FrozenValueView::Vec(mut pairs) = node.args().next().unwrap().view() else {
        panic!("nested vec")
    };
    let first = pairs.next().unwrap();
    assert_eq!(first, pairs.next().unwrap());
    let FrozenValueView::Pair(_, child) = first.view() else {
        panic!("nested pair")
    };
    assert_eq!(child, root.value());
    Ok(())
}

#[sort(name = "NativeTerm")]
pub struct NativeTerm;
#[constructor(name = "NativeLeaf")]
pub fn NativeLeaf(value: egg::I64) -> NativeTerm;
#[relation(name = "NativeSeen")]
pub fn NativeSeen(value: NativeTerm);

#[test]
fn native_and_typed_producers_share_names_signatures_and_rows() -> Result<(), TypedError> {
    use egglog_experimental::typed::native::with_frozen;
    let mut native = egglog::EGraph::default();
    native.parse_and_run_program(None, "(datatype NativeTerm (NativeLeaf i64)) (relation NativeSeen (NativeTerm)) (function Empty (i64) i64 :no-merge) (let root (NativeLeaf 7)) (NativeSeen root)")
        .map_err(|e| TypedError::Decode(e.to_string()))?;
    let root = native
        .eval_expr(&egglog::ast::Expr::Var(egglog::span!(), "root".into()))
        .map_err(|e| TypedError::Decode(e.to_string()))?;
    let roots = [root.clone(), root];
    let tuples = native.num_tuples();
    for graph in [&native, &native.clone()] {
        with_frozen(graph, &roots, FreezeLimits::default(), |frozen, roots| {
            assert_eq!(roots.len(), 2);
            assert_eq!(roots[0], roots[1]);
            assert!(frozen.contains(roots[0]));
            assert_eq!(roots[0].sort(), NativeTerm::sort_ref());
            let node = class(roots[0]).nodes().next().unwrap();
            assert_eq!(node.name(), NativeLeaf(0).call_name().unwrap());
            assert!(matches!(
                node.args().next().unwrap().view(),
                FrozenValueView::Scalar(FrozenScalar::I64(7))
            ));
            let tables: Vec<_> = frozen.tables().collect();
            let relation = tables
                .iter()
                .find(|t| t.name() == NativeSeen(var::<NativeTerm>("x")).call_name())
                .unwrap();
            assert_eq!(relation.inputs(), [NativeTerm::sort_ref()]);
            assert_eq!(relation.output(), egg::Unit::sort_ref());
            assert_eq!(
                relation.rows().next().unwrap().args().next().unwrap(),
                roots[0]
            );
            assert!(matches!(
                relation.rows().next().unwrap().output().view(),
                FrozenValueView::Scalar(FrozenScalar::Unit)
            ));
            assert_eq!(
                tables
                    .iter()
                    .find(|t| t.name() == "Empty")
                    .unwrap()
                    .rows()
                    .len(),
                0
            );
            assert_eq!(frozen.eclasses().count(), 1);
            assert!(tables.iter().all(|t| t.name() != "root"));
            Ok(())
        })?;
    }
    assert_eq!(native.num_tuples(), tuples);
    Ok(())
}

#[test]
fn native_modes_fail_closed_even_without_rows() {
    use egglog_experimental::typed::native::with_frozen;
    for core in [
        egglog::EGraph::new_with_term_encoding(),
        egglog::EGraph::new_with_proofs(),
    ] {
        let mut called = false;
        let result = with_frozen(&core, &[], FreezeLimits::default(), |_, _| {
            called = true;
            Ok(())
        });
        assert!(matches!(result, Err(TypedError::Invalid(_))));
        assert!(!called);
    }
}

#[test]
fn hundred_thousand_native_rows_freeze_traverse_and_drop_iteratively() -> Result<(), TypedError> {
    use egglog::Write;
    use egglog_experimental::typed::native::with_frozen;
    const COUNT: usize = 100_000;
    #[derive(Clone)]
    struct Seed(egglog::ArcSort);
    impl egglog::Primitive for Seed {
        fn name(&self) -> &str {
            "seed-chain"
        }
        fn get_type_constraints(
            &self,
            span: &egglog::ast::Span,
        ) -> Box<dyn egglog::constraint::TypeConstraint> {
            egglog::constraint::SimpleTypeConstraint::new(
                self.name(),
                vec![self.0.clone()],
                span.clone(),
            )
            .into_box()
        }
    }
    impl egglog::WritePrim for Seed {
        fn apply<'a, 'db>(
            &self,
            mut state: egglog::WriteState<'a, 'db>,
            _: &[egglog::Value],
        ) -> Option<egglog::Value> {
            let mut value = state.add("End", egglog::RawValues(vec![])).unwrap();
            for _ in 1..COUNT {
                value = state.add("Next", egglog::RawValues(vec![value])).unwrap();
            }
            Some(value)
        }
    }
    let mut native = egglog::EGraph::default();
    native
        .parse_and_run_program(None, "(datatype Deep (End) (Next Deep))")
        .unwrap();
    let sort = native.get_sort_by_name("Deep").unwrap().clone();
    native.add_write_primitive(Seed(sort), None);
    native
        .parse_and_run_program(None, "(let root (seed-chain))")
        .unwrap();
    let root = native
        .eval_expr(&egglog::ast::Expr::Var(egglog::span!(), "root".into()))
        .unwrap();
    let tuples = native.num_tuples();
    let mut called = false;
    let failed = with_frozen(
        &native,
        std::slice::from_ref(&root),
        FreezeLimits {
            max_nodes: COUNT,
            max_edges: 2 * COUNT - 2,
        },
        |_, _| {
            called = true;
            Ok(())
        },
    );
    assert!(matches!(failed, Err(TypedError::LoweringLimit(_))));
    assert!(!called);
    assert_eq!(native.num_tuples(), tuples);
    with_frozen(
        &native,
        &[root],
        FreezeLimits {
            max_nodes: COUNT,
            max_edges: 2 * COUNT,
        },
        |frozen, roots| {
            assert_eq!(frozen.eclasses().len(), COUNT);
            let mut current = Some(class(roots[0]));
            let mut count = 0;
            while let Some(value) = current {
                count += 1;
                current = value.nodes().next().unwrap().args().next().map(class);
            }
            assert_eq!(count, COUNT);
            Ok(())
        },
    )?;
    assert_eq!(native.num_tuples(), tuples);
    // Both snapshot destruction above and native source destruction are tested.
    drop(native);
    Ok(())
}

#[test]
fn function_outputs_retain_empty_classes_and_native_container_aliases() -> Result<(), TypedError> {
    use egglog_experimental::typed::native::with_frozen;
    let mut native = egglog::EGraph::default();
    native.parse_and_run_program(None, "(datatype EmptyClass (Gone)) (function Kept () EmptyClass :no-merge) (let root (Gone)) (set (Kept) root) (delete (Gone)) (sort MyMap (Map String i64)) (function Mapping () MyMap :no-merge) (set (Mapping) (map-insert (map-empty) \"key\" 7))").unwrap();
    with_frozen(&native, &[], FreezeLimits::default(), |frozen, _| {
        let kept = frozen.tables().find(|t| t.name() == "Kept").unwrap();
        let output = class(kept.rows().next().unwrap().output());
        assert_eq!(output.nodes().len(), 0);
        assert_eq!(frozen.eclasses().len(), 1);
        assert!(output.sort().container_shape().is_none());
        let table = frozen.tables().find(|t| t.name() == "Mapping").unwrap();
        let map = table.rows().next().unwrap().output();
        let sort = map.sort();
        assert_eq!(sort.name(), "MyMap");
        assert_eq!(
            sort.container_shape(),
            Some(("Map", &[egg::String::sort_ref(), egg::I64::sort_ref()][..]))
        );
        let FrozenValueView::Map(mut entries) = map.view() else {
            panic!("map alias")
        };
        let (key, value) = entries.next().unwrap();
        assert!(
            matches!(key.view(), FrozenValueView::Scalar(FrozenScalar::String(s)) if s == "key")
        );
        assert!(matches!(
            value.view(),
            FrozenValueView::Scalar(FrozenScalar::I64(7))
        ));
        assert!(value.sort().container_shape().is_none());
        Ok(())
    })
}

#[derive(Debug)]
struct AliasUnit;
impl egglog::prelude::BaseSort for AliasUnit {
    type Base = ();
    fn name(&self) -> &str {
        "AliasUnit"
    }
    fn register_primitives(&self, _: &mut egglog::EGraph) {}
    fn reconstruct_termdag(
        &self,
        _: &egglog::sort::BaseValues,
        _: egglog::Value,
        dag: &mut egglog::TermDag,
    ) -> egglog::TermId {
        dag.lit(egglog::ast::Literal::Unit)
    }
}
#[derive(Debug)]
struct Unsupported;
impl egglog::prelude::BaseSort for Unsupported {
    type Base = u32;
    fn name(&self) -> &str {
        "Unsupported"
    }
    fn register_primitives(&self, _: &mut egglog::EGraph) {}
    fn reconstruct_termdag(
        &self,
        _: &egglog::sort::BaseValues,
        _: egglog::Value,
        _: &mut egglog::TermDag,
    ) -> egglog::TermId {
        panic!("freeze must not extract")
    }
}

#[test]
fn native_unit_aliases_remain_exact_and_unsupported_codecs_error() -> Result<(), TypedError> {
    use egglog_experimental::typed::native::with_frozen;
    let mut native = egglog::EGraph::default();
    egglog::prelude::add_base_sort(&mut native, AliasUnit, egglog::span!()).unwrap();
    let unit = native.base_to_value(());
    let roots = [
        (native.get_sort_by_name("AliasUnit").unwrap().clone(), unit),
        (native.get_sort_by_name("Unit").unwrap().clone(), unit),
    ];
    with_frozen(&native, &roots, FreezeLimits::default(), |_, roots| {
        assert_ne!(roots[0], roots[1]);
        assert_eq!(roots[0].sort().name(), "AliasUnit");
        assert_eq!(roots[1].sort(), egg::Unit::sort_ref());
        assert!(
            roots
                .iter()
                .all(|v| matches!(v.view(), FrozenValueView::Scalar(FrozenScalar::Unit)))
        );
        Ok(())
    })?;
    egglog::prelude::add_base_sort(&mut native, Unsupported, egglog::span!()).unwrap();
    let value = native.base_to_value(7u32);
    let roots = [(
        native.get_sort_by_name("Unsupported").unwrap().clone(),
        value,
    )];
    let mut called = false;
    let result = with_frozen(&native, &roots, FreezeLimits::default(), |_, _| {
        called = true;
        Ok(())
    });
    assert!(matches!(result, Err(TypedError::Decode(_))));
    assert!(!called);
    assert_eq!(native.num_tuples(), 0);
    native
        .parse_and_run_program(
            None,
            "(function EmptyUnsupported (Unsupported) i64 :no-merge)",
        )
        .unwrap();
    let result = with_frozen(&native, &[], FreezeLimits::default(), |_, _| {
        called = true;
        Ok(())
    });
    assert!(matches!(result, Err(TypedError::Decode(_))));
    assert!(!called);
    assert_eq!(native.num_tuples(), 0);
    Ok(())
}
