use egglog::extract::DEFAULT_COST_MODEL;
use egglog::sort::{PairContainer, Presort, VecContainer, VecSort};
use egglog::*;
use egglog_experimental::builtin::{PortableEGraph, PortablePrimitive, PortableTypeInfo};
use egglog_experimental::{
    add_literal_prim, add_primitive, add_primitive_with_validator, builtin, proto,
};
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};

#[test]
fn native_signature_all_selection_routes_intersect_native_predicate() {
    // This regression uses only baseline APIs, so the same test can demonstrate
    // behavioral red-before/fix-after independently of the new binding APIs.
    #[derive(Clone)]
    struct Narrowed {
        definition: egglog::builtin::BuiltinDescription,
        native: ArcSort,
    }
    impl Primitive for Narrowed {
        fn name(&self) -> &str {
            "signature-intersection"
        }
        fn get_type_constraints(&self, span: &ast::Span) -> Box<dyn constraint::TypeConstraint> {
            constraint::SimpleTypeConstraint::new(
                self.name(),
                vec![self.native.clone(), self.native.clone()],
                span.clone(),
            )
            .into_box()
        }
        fn builtin_description(&self) -> Option<&egglog::builtin::BuiltinDescription> {
            Some(&self.definition)
        }
    }
    impl PurePrim for Narrowed {
        fn apply<'a, 'db>(&self, _: PureState<'a, 'db>, _: &[Value]) -> Option<Value> {
            panic!("signature validation must not execute this fixture")
        }
    }
    let mut graph = EGraph::default();
    let integer = graph.get_sort_by_name("i64").unwrap().clone();
    let string = graph.get_sort_by_name("String").unwrap().clone();
    let definition = egglog::builtin::closed_signature(
        "test.signature_intersection",
        "signature-intersection",
        &[("input", integer.clone())],
        &[],
        string,
    )
    .unwrap();
    graph.add_pure_primitive(
        Narrowed {
            definition,
            native: integer.clone(),
        },
        Some(Arc::new(|_: &mut TermDag, _: &[TermId]| {
            panic!("signature validation must not execute a validator")
        })),
    );
    let actual = [integer.clone(), integer];
    let types = graph.type_info();
    for key in ["signature-intersection", "test.signature_intersection"] {
        assert!(
            !types.get_prims(key).unwrap()[0].accept(&actual, types),
            "native identity constraints must also satisfy the String-result descriptor"
        );
        for ctx in [Context::Pure, Context::Read, Context::Write, Context::Full] {
            assert!(
                ResolvedCall::from_resolution(key, &actual, types, ctx, &ast::Span::Panic).is_err()
            );
        }
        assert!(
            types
                .export_function_target(
                    key,
                    &actual[..1],
                    &actual[1],
                    None,
                    &mut proto::Program::default()
                )
                .is_err()
        );
    }
    graph
        .parse_and_run_program(
            None,
            "(sort F (UnstableFn (i64) i64)) (function saved () F :merge new)",
        )
        .unwrap();
    for key in ["signature-intersection", "test.signature_intersection"] {
        assert!(
            graph
                .parse_and_run_program(None, &format!("(set (saved) (unstable-fn {key:?}))"))
                .is_err()
        );
    }
}

#[test]
fn function_value_observer_keeps_typed_occurrences() {
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(
            None,
            r#"
        (sort X)
        (sort SI (Set i64))
        (sort SX (Set X))
        (function si () SI :merge new)
        (function sx () SX :merge new)
        (set (si) (set-empty))
        (set (sx) (set-empty))
        (sort F (UnstableFn () bool))
        (datatype W (Wrap F) (Other F))
        (let $fi (unstable-fn "egglog.core.bool_ne" (si) (si)))
        (let $fx (unstable-fn "egglog.core.bool_ne" (sx) (sx)))
        (check (!= $fi $fx))
        (let $wi (Wrap $fi))
        (let $wx (Wrap $fx))
        (let $other (Other $fi))
        (union $wi $wx)
    "#,
        )
        .unwrap();
    let mut roots = vec![];
    for name in ["$fi", "$fx", "$wi", "$other"] {
        roots.push(
            graph
                .eval_expr(&ast::Expr::Var(ast::Span::Panic, name.into()))
                .unwrap(),
        );
    }
    let mut nodes: Vec<(TermId, String, Vec<usize>)> = vec![];
    let best_roots = vec![roots[0].clone(), roots[1].clone(), roots[0].clone()];
    let legacy = graph.extract_best(best_roots.clone()).unwrap();
    let (best, ids) = graph
        .extract_best_with_cost_model_and_observer(
            best_roots,
            DEFAULT_COST_MODEL,
            |_, term, sort, _, children| {
                let id = nodes.len();
                nodes.push((term, sort.name().into(), children.to_vec()));
                Ok(id)
            },
        )
        .unwrap();
    assert_eq!(best.termdag, legacy.termdag);
    assert_eq!(
        best.terms
            .iter()
            .map(|t| t.as_ref().map(|t| (t.term, t.cost)))
            .collect::<Vec<_>>(),
        legacy
            .terms
            .iter()
            .map(|t| t.as_ref().map(|t| (t.term, t.cost)))
            .collect::<Vec<_>>()
    );
    assert_eq!(
        best.terms[0].as_ref().unwrap().term,
        best.terms[1].as_ref().unwrap().term
    );
    assert_ne!(ids[0], ids[1]);
    assert_eq!(ids[0], ids[2], "duplicate roots retain consumer sharing");
    for (id, expected) in ids.iter().take(2).zip(["SI", "SX"]) {
        let children = &nodes[id.unwrap()].2;
        assert_eq!(
            children.len(),
            2,
            "target-name literal is not a semantic child"
        );
        assert_eq!(nodes[children[0]].1, expected);
        assert_eq!(children[0], children[1]);
    }
    let legacy = graph
        .extract_variants(vec![roots[2].clone(), roots[3].clone()], 2)
        .unwrap();
    nodes.clear();
    let (variants, ids) = graph
        .extract_variants_with_cost_model_and_observer(
            vec![roots[2].clone(), roots[3].clone()],
            2,
            DEFAULT_COST_MODEL,
            |_, term, sort, _, children| {
                let id = nodes.len();
                nodes.push((term, sort.name().into(), children.to_vec()));
                Ok(id)
            },
        )
        .unwrap();
    assert_eq!(variants.termdag, legacy.termdag);
    let terms: Vec<_> = variants.variants[0]
        .iter()
        .map(|t| (t.term, t.cost))
        .collect();
    assert_eq!(
        terms,
        legacy.variants[0]
            .iter()
            .map(|t| (t.term, t.cost))
            .collect::<Vec<_>>()
    );
    assert_eq!(terms.len(), 2);
    assert_eq!(terms[0], terms[1]);
    assert_eq!(terms[0].1, 1);
    assert_ne!(
        ids[0][0], ids[0][1],
        "selected variants must not be deduplicated by Eq root or TermId"
    );
    let mut prefixes: Vec<_> = ids[0]
        .iter()
        .map(|id| {
            let function = nodes[*id].2[0];
            nodes[nodes[function].2[0]].1.as_str()
        })
        .collect();
    prefixes.sort();
    assert_eq!(prefixes, ["SI", "SX"]);
    let shared = nodes[ids[1][0]].2[0];
    assert!(
        ids[0].iter().any(|id| nodes[*id].2[0] == shared),
        "distinct roots retain their common selected function child"
    );
    let error = graph
        .extract_best_with_cost_model_and_observer(
            vec![roots[0].clone()],
            DEFAULT_COST_MODEL,
            |_, _, _, _, _: &[()]| Err::<(), _>(Error::ExtractError("observer failure".into())),
        )
        .unwrap_err();
    assert!(error.to_string().contains("observer failure"));
    let error = graph
        .extract_variants_with_cost_model_and_observer(
            vec![roots[2].clone()],
            2,
            DEFAULT_COST_MODEL,
            |_, _, _, _, _: &[()]| Err::<(), _>(Error::ExtractError("observer failure".into())),
        )
        .unwrap_err();
    assert!(error.to_string().contains("observer failure"));
}

#[test]
fn function_value_observer_uses_semantic_view_children() {
    let mut graph = EGraph::new_with_proofs();
    graph
        .parse_and_run_program(None, "(datatype M (Num i64)) (let $m (Num 5))")
        .unwrap();
    let mut values = vec![];
    graph
        .constructor_enodes("Num", |row| values.push(row.eclass))
        .unwrap();
    assert_eq!(values.len(), 1);
    let root = (graph.get_sort_by_name("M").unwrap().clone(), values[0]);
    let mut nodes: Vec<(String, Vec<usize>)> = vec![];
    let (_, roots) = graph
        .extract_best_with_cost_model_and_observer(
            vec![root],
            DEFAULT_COST_MODEL,
            |_, _, sort, _, children| {
                let id = nodes.len();
                nodes.push((sort.name().into(), children.to_vec()));
                Ok(id)
            },
        )
        .unwrap();
    let root = &nodes[roots[0].unwrap()];
    assert_eq!(root.0, "M");
    assert_eq!(root.1.len(), 1);
    assert_eq!(nodes[root.1[0]].0, "i64");
}

#[test]
fn multiset_index_operations_preserve_function_capture_prefixes() {
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(
            None,
            r#"
        (sort PrefixMS (MultiSet i64))
        (sort PrefixFn (UnstableFn (PrefixMS i64) i64))
        (function prefix-index (i64 PrefixMS i64) i64 :merge new)
        (let xs (multiset-of 1 1 2))
        (let f (unstable-fn "prefix-index" 41))
        (set (prefix-index 42 xs 1) 99)
        (unstable-multiset-fill-index xs f)
        (check (= (prefix-index 41 xs 1) 2))
        (check (= (prefix-index 41 xs 2) 1))
        (check (= (prefix-index 42 xs 1) 99))
        (unstable-multiset-clear-index xs f)
        (fail (check (= (prefix-index 41 xs 1) 2)))
        (fail (check (= (prefix-index 41 xs 2) 1)))
        (check (= (prefix-index 42 xs 1) 99))
    "#,
        )
        .unwrap();
}

#[test]
fn function_value_structural_provenance_and_application_catalog() {
    let mut graph = EGraph::default();
    let catalog = graph
        .type_info()
        .portable_builtin_catalog()
        .unwrap()
        .definitions;
    assert!(
        !catalog
            .primitives
            .iter()
            .any(|primitive| primitive.name == "egglog.core.fn.apply")
    );
    graph
        .parse_and_run_program(
            None,
            "(sort F (UnstableFn (i64) i64)) (sort G (UnstableFn (i64) i64))",
        )
        .unwrap();
    let mut sorts = vec![];
    let f = graph.get_sort_by_name("F").unwrap().clone();
    let g = graph.get_sort_by_name("G").unwrap().clone();
    let index = graph.export_sort(&f, &mut sorts).unwrap();
    assert_eq!(graph.export_sort(&g, &mut sorts).unwrap(), index);
    let Some(proto::sort::Kind::Func(function)) = &sorts[index as usize].kind else {
        panic!("expected structural Func")
    };
    assert_eq!(function.params, [function.result]);
    let mut imported = vec![];
    assert_eq!(
        builtin::import_sort(&sorts, index, &mut imported).unwrap(),
        index
    );
    assert_eq!(imported, sorts);
    for sort in [f, g] {
        let i64_sort = graph.get_sort_by_name("i64").unwrap().clone();
        let native = [sort.clone(), i64_sort.clone(), i64_sort.clone()];
        let instance = graph
            .type_info()
            .instantiate_builtin("egglog.core.fn.apply", &sort)
            .unwrap();
        instance.check_abi(&[None, None], None, false).unwrap();
        assert!(instance.check_abi(&[None], None, false).is_err());
        assert!(instance.check_abi(&[None, None], None, true).is_err());
        assert!(
            instance
                .check_abi(
                    &[Some((std::any::TypeId::of::<i64>(), false)), None],
                    None,
                    false
                )
                .is_err()
        );
        for context in [Context::Pure, Context::Read, Context::Write, Context::Full] {
            let source = ResolvedCall::from_resolution(
                "unstable-app",
                &native,
                graph.type_info(),
                context,
                &ast::Span::Panic,
            )
            .unwrap();
            let keyed = ResolvedCall::from_resolution(
                "egglog.core.fn.apply",
                &native,
                graph.type_info(),
                context,
                &ast::Span::Panic,
            )
            .unwrap();
            assert_eq!(source, keyed);
            let ResolvedCall::Primitive(primitive) = keyed else {
                unreachable!()
            };
            assert!(primitive.validator().is_none());
        }
    }
    graph
        .parse_and_run_program(
            None,
            r#"(function captured_unary () F :merge old)
                (set (captured_unary) (unstable-fn "+" 1))
                (function raw_application () F :merge old)
                (set (raw_application) (unstable-fn "unstable-app" (captured_unary)))
                (check (= (unstable-app (raw_application) 2) 3))"#,
        )
        .unwrap();
    let (sort, value) = graph
        .eval_expr(&ast::Expr::Call(
            ast::Span::Panic,
            "raw_application".into(),
            vec![],
        ))
        .unwrap();
    assert_eq!(
        graph
            .export_function_value_target(&sort, value)
            .unwrap_err(),
        "native application function value requires a program-defined adapter"
    );
}

#[test]
fn remaining_scalar_catalog_preserves_closed_providers() {
    let mut graph = EGraph::default();
    let catalog = graph
        .type_info()
        .portable_builtin_catalog()
        .unwrap()
        .definitions;
    let cases: &[(&str, &str, &[&str], Option<&str>)] = &[
        ("i64.bitor", "|", &["i64", "i64", "i64"], Some("__or__")),
        ("i64.bitxor", "^", &["i64", "i64", "i64"], Some("__xor__")),
        ("i64.shl", "<<", &["i64", "i64", "i64"], Some("__lshift__")),
        ("i64.shr", ">>", &["i64", "i64", "i64"], Some("__rshift__")),
        ("i64.not", "not-i64", &["i64", "i64"], Some("__invert__")),
        ("i64.log2", "log2", &["i64", "i64"], Some("log2")),
        ("i64.abs", "abs", &["i64", "i64"], Some("__abs__")),
        ("i64.gt", ">", &["i64", "i64", "Unit"], Some("__gt__")),
        ("i64.le", "<=", &["i64", "i64", "Unit"], Some("__le__")),
        ("i64.bool_eq", "bool-=", &["i64", "i64", "bool"], None),
        (
            "i64.bool_lt",
            "bool-<",
            &["i64", "i64", "bool"],
            Some("bool_lt"),
        ),
        (
            "i64.bool_gt",
            "bool->",
            &["i64", "i64", "bool"],
            Some("bool_gt"),
        ),
        (
            "i64.bool_le",
            "bool-<=",
            &["i64", "i64", "bool"],
            Some("bool_le"),
        ),
        (
            "i64.bool_ge",
            "bool->=",
            &["i64", "i64", "bool"],
            Some("bool_ge"),
        ),
        (
            "string.count_matches",
            "count-matches",
            &["String", "String", "i64"],
            Some("count_matches"),
        ),
        ("f64.sub", "-", &["f64", "f64", "f64"], Some("__sub__")),
        ("f64.mul", "*", &["f64", "f64", "f64"], Some("__mul__")),
        ("f64.div", "/", &["f64", "f64", "f64"], Some("__truediv__")),
        ("f64.rem", "%", &["f64", "f64", "f64"], Some("__mod__")),
        ("f64.pow", "^", &["f64", "f64", "f64"], Some("__pow__")),
        ("f64.neg", "neg", &["f64", "f64"], Some("__neg__")),
        ("f64.lt", "<", &["f64", "f64", "Unit"], Some("__lt__")),
        ("f64.gt", ">", &["f64", "f64", "Unit"], Some("__gt__")),
        ("f64.le", "<=", &["f64", "f64", "Unit"], Some("__le__")),
        ("f64.ge", ">=", &["f64", "f64", "Unit"], Some("__ge__")),
        ("f64.min", "min", &["f64", "f64", "f64"], Some("min")),
        ("f64.max", "max", &["f64", "f64", "f64"], Some("max")),
        ("f64.abs", "abs", &["f64", "f64"], Some("__abs__")),
        ("f64.exp", "exp", &["f64", "f64"], Some("exp")),
        ("f64.log", "log", &["f64", "f64"], Some("log")),
        ("f64.sqrt", "sqrt", &["f64", "f64"], Some("sqrt")),
        ("f64.from_i64", "to-f64", &["i64", "f64"], Some("from_i64")),
        ("f64.to_i64", "to-i64", &["f64", "i64"], Some("to_i64")),
        (
            "f64.to_string",
            "to-string",
            &["f64", "String"],
            Some("to_string"),
        ),
        ("bool.guard", "guard", &["bool", "Unit"], None),
    ];
    assert_eq!(cases.len(), 35);
    let missing: Vec<_> = cases
        .iter()
        .filter_map(|(suffix, ..)| {
            let key = format!("egglog.core.{suffix}");
            (!catalog.primitives.iter().any(|d| d.name == key)).then_some(key)
        })
        .collect();
    assert!(
        missing.is_empty(),
        "missing scalar catalog entries: {missing:?}"
    );
    for &(suffix, alias, names, _python) in cases {
        let key = format!("egglog.core.{suffix}");
        let declarations: Vec<_> = catalog
            .primitives
            .iter()
            .filter(|d| d.name == key)
            .collect();
        assert_eq!(declarations.len(), 1, "{key}");
        let declaration = declarations[0];
        let primitive = declaration;
        assert_eq!(
            builtin::signature_sorts(&catalog, primitive).unwrap(),
            names,
            "{key}"
        );
        let Some(signature) = &primitive.signature else {
            unreachable!()
        };
        assert!(signature.type_param_count == 0 && signature.varargs.is_empty());
        let sorts: Vec<_> = names
            .iter()
            .map(|name| graph.get_sort_by_name(name).unwrap().clone())
            .collect();
        for context in [Context::Pure, Context::Read, Context::Write, Context::Full] {
            let alias = ResolvedCall::from_resolution(
                alias,
                &sorts,
                graph.type_info(),
                context,
                &ast::Span::Panic,
            )
            .unwrap();
            let keyed = ResolvedCall::from_resolution(
                &key,
                &sorts,
                graph.type_info(),
                context,
                &ast::Span::Panic,
            )
            .unwrap();
            assert_eq!(alias, keyed, "{key}");
            let ResolvedCall::Primitive(primitive) = keyed else {
                unreachable!()
            };
            assert!(primitive.validator().is_some(), "{key}");
        }
        for mutation in ["input", "output", "arity"] {
            let mut wrong = primitive.clone();
            let Some(s) = &mut wrong.signature else {
                unreachable!()
            };
            let index = if mutation == "output" {
                s.output.unwrap()
            } else {
                s.inputs[0].sort
            };
            let other = catalog.sorts.iter().position(|sort| matches!(&sort.kind,
                Some(proto::sort::Kind::Application(f)) if f.args.is_empty() && f.name != names[if mutation == "output" {names.len()-1} else {0}])).unwrap() as u32;
            assert_ne!(other, index);
            match mutation {
                "input" => s.inputs[0].sort = other,
                "output" => s.output = Some(other),
                _ => {
                    s.inputs.pop();
                }
            }
            assert!(
                graph
                    .type_info()
                    .check_portable_builtin_signature(&catalog, &wrong)
                    .is_err(),
                "{key}: {mutation}"
            );
        }
    }
}

#[test]
fn remaining_scalar_generic_catalog_preserves_homogeneous_providers() {
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(
            None,
            "(datatype Item (A) (B)) (sort Items (Vec Item)) (sort Ints (Vec i64))",
        )
        .unwrap();
    let catalog = graph
        .type_info()
        .portable_builtin_catalog()
        .unwrap()
        .definitions;
    for (key, alias, output, validator) in [
        ("egglog.core.bool_ne", "bool-!=", "bool", true),
        ("egglog.core.value_eq", "value-eq", "Unit", false),
    ] {
        let declaration = catalog
            .primitives
            .iter()
            .find(|d| d.name == key)
            .unwrap_or_else(|| panic!("missing {key}"));
        let primitive = declaration;
        let Some(signature) = &primitive.signature else {
            unreachable!()
        };
        assert_eq!(signature.type_param_count, 1);
        assert_eq!(signature.inputs.len(), 2);
        assert!(signature.varargs.is_empty());
        assert_eq!(signature.inputs[0].sort, signature.inputs[1].sort);
        assert_eq!(
            catalog.sorts[signature.inputs[0].sort as usize].kind,
            Some(proto::sort::Kind::Var(0))
        );
        assert!(
            matches!(&catalog.sorts[signature.output.unwrap() as usize].kind, Some(proto::sort::Kind::Application(f)) if f.name == output && f.args.is_empty())
        );
        for name in [
            "i64", "bool", "f64", "String", "BigInt", "BigRat", "Unit", "Item", "Items", "Ints",
        ] {
            let sorts =
                [name, name, output].map(|name| graph.get_sort_by_name(name).unwrap().clone());
            for context in [Context::Pure, Context::Read, Context::Write, Context::Full] {
                let source = ResolvedCall::from_resolution(
                    alias,
                    &sorts,
                    graph.type_info(),
                    context,
                    &ast::Span::Panic,
                )
                .unwrap();
                let canonical = ResolvedCall::from_resolution(
                    key,
                    &sorts,
                    graph.type_info(),
                    context,
                    &ast::Span::Panic,
                )
                .unwrap();
                assert_eq!(source, canonical);
                let ResolvedCall::Primitive(primitive) = canonical else {
                    unreachable!()
                };
                assert_eq!(primitive.validator().is_some(), validator);
            }
        }
        for expression in [format!("({alias} 1)"), format!("({alias} 1 2 3)")] {
            let error = graph
                .parse_and_run_program(None, &expression)
                .unwrap_err()
                .to_string();
            assert!(error.contains(alias), "{error}");
            assert!(!error.contains(key), "{error}");
        }
        let error = graph
            .parse_and_run_program(None, &format!("({alias} 1 true)"))
            .unwrap_err()
            .to_string();
        assert!(error.contains("bool") && error.contains("i64"), "{error}");
        assert!(!error.contains(key), "{error}");
    }
}

#[test]
fn remaining_scalar_native_boundaries() {
    let mut graph = EGraph::default();
    graph.parse_and_run_program(None, r#"
        (check (= (| 2 4) 6) (= (^ 6 2) 4) (= (<< 1 63) -9223372036854775808) (= (>> -8 2) -2))
        (check (= (not-i64 0) -1) (= (log2 8) 3) (= (abs -7) 7) (> 3 2) (<= 2 2))
        (check (= (bool-= 1 1) true) (= (bool-= 1 2) false))
        (check (= (bool-< 1 2) true) (= (bool-< 2 2) false) (= (bool-< 3 2) false))
        (check (= (bool-> 3 2) true) (= (bool-> 2 2) false) (= (bool-> 1 2) false))
        (check (= (bool-<= 1 2) true) (= (bool-<= 2 2) true) (= (bool-<= 3 2) false))
        (check (= (bool->= 3 2) true) (= (bool->= 2 2) true) (= (bool->= 1 2) false))
        (check (= (bool-< -9223372036854775808 9223372036854775807) true))
        (check (= (count-matches "ééé" "éé") 1) (= (count-matches "é" "") 2) (= (count-matches "" "") 1))
        (check (= (- 3.0 2.0) 1.0) (= (* 3.0 2.0) 6.0) (= (/ 3.0 2.0) 1.5) (= (% 3.0 2.0) 1.0))
        (check (= (^ 4.0 0.5) 2.0) (= (neg 2.0) -2.0) (< 1.0 2.0) (> 2.0 1.0) (<= 1.0 1.0) (>= 1.0 1.0))
        (check (= (min 1.0 2.0) 1.0) (= (max 1.0 2.0) 2.0) (= (abs -2.0) 2.0) (= (exp 0.0) 1.0) (= (log 1.0) 0.0) (= (sqrt 4.0) 2.0))
        (check (= (to-f64 2) 2.0) (= (to-i64 -2.9) -2) (= (to-string 2.0) "2.0") (guard true))
        (check (= (bool-!= 1 2) true) (= (bool-!= true true) false) (value-eq "a" "a"))
        (datatype Item (A) (B)) (sort Items (Vec Item)) (A) (B)
        (check (= (bool-!= (A) (B)) true) (= (bool-!= (vec-of (A)) (vec-of (B))) true))
        (fail (check (value-eq (A) (B))))
        (union (A) (B))
        (check (= (bool-!= (A) (B)) false) (= (bool-!= (vec-of (A)) (vec-of (B))) false) (value-eq (A) (B)) (value-eq (vec-of (A)) (vec-of (B))))
    "#).unwrap();
    for expression in [
        "(<< 1 -1)",
        "(<< 1 64)",
        "(>> 1 -1)",
        "(>> 1 64)",
        "(log2 0)",
        "(log2 -1)",
        "(abs -9223372036854775808)",
        "(/ 1.0 0.0)",
        "(/ 1.0 -0.0)",
        "(% 1.0 0.0)",
        "(% 1.0 -0.0)",
        "(log 0.0)",
        "(sqrt -1.0)",
        "(guard false)",
    ] {
        assert!(
            EGraph::default()
                .parse_and_run_program(None, &format!("(let $invalid {expression})"))
                .is_err(),
            "{expression}"
        );
    }
    let error = EGraph::new_with_proofs()
        .parse_and_run_program(None, "(check (value-eq 1 1))")
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("primitive operation lacks a validator function"),
        "{error}"
    );
}

#[test]
fn inequality_native_baseline() {
    let text = r#"
        (check (!= 1 2) (!= true false))
        (fail (check (!= 1 1)))
        (fail (check (!= false false)))
        (datatype Item (A) (B))
        (sort Items (Vec Item))
        (sort Ints (Vec i64))
        (A) (B)
        (check (!= (A) (B)) (!= (vec-of (A)) (vec-of (B))) (!= (vec-of 1) (vec-of 2)))
        (fail (check (!= (vec-of (A)) (vec-of (A)))))
        (union (A) (B))
        (check (= (A) (B)) (= (vec-of (A)) (vec-of (B))))
        (fail (check (!= (A) (B))))
        (fail (check (!= (vec-of (A)) (vec-of (B)))))
    "#;
    for mode in 0..3 {
        let mut graph = match mode {
            0 => EGraph::default(),
            1 => EGraph::new_with_proofs(),
            _ => EGraph::new_with_proofs().with_proof_testing(),
        };
        graph
            .parse_and_run_program(None, text)
            .unwrap_or_else(|error| panic!("mode {mode}: {error}"));
        if mode > 0 {
            graph
                .parse_and_run_program(None, "(datatype Witness (Wrap)) (rule ((!= 1 2)) ((Wrap))) (run 1) (prove-exists Wrap)")
                .unwrap();
        }
    }
}

#[test]
fn inequality_catalog_uses_one_generic_registration() {
    let mut graph = EGraph::default();
    let catalog = graph.type_info().portable_builtin_catalog().unwrap();
    let declaration = catalog
        .definitions
        .primitives
        .iter()
        .find(|d| d.name == "egglog.core.ne")
        .expect("native inequality is missing its canonical descriptor");
    let primitive = declaration;
    let Some(signature) = &primitive.signature else {
        unreachable!()
    };
    assert_eq!(signature.type_param_count, 1);
    assert_eq!(signature.inputs.len(), 2);
    assert!(signature.varargs.is_empty());
    assert_eq!(signature.inputs[0].sort, signature.inputs[1].sort);
    assert_eq!(
        catalog.definitions.sorts[signature.inputs[0].sort as usize].kind,
        Some(proto::sort::Kind::Var(0))
    );
    assert!(
        matches!(&catalog.definitions.sorts[signature.output.unwrap() as usize].kind,
        Some(proto::sort::Kind::Application(f)) if f.name == "Unit" && f.args.is_empty())
    );
    assert!(
        !catalog
            .undescribed_primitives
            .iter()
            .any(|name| name == "!=")
    );
    graph.parse_and_run_program(None, "(datatype Item (A) (B)) (sort Items (Vec Item)) (sort Ints (Vec i64)) (sort Pairs (Pair Item i64)) (sort Sets (Set Item)) (sort Maps (Map i64 Item))").unwrap();
    for name in [
        "i64", "bool", "f64", "String", "BigInt", "BigRat", "Unit", "Item", "Items", "Ints",
        "Pairs", "Sets", "Maps",
    ] {
        let sort = graph.get_sort_by_name(name).unwrap().clone();
        let sorts = [
            sort.clone(),
            sort,
            graph.get_sort_by_name("Unit").unwrap().clone(),
        ];
        for context in [Context::Pure, Context::Read, Context::Write, Context::Full] {
            let alias = ResolvedCall::from_resolution(
                "!=",
                &sorts,
                graph.type_info(),
                context,
                &ast::Span::Panic,
            )
            .unwrap();
            let canonical = ResolvedCall::from_resolution(
                "egglog.core.ne",
                &sorts,
                graph.type_info(),
                context,
                &ast::Span::Panic,
            )
            .unwrap();
            assert_eq!(alias, canonical);
            let ResolvedCall::Primitive(primitive) = canonical else {
                unreachable!()
            };
            assert!(primitive.validator().is_some());
        }
        let mut program = proto::Program {
            ..Default::default()
        };
        let input = graph.export_sort(&sorts[0], &mut program.sorts).unwrap();
        let output = graph.export_sort(&sorts[2], &mut program.sorts).unwrap();
        assert_eq!(
            graph
                .type_info()
                .resolve_portable_builtin(
                    &program,
                    "egglog.core.ne",
                    &[input, input],
                    output,
                    &sorts
                )
                .unwrap(),
            "egglog.core.ne"
        );
    }
    for text in ["(!= 1)", "(!= 1 2 3)"] {
        let error = graph
            .parse_and_run_program(None, text)
            .unwrap_err()
            .to_string();
        assert!(error.contains("!="), "{error}");
        assert!(!error.contains("egglog.core.ne"), "{error}");
    }
    let error = graph
        .parse_and_run_program(None, "(!= 1 true)")
        .unwrap_err()
        .to_string();
    assert!(error.contains("bool") && error.contains("i64"), "{error}");
}

#[test]
fn inequality_catalog_export_does_not_execute_generic_provider() {
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    let mut graph = EGraph::default();
    add_primitive_with_validator!(&mut graph, "counted-generic" [id = "test.counted-generic"] = |a: #, b: #| -?> () {
        { CALLS.fetch_add(1, Ordering::SeqCst); (a != b).then_some(()) }
    }, |_: &mut TermDag, _: &[TermId]| { CALLS.fetch_add(1, Ordering::SeqCst); None });
    let before = graph
        .type_info()
        .portable_builtin_catalog()
        .unwrap()
        .definitions;
    let after = graph
        .type_info()
        .portable_builtin_catalog()
        .unwrap()
        .definitions;
    assert_eq!(before, after);
    assert!(
        before
            .primitives
            .iter()
            .any(|d| d.name == "test.counted-generic")
    );
    assert_eq!(CALLS.load(Ordering::SeqCst), 0);
}

#[test]
fn bigrat_properties_export_actual_signatures_and_views() {
    let mut graph = EGraph::default();
    let program = graph
        .type_info()
        .portable_builtin_catalog()
        .unwrap()
        .definitions;
    for name in ["numer", "denom"] {
        let key = format!("egglog.core.bigrat.{name}");
        let declaration = program
            .primitives
            .iter()
            .find(|d| d.name == key)
            .unwrap_or_else(|| panic!("missing native catalog definition {key}"));
        let primitive = declaration;
        assert_eq!(
            builtin::signature_sorts(&program, primitive).unwrap(),
            ["BigRat", "BigInt"]
        );
        let Some(signature) = &primitive.signature else {
            unreachable!()
        };
        assert!(signature.varargs.is_empty());
        let sorts = ["BigRat", "BigInt"].map(|s| graph.get_sort_by_name(s).unwrap().clone());
        for context in [Context::Pure, Context::Read, Context::Write, Context::Full] {
            let ResolvedCall::Primitive(alias) = ResolvedCall::from_resolution(
                name,
                &sorts,
                graph.type_info(),
                context,
                &ast::Span::Panic,
            )
            .unwrap() else {
                unreachable!()
            };
            let ResolvedCall::Primitive(canonical) = ResolvedCall::from_resolution(
                &key,
                &sorts,
                graph.type_info(),
                context,
                &ast::Span::Panic,
            )
            .unwrap() else {
                unreachable!()
            };
            assert_eq!(alias, canonical);
            assert!(canonical.validator().is_none());
        }
    }
}

#[test]
fn numeric_catalog_members_preserve_native_providers_and_typed_views() {
    let mut graph = EGraph::default();
    let program = graph
        .type_info()
        .portable_builtin_catalog()
        .unwrap()
        .definitions;
    let mut count = 0;
    for declaration in &program.primitives {
        let primitive = declaration;
        let owner = if primitive.name.starts_with("egglog.core.bigint.") {
            "BigInt"
        } else if primitive.name.starts_with("egglog.core.bigrat.") {
            "BigRat"
        } else {
            continue;
        };
        let member = primitive.name.rsplit('.').next().unwrap();
        if matches!(member, "from_i64" | "from_string" | "make") {
            continue; // Constructor contracts are checked separately.
        }
        count += 1;
        let Some(signature) = &primitive.signature else {
            unreachable!()
        };
        assert!(signature.type_param_count == 0 && signature.varargs.is_empty());
        let sort_names = builtin::signature_sorts(&program, primitive).unwrap();
        assert_eq!(sort_names[0], owner);
        match member {
            "numer" | "denom" => assert_eq!(sort_names, ["BigRat", "BigInt"]),
            "shl" | "shr" => assert_eq!(sort_names, ["BigInt", "i64", "BigInt"]),
            "lt" | "gt" | "le" | "ge" => assert_eq!(sort_names, [owner, owner, "Unit"]),
            "bool_eq" | "bool_lt" | "bool_gt" | "bool_le" | "bool_ge" => {
                assert_eq!(sort_names, ["BigInt", "BigInt", "bool"]);
            }
            "to_string" => assert_eq!(sort_names, ["BigInt", "String"]),
            "to_i64" => assert_eq!(sort_names, ["BigRat", "i64"]),
            "to_f64" => assert_eq!(sort_names, ["BigRat", "f64"]),
            _ => assert!(sort_names.iter().all(|name| name == owner)),
        }
        let aliases = graph
            .type_info()
            .builtin_description(&primitive.name)
            .unwrap()
            .aliases
            .clone();
        let alias = &aliases[0];
        let native_sorts = sort_names
            .iter()
            .map(|name| graph.get_sort_by_name(name).unwrap().clone())
            .collect::<Vec<_>>();
        for context in [Context::Pure, Context::Read, Context::Write, Context::Full] {
            let ResolvedCall::Primitive(source) = ResolvedCall::from_resolution(
                alias,
                &native_sorts,
                graph.type_info(),
                context,
                &ast::Span::Panic,
            )
            .unwrap() else {
                unreachable!()
            };
            let ResolvedCall::Primitive(canonical) = ResolvedCall::from_resolution(
                &primitive.name,
                &native_sorts,
                graph.type_info(),
                context,
                &ast::Span::Panic,
            )
            .unwrap() else {
                unreachable!()
            };
            assert_eq!(source, canonical);
            assert!(source.validator().is_none() && canonical.validator().is_none());
        }
    }
    assert_eq!(count, 47);
}

#[test]
fn closed_i64_catalog_preserves_signatures_aliases_and_borrowed_views() {
    let mut graph = EGraph::default();
    let program = graph
        .type_info()
        .portable_builtin_catalog()
        .unwrap()
        .definitions;
    let float = program
        .sorts
        .iter()
        .position(|s| matches!(&s.kind, Some(proto::sort::Kind::Application(f)) if f.name == "f64"))
        .unwrap() as u32;
    for (key, alias, output) in [
        ("sub", "-", "i64"),
        ("mul", "*", "i64"),
        ("div", "/", "i64"),
        ("rem", "%", "i64"),
        ("bitand", "&", "i64"),
        ("lt", "<", "Unit"),
        ("ge", ">=", "Unit"),
        ("min", "min", "i64"),
        ("max", "max", "i64"),
    ] {
        let key = format!("egglog.core.i64.{key}");
        let definitions: Vec<_> = program
            .primitives
            .iter()
            .filter(|d| d.name == key)
            .collect();
        assert_eq!(definitions.len(), 1, "{key}");
        let declaration = definitions[0];
        let primitive = declaration;
        assert_eq!(
            builtin::signature_sorts(&program, primitive).unwrap(),
            ["i64", "i64", output]
        );
        let Some(signature) = &primitive.signature else {
            unreachable!()
        };
        assert!(signature.type_param_count == 0);
        assert!(signature.varargs.is_empty());
        let sorts = ["i64", "i64", output].map(|s| graph.get_sort_by_name(s).unwrap().clone());
        for context in [Context::Pure, Context::Read, Context::Write, Context::Full] {
            let ResolvedCall::Primitive(source) = ResolvedCall::from_resolution(
                alias,
                &sorts,
                graph.type_info(),
                context,
                &ast::Span::Panic,
            )
            .unwrap() else {
                unreachable!()
            };
            let ResolvedCall::Primitive(canonical) = ResolvedCall::from_resolution(
                &key,
                &sorts,
                graph.type_info(),
                context,
                &ast::Span::Panic,
            )
            .unwrap() else {
                unreachable!()
            };
            assert_eq!(source, canonical);
            assert!(canonical.validator().is_some());
        }
        for corrupt_output in [false, true] {
            let mut wrong = primitive.clone();
            let Some(signature) = &mut wrong.signature else {
                unreachable!()
            };
            if corrupt_output {
                signature.output = Some(float);
            } else {
                signature.inputs[0].sort = float;
            }
            assert!(
                graph
                    .type_info()
                    .check_portable_builtin_signature(&program, &wrong)
                    .is_err()
            );
        }
        let mut unknown = primitive.clone();
        unknown.name = format!("test.unregistered.{key}");
        assert!(
            graph
                .type_info()
                .check_portable_builtin_signature(&program, &unknown)
                .is_err()
        );
    }
}

#[test]
fn closed_i64_native_partiality_and_signed_extrema() {
    let mut graph = EGraph::default();
    for (expression, expected) in [
        ("(- -13 5)", -18),
        ("(* -13 5)", -65),
        ("(/ -13 5)", -2),
        ("(% -13 5)", -3),
        ("(& -13 5)", 1),
        ("(min -9223372036854775808 9223372036854775807)", i64::MIN),
        ("(max -9223372036854775808 9223372036854775807)", i64::MAX),
    ] {
        graph
            .parse_and_run_program(None, &format!("(check (= {expression} {expected}))"))
            .unwrap();
    }
    for (fact, matches) in [
        ("(< -13 5)", true),
        ("(< 5 -13)", false),
        ("(>= -13 5)", false),
        ("(>= 5 -13)", true),
        ("(< 5 5)", false),
        ("(>= 5 5)", true),
    ] {
        assert_eq!(
            graph
                .parse_and_run_program(None, &format!("(check {fact})"))
                .is_ok(),
            matches,
            "{fact}"
        );
    }
    for expression in [
        "(/ 1 0)",
        "(% 1 0)",
        "(/ -9223372036854775808 -1)",
        "(% -9223372036854775808 -1)",
        "(- -9223372036854775808 1)",
        "(* 9223372036854775807 2)",
    ] {
        assert!(
            EGraph::default()
                .parse_and_run_program(None, &format!("(let invalid {expression})"))
                .is_err(),
            "{expression}"
        );
    }
}

#[test]
fn set_catalog_precedes_instances_and_preserves_native_aliases() {
    let mut graph = EGraph::default();
    let before = graph.type_info().portable_builtin_catalog().unwrap();
    assert!(!before.undescribed_families.iter().any(|f| f == "Set"));
    assert!(
        !before
            .undescribed_family_primitives
            .iter()
            .any(|f| f.starts_with("Set::"))
    );
    let family = before
        .definitions
        .primitive_sorts
        .iter()
        .find(|d| d.name == "Set")
        .unwrap();
    assert_eq!(family.arity, 1);
    assert_eq!(
        before
            .definitions
            .primitives
            .iter()
            .filter(|d| d.name.starts_with("egglog.core.set."))
            .count(),
        11
    );
    graph.parse_and_run_program(None, "(sort SI (Set i64)) (sort Other (Set i64)) (sort Math) (constructor A () Math) (sort SM (Set Math))").unwrap();
    for (element, set) in [("i64", "SI"), ("Math", "SM")] {
        for (key, alias, inputs, output) in [
            ("empty", "set-empty", &[][..], set),
            ("of", "set-of", &[element, element][..], set),
            ("get", "set-get", &[set, "i64"][..], element),
            ("insert", "set-insert", &[set, element][..], set),
            ("remove", "set-remove", &[set, element][..], set),
            ("length", "set-length", &[set][..], "i64"),
            ("contains", "set-contains", &[set, element][..], "Unit"),
            (
                "not_contains",
                "set-not-contains",
                &[set, element][..],
                "Unit",
            ),
            ("union", "set-union", &[set, set][..], set),
            ("diff", "set-diff", &[set, set][..], set),
            ("intersect", "set-intersect", &[set, set][..], set),
        ] {
            let key = format!("egglog.core.set.{key}");
            let sorts = inputs
                .iter()
                .copied()
                .chain([output])
                .map(|name| graph.get_sort_by_name(name).unwrap().clone())
                .collect::<Vec<_>>();
            let d = before
                .definitions
                .primitives
                .iter()
                .find(|d| d.name == key)
                .unwrap();
            let p = &d;
            let Some(s) = &p.signature else {
                unreachable!()
            };
            assert_eq!(s.type_param_count, 1);
            assert_eq!(s.varargs.len(), usize::from(alias == "set-of"));
            assert_eq!(
                s.inputs.len(),
                if alias == "set-of" { 0 } else { inputs.len() }
            );
            for context in [Context::Pure, Context::Read, Context::Write, Context::Full] {
                let ResolvedCall::Primitive(a) = ResolvedCall::from_resolution(
                    alias,
                    &sorts,
                    graph.type_info(),
                    context,
                    &ast::Span::Panic,
                )
                .unwrap() else {
                    unreachable!()
                };
                let ResolvedCall::Primitive(b) = ResolvedCall::from_resolution(
                    &key,
                    &sorts,
                    graph.type_info(),
                    context,
                    &ast::Span::Panic,
                )
                .unwrap() else {
                    unreachable!()
                };
                assert_eq!(a, b);
                assert_eq!(a.validator().is_some(), alias != "set-get");
                let mut exported = proto::Program::default();
                assert_eq!(a.export_builtin(&mut exported).unwrap(), key);
            }
        }
    }
    assert_eq!(
        graph
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions,
        before.definitions
    );
    graph.parse_and_run_program(None, "(function first () SI :merge new) (function second () Other :merge new) (set (first) (set-empty)) (set (second) (set-of)) (check (= (set-length (first)) 0)) (check (= (set-length (second)) 0))").unwrap();
    for invalid in [
        "(set-empty)",
        "(set-union (first) (second))",
        "(set (first) (set-of 1.0))",
        "(set (first) (set-empty 1))",
        "(set-get (first))",
    ] {
        assert!(
            graph.parse_and_run_program(None, invalid).is_err(),
            "{invalid}"
        );
    }
}

#[test]
fn exact_integer_families_and_constructors_use_actual_native_providers() {
    let mut graph = EGraph::default();
    assert!(graph.get_sort_by_name("Rational").is_none());
    let catalog = graph.type_info().portable_builtin_catalog().unwrap();
    assert!(
        !catalog
            .definitions
            .primitives
            .iter()
            .any(|d| d.name.starts_with("egglog.experimental.rational."))
    );
    for name in ["BigInt", "BigRat"] {
        let family = catalog
            .definitions
            .primitive_sorts
            .iter()
            .find(|d| d.name == name)
            .unwrap();
        assert_eq!(family.arity, 0);
    }
    for (key, alias, inputs, output) in [
        (
            "egglog.core.bigint.from_i64",
            "bigint",
            &["i64"][..],
            "BigInt",
        ),
        (
            "egglog.core.bigint.from_string",
            "from-string",
            &["String"][..],
            "BigInt",
        ),
        (
            "egglog.core.bigrat.make",
            "bigrat",
            &["BigInt", "BigInt"][..],
            "BigRat",
        ),
    ] {
        let d = catalog
            .definitions
            .primitives
            .iter()
            .find(|d| d.name == key)
            .unwrap();
        let p = &d;
        let Some(s) = &p.signature else {
            unreachable!()
        };
        assert!(s.type_param_count == 0 && s.varargs.is_empty());
        assert_eq!(s.inputs.len(), inputs.len());
        for (sort, name) in s
            .inputs
            .iter()
            .map(|arg| arg.sort)
            .chain(s.output)
            .zip(inputs.iter().copied().chain([output]))
        {
            assert!(
                matches!(&catalog.definitions.sorts[sort as usize].kind, Some(proto::sort::Kind::Application(f)) if f.name == name && f.args.is_empty())
            );
        }
        let sorts = inputs
            .iter()
            .chain([&output])
            .map(|name| graph.get_sort_by_name(name).unwrap().clone())
            .collect::<Vec<_>>();
        for context in [Context::Pure, Context::Read, Context::Write, Context::Full] {
            let ResolvedCall::Primitive(alias) = ResolvedCall::from_resolution(
                alias,
                &sorts,
                graph.type_info(),
                context,
                &ast::Span::Panic,
            )
            .unwrap() else {
                unreachable!()
            };
            let ResolvedCall::Primitive(canonical) = ResolvedCall::from_resolution(
                key,
                &sorts,
                graph.type_info(),
                context,
                &ast::Span::Panic,
            )
            .unwrap() else {
                unreachable!()
            };
            assert_eq!(alias, canonical); // same concrete sorts and native context IDs
            assert!(alias.validator().is_none() && canonical.validator().is_none());
        }
    }
    graph.parse_and_run_program(None, "(check (= (bigint 7) (from-string \"7\"))) (check (= (bigrat (bigint 2) (bigint -4)) (bigrat (bigint -1) (bigint 2)))) (fail (from-string \"not-an-integer\")) (fail (bigrat (bigint 1) (bigint 0)))").unwrap();
}

#[test]
fn annotated_builtins_resolve_in_the_nonexecuting_authoring_context() {
    use ast::{Action, Command, Expr, Literal};
    for mode in 0..4 {
        let mut graph = match mode {
            0 => EGraph::default(),
            1 => EGraph::new_with_term_encoding(),
            2 => EGraph::new_with_proofs(),
            _ => EGraph::new_with_proofs().with_proof_testing(),
        };
        let declarations = graph
            .parse_program(None, "(sort V (Vec i64)) (relation Values (V))")
            .unwrap();
        for declaration in declarations {
            graph.resolve_command_before_proofs(declaration).unwrap();
        }
        // The logical sort exists, while the encoded runtime has not installed
        // this family instance. Selecting only from runtime TypeInfo cannot work.
        assert_eq!(graph.get_sort_by_name("V").is_none(), mode > 0);
        let program = proto::Program {
            sorts: vec![
                proto::Sort {
                    kind: Some(proto::sort::Kind::Application(proto::SortApplication {
                        name: "i64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
                proto::Sort {
                    kind: Some(proto::sort::Kind::Application(proto::SortApplication {
                        name: "Vec".into(),
                        args: vec![0],
                    })),
                    ..Default::default()
                },
            ],
            ..Default::default()
        };
        let add = graph
            .resolve_builtin_call(
                &program,
                "egglog.core.i64.add",
                &[0, 0],
                0,
                &["i64", "i64", "i64"],
            )
            .unwrap();
        let empty = graph
            .resolve_builtin_call(&program, "egglog.core.vec.empty", &[], 1, &["V"])
            .unwrap();
        let span = ast::Span::Panic;
        let plus = Expr::Call(
            span.clone(),
            add,
            vec![
                Expr::Lit(span.clone(), Literal::Int(1)),
                Expr::Lit(span.clone(), Literal::Int(2)),
            ],
        );
        graph
            .resolve_command_before_proofs(Command::Action(Action::Expr(span.clone(), plus)))
            .unwrap();
        let empty = Expr::Call(
            span.clone(),
            "Values".into(),
            vec![Expr::Call(span.clone(), empty, vec![])],
        );
        graph
            .resolve_command_before_proofs(Command::Action(Action::Expr(span, empty)))
            .unwrap();
        assert!(
            graph
                .resolve_builtin_call(&program, "egglog.core.i64.add", &[0], 0, &["i64", "i64"])
                .is_err()
        );
        assert!(
            graph
                .resolve_builtin_call(&program, "egglog.core.vec.empty", &[], 1, &["i64"])
                .is_err()
        );
        assert!(
            graph
                .resolve_builtin_call(&program, "egglog.core.vec.empty", &[], 1, &["missing"])
                .is_err()
        );
    }
}

#[test]
fn flat_map_export_packs_existing_refs_without_native_pair_vec_aliases() {
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(
            None,
            "(datatype Pair (Z)) (sort Vec) (sort Map) (sort M (Map Pair Pair))",
        )
        .unwrap();
    let n = graph.get_sort_by_name("Pair").unwrap().clone();
    let m = graph.get_sort_by_name("M").unwrap().clone();
    for count in [0, 1, 3] {
        let mut sorts = vec![n.clone(); count * 2];
        sorts.push(m.clone());
        let ResolvedCall::Primitive(primitive) = ResolvedCall::from_resolution(
            "map-of",
            &sorts,
            graph.type_info(),
            Context::Pure,
            &ast::Span::Panic,
        )
        .unwrap() else {
            panic!("primitive")
        };
        let mut program = proto::Program {
            files: vec![proto::SourceFile {
                name: "map.egg".into(),
                contents: None,
            }],
            ..Default::default()
        };
        assert!(primitive.export_builtin(&mut program).is_err());
        let sort_id = graph.export_sort(&n, &mut program.sorts).unwrap();
        for offset in [0, 2] {
            program.nodes.push(proto::Node {
                sort_id,
                kind: Some(proto::node::Kind::Union(proto::Union::default())),
                span: Some(proto::Span {
                    file: 0,
                    start: offset,
                    end: offset + 1,
                }),
            });
        }
        let original = program.nodes.clone();
        let args = [0, 1, 0, 0, 1, 0][..count * 2].to_vec();
        let span = Some(proto::Span {
            file: 0,
            start: 0,
            end: 10,
        });
        let mut invalid = args.clone();
        invalid.push(0);
        let before = program.clone();
        assert!(
            primitive
                .export_builtin_call(&graph, &invalid, span, &mut program)
                .is_err()
        );
        assert_eq!(
            program, before,
            "wrong arity must not mutate the destination"
        );
        let mut invalid = args.clone();
        if let Some(first) = invalid.first_mut() {
            *first = program.nodes.len() as u32;
            assert!(
                primitive
                    .export_builtin_call(&graph, &invalid, span, &mut program)
                    .is_err()
            );
            assert_eq!(
                program, before,
                "invalid input reference must not mutate the destination"
            );
        }
        let call = primitive
            .export_builtin_call(&graph, &args, span, &mut program)
            .unwrap();
        assert_eq!(call.func, "egglog.core.map.of");
        assert_eq!(call.args.len(), 1);
        assert_eq!(&program.nodes[..2], original);
        assert_eq!(program.nodes.len(), count + 3);
        for (pair, fields) in program.nodes[2..2 + count].iter().zip(args.chunks_exact(2)) {
            let Some(proto::node::Kind::PrimitiveValue(proto::PrimitiveValue {
                value: Some(proto::primitive_value::Value::Pair(value)),
            })) = &pair.kind
            else {
                panic!("pair value")
            };
            assert_eq!(value.first, Some(fields[0]));
            assert_eq!(value.second, Some(fields[1]));
            assert_eq!(pair.span, span);
        }
        let Some(proto::node::Kind::PrimitiveValue(proto::PrimitiveValue {
            value: Some(proto::primitive_value::Value::Vec(vector)),
        })) = &program.nodes[*call.args.first().unwrap() as usize].kind
        else {
            panic!("vector value")
        };
        assert_eq!(vector.items, (2..2 + count as u32).collect::<Vec<_>>());
        assert_eq!(program.nodes.last().unwrap().span, span);
        assert!(
            program.declarations.is_empty(),
            "builtin signatures stay in GetBuiltins"
        );
        let catalog = graph
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions;
        let primitives = catalog
            .primitives
            .iter()
            .filter(|primitive| primitive.name == "egglog.core.map.of")
            .collect::<Vec<_>>();
        assert_eq!(
            primitives.len(),
            1,
            "packing values need no Pair/Vec constructor callables"
        );
        assert_eq!(primitives[0].name, "egglog.core.map.of");
        let Some(signature) = &primitives[0].signature else {
            unreachable!()
        };
        assert_eq!(signature.type_param_count, 2);
        assert_eq!(signature.inputs.len(), 1);
        assert!(signature.varargs.is_empty());
        let Some(proto::sort::Kind::Application(vector)) =
            &catalog.sorts[signature.inputs[0].sort as usize].kind
        else {
            panic!("Vec<Pair<K, V>> signature input")
        };
        assert_eq!(vector.name, "Vec");
        assert_eq!(vector.args.len(), 1);
        let Some(proto::sort::Kind::Application(pair)) =
            &catalog.sorts[vector.args[0] as usize].kind
        else {
            panic!("Pair<K, V> signature element")
        };
        assert_eq!(pair.name, "Pair");
        let Some(proto::sort::Kind::Application(map)) =
            &catalog.sorts[signature.output.unwrap() as usize].kind
        else {
            panic!("Map<K, V> signature result")
        };
        assert_eq!(map.name, "Map");
        assert_eq!(pair.args, map.args);
        assert_eq!(map.args.len(), 2);
    }
}

#[test]
fn map_catalog_precedes_instances_and_uses_one_vec_of_pairs_input() {
    let mut graph = EGraph::default();
    let before = graph
        .type_info()
        .portable_builtin_catalog()
        .unwrap()
        .definitions;
    let family = before
        .primitive_sorts
        .iter()
        .find(|d| d.name == "Map")
        .unwrap();
    assert_eq!(family.arity, 2);
    for method in ["empty", "of", "get", "insert"] {
        let declaration = before
            .primitives
            .iter()
            .find(|d| d.name == format!("egglog.core.map.{method}"))
            .expect("canonical Map provider must exist before instances");
        if method == "of" {
            let p = &declaration;
            let Some(signature) = &p.signature else {
                unreachable!()
            };
            assert_eq!(signature.inputs.len(), 1);
            assert!(signature.varargs.is_empty());
            let Some(proto::sort::Kind::Application(vec)) =
                &before.sorts[signature.inputs[0].sort as usize].kind
            else {
                panic!("Vec")
            };
            assert_eq!(vec.name, "Vec");
            let Some(proto::sort::Kind::Application(pair)) =
                &before.sorts[vec.args[0] as usize].kind
            else {
                panic!("Pair")
            };
            assert_eq!(pair.name, "Pair");
        }
    }
    graph
        .parse_and_run_program(None, "(sort M (Map i64 f64))")
        .unwrap();
    assert_eq!(
        graph
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions,
        before
    );
}

#[test]
fn map_from_computed_pairs_preserves_flat_construction_and_duplicates() {
    EGraph::default()
        .parse_and_run_program(
            None,
            "
        (sort M (Map i64 f64))
        (sort P (Pair i64 f64)) (sort V (Vec P))
        (function entries () V :merge new)
        (set (entries) (vec-of (pair 1 2.0) (pair 3 4.0) (pair 1 5.0)))
        (check (= (map-from-pairs (entries)) (map-of 1 2.0 3 4.0 1 5.0)))
        (check (= (map-get (map-from-pairs (entries)) 1) 5.0))
        (check (= (map-get (map-insert (map-empty) 1 6.0) 1) 6.0))
        (set (entries) (vec-empty))
        (check (= (map-from-pairs (entries)) (map-of)))
        (check (= (map-of) (map-empty)))
    ",
        )
        .unwrap();
}

#[test]
fn real_map_accepts_both_foreign_aliases_and_rejects_wrong_nested_sorts() {
    for owner_first in [false, true] {
        let mut graph = EGraph::default();
        if owner_first {
            graph
                .parse_and_run_program(None, "(sort M (Map i64 f64))")
                .unwrap();
        }
        graph
            .parse_and_run_program(
                None,
                "
            (sort P (Pair i64 f64)) (sort Q (Pair i64 f64))
            (sort VP (Vec P)) (sort VQ (Vec Q))
            (sort BadP (Pair f64 i64)) (sort BadV (Vec BadP))
            (sort ScalarV (Vec i64))
            (function p () VP :merge new) (function q () VQ :merge new)
            (function bad () BadV :merge new) (function scalar () ScalarV :merge new)
            (set (p) (vec-of (pair 1 2.0))) (set (q) (vec-of (pair 3 4.0)))
        ",
            )
            .unwrap();
        if !owner_first {
            graph
                .parse_and_run_program(None, "(sort M (Map i64 f64))")
                .unwrap();
        }
        graph
            .parse_and_run_program(
                None,
                "
            (check (= (map-get (map-from-pairs (p)) 1) 2.0))
            (check (= (map-get (map-from-pairs (q)) 3) 4.0))
        ",
            )
            .unwrap();
        for invalid in [
            "(map-from-pairs (bad))",
            "(map-from-pairs (scalar))",
            "(map-from-pairs)",
            "(map-from-pairs (p) (q))",
            "(map-from-pairs (vec-empty))",
        ] {
            assert!(
                graph.parse_and_run_program(None, invalid).is_err(),
                "{invalid}"
            );
        }
        let error = graph
            .parse_and_run_program(None, "(map-of 1 2.0 3)")
            .unwrap_err()
            .to_string();
        assert!(error.contains("map-of"), "{error}");
        assert!(!error.contains("egglog.core.map"), "{error}");
    }
}

#[test]
fn resolved_call_export_checks_direct_annotations_and_preserves_ordinary_calls() {
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(
            None,
            "(sort P (Pair i64 i64)) (sort V (Vec i64)) (sort M (Map i64 i64))",
        )
        .unwrap();
    let i = graph.get_sort_by_name("i64").unwrap().clone();
    for (name, output, count, key) in [
        ("+", "i64", 2, "egglog.core.i64.add"),
        ("|", "i64", 2, "egglog.core.i64.bitor"),
        ("pair", "P", 2, "egglog.core.pair.make"),
        ("vec-of", "V", 2, "egglog.core.vec.of"),
        ("map-of", "M", 2, "egglog.core.map.of"),
    ] {
        let mut native = vec![i.clone(); count];
        native.push(graph.get_sort_by_name(output).unwrap().clone());
        let ResolvedCall::Primitive(primitive) = ResolvedCall::from_resolution(
            name,
            &native,
            graph.type_info(),
            Context::Pure,
            &ast::Span::Panic,
        )
        .unwrap() else {
            unreachable!()
        };
        let mut source = proto::Program::default();
        let sort_id = graph.export_sort(&i, &mut source.sorts).unwrap();
        source.nodes.push(proto::Node {
            sort_id,
            kind: Some(proto::node::Kind::PrimitiveValue(proto::PrimitiveValue {
                value: Some(proto::primitive_value::Value::I64(2)),
            })),
            ..Default::default()
        });
        let call = primitive
            .export_builtin_call(&graph, &[0, 0], None, &mut source.clone())
            .unwrap();
        assert_eq!(call.func, key);
        if name != "map-of" {
            assert_eq!(call.args, [0, 0]);
        }
        for args in [&[0][..], &[0, 9][..], &[0, 0, 0][..]] {
            assert!(
                primitive
                    .export_builtin_call(&graph, args, None, &mut source.clone())
                    .is_err()
            );
        }
        for wrong in [
            proto::sort::Kind::Eq("i64".into()),
            proto::sort::Kind::Var(0),
            proto::sort::Kind::Application(proto::SortApplication {
                name: "f64".into(),
                args: vec![],
            }),
            proto::sort::Kind::Application(proto::SortApplication {
                name: "Vec".into(),
                args: vec![0],
            }),
        ] {
            let mut bad = source.clone();
            bad.sorts[0].kind = Some(wrong);
            assert!(
                primitive
                    .export_builtin_call(&graph, &[0, 0], None, &mut bad)
                    .is_err()
            );
        }
        let mut relocated = source.clone();
        relocated.sorts.insert(
            0,
            proto::Sort {
                kind: Some(proto::sort::Kind::Eq("Other".into())),
                ..Default::default()
            },
        );
        relocated.nodes[0].sort_id += 1;
        primitive
            .export_builtin_call(&graph, &[0, 0], None, &mut relocated)
            .unwrap();
    }
    let ResolvedCall::Primitive(unsupported) = ResolvedCall::from_resolution(
        "ordering-min",
        &[i.clone(), i.clone(), i],
        graph.type_info(),
        Context::Pure,
        &ast::Span::Panic,
    )
    .unwrap() else {
        unreachable!()
    };
    let mut source = proto::Program {
        sorts: vec![proto::Sort {
            kind: Some(proto::sort::Kind::Application(proto::SortApplication {
                name: "i64".into(),
                args: vec![],
            })),
            ..Default::default()
        }],
        nodes: vec![proto::Node {
            sort_id: 0,
            kind: Some(proto::node::Kind::Var("x".into())),
            ..Default::default()
        }],
        ..Default::default()
    };
    assert!(
        unsupported
            .export_builtin_call(&graph, &[0, 0], None, &mut source)
            .is_err()
    );
}

#[test]
fn constant_catalog_export_does_not_execute_the_body_or_validator() {
    static BODY: AtomicUsize = AtomicUsize::new(0);
    static VALIDATOR: AtomicUsize = AtomicUsize::new(0);
    let mut graph = EGraph::default();
    add_primitive_with_validator!(
        &mut graph,
        "constant"[id = "test.constant"] = || -> i64 {
            {
                BODY.fetch_add(1, Ordering::SeqCst);
                7
            }
        },
        |_: &mut TermDag, _: &[TermId]| {
            VALIDATOR.fetch_add(1, Ordering::SeqCst);
            None
        }
    );
    let catalog = graph
        .type_info()
        .portable_builtin_catalog()
        .unwrap()
        .definitions;
    let declaration = catalog
        .primitives
        .iter()
        .find(|d| d.name == "test.constant")
        .unwrap();
    assert!(declaration.signature.is_some());
    assert_eq!(BODY.load(Ordering::SeqCst), 0);
    assert_eq!(VALIDATOR.load(Ordering::SeqCst), 0);
    let i = graph.get_sort_by_name("i64").unwrap().clone();
    let ResolvedCall::Primitive(primitive) = ResolvedCall::from_resolution(
        "constant",
        &[i],
        graph.type_info(),
        Context::Pure,
        &ast::Span::Panic,
    )
    .unwrap() else {
        unreachable!()
    };
    let mut exported = proto::Program::default();
    assert_eq!(
        primitive
            .export_builtin_call(&graph, &[], None, &mut exported)
            .unwrap()
            .func,
        "test.constant"
    );
    assert_eq!(BODY.load(Ordering::SeqCst), 0);
    assert_eq!(VALIDATOR.load(Ordering::SeqCst), 0);
    graph
        .parse_and_run_program(None, "(check (= (constant) 7))")
        .unwrap();
    assert!(BODY.load(Ordering::SeqCst) > 0);
    assert_eq!(
        graph
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions,
        catalog
    );
}

#[test]
fn map_constructor_validator_consumes_canonical_values_and_keeps_flat_normal_form() {
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(
            None,
            "(sort M (Map i64 i64)) (sort P (Pair i64 i64)) (sort V (Vec P))",
        )
        .unwrap();
    let m = graph.get_sort_by_name("M").unwrap().clone();
    let v = graph.get_sort_by_name("V").unwrap().clone();
    let ResolvedCall::Primitive(primitive) = ResolvedCall::from_resolution(
        "map-from-pairs",
        &[v, m],
        graph.type_info(),
        Context::Pure,
        &ast::Span::Panic,
    )
    .unwrap() else {
        unreachable!()
    };
    let validate = primitive.validator().unwrap();
    let mut terms = TermDag::default();
    let one = terms.lit(1.into());
    let two = terms.lit(2.into());
    let three = terms.lit(3.into());
    let a = terms.app("pair".into(), vec![one, two]);
    let b = terms.app("pair".into(), vec![one, three]);
    let entries = terms.app("vec-of".into(), vec![a, b]);
    let expected = terms.app("map-of".into(), vec![one, three]);
    assert_eq!(validate(&mut terms, &[entries]), Some(expected));
    let empty = terms.app("map-of".into(), vec![]);
    for name in ["vec-of", "vec-empty"] {
        let entries = terms.app(name.into(), vec![]);
        assert_eq!(validate(&mut terms, &[entries]), Some(empty));
    }
    let short = terms.app("pair".into(), vec![one]);
    let malformed = terms.app("vec-of".into(), vec![short]);
    let wrong = terms.app("vec-empty".into(), vec![a]);
    let raw = terms.app("vec-of".into(), vec![one]);
    for bad in [one, a, malformed, wrong, raw] {
        assert_eq!(validate(&mut terms, &[bad]), None);
    }
    assert_eq!(validate(&mut terms, &[]), None);
    assert_eq!(validate(&mut terms, &[entries, entries]), None);
}

#[test]
fn map_packing_preserves_ordered_failing_child_evaluation() {
    for packed in [false, true] {
        let calls = Arc::new(std::sync::Mutex::new(vec![]));
        let observed = calls.clone();
        let mut graph = EGraph::default();
        egglog::add_primitive!(&mut graph, "observe" = {observed: Arc<std::sync::Mutex<Vec<i64>>>} |x: i64| -?> i64 {{
            self.ctx.lock().unwrap().push(x);
            (x != 3).then_some(x)
        }});
        graph
            .parse_and_run_program(
                None,
                "(sort M (Map i64 i64)) (sort P (Pair i64 i64)) (sort V (Vec P))",
            )
            .unwrap();
        let expr = if packed {
            "(map-from-pairs (vec-of (pair (observe 1) (observe 2)) (pair (observe 3) (observe 4))))"
        } else {
            "(map-of (observe 1) (observe 2) (observe 3) (observe 4))"
        };
        assert!(graph.parse_and_run_program(None, expr).is_err());
        assert_eq!(*calls.lock().unwrap(), [1, 2, 3]);
    }
}

#[test]
fn scalar_families_and_actual_operation_views_are_complete() {
    let catalog = EGraph::default()
        .type_info()
        .portable_builtin_catalog()
        .unwrap();
    for (family, _name) in [("String", "String"), ("bool", "Bool"), ("Unit", "Unit")] {
        let declaration = catalog
            .definitions
            .primitive_sorts
            .iter()
            .find(|d| d.name == family)
            .unwrap();
        assert_eq!(declaration.arity, 0);
        assert!(!catalog.undescribed_sorts.iter().any(|s| s == family));
    }
    for (key, _alias, fixed, _python_name, _rust_name, _trait_name) in [
        ("string.concat", "+", 0, "__add__", "add", Some("Add")),
        ("string.replace", "replace", 3, "replace", "replace", None),
        ("bool.not", "not", 1, "__invert__", "not", Some("Not")),
        ("bool.and", "and", 2, "__and__", "bitand", Some("BitAnd")),
        ("bool.or", "or", 0, "__or__", "bitor", Some("BitOr")),
        ("bool.xor", "xor", 2, "__xor__", "bitxor", Some("BitXor")),
        ("bool.implies", "=>", 2, "implies", "implies", None),
        (
            "i64.to_string",
            "to-string",
            1,
            "to_string",
            "to_string",
            None,
        ),
    ] {
        let d = catalog
            .definitions
            .primitives
            .iter()
            .find(|d| d.name == format!("egglog.core.{key}"))
            .unwrap();
        let p = &d;
        let Some(s) = &p.signature else {
            unreachable!()
        };
        assert!(s.type_param_count == 0);
        assert_eq!(s.inputs.len(), fixed);
        assert_eq!(s.varargs.len(), usize::from(fixed == 0));
    }
    for migrated in ["guard", "count-matches", "bool-<"] {
        assert!(
            !catalog
                .undescribed_primitives
                .iter()
                .any(|name| name == migrated)
        );
    }
}

#[test]
fn scalar_variadic_aliases_share_resolved_provider_contexts_and_validators() {
    let mut graph = EGraph::default();
    for (family, alias, key) in [
        ("String", "+", "egglog.core.string.concat"),
        ("bool", "or", "egglog.core.bool.or"),
        ("i64", "+", "egglog.core.i64.add"),
        ("f64", "+", "egglog.core.f64.add"),
    ] {
        let sort = graph.get_sort_by_name(family).unwrap().clone();
        for count in [0, 1, 2, 5] {
            let sorts = vec![sort.clone(); count + 1];
            for context in [Context::Pure, Context::Read, Context::Write, Context::Full] {
                let alias_result = ResolvedCall::from_resolution(
                    alias,
                    &sorts,
                    graph.type_info(),
                    context,
                    &ast::Span::Panic,
                );
                let key_result = ResolvedCall::from_resolution(
                    key,
                    &sorts,
                    graph.type_info(),
                    context,
                    &ast::Span::Panic,
                );
                if matches!(family, "i64" | "f64") && count != 2 {
                    assert!(alias_result.is_err());
                    assert!(key_result.is_err());
                    continue;
                }
                let ResolvedCall::Primitive(alias_prim) = alias_result.unwrap() else {
                    unreachable!()
                };
                let ResolvedCall::Primitive(key_prim) = key_result.unwrap() else {
                    unreachable!()
                };
                assert_eq!(
                    alias_prim, key_prim,
                    "same context-ID set and concrete sorts"
                );
                assert!(Arc::ptr_eq(
                    alias_prim.validator().unwrap(),
                    key_prim.validator().unwrap()
                ));
                let mut exported = proto::Program {
                    ..Default::default()
                };
                let sort_id = graph.export_sort(&sort, &mut exported.sorts).unwrap();
                for index in 0..count {
                    use proto::primitive_value::Value as V;
                    let value = match family {
                        "String" => V::String(format!("s{index}\0\n☃")),
                        "bool" => V::Bool(index % 2 == 0),
                        "i64" => V::I64(index as i64),
                        "f64" => V::F64Bits((index as f64).to_bits()),
                        _ => unreachable!(),
                    };
                    exported.nodes.push(proto::Node {
                        sort_id,
                        kind: Some(proto::node::Kind::PrimitiveValue(proto::PrimitiveValue {
                            value: Some(value),
                        })),
                        ..Default::default()
                    });
                }
                let args = (0..count as u32).rev().collect::<Vec<_>>();
                let call = alias_prim
                    .export_builtin_call(&graph, &args, None, &mut exported)
                    .unwrap();
                assert_eq!(call.func, key);
                assert_eq!(call.args, args);
                assert_eq!(key_prim.export_builtin(&mut exported).unwrap(), key);
                let native_key = graph
                    .type_info()
                    .resolve_portable_builtin(
                        &exported,
                        key,
                        &vec![sort_id; count],
                        sort_id,
                        &sorts,
                    )
                    .unwrap();
                assert_eq!(native_key, key);
            }
        }
    }
}

#[test]
fn scalar_variadic_validators_preserve_empty_many_utf8_and_truth_tables() {
    let mut graph = EGraph::default();
    for (name, family) in [("+", "String"), ("or", "bool")] {
        let sort = graph.get_sort_by_name(family).unwrap().clone();
        for count in [0, 1, 2, 5] {
            let ResolvedCall::Primitive(p) = ResolvedCall::from_resolution(
                name,
                &vec![sort.clone(); count + 1],
                graph.type_info(),
                Context::Pure,
                &ast::Span::Panic,
            )
            .unwrap() else {
                unreachable!()
            };
            let mut terms = TermDag::default();
            let mut args = vec![];
            for index in 0..count {
                args.push(terms.lit(if family == "String" {
                    ast::Literal::String(format!("{index}\0\n☃"))
                } else {
                    ast::Literal::Bool(index == 1)
                }));
            }
            let expected = terms.lit(if family == "String" {
                ast::Literal::String((0..count).map(|index| format!("{index}\0\n☃")).collect())
            } else {
                ast::Literal::Bool(count > 1)
            });
            assert_eq!(p.validator().unwrap()(&mut terms, &args), Some(expected));
            let invalid = terms.app("not-a-literal".into(), vec![]);
            assert_eq!(p.validator().unwrap()(&mut terms, &[invalid]), None);
        }
    }
    for a in [false, true] {
        graph
            .parse_and_run_program(None, &format!("(check (= (not {a}) {}))", !a))
            .unwrap();
        for b in [false, true] {
            for (op, expected) in [
                ("and", a && b),
                ("or", a || b),
                ("xor", a ^ b),
                ("=>", !a || b),
            ] {
                graph
                    .parse_and_run_program(None, &format!("(check (= ({op} {a} {b}) {expected}))"))
                    .unwrap();
            }
        }
    }
    graph
        .parse_and_run_program(
            None,
            r#"
        (check (= (+) ""))
        (check (= (+ "☃") "☃"))
        (check (= (+ "a" "b" "☃" "c") "ab☃c"))
        (check (= (replace "ababa" "ba" "☃") "a☃☃"))
        (check (= (to-string -42) "-42"))
        (check (= (or) false))
        (check (= (or false) false))
        (check (= (or false true false false) true))
        (check (= () ()))
    "#,
        )
        .unwrap();
}

#[test]
fn scalar_catalog_operations_preserve_native_proofs() {
    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(
            None,
            r#"
        (datatype E (Text String) (Truth bool) (Number i64))
        (Text "") (Text "a") (Text "ab") (Text "abc")
        (Truth false) (Truth true) (Number 3)
        (prove (= (Text (+)) (Text "")))
        (prove (= (Text (+ "a")) (Text "a")))
        (prove (= (Text (+ "a" "b")) (Text "ab")))
        (prove (= (Text (+ "a" "b" "c")) (Text "abc")))
        (prove (= (Truth (or)) (Truth false)))
        (prove (= (Truth (or true)) (Truth true)))
        (prove (= (Truth (or false true)) (Truth true)))
        (prove (= (Truth (or false true false)) (Truth true)))
        (prove (= (Truth (not false)) (Truth true)))
        (prove (= (Number (+ 1 2)) (Number 3)))
    "#,
        )
        .unwrap();
}

#[test]
fn authoritative_family_exports_without_a_described_callable() {
    struct CatalogOnly;
    impl Presort for CatalogOnly {
        fn presort_name() -> &'static str {
            "CatalogOnly"
        }
        fn reserved_primitives() -> Vec<&'static str> {
            vec![]
        }
        fn make_sort(
            _: &TypeInfo,
            _: String,
            _: &[ast::Expr],
            _: ast::Span,
        ) -> Result<ArcSort, TypeError> {
            panic!("catalog export must not instantiate a native factory")
        }
    }
    let mut graph = EGraph::default();
    graph
        .type_info()
        .add_presort::<CatalogOnly>(ast::Span::Panic)
        .unwrap();
    graph
        .type_info()
        .register_builtin_family(builtin::FamilyDescription {
            name: "CatalogOnly".into(),
            arity: 1,
        })
        .unwrap();
    let catalog = graph.type_info().portable_builtin_catalog().unwrap();
    assert!(
        catalog
            .definitions
            .primitive_sorts
            .iter()
            .any(|d| d.name == "CatalogOnly" && d.arity == 1)
    );
    assert!(
        !catalog
            .undescribed_families
            .iter()
            .any(|name| name == "CatalogOnly")
    );
}

#[test]
fn family_registration_rejects_native_kind_and_arity_mismatches_transactionally() {
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(None, "(sort NativeEq) (sort Alias (Vec i64))")
        .unwrap();
    let before = graph.type_info().portable_builtin_catalog().unwrap();
    for (name, arity) in [("bool", 1), ("NativeEq", 0), ("Alias", 0), ("Absent", 0)] {
        assert!(
            graph
                .type_info()
                .register_builtin_family(builtin::FamilyDescription {
                    name: name.into(),
                    arity,
                })
                .is_err(),
            "invalid family {name}/{arity}"
        );
        let after = graph.type_info().portable_builtin_catalog().unwrap();
        assert_eq!(after.definitions, before.definitions);
        assert_eq!(after.undescribed_primitives, before.undescribed_primitives);
        assert_eq!(after.undescribed_sorts, before.undescribed_sorts);
        assert_eq!(after.undescribed_families, before.undescribed_families);
        assert_eq!(
            after.undescribed_family_primitives,
            before.undescribed_family_primitives
        );
    }
}

#[test]
fn family_registration_uses_presort_despite_same_named_nominal_sort() {
    let mut graph = EGraph::default();
    let before = graph
        .type_info()
        .portable_builtin_catalog()
        .unwrap()
        .definitions;
    graph.parse_and_run_program(None, "(sort Pair)").unwrap();
    graph
        .type_info()
        .register_builtin_family(builtin::FamilyDescription {
            name: "Pair".into(),
            arity: 2,
        })
        .unwrap();
    assert_eq!(
        graph
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions,
        before
    );
    let error = graph
        .type_info()
        .register_builtin_family(builtin::FamilyDescription {
            name: "Pair".into(),
            arity: 1,
        })
        .unwrap_err();
    assert!(
        error.contains("conflict") && error.contains("Pair"),
        "{error}"
    );
    assert_eq!(
        graph
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions,
        before
    );
    graph
        .parse_and_run_program(
            None,
            "(constructor P () Pair) (sort Real (Pair Pair i64)) (pair (P) 7)",
        )
        .unwrap();
    let mut sorts = vec![];
    let nominal = graph.get_sort_by_name("Pair").unwrap().clone();
    let scalar = graph.get_sort_by_name("i64").unwrap().clone();
    let actual = graph.get_sort_by_name("Real").unwrap().clone();
    let first = graph.export_sort(&nominal, &mut sorts).unwrap();
    let second = graph.export_sort(&scalar, &mut sorts).unwrap();
    let output = graph.export_sort(&actual, &mut sorts).unwrap();
    let program = proto::Program {
        sorts,
        ..Default::default()
    };
    let native = [nominal, scalar, actual];
    graph
        .type_info()
        .resolve_portable_builtin(
            &program,
            "egglog.core.pair.make",
            &[first, second],
            output,
            &native,
        )
        .unwrap();
    for index in [first, second, output] {
        let mut wrong = program.clone();
        wrong.sorts[index as usize].kind =
            Some(match wrong.sorts[index as usize].kind.as_ref().unwrap() {
                proto::sort::Kind::Eq(name) => {
                    proto::sort::Kind::Application(proto::SortApplication {
                        name: name.clone(),
                        args: vec![],
                    })
                }
                proto::sort::Kind::Application(f) => proto::sort::Kind::Eq(f.name.clone()),
                _ => unreachable!(),
            });
        assert!(
            graph
                .type_info()
                .resolve_portable_builtin(
                    &wrong,
                    "egglog.core.pair.make",
                    &[first, second],
                    output,
                    &native
                )
                .is_err(),
            "other-kind native availability must not satisfy sort {index}"
        );
    }
}

#[test]
fn export_is_inert_and_reports_unmigrated_registrations() {
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    let mut graph = EGraph::default();
    add_literal_prim!(
        &mut graph,
        "counted"[id = "test.counted"] = |a: i64| -> i64 {
            {
                CALLS.fetch_add(1, Ordering::SeqCst);
                a
            }
        }
    );
    add_primitive!(
        &mut graph,
        "unannotated-catalog-operation" = |a: i64| -> i64 { a }
    );
    let catalog = graph.type_info().portable_builtin_catalog().unwrap();
    assert_eq!(CALLS.load(Ordering::SeqCst), 0);
    assert!(
        catalog
            .undescribed_primitives
            .iter()
            .any(|name| name == "unannotated-catalog-operation")
    );
    assert!(
        catalog
            .undescribed_primitives
            .iter()
            .all(|name| name != "ordering-min" && name != "ordering-max")
    );
    assert!(catalog.undescribed_families.is_empty());
    assert!(catalog.undescribed_family_primitives.is_empty());
    assert!(catalog.undescribed_sorts.is_empty());
    let keys = catalog
        .definitions
        .primitives
        .iter()
        .map(|declaration| declaration.name.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        keys,
        [
            "egglog.core.bigint.add",
            "egglog.core.bigint.bitand",
            "egglog.core.bigint.bitor",
            "egglog.core.bigint.bits",
            "egglog.core.bigint.bitxor",
            "egglog.core.bigint.bool_eq",
            "egglog.core.bigint.bool_ge",
            "egglog.core.bigint.bool_gt",
            "egglog.core.bigint.bool_le",
            "egglog.core.bigint.bool_lt",
            "egglog.core.bigint.div",
            "egglog.core.bigint.from_i64",
            "egglog.core.bigint.from_string",
            "egglog.core.bigint.ge",
            "egglog.core.bigint.gt",
            "egglog.core.bigint.le",
            "egglog.core.bigint.lt",
            "egglog.core.bigint.max",
            "egglog.core.bigint.min",
            "egglog.core.bigint.mul",
            "egglog.core.bigint.not",
            "egglog.core.bigint.rem",
            "egglog.core.bigint.shl",
            "egglog.core.bigint.shr",
            "egglog.core.bigint.sub",
            "egglog.core.bigint.to_string",
            "egglog.core.bigrat.abs",
            "egglog.core.bigrat.add",
            "egglog.core.bigrat.cbrt",
            "egglog.core.bigrat.ceil",
            "egglog.core.bigrat.denom",
            "egglog.core.bigrat.div",
            "egglog.core.bigrat.floor",
            "egglog.core.bigrat.ge",
            "egglog.core.bigrat.gt",
            "egglog.core.bigrat.le",
            "egglog.core.bigrat.log",
            "egglog.core.bigrat.lt",
            "egglog.core.bigrat.make",
            "egglog.core.bigrat.max",
            "egglog.core.bigrat.min",
            "egglog.core.bigrat.mul",
            "egglog.core.bigrat.neg",
            "egglog.core.bigrat.numer",
            "egglog.core.bigrat.pow",
            "egglog.core.bigrat.round",
            "egglog.core.bigrat.sqrt",
            "egglog.core.bigrat.sub",
            "egglog.core.bigrat.to_f64",
            "egglog.core.bigrat.to_i64",
            "egglog.core.bool.and",
            "egglog.core.bool.guard",
            "egglog.core.bool.implies",
            "egglog.core.bool.not",
            "egglog.core.bool.or",
            "egglog.core.bool.xor",
            "egglog.core.bool_ne",
            "egglog.core.f64.abs",
            "egglog.core.f64.add",
            "egglog.core.f64.div",
            "egglog.core.f64.exp",
            "egglog.core.f64.from_i64",
            "egglog.core.f64.ge",
            "egglog.core.f64.gt",
            "egglog.core.f64.le",
            "egglog.core.f64.log",
            "egglog.core.f64.lt",
            "egglog.core.f64.max",
            "egglog.core.f64.min",
            "egglog.core.f64.mul",
            "egglog.core.f64.neg",
            "egglog.core.f64.pow",
            "egglog.core.f64.rem",
            "egglog.core.f64.sqrt",
            "egglog.core.f64.sub",
            "egglog.core.f64.to_i64",
            "egglog.core.f64.to_string",
            "egglog.core.i64.abs",
            "egglog.core.i64.add",
            "egglog.core.i64.bitand",
            "egglog.core.i64.bitor",
            "egglog.core.i64.bitxor",
            "egglog.core.i64.bool_eq",
            "egglog.core.i64.bool_ge",
            "egglog.core.i64.bool_gt",
            "egglog.core.i64.bool_le",
            "egglog.core.i64.bool_lt",
            "egglog.core.i64.div",
            "egglog.core.i64.ge",
            "egglog.core.i64.gt",
            "egglog.core.i64.le",
            "egglog.core.i64.log2",
            "egglog.core.i64.lt",
            "egglog.core.i64.max",
            "egglog.core.i64.min",
            "egglog.core.i64.mul",
            "egglog.core.i64.not",
            "egglog.core.i64.rem",
            "egglog.core.i64.shl",
            "egglog.core.i64.shr",
            "egglog.core.i64.sub",
            "egglog.core.i64.to_string",
            "egglog.core.map.contains",
            "egglog.core.map.empty",
            "egglog.core.map.get",
            "egglog.core.map.insert",
            "egglog.core.map.length",
            "egglog.core.map.not_contains",
            "egglog.core.map.of",
            "egglog.core.map.remove",
            "egglog.core.multiset.clear_index",
            "egglog.core.multiset.contains",
            "egglog.core.multiset.contains_swapped",
            "egglog.core.multiset.count",
            "egglog.core.multiset.fill_index",
            "egglog.core.multiset.filter",
            "egglog.core.multiset.filter_not",
            "egglog.core.multiset.flat_map",
            "egglog.core.multiset.insert",
            "egglog.core.multiset.intersection",
            "egglog.core.multiset.length",
            "egglog.core.multiset.map",
            "egglog.core.multiset.not_contains",
            "egglog.core.multiset.not_contains_swapped",
            "egglog.core.multiset.of",
            "egglog.core.multiset.pick",
            "egglog.core.multiset.pick_max",
            "egglog.core.multiset.reduce",
            "egglog.core.multiset.remove",
            "egglog.core.multiset.remove_swapped",
            "egglog.core.multiset.reset_counts",
            "egglog.core.multiset.single",
            "egglog.core.multiset.subtract",
            "egglog.core.multiset.subtract_swapped",
            "egglog.core.multiset.sum",
            "egglog.core.multiset.sum_multisets",
            "egglog.core.multiset.union_values",
            "egglog.core.ne",
            "egglog.core.pair.first",
            "egglog.core.pair.make",
            "egglog.core.pair.second",
            "egglog.core.set.contains",
            "egglog.core.set.diff",
            "egglog.core.set.empty",
            "egglog.core.set.get",
            "egglog.core.set.insert",
            "egglog.core.set.intersect",
            "egglog.core.set.length",
            "egglog.core.set.not_contains",
            "egglog.core.set.of",
            "egglog.core.set.remove",
            "egglog.core.set.union",
            "egglog.core.string.concat",
            "egglog.core.string.count_matches",
            "egglog.core.string.replace",
            "egglog.core.value_eq",
            "egglog.core.vec.append",
            "egglog.core.vec.contains",
            "egglog.core.vec.empty",
            "egglog.core.vec.get",
            "egglog.core.vec.length",
            "egglog.core.vec.map",
            "egglog.core.vec.not_contains",
            "egglog.core.vec.of",
            "egglog.core.vec.pop",
            "egglog.core.vec.push",
            "egglog.core.vec.range",
            "egglog.core.vec.remove",
            "egglog.core.vec.set",
            "egglog.core.vec.union",
            "test.counted"
        ]
    );
    graph
        .parse_and_run_program(None, "(check (= (counted 7) 7))")
        .unwrap();
    assert!(CALLS.load(Ordering::SeqCst) > 0);
}

#[test]
fn pair_definitions_precede_instances_and_preserve_nominal_overloads() {
    let mut graph = EGraph::default();
    let before = graph.type_info().portable_builtin_catalog().unwrap();
    assert!(
        !before
            .undescribed_families
            .iter()
            .any(|name| name == "Pair")
    );
    assert!(
        !before
            .undescribed_family_primitives
            .iter()
            .any(|name| name.starts_with("Pair::"))
    );
    let family = before
        .definitions
        .primitive_sorts
        .iter()
        .find(|family| family.name == "Pair")
        .unwrap();
    assert_eq!(family.arity, 2);
    for (key, _alias, inputs, output) in [
        ("make", "pair", vec![0, 1], 2),
        ("first", "pair-first", vec![2], 0),
        ("second", "pair-second", vec![2], 1),
    ] {
        let mut definition = proto::BuiltinCatalog::default();
        graph
            .type_info()
            .export_builtin_definition(&format!("egglog.core.pair.{key}"), &mut definition)
            .unwrap();
        let d = definition.primitives.first().unwrap();
        let p = &d;
        let Some(s) = &p.signature else {
            panic!("signature")
        };
        assert_eq!(s.type_param_count, 2);
        assert!(s.varargs.is_empty());
        let patterns = [
            definition
                .sorts
                .iter()
                .position(|s| s.kind == Some(proto::sort::Kind::Var(0)))
                .unwrap() as u32,
            definition
                .sorts
                .iter()
                .position(|s| s.kind == Some(proto::sort::Kind::Var(1)))
                .unwrap() as u32,
            definition
                .sorts
                .iter()
                .position(
                    |s| matches!(&s.kind, Some(proto::sort::Kind::Application(f)) if f.name == "Pair"),
                )
                .unwrap() as u32,
        ];
        assert_eq!(
            s.inputs.iter().map(|a| a.sort).collect::<Vec<_>>(),
            inputs.into_iter().map(|i| patterns[i]).collect::<Vec<_>>()
        );
        assert_eq!(s.output, Some(patterns[output]));
        let Some(proto::sort::Kind::Application(f)) = &definition.sorts[patterns[2] as usize].kind
        else {
            unreachable!()
        };
        assert_eq!(f.args, patterns[..2]);
        assert_eq!(
            s.inputs.iter().map(|a| a.name.as_str()).collect::<Vec<_>>(),
            if key == "make" {
                vec!["first", "second"]
            } else {
                vec!["pair"]
            }
        );
    }
    graph
        .parse_and_run_program(
            None,
            r#"
        (sort P (Pair i64 String)) (sort Q (Pair i64 String))
        (sort R (Pair String i64)) (sort V (Vec P)) (sort Nested (Pair P V))
        (function p () P :merge new) (function q () Q :merge new)
        (function r () R :merge new) (function n () Nested :merge new)
        (set (p) (pair 1 "a")) (set (q) (pair 2 "b"))
        (set (r) (pair "c" 3)) (set (n) (pair (p) (vec-of (p))))
        (check (= (pair-first (p)) 1) (= (pair-second (q)) "b"))
        (check (= (pair-first (r)) "c") (= (pair-second (r)) 3))
        (check (= (pair-first (n)) (p)) (= (vec-get (pair-second (n)) 0) (p)))
    "#,
        )
        .unwrap();
    assert_eq!(
        graph
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions,
        before.definitions
    );
    for bad in [
        "(set (p) (q))",
        "(set (p) (pair \"a\" 1))",
        "(set (p) (pair 1))",
        "(pair-first 1)",
    ] {
        assert!(
            graph.clone().parse_and_run_program(None, bad).is_err(),
            "{bad}"
        );
    }
    let mut sorts = vec![];
    let p = graph.get_sort_by_name("P").unwrap();
    let q = graph.get_sort_by_name("Q").unwrap();
    assert_eq!(
        graph.export_sort(p, &mut sorts).unwrap(),
        graph.export_sort(q, &mut sorts).unwrap()
    );
    let nested = graph
        .export_sort(graph.get_sort_by_name("Nested").unwrap(), &mut sorts)
        .unwrap();
    assert!(
        matches!(&sorts[nested as usize].kind, Some(proto::sort::Kind::Application(f)) if f.name == "Pair" && f.args.len() == 2)
    );
    let i = graph.get_sort_by_name("i64").unwrap();
    let s = graph.get_sort_by_name("String").unwrap();
    for (alias, key, types) in [
        (
            "pair",
            "egglog.core.pair.make",
            vec![i.clone(), s.clone(), p.clone()],
        ),
        (
            "pair-first",
            "egglog.core.pair.first",
            vec![p.clone(), i.clone()],
        ),
        (
            "pair-second",
            "egglog.core.pair.second",
            vec![p.clone(), s.clone()],
        ),
    ] {
        for context in [Context::Pure, Context::Read, Context::Write, Context::Full] {
            assert_eq!(
                ResolvedCall::from_resolution(
                    alias,
                    &types,
                    graph.type_info(),
                    context,
                    &ast::Span::Panic
                )
                .unwrap(),
                ResolvedCall::from_resolution(
                    key,
                    &types,
                    graph.type_info(),
                    context,
                    &ast::Span::Panic
                )
                .unwrap()
            );
        }
    }
}

#[test]
fn pair_instances_reject_wrong_ownership_annotations_and_converters() {
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(None, "(sort P (Pair i64 String)) (sort V (Vec i64))")
        .unwrap();
    let p = graph.get_sort_by_name("P").unwrap().clone();
    let v = graph.get_sort_by_name("V").unwrap().clone();
    let i = graph.get_sort_by_name("i64").unwrap().clone();
    let s = graph.get_sort_by_name("String").unwrap().clone();
    let before = graph
        .type_info()
        .portable_builtin_catalog()
        .unwrap()
        .definitions;
    assert!(
        graph
            .type_info()
            .instantiate_builtin("egglog.core.pair.make", &v)
            .is_err()
    );
    assert!(
        graph
            .type_info()
            .instantiate_builtin("egglog.core.vec.of", &p)
            .is_err()
    );
    for (key, types) in [
        (
            "egglog.core.pair.make",
            vec![s.clone(), i.clone(), p.clone()],
        ),
        (
            "egglog.core.pair.make",
            vec![i.clone(), s.clone(), v.clone()],
        ),
        ("egglog.core.pair.first", vec![p.clone(), s.clone()]),
        ("egglog.core.pair.second", vec![p.clone(), i.clone()]),
    ] {
        assert!(
            ResolvedCall::from_resolution(
                key,
                &types,
                graph.type_info(),
                Context::Pure,
                &ast::Span::Panic
            )
            .is_err()
        );
    }
    for wrong in 0..4 {
        let instance = graph
            .type_info()
            .instantiate_builtin("egglog.core.pair.first", &p)
            .unwrap();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| match wrong {
            0 => {
                add_primitive_with_validator!(&mut graph, "bad-pair" [instance = instance] = |xs: @VecContainer| -> # {
                    { CALLS.fetch_add(1, Ordering::SeqCst); xs.data[0] }
                }, |_: &mut TermDag, _: &[TermId]| { CALLS.fetch_add(1, Ordering::SeqCst); None });
            }
            1 => {
                add_primitive!(&mut graph, "bad-pair" [instance = instance] = |xs: @PairContainer| -> String { { let _ = xs; String::new() } });
            }
            2 => {
                add_primitive!(&mut graph, "bad-pair" [instance = instance] = |xs: @PairContainer, extra: #| -> # { { let _ = extra; xs.first } });
            }
            _ => {
                add_primitive!(&mut graph, "bad-pair" [instance = instance] = [mut xs: @PairContainer] -> # { xs.next().unwrap().first });
            }
        }));
        assert!(result.is_err(), "bad converter {wrong}");
        assert!(!graph.type_info().is_primitive("bad-pair"));
        assert_eq!(
            graph
                .type_info()
                .portable_builtin_catalog()
                .unwrap()
                .definitions,
            before
        );
        assert_eq!(CALLS.load(Ordering::SeqCst), 0);
    }
}

#[test]
fn vec_definitions_precede_instances_and_preserve_nominal_overloads() {
    let mut graph = EGraph::default();
    let before = graph.type_info().portable_builtin_catalog().unwrap();
    assert!(!before.undescribed_families.iter().any(|name| name == "Vec"));
    assert!(
        !before
            .undescribed_family_primitives
            .iter()
            .any(|name| name == "Vec::unstable-vec-map")
    );
    assert!(
        !before
            .undescribed_family_primitives
            .iter()
            .any(|name| matches!(name.as_str(), "Vec::vec-of" | "Vec::vec-range"))
    );
    for key in [
        "egglog.core.vec.empty",
        "egglog.core.vec.of",
        "egglog.core.vec.get",
        "egglog.core.vec.range",
        "egglog.core.vec.map",
    ] {
        assert!(
            before
                .definitions
                .primitives
                .iter()
                .any(|declaration| declaration.name == key)
        );
    }
    graph
        .parse_and_run_program(
            None,
            r#"
        (sort V (Vec i64)) (sort W (Vec i64)) (sort Nested (Vec V)) (sort F (Vec f64))
        (function v () V :merge new) (function w () W :merge new)
        (function nested () Nested :merge new)
        (set (v) (vec-empty)) (set (w) (vec-of 3 4))
        (set (nested) (vec-of (v)))
        (check (= (vec-get (w) 1) 4) (= (vec-get (nested) 0) (v)))
        (set (v) (vec-range 1)) (set (w) (vec-range 5))
        (check (= (vec-get (v) 0) 0) (= (vec-get (w) 4) 4))
    "#,
        )
        .unwrap();
    assert_eq!(
        graph
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions,
        before.definitions
    );
    assert!(graph.parse_and_run_program(None, "(set (v) (w))").is_err());
    assert!(
        graph
            .parse_and_run_program(None, "(set (v) (vec-of 1.0))")
            .is_err()
    );
    let v = graph.get_sort_by_name("V").unwrap().clone();
    let i = graph.get_sort_by_name("i64").unwrap().clone();
    let w = graph.get_sort_by_name("W").unwrap().clone();
    let f = graph.get_sort_by_name("F").unwrap().clone();
    let float = graph.get_sort_by_name("f64").unwrap().clone();
    assert!(
        graph
            .type_info()
            .instantiate_builtin("egglog.core.vec.range", &f)
            .is_err()
    );
    assert!(
        graph
            .type_info()
            .instantiate_builtin("egglog.core.vec.range", &i)
            .is_err()
    );
    for (alias, key, types) in [
        ("vec-empty", "egglog.core.vec.empty", vec![v.clone()]),
        ("vec-of", "egglog.core.vec.of", vec![i.clone(), v.clone()]),
        (
            "vec-range",
            "egglog.core.vec.range",
            vec![i.clone(), v.clone()],
        ),
        (
            "vec-range",
            "egglog.core.vec.range",
            vec![i.clone(), w.clone()],
        ),
        (
            "vec-get",
            "egglog.core.vec.get",
            vec![v.clone(), i.clone(), i.clone()],
        ),
    ] {
        for context in [Context::Pure, Context::Read, Context::Write, Context::Full] {
            let canonical = ResolvedCall::from_resolution(
                key,
                &types,
                graph.type_info(),
                context,
                &ast::Span::Panic,
            )
            .unwrap();
            if key == "egglog.core.vec.range" {
                let ResolvedCall::Primitive(primitive) = &canonical else {
                    unreachable!()
                };
                assert!(primitive.validator().is_none());
            }
            assert_eq!(
                ResolvedCall::from_resolution(
                    alias,
                    &types,
                    graph.type_info(),
                    context,
                    &ast::Span::Panic
                )
                .unwrap(),
                canonical,
            );
        }
    }
    for types in [
        vec![v.clone()],
        vec![i.clone(), i.clone(), v.clone()],
        vec![f.clone(), v.clone()],
        vec![float, v.clone()],
        vec![i.clone(), f.clone()],
    ] {
        for alias in ["vec-range", "egglog.core.vec.range"] {
            assert!(
                ResolvedCall::from_resolution(
                    alias,
                    &types,
                    graph.type_info(),
                    Context::Full,
                    &ast::Span::Panic
                )
                .is_err()
            );
        }
    }
}

#[test]
fn ordinary_vec_map_definitions_are_complete() {
    let catalog = EGraph::default()
        .type_info()
        .portable_builtin_catalog()
        .unwrap();
    for key in [
        "egglog.core.vec.append",
        "egglog.core.vec.union",
        "egglog.core.vec.push",
        "egglog.core.vec.pop",
        "egglog.core.vec.length",
        "egglog.core.vec.contains",
        "egglog.core.vec.not_contains",
        "egglog.core.vec.set",
        "egglog.core.vec.remove",
        "egglog.core.map.remove",
        "egglog.core.map.length",
        "egglog.core.map.contains",
        "egglog.core.map.not_contains",
    ] {
        assert!(
            catalog
                .definitions
                .primitives
                .iter()
                .any(|declaration| declaration.name == key),
            "missing definition {key}"
        );
    }
}

#[test]
fn ordinary_vec_map_signatures_aliases_and_contexts_are_exact() {
    let mut graph = EGraph::default();
    let before = graph
        .type_info()
        .portable_builtin_catalog()
        .unwrap()
        .definitions;
    graph
        .parse_and_run_program(None, "(sort VI (Vec i64)) (sort MI (Map String i64))")
        .unwrap();
    assert_eq!(
        graph
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions,
        before
    );
    for (family, key, fixed, output, native) in [
        ("vec", "push", vec![1, 0], 1, vec!["VI", "i64", "VI"]),
        ("vec", "pop", vec![1], 1, vec!["VI", "VI"]),
        ("vec", "length", vec![1], 2, vec!["VI", "i64"]),
        ("vec", "contains", vec![1, 0], 3, vec!["VI", "i64", "Unit"]),
        (
            "vec",
            "not_contains",
            vec![1, 0],
            3,
            vec!["VI", "i64", "Unit"],
        ),
        (
            "vec",
            "set",
            vec![1, 2, 0],
            1,
            vec!["VI", "i64", "i64", "VI"],
        ),
        ("vec", "remove", vec![1, 2], 1, vec!["VI", "i64", "VI"]),
        ("map", "remove", vec![2, 0], 2, vec!["MI", "String", "MI"]),
        ("map", "length", vec![2], 5, vec!["MI", "i64"]),
        (
            "map",
            "contains",
            vec![2, 0],
            6,
            vec!["MI", "String", "Unit"],
        ),
        (
            "map",
            "not_contains",
            vec![2, 0],
            6,
            vec!["MI", "String", "Unit"],
        ),
    ] {
        let canonical = format!("egglog.core.{family}.{key}");
        let alias = format!("{family}-{}", key.replace('_', "-"));
        let definitions = if family == "vec" {
            VecSort::builtin_definitions()
                .iter()
                .map(|description| builtin::project_description(description).unwrap())
                .collect::<Vec<_>>()
        } else {
            egglog::sort::MapSort::builtin_definitions()
                .iter()
                .filter(|description| description.key != "egglog.core.map.flat")
                .map(|description| builtin::project_description(description).unwrap())
                .collect::<Vec<_>>()
        };
        let (definition, declaration) = definitions
            .iter()
            .find_map(|p| {
                p.primitives
                    .iter()
                    .find(|d| d.name == canonical)
                    .map(|d| (p, d))
            })
            .unwrap();
        let primitive = declaration;
        let Some(signature) = &primitive.signature else {
            unreachable!()
        };
        assert_eq!(
            signature.type_param_count,
            if family == "vec" { 1 } else { 2 }
        );
        use egglog::builtin::{BuiltinTyping, SortPattern};
        let key_sort = SortPattern::Param(0);
        let value_sort = SortPattern::Param(1);
        let patterns = if family == "vec" {
            vec![
                key_sort.clone(),
                SortPattern::Family {
                    name: "Vec".into(),
                    args: vec![key_sort],
                },
                SortPattern::Family {
                    name: "i64".into(),
                    args: vec![],
                },
                SortPattern::Family {
                    name: "Unit".into(),
                    args: vec![],
                },
            ]
        } else {
            let pair = SortPattern::Family {
                name: "Pair".into(),
                args: vec![key_sort.clone(), value_sort.clone()],
            };
            vec![
                key_sort.clone(),
                value_sort.clone(),
                SortPattern::Family {
                    name: "Map".into(),
                    args: vec![key_sort, value_sort],
                },
                pair.clone(),
                SortPattern::Family {
                    name: "Vec".into(),
                    args: vec![pair],
                },
                SortPattern::Family {
                    name: "i64".into(),
                    args: vec![],
                },
                SortPattern::Family {
                    name: "Unit".into(),
                    args: vec![],
                },
            ]
        };
        let described = builtin::native_definition(definition).unwrap();
        let BuiltinTyping::Signature(described) = described.typing else {
            unreachable!()
        };
        assert_eq!(
            described
                .fixed
                .iter()
                .map(|argument| &argument.sort)
                .collect::<Vec<_>>(),
            fixed
                .iter()
                .map(|index| &patterns[*index])
                .collect::<Vec<_>>(),
            "{canonical}"
        );
        assert_eq!(described.output, patterns[output], "{canonical}");
        assert!(signature.varargs.is_empty());
        builtin::import_definition(definition, &mut proto::BuiltinCatalog::default()).unwrap();
        let native = native
            .iter()
            .map(|name| graph.get_sort_by_name(name).unwrap().clone())
            .collect::<Vec<_>>();
        for context in [Context::Pure, Context::Read, Context::Write, Context::Full] {
            assert_eq!(
                ResolvedCall::from_resolution(
                    &canonical,
                    &native,
                    graph.type_info(),
                    context,
                    &ast::Span::Panic
                )
                .unwrap(),
                ResolvedCall::from_resolution(
                    &alias,
                    &native,
                    graph.type_info(),
                    context,
                    &ast::Span::Panic
                )
                .unwrap()
            );
        }
    }
}

#[test]
fn vec_tail_receiver_and_equality_restriction_are_exact() {
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(
            None,
            "(sort A) (sort VI (Vec i64)) (sort VA (Vec A)) (sort VVA (Vec VA))",
        )
        .unwrap();
    for (name, equality) in [("VI", false), ("VA", true), ("VVA", false)] {
        let vector = graph.get_sort_by_name(name).unwrap().clone();
        assert_eq!(
            graph
                .type_info()
                .instantiate_builtin("egglog.core.vec.union", &vector)
                .is_ok(),
            equality
        );
        for arity in [0, 1, 3] {
            let sorts = vec![vector.clone(); arity + 1];
            for context in [Context::Pure, Context::Read, Context::Write, Context::Full] {
                assert_eq!(
                    ResolvedCall::from_resolution(
                        "vec-append",
                        &sorts,
                        graph.type_info(),
                        context,
                        &ast::Span::Panic
                    )
                    .unwrap(),
                    ResolvedCall::from_resolution(
                        "egglog.core.vec.append",
                        &sorts,
                        graph.type_info(),
                        context,
                        &ast::Span::Panic
                    )
                    .unwrap(),
                );
                for key in ["vec-union", "egglog.core.vec.union"] {
                    assert_eq!(
                        ResolvedCall::from_resolution(
                            key,
                            &vec![vector.clone(); 3],
                            graph.type_info(),
                            context,
                            &ast::Span::Panic
                        )
                        .is_ok(),
                        equality && matches!(context, Context::Write | Context::Full)
                    );
                }
            }
        }
    }
    for definition in VecSort::builtin_definitions()
        .iter()
        .map(|description| builtin::project_description(description).unwrap())
        .collect::<Vec<_>>()
    {
        let index = definition
            .primitives
            .iter()
            .position(|d| d.name == "egglog.core.vec.append" || d.name == "egglog.core.vec.union");
        let Some(index) = index else { continue };
        let primitive = &definition.primitives[index];
        let Some(signature) = &primitive.signature else {
            unreachable!()
        };
        let union = primitive.name.ends_with("union");
        assert_eq!(signature.type_param_count, 1);
        assert_eq!(signature.output, Some(1));
        assert_eq!(
            signature.inputs.iter().map(|a| a.sort).collect::<Vec<_>>(),
            if union { vec![1, 1] } else { vec![] }
        );
        assert_eq!(
            signature.varargs.iter().map(|a| a.sort).collect::<Vec<_>>(),
            if union { vec![] } else { vec![1] }
        );
        let mut installed = proto::BuiltinCatalog::default();
        builtin::import_definition(&definition, &mut installed).unwrap();
        let mut invalid = definition.clone();
        let signature = invalid.primitives[index].signature.as_mut().unwrap();
        signature.type_param_count += 1;
        assert!(builtin::import_definition(&invalid, &mut installed).is_err());
    }
}

#[test]
fn vec_instance_macro_rejects_conversion_and_arity_mismatches_before_registration() {
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(None, "(sort V (Vec i64))")
        .unwrap();
    let before = graph
        .type_info()
        .portable_builtin_catalog()
        .unwrap()
        .definitions;
    for wrong in 0..6 {
        let native = graph.get_sort_by_name("V").unwrap().clone();
        let instance = graph
            .type_info()
            .instantiate_builtin(
                if wrong < 3 {
                    "egglog.core.vec.get"
                } else {
                    "egglog.core.vec.range"
                },
                &native,
            )
            .unwrap();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            if wrong == 0 {
                add_primitive_with_validator!(&mut graph, "bad" [instance = instance] = |xs: @VecContainer, index: String| -?> # {
                    { CALLS.fetch_add(1, Ordering::SeqCst); xs.data.get(index.len()).copied() }
                }, |_: &mut TermDag, _: &[TermId]| { CALLS.fetch_add(1, Ordering::SeqCst); None });
            } else if wrong == 1 {
                add_primitive!(&mut graph, "bad" [instance = instance] = |xs: @VecContainer, index: i64| -> bool { { let _ = (xs, index); false } });
            } else if wrong == 2 {
                add_primitive!(&mut graph, "bad" [instance = instance] = [mut xs: #] -> # { xs.next().unwrap() });
            } else if wrong == 3 {
                add_primitive_with_validator!(&mut graph, "bad" [instance = instance] = |end: String| -> @VecContainer {
                    { CALLS.fetch_add(1, Ordering::SeqCst); let _ = end; VecContainer { do_rebuild: false, data: vec![] } }
                }, |_: &mut TermDag, _: &[TermId]| { CALLS.fetch_add(1, Ordering::SeqCst); None });
            } else if wrong == 4 {
                add_primitive!(
                    &mut graph,
                    "bad"[instance = instance] = |end: i64| -> i64 { end }
                );
            } else {
                add_primitive!(&mut graph, "bad" [instance = instance] = [end: i64] -> @VecContainer { { let _ = end; VecContainer { do_rebuild: false, data: vec![] } } });
            }
        }));
        assert!(result.is_err());
        assert_eq!(
            graph
                .type_info()
                .portable_builtin_catalog()
                .unwrap()
                .definitions,
            before
        );
        assert_eq!(CALLS.load(Ordering::SeqCst), 0);
    }
}

#[test]
fn generic_signature_import_remaps_children_and_ignores_binder_labels() {
    let mut definitions = VecSort::builtin_definitions()
        .iter()
        .map(|description| builtin::project_description(description).unwrap())
        .collect::<Vec<_>>();
    let mut definition = definitions.remove(1);
    let mut destination = proto::BuiltinCatalog {
        sorts: vec![proto::Sort {
            kind: Some(proto::sort::Kind::Eq("Prior".into())),
            ..Default::default()
        }],
        ..Default::default()
    };
    builtin::import_definition(&definition, &mut destination).unwrap();
    let before = destination.clone();
    let primitive = &mut definition.primitives.last_mut().unwrap();
    let Some(signature) = &mut primitive.signature else {
        unreachable!()
    };
    signature.varargs[0].name = "renamed".into();
    builtin::import_definition(&definition, &mut destination).unwrap();
    assert_eq!(destination, before);
    definition.sorts[0].kind = Some(proto::sort::Kind::Var(1));
    assert!(builtin::import_definition(&definition, &mut destination).is_err());
}

#[test]
fn program_primitive_reconciliation_checks_body_scope_and_identity() {
    let source = proto::Program {
        sorts: vec![proto::Sort {
            kind: Some(proto::sort::Kind::Application(proto::SortApplication {
                name: "i64".into(),
                args: vec![],
            })),
            ..Default::default()
        }],
        nodes: vec![proto::Node {
            sort_id: 0,
            kind: Some(proto::node::Kind::Var("_0".into())),
            ..Default::default()
        }],
        declarations: vec![proto::Declaration {
            kind: Some(proto::declaration::Kind::UserDefinedPrimitive(
                proto::UserDefinedPrimitive {
                    name: "identity".into(),
                    inputs: vec![proto::Arg {
                        name: "value".into(),
                        sort: 0,
                    }],
                    output: 0,
                    body: Some(0),
                },
            )),
            ..Default::default()
        }],
        ..Default::default()
    };
    let mut destination = proto::Program {
        sorts: vec![proto::Sort {
            kind: Some(proto::sort::Kind::Eq("Prior".into())),
            ..Default::default()
        }],
        ..Default::default()
    };
    assert_eq!(
        builtin::definitions::reconcile_declarations(&source, &mut destination).unwrap(),
        [true]
    );
    let before = destination.clone();
    for mutation in [
        "label",
        "missing",
        "bounds",
        "free",
        "out-of-scope",
        "noncanonical",
        "sort",
        "changed-body",
        "shared-scope",
        "cycle",
        "lambda",
    ] {
        let mut candidate = source.clone();
        let Some(proto::declaration::Kind::UserDefinedPrimitive(primitive)) =
            &mut candidate.declarations[0].kind
        else {
            unreachable!()
        };
        match mutation {
            "label" => primitive.inputs[0].name = "renamed".into(),
            "missing" => primitive.body = None,
            "bounds" => primitive.body = Some(9),
            "free" => candidate.nodes[0].kind = Some(proto::node::Kind::Var("outer".into())),
            "out-of-scope" => candidate.nodes[0].kind = Some(proto::node::Kind::Var("_1".into())),
            "noncanonical" => candidate.nodes[0].kind = Some(proto::node::Kind::Var("_00".into())),
            "sort" => {
                candidate.sorts.push(proto::Sort {
                    kind: Some(proto::sort::Kind::Application(proto::SortApplication {
                        name: "bool".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                });
                candidate.nodes[0].sort_id = 1;
            }
            "changed-body" => {
                candidate.nodes[0].kind =
                    Some(proto::node::Kind::PrimitiveValue(proto::PrimitiveValue {
                        value: Some(proto::primitive_value::Value::I64(1)),
                    }))
            }
            "shared-scope" => candidate.declarations.push(proto::Declaration {
                kind: Some(proto::declaration::Kind::UserDefinedPrimitive(
                    proto::UserDefinedPrimitive {
                        name: "nullary".into(),
                        inputs: vec![],
                        output: 0,
                        body: Some(0),
                    },
                )),
                ..Default::default()
            }),
            "cycle" => {
                candidate.nodes[0].kind = Some(proto::node::Kind::Call(proto::Call {
                    func: "identity".into(),
                    args: vec![0],
                }))
            }
            "lambda" => {
                candidate.nodes[0].kind =
                    Some(proto::node::Kind::PrimitiveValue(proto::PrimitiveValue {
                        value: Some(proto::primitive_value::Value::Lambda(proto::Lambda {
                            captures: vec![],
                            body: 0,
                        })),
                    }))
            }
            _ => unreachable!(),
        }
        let result = builtin::definitions::reconcile_declarations(&candidate, &mut destination);
        assert_eq!(
            result.is_ok(),
            mutation == "label",
            "{mutation}: {result:?}"
        );
        assert_eq!(destination, before, "{mutation}");
        let mut fresh = proto::Program::default();
        let fresh_result = builtin::definitions::reconcile_declarations(&candidate, &mut fresh);
        assert_eq!(
            fresh_result.is_ok(),
            matches!(mutation, "label" | "changed-body"),
            "fresh {mutation}: {fresh_result:?}"
        );
    }
    let mut distinct = source;
    let Some(proto::declaration::Kind::UserDefinedPrimitive(primitive)) =
        &mut distinct.declarations[0].kind
    else {
        unreachable!()
    };
    primitive.name = "another_identity".into();
    assert_eq!(
        builtin::definitions::reconcile_declarations(&distinct, &mut destination).unwrap(),
        [true]
    );
    assert_eq!(destination.declarations.len(), 2);
}

#[test]
fn migrated_vec_operations_preserve_native_proofs() {
    EGraph::new_with_proofs()
        .parse_and_run_program(
            None,
            r#"
        (sort V (Vec i64))
        (datatype E (Wrap V) (Num i64))
        (Wrap (vec-empty)) (Wrap (vec-of 1 2)) (Num (vec-get (vec-of 1 2) 1))
        (prove (= (Num 2) (Num (vec-get (vec-of 1 2) 1))))
        (prove (= (Wrap (vec-of)) (Wrap (vec-empty))))
    "#,
        )
        .unwrap();
}

#[test]
fn builtin_dispatch_rejects_native_bindings_that_disagree_with_wire_sorts() {
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(None, "(sort V (Vec i64)) (sort W (Vec f64))")
        .unwrap();
    let v = graph.get_sort_by_name("V").unwrap().clone();
    let w = graph.get_sort_by_name("W").unwrap().clone();
    let mut program = proto::Program {
        ..Default::default()
    };
    let output = graph.export_sort(&v, &mut program.sorts).unwrap();
    assert!(
        graph
            .type_info()
            .resolve_portable_builtin(&program, "egglog.core.vec.empty", &[], output, &[w])
            .is_err()
    );
}

#[test]
fn empty_definition_keys_are_rejected_by_import_and_registration() {
    #[derive(Clone)]
    struct Invalid(egglog::builtin::BuiltinDescription);
    impl Primitive for Invalid {
        fn name(&self) -> &str {
            "invalid-definition"
        }
        fn get_type_constraints(&self, span: &ast::Span) -> Box<dyn constraint::TypeConstraint> {
            egglog::builtin::rooted_type_constraints("", &self.0, span)
        }
        fn builtin_description(&self) -> Option<&egglog::builtin::BuiltinDescription> {
            Some(&self.0)
        }
    }
    impl PurePrim for Invalid {
        fn apply<'a, 'db>(&self, _: PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
            args.first().copied()
        }
    }
    let mut graph = EGraph::default();
    let sort = graph.get_sort_by_name("i64").unwrap().clone();
    let mut definition = builtin::closed_signature(
        "test.valid",
        "invalid-definition",
        &[("value", sort.clone())],
        &[],
        sort,
    )
    .unwrap();
    let mut native = builtin::native_definition(&definition).unwrap();
    let primitive = &mut definition.primitives.last_mut().unwrap();
    primitive.name.clear();
    native.key.clear();
    let imported = builtin::import_definition(&definition, &mut proto::BuiltinCatalog::default());
    let primitive = Invalid(native);
    let destination = proto::Program::default();
    assert!(builtin::project_description(primitive.builtin_description().unwrap()).is_err());
    assert_eq!(destination, proto::Program::default());
    graph.add_pure_primitive(primitive, None);
    assert!(imported.is_err(), "empty key must not import");
    assert!(
        graph.type_info().portable_builtin_catalog().is_err(),
        "empty key must not register"
    );
}

#[test]
fn canonical_signature_drives_native_checking_and_export() {
    #[derive(Clone)]
    struct Identity(Arc<egglog::builtin::BuiltinDescription>);
    impl Primitive for Identity {
        fn name(&self) -> &str {
            "identity"
        }
        fn get_type_constraints(&self, span: &ast::Span) -> Box<dyn constraint::TypeConstraint> {
            egglog::builtin::rooted_type_constraints("test.identity", &self.0, span)
        }
        fn builtin_description(&self) -> Option<&egglog::builtin::BuiltinDescription> {
            Some(&self.0)
        }
    }
    impl PurePrim for Identity {
        fn apply<'a, 'db>(&self, _: PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
            args.first().copied()
        }
    }
    for (sort_name, good, bad) in [("i64", "1", "1.0"), ("f64", "1.0", "1")] {
        let mut graph = EGraph::default();
        let sort = graph.get_sort_by_name(sort_name).unwrap();
        let definition = egglog::builtin::closed_signature(
            "test.identity",
            "identity",
            &[("value", sort.clone())],
            &[],
            sort.clone(),
        )
        .unwrap();
        graph.add_pure_primitive(Identity(Arc::new(definition.clone())), None);
        graph
            .parse_and_run_program(None, &format!("(check (= (identity {good}) {good}))"))
            .unwrap();
        assert!(
            graph
                .parse_and_run_program(None, &format!("(identity {bad})"))
                .is_err()
        );
        let mut exported = proto::BuiltinCatalog {
            ..Default::default()
        };
        let catalog = graph.type_info().portable_builtin_catalog().unwrap();
        let definition = builtin::project_description(&definition).unwrap();
        builtin::import_definition(&definition, &mut exported).unwrap();
        assert!(
            catalog
                .definitions
                .primitives
                .iter()
                .any(|declaration| declaration.name == "test.identity")
        );
        assert_eq!(exported, definition);
    }
}

#[test]
fn duplicate_catalog_identity_does_not_replace_native_aliases() {
    let mut graph = EGraph::default();
    add_literal_prim!(
        &mut graph,
        "one"[id = "test.duplicate"] = |a: i64| -> i64 { a }
    );
    add_literal_prim!(
        &mut graph,
        "two"[id = "test.duplicate"] = |a: i64| -> i64 { a + 1 }
    );
    assert!(graph.type_info().portable_builtin_catalog().is_err());
    graph
        .parse_and_run_program(None, "(check (= (one 1) 1) (= (two 1) 2))")
        .unwrap();
}

#[test]
fn migrated_addition_keeps_native_proof_and_context_behavior() {
    let mut proofs = EGraph::new_with_proofs();
    proofs
        .parse_and_run_program(
            None,
            "(datatype E (Num i64)) (Num (+ 1 2)) (prove (= (Num 3) (Num (+ 1 2))))",
        )
        .unwrap();
    let mut graph = EGraph::default();
    for name in ["egglog.core.i64.add", "egglog.core.f64.add"] {
        let sort = graph
            .get_sort_by_name(if name.contains("i64") { "i64" } else { "f64" })
            .unwrap()
            .clone();
        let types = [sort.clone(), sort.clone(), sort];
        let alias = ResolvedCall::from_resolution(
            "+",
            &types,
            graph.type_info(),
            Context::Pure,
            &ast::Span::Panic,
        )
        .unwrap();
        let keyed = ResolvedCall::from_resolution(
            name,
            &types,
            graph.type_info(),
            Context::Pure,
            &ast::Span::Panic,
        )
        .unwrap();
        assert_eq!(
            alias, keyed,
            "wire key must retain the same native registration identity"
        );
        let primitives = graph.type_info().get_prims(name).unwrap();
        assert_eq!(primitives.len(), 1);
        for context in [Context::Pure, Context::Read, Context::Write, Context::Full] {
            assert!(primitives[0].is_valid_in_context(context));
        }
    }
}

#[test]
fn native_builtin_arity_errors_keep_source_aliases() {
    let error = EGraph::default()
        .parse_and_run_program(None, "(+ 1)")
        .unwrap_err()
        .to_string();
    assert!(error.contains('+'));
    assert!(
        !error.contains("egglog.core."),
        "native source diagnostic changed: {error}"
    );
}

#[test]
fn imported_signatures_keep_namespaces_and_diagnostic_labels_separate() {
    let graph = EGraph::default();
    let sort = graph.get_sort_by_name("i64").unwrap().clone();
    let definition =
        builtin::closed_signature("i64", "identity", &[("value", sort.clone())], &[], sort)
            .unwrap();
    let mut destination = proto::BuiltinCatalog::default();
    builtin::import_definition(&definition, &mut destination).unwrap();
    assert_eq!(destination.primitive_sorts.len(), 1);
    assert_eq!(destination.primitives.len(), 1);
    assert_eq!(
        destination.primitive_sorts[0].name,
        destination.primitives[0].name
    );
    let before = destination.clone();
    let mut relabeled = definition.clone();
    let Some(signature) = &mut relabeled.primitives[0].signature else {
        unreachable!()
    };
    signature.inputs[0].name = "diagnostic label".into();
    builtin::import_definition(&relabeled, &mut destination).unwrap();
    assert_eq!(destination, before);
    let Some(signature) = &mut relabeled.primitives[0].signature else {
        unreachable!()
    };
    signature.inputs.clear();
    assert!(builtin::import_definition(&relabeled, &mut destination).is_err());
    assert_eq!(destination, before);
}
