#![cfg(feature = "typed")]
use egglog_experimental::typed::{builtins as eg, prelude::*};

#[sort]
pub struct Math;
#[declarations]
impl Math {
    pub fn Num(value: eg::I64) -> Self;
    pub fn Add(left: Math, right: Math) -> Self;
    pub fn Unused(value: eg::String) -> Self;
}
#[function(no_merge)]
pub fn Read(key: eg::I64) -> eg::I64;
#[relation]
pub fn Pending(key: eg::I64);
#[relation]
pub fn Copied(key: eg::I64);
#[relation]
pub fn Pair(left: eg::I64, right: eg::I64);
#[function(no_merge)]
pub fn ResultTable() -> Math;
#[function(no_merge)]
pub fn KeyedResult(key: eg::I64) -> Math;
#[sort]
pub struct Chain;
#[constructor]
pub fn End() -> Chain;
#[constructor]
pub fn Next(child: Chain) -> Chain;

#[test]
fn birewrite_keeps_directional_bindings_and_occurrences() -> Result<(), TypedError> {
    let number = var::<eg::I64>("number");
    let extra = var::<eg::I64>("extra");
    let directions = birewrite(
        Math::Num(&number),
        Math::Add(Math::Num(&number), Math::Num(&extra)),
    );
    let mut graph = EGraph::default();
    assert!(matches!(
        graph.run(ruleset(&directions)),
        Err(TypedError::Invalid(_))
    ));
    assert_eq!(graph.num_tuples()?, 0);

    // A condition binds the extra RHS variable in the forward direction.
    // The reverse direction already binds it through its own root pattern.
    let directions = directions.map(|rule| rule.when(eq(&extra, 0)));
    let group = ruleset((&directions, &directions));
    assert_eq!(group.len(), 2, "clones retain the two distinct occurrences");
    graph.register(Math::Num(1))?;
    graph.run(group.repeat(1))?;
    assert!(graph.check(eq(Math::Num(1), Math::Add(Math::Num(1), Math::Num(0)),))?);
    Ok(())
}

#[test]
// Borrowing the array deliberately exercises the borrowed generic input adapter.
#[allow(clippy::needless_borrows_for_generic_args)]
fn expression_facts_match_rows_without_materializing_them() -> Result<(), TypedError> {
    let number = Math::Num(7);
    let mut graph = EGraph::new(EGraphOptions::default());
    assert!(!graph.check(&number)?);
    assert!(!graph.check(Read(7,))?);
    assert_eq!(graph.num_tuples()?, 0);
    let borrowed: Fact = (&number).into();
    let owned: Fact = number.clone().into();
    assert!(!graph.check([borrowed, owned])?);
    // Registration evaluates an expression; checking only queries for it.
    graph.register(&number)?;
    assert!(graph.check(number.clone())?);
    assert!(graph.check((&number, [number.clone()], vec![&number]))?);
    let refs = [&number, &number];
    assert!(graph.check(&refs)?);
    assert!(graph.check(refs.as_slice())?);
    let values = vec![number.clone()];
    assert!(graph.check(&values)?);
    let group = ruleset(|key: &eg::I64| rule(Math::Num(key), Copied(key)).when(Read(key)));
    graph.run(&group)?;
    assert!(!graph.check(Copied(7,))?);
    graph.register(set(Read(7), 1))?;
    graph.run(group.until(&number))?;
    // The already-satisfied stop condition need not execute a rule iteration.
    graph.run(&group)?;
    assert!(graph.check(Copied(7,))?);
    Ok(())
}

#[test]
fn expression_facts_mean_successful_evaluation_not_boolean_truth() -> Result<(), TypedError> {
    let mut graph = EGraph::new(EGraphOptions::default());
    assert!(graph.check((eg::Bool::from(false), eg::Bool::from(true)))?);
    assert!(graph.check(eg::I64::from(3).bool_lt(1))?);
    assert!(!graph.check(eq(eg::I64::from(3).bool_lt(1), true))?);
    assert!(graph.check(eg::I64::from(3) / 1)?);
    assert!(!graph.check(eg::I64::from(3) / 0)?);
    assert!(graph.check(())?);
    let group = ruleset(rule(eg::Bool::from(false), Pending(8)));
    graph.run(&group)?;
    assert!(graph.check(Pending(8,))?);
    Ok(())
}

#[sort]
pub struct DeclarationOrder;
#[declarations]
impl DeclarationOrder {
    #[constructor(name = "order::First")]
    pub fn First(value: eg::I64) -> Self;
    #[constructor(name = "order::Second")]
    pub fn Second(value: eg::I64) -> Self;
}
#[function(no_merge)]
pub fn OrderedResult() -> DeclarationOrder;

#[test]
fn basic_typed_execution() -> Result<(), TypedError> {
    let group = ruleset(|x: &eg::I64, y: &eg::I64| {
        rewrite(
            Math::Add(Math::Num(x.clone()), Math::Num(y.clone())),
            Math::Num(x + y),
        )
    });
    let root = let_("sum", Math::Add(Math::Num(2), Math::Num(3)));
    let mut egraph = EGraph::new(EGraphOptions::default());
    egraph.register(&root)?;
    egraph.run(group.saturate())?;
    assert!(egraph.check(eq(root.clone(), Math::Num(5,)))?);
    let best = egraph.extract(&root)?;
    assert_eq!(
        i64::try_from(
            get_args(&best, |value: &eg::I64| Math::Num(value))?
                .unwrap()
                .0
        )
        .unwrap(),
        5
    );
    Ok(())
}

#[test]
fn conditions_can_bind_rhs_variables_after_rewrite_construction() -> Result<(), TypedError> {
    let group = ruleset(|key: &eg::I64, value: &eg::I64| {
        rewrite(Math::Num(key), Math::Num(value))
            .when(Pending(key))
            .when(eq(value, Read(key)))
            .label("read-guarded rewrite")
    });
    let mut graph = EGraph::new(EGraphOptions::default());
    let root = let_("guarded-root", Math::Num(7));
    graph.register((&root, Pending(7)))?;
    // A missing condition row filters matches instead of failing an RHS read.
    graph.run(&group)?;
    assert!(!graph.check(eq(&root, Math::Num(9,)))?);
    graph.register(set(Read(7), 9))?;
    graph.run(&group)?;
    assert!(graph.check(eq(&root, Math::Num(9,)))?);
    Ok(())
}

#[test]
fn explicit_names_are_exact_and_query_local() -> Result<(), TypedError> {
    let key = var::<eg::I64>("key");
    assert_eq!(key, var::<eg::I64>("key"));
    assert_ne!(key, var::<eg::I64>("Key"));
    assert_ne!(var::<eg::I64>("é"), var::<eg::I64>("e\u{301}"));
    let group = ruleset(rule(Pending(&key), Copied(var::<eg::I64>("key"))));
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register((Pending(1), Math::Num(1)))?;
    graph.run(group.until(Copied(var::<eg::I64>("key"))))?;
    assert!(graph.check(Copied(&key,))?);
    assert!(graph.check(eq(var::<Math>("key"), Math::Num(1,)))?);
    // A separate query can use the same spelling with another exact sort.
    assert!(graph.check(eq(var::<eg::I64>("key"), 1))?);
    let separate_groups = ruleset((
        rule(Pending(var::<eg::I64>("same")), ()),
        rule(eq(var::<Math>("same"), Math::Num(1)), ()),
    ));
    graph.run(&separate_groups)?;
    Ok(())
}

#[test]
fn conflicting_named_sorts_fail_before_mutation_in_queries_and_actions() -> Result<(), TypedError> {
    let number = var::<eg::I64>("x");
    let math = var::<Math>("x");
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register(Pending(1))?;
    let before = graph.num_tuples()?;
    for step in [
        rule(eq(&math, Math::Num(&number)), ()),
        rule(eq(&math, Math::Num(1)), Pending(&number)),
        rewrite(Math::Num(&number), &math),
    ] {
        let result = graph.run(ruleset(step));
        assert!(
            matches!(result, Err(TypedError::Invalid(ref msg)) if msg.contains("conflicting sorts"))
        );
        assert_eq!(graph.num_tuples()?, before);
        assert!(graph.check(Pending(1,))?);
    }
    assert!(matches!(
        graph.check(eq(&math, Math::Num(&number,))),
        Err(TypedError::Invalid(_))
    ));
    assert!(matches!(
        graph.run(ruleset(()).until(eq(&math, Math::Num(&number,)))),
        Err(TypedError::Invalid(_))
    ));
    assert_eq!(graph.num_tuples()?, before);
    Ok(())
}

#[test]
fn explicit_names_never_alias_generated_variables() -> Result<(), TypedError> {
    let named = var::<eg::I64>("%typed_v_0");
    let mut retained = None;
    let group = ruleset(|fresh: &eg::I64| {
        retained = Some(fresh.clone());
        assert_ne!(fresh, &named);
        rule((eq(fresh, 1), eq(&named, 2)), Pair(fresh, &named))
    });
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.run(&group)?;
    assert!(graph.check(Pair(1, 2))?);
    let retained = retained.unwrap();
    assert!(graph.check((eq(&retained, 1), eq(&named, 2)))?);
    graph.run(ruleset(()).until(eq(&retained, 1)))?;
    for value in [named, retained, fresh_pair::<eg::I64>().0] {
        assert!(matches!(
            graph.register(&value),
            Err(TypedError::Invalid(_))
        ));
        assert!(matches!(graph.extract(&value), Err(TypedError::Invalid(_))));
        assert!(graph.check(Pair(1, 2))?);
    }
    Ok(())
}

#[test]
fn conditions_preserve_original_rules_and_fork_installed_cursors() -> Result<(), TypedError> {
    let key = var::<eg::I64>("key");
    let original = rule(Pending(&key), Copied(&key)).label("copy");
    let unchanged = original.clone().when(()).label("diagnostic only");
    assert_eq!(ruleset((&original, &unchanged)).len(), 1);
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register([Pending(1), Pending(2)])?;
    graph.run(ruleset(&original))?;
    graph.register([delete(Copied(1)), delete(Copied(2))])?;
    let conditioned = original.clone().when(eq(&key, 1));
    assert_eq!(ruleset((&original, &conditioned)).len(), 2);
    for _ in 0..2 {
        graph.push()?;
        graph.run(ruleset(&conditioned))?;
        assert!(graph.check(Copied(1,))?);
        assert!(!graph.check(Copied(2,))?);
        graph.pop()?;
    }
    graph.run(ruleset(&unchanged))?;
    assert!(!graph.check(Copied(1,))?);
    assert!(!graph.check(Copied(2,))?);
    Ok(())
}

#[test]
fn sequential_reads_and_capture_identity() -> Result<(), TypedError> {
    let mut egraph = EGraph::new(EGraphOptions::default());
    let read = Read(1);
    let before = let_("before", read.clone());
    let after = let_("after", read);
    egraph.register((
        set(Read(1), 10),
        &before,
        delete(Read(1)),
        set(Read(1), 20),
        &after,
    ))?;
    assert_eq!(i64::try_from(egraph.extract(&before)?).unwrap(), 10);
    assert_eq!(i64::try_from(egraph.extract(&after)?).unwrap(), 20);
    assert!(egraph.register(let_("before", eg::I64::from(99))).is_err());
    assert!(egraph.check(())?);
    Ok(())
}

#[test]
fn float_authoring_preserves_bits() {
    assert_ne!(eg::F64::from(0.0), eg::F64::from(-0.0));
    assert_ne!(
        eg::F64::from(f64::from_bits(0x7ff8000000000001)),
        eg::F64::from(f64::from_bits(0x7ff8000000000002))
    );
}

#[test]
fn invalid_until_is_preflight_error() -> Result<(), TypedError> {
    let mut egraph = EGraph::new(EGraphOptions::default());
    let group = ruleset(());
    assert!(
        egraph
            .run(group.saturate().until(eg::I64::from(1)))
            .is_err()
    );
    assert!(egraph.check(())?);
    Ok(())
}

#[test]
fn rhs_only_variables_are_rejected_at_submission() -> Result<(), TypedError> {
    let mut retained = None;
    let _ = ruleset(|x: &Math| {
        retained = Some(x.clone());
        rule(eq(x, Math::Num(0)), x)
    });
    let invalid = [
        ruleset(rule((), retained.unwrap())),
        ruleset(|x: &Math| rule((), x)),
    ];
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register(Pending(1))?;
    let before = graph.num_tuples()?;
    for group in invalid {
        assert!(matches!(graph.run(&group), Err(TypedError::Invalid(_))));
        assert_eq!(graph.num_tuples()?, before);
        assert!(graph.check(Pending(1,))?);
    }
    Ok(())
}

#[test]
fn direct_rule_inputs_accept_singletons_tuples_arrays_vectors_and_empty_sides()
-> Result<(), TypedError> {
    let group = ruleset(|key: &eg::I64| {
        (
            rule(Pending(key.clone()), Copied(key.clone())),
            rule(
                (Pending(key.clone()), eq(key.clone(), 1)),
                (
                    Pair(key.clone(), 9),
                    set(Read(key.clone()), 7),
                    Math::Num(0),
                ),
            ),
            rule([Pending(key.clone())], [Copied(key.clone())]),
            rule(vec![Pending(key.clone())], vec![set(Read(key.clone()), 7)]),
            rule(Pending(key), ()),
            rule((), Pending(2)),
            rule((), ()),
        )
    });
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register(Pending(1))?;
    graph.run(&group)?;
    assert!(graph.check((Copied(1,), Pair(1, 9), eq(Read(1,), 7), Pending(2,)))?);
    Ok(())
}

#[test]
fn rules_sharing_a_scope_validate_independently() -> Result<(), TypedError> {
    let mut invalid = None;
    let group = ruleset(|key: &eg::I64| {
        let first = rule(Pending(key), Copied(key));
        invalid = Some(rule((), Copied(key)));
        let second = rule(Pending(key), Copied(key));
        (first.clone(), second, first)
    });
    assert_eq!(group.len(), 2);
    let mut graph = EGraph::new(EGraphOptions::default());
    assert!(matches!(
        graph.run(ruleset(invalid.unwrap())),
        Err(TypedError::Invalid(_))
    ));
    graph.register(Pending(1))?;
    graph.run(&group)?;
    assert!(graph.check(Copied(1,))?);
    Ok(())
}

#[test]
fn infallible_authoring_finishes_before_submission_rejects_invalid_rules() -> Result<(), TypedError>
{
    let mut visited = vec![];
    let mut retained = None;
    let group = ruleset(|key: &eg::I64| {
        retained = Some(key.clone());
        (
            {
                visited.push("first");
                rule(Pending(key), Copied(key))
            },
            {
                visited.push("invalid");
                rule((), Copied(key))
            },
            {
                visited.push("later");
                rule((), Pending(2))
            },
        )
    });
    assert_eq!(visited, ["first", "invalid", "later"]);
    assert_eq!(group.len(), 3);
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register(Pending(1))?;
    let before = graph.num_tuples()?;
    assert!(matches!(graph.run(&group), Err(TypedError::Invalid(_))));
    assert_eq!(graph.num_tuples()?, before);
    assert!(!graph.check((Copied(1,), Pending(2,)))?);
    let key = retained.unwrap();
    graph.run(ruleset(rule(Pending(&key), Copied(&key))))?;
    assert!(graph.check(Copied(1,))?);
    Ok(())
}

#[test]
fn submission_rejects_fresh_and_installed_captures_in_rules() -> Result<(), TypedError> {
    let mut graph = EGraph::new(EGraphOptions::default());
    let captured = let_("not-a-rule-variable", Math::Num(0));
    for installed in [false, true] {
        if installed {
            graph.register(&captured)?;
        }
        let before = graph.num_tuples()?;
        for step in [
            rule(&captured, ()),
            rule(eq(&captured, Math::Num(0)), ()),
            rule((), &captured),
            rewrite(Math::Num(0), Math::Num(1)).when(eq(&captured, Math::Num(0))),
        ] {
            assert!(matches!(
                graph.run(ruleset(step)),
                Err(TypedError::Invalid(_))
            ));
            assert_eq!(graph.num_tuples()?, before);
            assert!(graph.check(())?);
        }
    }
    Ok(())
}

#[test]
fn symbolic_panic_preserves_the_completed_prefix() {
    let mut graph = EGraph::new(EGraphOptions::default());
    let action = panic("stop after the first row");
    let error = graph.register((Pending(1), action, Pending(2)));
    assert!(matches!(error, Err(TypedError::Core { completed, .. }) if completed > 0));
    assert!(matches!(graph.check(()), Err(TypedError::NeedsRestore)));
    assert_eq!(graph.into_raw().num_tuples(), 1);
}

#[test]
fn repeated_callbacks_generate_fresh_reusable_variables() -> Result<(), TypedError> {
    let mut parameters = vec![];
    let mut build = || {
        ruleset(|key: &eg::I64| {
            parameters.push(key.clone());
            rule(Pending(key), Copied(key))
        })
    };
    let group = ruleset([build(), build(), build()]);
    assert_eq!(group.len(), 3);
    assert_ne!(parameters[0], parameters[1]);
    assert_ne!(parameters[1], parameters[2]);
    let cross = ruleset(|key: &eg::I64| {
        rule(
            (Pending(key), Pending(&parameters[0])),
            Pair(key, &parameters[0]),
        )
    });
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register([Pending(1), Pending(2)])?;
    graph.run(ruleset((group, cross)))?;
    assert!(graph.check([Copied(1,), Copied(2,)])?);
    assert!(graph.check([Pair(1, 2), Pair(2, 1)])?);
    assert!(graph.check(eq(&parameters[0], 1))?);
    Ok(())
}

#[test]
fn nested_callbacks_keep_distinct_reusable_variables() -> Result<(), TypedError> {
    let group = ruleset(|outer: &eg::I64| {
        let mut retained_inner = None;
        let nested = ruleset(|inner: &eg::I64| {
            assert_ne!(outer, inner);
            retained_inner = Some(inner.clone());
            rule(
                (Pending(outer), Pending(inner), ne(outer, inner)),
                Pair(outer, inner),
            )
        });
        let retained = retained_inner.unwrap();
        let later = rule(Pending(&retained), Copied(&retained));
        let parent = rule(Pending(outer), Copied(outer));
        (nested, later, parent)
    });
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register([Pending(1), Pending(2)])?;
    graph.run(&group)?;
    assert!(graph.check((Pair(1, 2), Pair(2, 1), Copied(1,)))?);
    assert!(!graph.check(Pair(1, 1))?);
    Ok(())
}

#[test]
fn owned_callback_variables_and_rules_are_portable_across_threads() -> Result<(), TypedError> {
    let mut from_thread = None;
    let parent = ruleset(|outer: &eg::I64| {
        let retained = outer.clone();
        let (thread_rule, parameter) = std::thread::spawn(move || {
            let reused = rule(Pending(&retained), Pair(&retained, 8));
            let mut parameter = None;
            let generated = ruleset(|key: &eg::I64| {
                parameter = Some(key.clone());
                rule(Pending(key), Copied(key))
            });
            (ruleset((reused, generated)), parameter.unwrap())
        })
        .join()
        .unwrap();
        assert_ne!(outer, &parameter);
        let returned = rule(Pending(&parameter), Pair(&parameter, 7));
        from_thread = Some(ruleset((thread_rule, returned)));
        rule(Pending(outer), Pair(outer, 9))
    });
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register(Pending(3))?;
    graph.run(ruleset((parent, from_thread.unwrap())))?;
    assert!(graph.check((Copied(3,), Pair(3, 7), Pair(3, 8), Pair(3, 9)))?);
    Ok(())
}

fn fresh_pair<S: EgglogValue>() -> (S, S) {
    let mut pair = None;
    ruleset(|left: &S, right: &S| {
        pair = Some((left.clone(), right.clone()));
    });
    pair.unwrap()
}

#[test]
fn fresh_callback_clones_preserve_query_identity() -> Result<(), TypedError> {
    let fields = fresh_pair::<eg::I64>();
    let cloned = fields.clone();
    let binder = fields.0;
    assert_eq!(binder, binder.clone());
    assert_eq!(binder, cloned.0);
    assert_ne!(binder, fields.1);
    assert_ne!(binder, fresh_pair::<eg::I64>().0);
    assert_ne!(binder, var::<eg::I64>("%typed_v_0"));
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register((Pending(1), Copied(2), Pair(1, 2)))?;
    assert!(!graph.check((Pending(binder.clone(),), Copied(binder.clone(),)))?);
    assert!(graph.check((
        Pending(fresh_pair::<eg::I64>().0),
        Copied(fresh_pair::<eg::I64>().0)
    ))?);
    let group = ruleset(rule(Pair(binder.clone(), binder.clone()), Copied(9)));
    graph.run(&group)?;
    assert!(!graph.check(Copied(9,))?);
    graph.register(Pair(4, 4))?;
    graph.run(&group)?;
    assert!(graph.check(Copied(9,))?);
    // Fresh callback arguments are ordinary query variables, including on the RHS.
    let copy = ruleset(rule(Pending(&binder), Copied(&binder)));
    graph.run(&copy)?;
    assert!(graph.check(Copied(1,))?);
    let (a, b) = fresh_pair::<eg::I64>();
    graph.run(ruleset(()).until(Pair(a, b)))?;
    Ok(())
}

#[test]
fn matched_partial_expressions_and_fields_can_be_reused_by_actions() -> Result<(), TypedError> {
    let number = Math::Num(1);
    let fields = fresh_pair::<Math>();
    let pattern = Math::Add(&number, &fields.1);
    let copy = rule(
        &pattern,
        (set(ResultTable(), &pattern), set(KeyedResult(1), &fields.1)),
    );
    let pair = fresh_pair::<eg::I64>();
    let copy_fields = rule(Pair(&pair.0, &pair.1), (Pending(&pair.0), Copied(&pair.1)));
    let mut graph = EGraph::new(EGraphOptions::default());
    let root = Math::Add(&number, Math::Num(2));
    graph.register((&root, Pair(3, 4)))?;
    graph.run(ruleset((copy, copy_fields)))?;
    assert!(graph.check((
        eq(ResultTable(), &root),
        eq(KeyedResult(1,), Math::Num(2,)),
        Pending(3,),
        Copied(4,),
    ))?);
    Ok(())
}

#[test]
fn unbound_fresh_fields_fail_submission_without_mutation() -> Result<(), TypedError> {
    let fields = fresh_pair::<eg::I64>();
    let (a, b) = fresh_pair::<Math>();
    let unbound = Math::Add(a, b);
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register(Pending(1))?;
    let before = graph.num_tuples()?;
    for step in [
        rule(Pending(&fields.0), Copied(&fields.1)),
        rule(Pending(&fields.0), set(ResultTable(), &unbound)),
        // A separate factory does not bind the first factory's fields.
        rule(
            {
                let (a, b) = fresh_pair::<eg::I64>();
                Pair(a, b)
            },
            Copied(&fields.0),
        ),
    ] {
        assert!(matches!(
            graph.run(ruleset(step)),
            Err(TypedError::Invalid(_))
        ));
        assert_eq!(graph.num_tuples()?, before);
        assert!(graph.check(Pending(1,))?);
    }
    assert!(matches!(
        graph.register((Copied(99,), &unbound)),
        Err(TypedError::Invalid(_))
    ));
    assert!(matches!(
        graph.register(let_("unbound-record", &unbound)),
        Err(TypedError::Invalid(_))
    ));
    assert!(matches!(
        graph.extract(&unbound),
        Err(TypedError::Invalid(_))
    ));
    assert!(matches!(
        graph.extract_many(&[&unbound]),
        Err(TypedError::Invalid(_))
    ));
    assert_eq!(graph.num_tuples()?, before);
    assert!(!graph.check(Copied(99,))?);
    assert!(graph.check(Pending(1,))?);
    Ok(())
}

#[test]
fn labels_and_noop_options_preserve_rule_occurrences() -> Result<(), TypedError> {
    ruleset(|key: &eg::I64| {
        let step = rule(Pending(key.clone()), Copied(key));
        assert_eq!(
            ruleset((
                step.clone(),
                step.clone().label("renamed"),
                step.clone().seminaive()
            ))
            .len(),
            1
        );
        let naive = step.clone().naive();
        let no_decomp = step.clone().no_decomp();
        let include_subsumed = step.clone().include_subsumed();
        assert_eq!(ruleset((naive.clone(), naive.clone().naive())).len(), 1);
        assert_eq!(
            ruleset((no_decomp.clone(), no_decomp.clone().no_decomp())).len(),
            1
        );
        assert_eq!(
            ruleset((
                include_subsumed.clone(),
                include_subsumed.clone().include_subsumed()
            ))
            .len(),
            1
        );
        assert_eq!(
            ruleset((
                step.clone(),
                naive.clone(),
                no_decomp,
                include_subsumed,
                naive.seminaive()
            ))
            .len(),
            5
        );
        let first = ruleset(step.clone());
        let overlap = ruleset((first.clone(), step, first));
        assert_eq!(overlap.len(), 1);
        overlap
    });
    Ok(())
}

#[test]
fn independently_constructed_rules_have_separate_incremental_cursors() -> Result<(), TypedError> {
    let mut original = None;
    let build = || ruleset(|key: &eg::I64| rule(Pending(key.clone()), Copied(key)));
    let old_group = ruleset(|key: &eg::I64| {
        let step = rule(Pending(key.clone()), Copied(key)).label("copy");
        original = Some(step.clone());
        step
    });
    let original = original.unwrap();
    let renamed = ruleset(original.clone().label("another diagnostic"));
    let fresh = build().label("copy");
    let combined = ruleset((old_group.clone(), fresh.clone(), renamed.clone(), fresh));
    assert_eq!(combined.len(), 2);
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register(Pending(1))?;
    graph.run(&old_group)?;
    assert!(graph.check(Copied(1,))?);
    graph.register(delete(Copied(1)))?;
    graph.run(&renamed)?;
    assert!(!graph.check(Copied(1,))?);
    graph.run(&combined)?;
    assert!(graph.check(Copied(1,))?);
    graph.register(delete(Copied(1)))?;
    graph.run(ruleset(original.no_decomp()))?;
    assert!(graph.check(Copied(1,))?);
    Ok(())
}

#[test]
fn pop_restores_rule_installation_and_incremental_cursors() -> Result<(), TypedError> {
    let group = ruleset(|key: &eg::I64| rule(Pending(key.clone()), Copied(key)));
    let schedule = Schedule::from(&group);
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register(Pending(1))?;
    graph.push()?;
    graph.run(&schedule)?;
    assert!(graph.check(Copied(1,))?);
    graph.pop()?;
    assert!(!graph.check(Copied(1,))?);
    graph.run(&schedule)?;
    assert!(graph.check(Copied(1,))?);
    graph.push()?;
    graph.register(Pending(2))?;
    graph.run(&schedule)?;
    assert!(graph.check(Copied(2,))?);
    graph.pop()?;
    assert!(!graph.check(Copied(2,))?);
    graph.register(Pending(2))?;
    graph.run(schedule)?;
    assert!(graph.check(Copied(2,))?);
    Ok(())
}

#[test]
fn owned_borrowed_and_temporary_schedules_preserve_lazy_rule_occurrences() -> Result<(), TypedError>
{
    #[ruleset]
    fn copy(key: &eg::I64) -> Rule {
        rule(Pending(key), Copied(key))
    }
    let schedule = Schedule::from(&copy);
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register(Pending(1))?;
    graph.run(&schedule)?;
    assert!(graph.check(Copied(1))?);

    graph.register(delete(Copied(1)))?;
    graph.run(&copy)?;
    assert!(!graph.check(Copied(1))?);
    graph.run(schedule)?;
    assert!(!graph.check(Copied(1))?);

    graph.register(Pending(2))?;
    graph.run(ruleset(rule(Pending(2), Copied(2))))?;
    assert!(graph.check(Copied(2))?);
    assert!(!graph.check(Copied(1))?);
    Ok(())
}

#[test]
fn deep_authoring_and_shared_destruction() {
    let mut a = Math::Num(0);
    for _ in 0..100_000 {
        a = Math::Add(a.clone(), a);
    }
    let b = a.clone();
    assert_eq!(a, b);
    assert!(format!("{a:?}").len() < 20_000);
    drop(a);
    std::thread::spawn(move || drop(b)).join().unwrap();
}

#[test]
fn missing_rhs_read_fails_instead_of_becoming_a_query_filter() -> Result<(), TypedError> {
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register(Pending(1))?;
    graph.push()?;
    let group = ruleset(|key: &eg::I64| rule((Pending(key.clone()),), (Read(key),)).naive());
    assert!(graph.run(&group).is_err());
    assert!(matches!(graph.check(()), Err(TypedError::NeedsRestore)));
    graph.pop()?;
    assert!(graph.check(Pending(1,))?);
    Ok(())
}

#[test]
fn failed_check_does_not_construct_terms() -> Result<(), TypedError> {
    let mut graph = EGraph::new(EGraphOptions::default());
    let term = Math::Num(999);
    assert!(!graph.check(&term)?);
    assert_eq!(graph.num_tuples()?, 0);
    graph.register(term.clone())?;
    assert!(graph.check(&term)?);
    Ok(())
}

#[test]
fn pop_reinstalls_captures_without_reusing_backend_names() -> Result<(), TypedError> {
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.push()?;
    let root = let_("scoped", Math::Num(7));
    graph.register(&root)?;
    graph.pop()?;
    assert!(graph.check(&root).is_err());
    graph.register(&root)?;
    assert!(graph.check(eq(root, Math::Num(7,)))?);
    Ok(())
}

#[test]
fn overloaded_empty_containers_keep_root_sort() -> Result<(), TypedError> {
    let mut graph = EGraph::new(EGraphOptions::default());
    let integers = eg::Vec::<eg::I64>::empty();
    let strings = eg::Vec::<eg::String>::empty();
    graph.register((&integers, &strings))?;
    let value = graph.extract(&integers)?;
    assert!(Vec::<eg::I64>::try_from(&value).unwrap().is_empty());
    Ok(())
}

#[test]
fn nested_captures_preserve_left_to_right_failure_prefix() -> Result<(), TypedError> {
    let mut graph = EGraph::new(EGraphOptions::default());
    let left = let_("confirmed-left", Math::Num(1));
    let right = let_("failed-right", Math::Num(eg::I64::from(1) / 0));
    let failure = graph.register(set(ResultTable(), Math::Add(left, right)));
    assert!(matches!(failure, Err(TypedError::Core { completed, .. }) if completed > 0));
    let raw = graph.into_raw();
    // Declarations have no tuples. The right initializer fails before constructing
    // its Num; retained tuples therefore witness the earlier left initializer.
    assert!(raw.num_tuples() > 0);
    Ok(())
}

#[test]
fn only_reached_declarations_are_installed_in_first_use_order() -> Result<(), TypedError> {
    for from_head in [false, true] {
        let mut graph = EGraph::new(EGraphOptions::default());
        if from_head {
            // Reaching a result sort does not declare its unrelated constructors.
            graph.register(delete(OrderedResult()))?;
            let frozen = graph.freeze()?;
            assert!(
                frozen
                    .table(|value: &eg::I64| DeclarationOrder::First(value))
                    .is_err()
            );
            assert!(
                frozen
                    .table(|value: &eg::I64| DeclarationOrder::Second(value))
                    .is_err()
            );
        }
        let root = let_("order-root", DeclarationOrder::Second(1));
        graph.register((&root, union(root.clone(), DeclarationOrder::First(1))))?;
        let frozen = graph.freeze()?;
        let egglog_experimental::typed::FrozenValueView::EClass(class) =
            frozen.as_view(&frozen.lookup(&root)?)?.view()
        else {
            panic!("expected equality root")
        };
        let operations: Vec<_> = class.nodes().map(|node| node.name().to_owned()).collect();
        assert_eq!(operations, ["order::Second", "order::First"]);
        // Both trees have equal cost; native tie-breaking follows the reached
        // declarations, not the source order of this Rust impl.
        assert_eq!(graph.extract(&root)?, DeclarationOrder::Second(1));
    }
    Ok(())
}

#[test]
fn ineligible_action_rejects_fresh_nested_capture_without_mutation() -> Result<(), TypedError> {
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register(set(Read(0), 10))?;
    let root = let_("explicit-boundary", Math::Num(1));
    let before = graph.num_tuples()?;
    let error = graph.register(set(KeyedResult(Read(0)), root.clone()));
    assert!(
        matches!(error, Err(TypedError::Invalid(message)) if message.contains("register(capture) first"))
    );
    assert_eq!(graph.num_tuples()?, before);
    graph.register((&root, delete(Read(0)), set(Read(0), 20)))?;
    graph.register(set(KeyedResult(Read(0)), root.clone()))?;
    assert!(graph.check(eq(KeyedResult(20,), root))?);
    assert!(!graph.check(KeyedResult(10,))?);
    Ok(())
}

#[test]
fn shallow_unshared_setup_has_only_one_root_slot() -> Result<(), TypedError> {
    let mut graph = EGraph::new(EGraphOptions::default());
    let root = Next(Next(End()));
    graph.register(&root)?;
    // Three constructor rows and one typed root row; no per-node globals or
    // duplicate root copy. Native constructor hash-consing is unchanged.
    assert_eq!(graph.num_tuples()?, 4);
    Ok(())
}

#[test]
fn shared_setup_and_unshared_depth_cuts_are_bounded() -> Result<(), TypedError> {
    let mut options = EGraphOptions::default();
    options.lowering_limits.max_ast_depth = 8;
    let mut graph = EGraph::new(options);
    let mut chain = End();
    for _ in 0..40 {
        chain = Next(chain);
    }
    graph.register(chain)?;
    // 41 public rows, 5 cut/root slots (a cut at depth 8).
    assert_eq!(graph.num_tuples()?, 46);
    let mut shared = Math::Num(0);
    for _ in 0..24 {
        shared = Math::Add(shared.clone(), shared);
    }
    graph.register(shared)?;
    assert_eq!(graph.num_tuples()?, 96);
    Ok(())
}

#[test]
fn setup_counts_cross_root_edges_and_publishes_each_capture() -> Result<(), TypedError> {
    let mut graph = EGraph::new(EGraphOptions::default());
    let shared = Math::Num(1);
    let left = Math::Add(shared.clone(), Math::Num(2));
    let right = Math::Add(shared, Math::Num(3));
    graph.register((&left, &right))?;
    // Five public constructor rows, one shared leaf slot, two root slots.
    assert_eq!(graph.num_tuples()?, 8);
    let first = let_("alias-first", left.clone());
    let second = let_("alias-second", left);
    graph.register((&first, &second))?;
    let frozen = graph.freeze()?;
    assert_eq!(frozen.lookup(&first)?, frozen.lookup(&second)?);
    Ok(())
}

#[test]
fn top_level_actions_factor_only_wholly_eligible_argument_trees() -> Result<(), TypedError> {
    let mut options = EGraphOptions::default();
    options.lowering_limits.max_expanded_nodes = 64;
    let mut graph = EGraph::new(options);
    let mut shared = Math::Num(0);
    for _ in 0..20 {
        shared = Math::Add(shared.clone(), shared);
    }
    graph.register(set(ResultTable(), shared.clone()))?;
    assert_eq!(graph.num_tuples()?, 42);
    let before = graph.num_tuples()?;
    let ineligible = Math::Add(shared, Math::Num(Read(0)));
    assert!(matches!(
        graph.register(set(KeyedResult(0,), ineligible)),
        Err(TypedError::LoweringLimit(_))
    ));
    assert_eq!(graph.num_tuples()?, before);
    assert!(graph.check(())?);
    Ok(())
}
