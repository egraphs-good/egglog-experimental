#![cfg(feature = "typed")]

use egglog_experimental::typed::{builtins::I64, prelude::*};
use std::sync::{
    LazyLock,
    atomic::{AtomicUsize, Ordering},
};

#[relation]
fn Pending(key: I64);
#[relation]
fn Copied(key: I64);
#[relation]
fn Finished(key: I64);
#[relation]
fn Pair(left: I64, right: I64);
#[relation]
fn Swapped(left: I64, right: I64);

static BUILDS: AtomicUsize = AtomicUsize::new(0);

mod named {
    use super::*;

    /// A public ruleset retains this authored name and documentation.
    #[ruleset(name = "copy group")]
    pub fn copy(key: &I64) -> Rule {
        BUILDS.fetch_add(1, Ordering::SeqCst);
        rule(Pending(key), Copied(key)).label("copy occurrence")
    }
}
use named::copy as copied_alias;

mod first {
    use super::*;

    #[ruleset]
    pub fn same() -> Rule {
        rule((), ())
    }
}

mod second {
    use super::*;

    #[ruleset]
    pub fn same() -> Rule {
        rule((), ())
    }
}
use first::same as reexported;

#[test]
fn default_names_follow_authored_modules_and_survive_reexports() {
    for (group, expected) in [
        (&*first::same, concat!(module_path!(), "::first::same")),
        (&*second::same, concat!(module_path!(), "::second::same")),
        (&*reexported, concat!(module_path!(), "::first::same")),
    ] {
        assert!(format!("{group:?}").ends_with(&format!("label: Some({expected:?}) }}")));
    }
    assert!(std::ptr::eq(&first::same, &reexported));
}

const OVERRIDE_NAME: &str = "same diagnostic";

#[ruleset(name = OVERRIDE_NAME)]
fn override_one() -> Rule {
    rule(Pending(91), Copied(91))
}

#[ruleset(name = concat!("same", " diagnostic").to_owned())]
fn override_two() -> Rule {
    rule(Pending(91), Copied(91))
}

#[test]
fn name_expressions_are_diagnostic_not_occurrence_identity() -> Result<(), TypedError> {
    for group in [&*override_one, &*override_two] {
        assert!(format!("{group:?}").ends_with(&format!("label: Some({OVERRIDE_NAME:?}) }}")));
    }
    assert_eq!(ruleset((&override_one, &override_two)).len(), 2);
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register(Pending(91))?;
    graph.run(&override_one)?;
    assert!(graph.check(Copied(91))?);
    graph.register(delete(Copied(91)))?;
    graph.run(&override_one)?;
    assert!(!graph.check(Copied(91))?);
    graph.run(&override_two)?;
    assert!(
        graph.check(Copied(91))?,
        "equal names must not merge cursors"
    );
    graph.register(delete(Copied(91)))?;
    graph.run(override_two.clone().label("renamed diagnostic"))?;
    assert!(
        !graph.check(Copied(91))?,
        "renaming must not reset a cursor"
    );
    Ok(())
}

#[ruleset]
fn finish(key: &I64) -> [Rule; 1] {
    [rule(Copied(key), Finished(key))]
}

#[ruleset]
fn combined() -> Ruleset {
    ruleset((&named::copy, &finish))
}

#[ruleset]
#[cfg(any())]
fn disabled() -> Ruleset {
    compile_error!("the generated static must retain cfg");
}

#[test]
fn lazy_groups_keep_names_occurrences_and_native_cursors() -> Result<(), TypedError> {
    assert_eq!(BUILDS.load(Ordering::SeqCst), 0);
    let authored_name: &LazyLock<Ruleset> = &named::copy;
    assert!(std::ptr::eq(authored_name, &copied_alias));
    assert_eq!(named::copy.len(), 1);
    assert_eq!(BUILDS.load(Ordering::SeqCst), 1);
    assert!(format!("{:?}", &*named::copy).contains("copy group"));
    assert!(format!("{:?}", &*finish).ends_with(&format!(
        "label: Some({:?}) }}",
        concat!(module_path!(), "::finish")
    )));

    let empty = ruleset(());
    let composition = ruleset((&combined, &empty, &named::copy, &finish));
    assert_eq!(
        composition.len(),
        2,
        "borrowed lazy groups deduplicate shared occurrences"
    );

    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register(Pending(1))?;
    graph.run(&named::copy)?;
    assert!(graph.check(Copied(1))?);
    let initial_names = graph
        .stats()?
        .num_matches_per_rule
        .into_keys()
        .collect::<Vec<_>>();
    assert!(
        initial_names
            .iter()
            .any(|name| name.contains("copy occurrence"))
    );

    graph.register(delete(Copied(1)))?;
    graph.run(&copied_alias)?;
    assert!(
        !graph.check(Copied(1))?,
        "a reexport must not author a fresh cursor"
    );
    graph.register(Pending(2))?;
    graph.push()?;
    graph.run(&composition)?;
    assert!(graph.check(Copied(2))?);
    assert!(
        !graph.check(Finished(2))?,
        "a direct group is one native run"
    );
    graph.run(&finish)?;
    assert!(graph.check(Finished(2))?);
    graph.pop()?;
    assert!(!graph.check(Finished(2))?);
    graph.run(composition)?;
    graph.run(&finish)?;
    assert!(graph.check(Finished(2))?);
    assert_eq!(BUILDS.load(Ordering::SeqCst), 1);
    Ok(())
}

#[expect(clippy::eq_op)]
#[ruleset]
fn swap(left: &I64, right: &I64) -> Vec<Rule> {
    let _ = left == left;
    let step = rule(Pair(left, right), Swapped(right, left));
    vec![step]
}

#[test]
fn mixed_schedule_inputs_preserve_order_and_borrowing() -> Result<(), TypedError> {
    let reverse = ruleset(|left: &I64, right: &I64| rule(Swapped(left, right), Pair(left, right)));
    let owned = ruleset(rule(Pair(3, 4), Pair(5, 6)));
    let shared = sequence((&swap, &reverse)).repeat(2);
    let schedule = sequence((&shared, owned, [&swap], &reverse));
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register((Pair(1, 2), Pair(3, 4)))?;
    graph.run(&schedule)?;
    assert!(graph.check((Swapped(2, 1), Pair(2, 1), Pair(5, 6)))?);
    graph.run(&schedule)?;
    graph.run(schedule)?;
    graph.run(swap.until(Swapped(2, 1)))?;
    graph.run(swap.repeat(2))?;
    graph.run(swap.saturate())?;
    Ok(())
}

#[ruleset]
fn thirty_two(
    v0: &I64,
    v1: &I64,
    v2: &I64,
    v3: &I64,
    v4: &I64,
    v5: &I64,
    v6: &I64,
    v7: &I64,
    v8: &I64,
    v9: &I64,
    v10: &I64,
    v11: &I64,
    v12: &I64,
    v13: &I64,
    v14: &I64,
    v15: &I64,
    v16: &I64,
    v17: &I64,
    v18: &I64,
    v19: &I64,
    v20: &I64,
    v21: &I64,
    v22: &I64,
    v23: &I64,
    v24: &I64,
    v25: &I64,
    v26: &I64,
    v27: &I64,
    v28: &I64,
    v29: &I64,
    v30: &I64,
    v31: &I64,
) -> [Rule; 32] {
    [
        rule(Pending(v0), Copied(v0)),
        rule(Pending(v1), Copied(v1)),
        rule(Pending(v2), Copied(v2)),
        rule(Pending(v3), Copied(v3)),
        rule(Pending(v4), Copied(v4)),
        rule(Pending(v5), Copied(v5)),
        rule(Pending(v6), Copied(v6)),
        rule(Pending(v7), Copied(v7)),
        rule(Pending(v8), Copied(v8)),
        rule(Pending(v9), Copied(v9)),
        rule(Pending(v10), Copied(v10)),
        rule(Pending(v11), Copied(v11)),
        rule(Pending(v12), Copied(v12)),
        rule(Pending(v13), Copied(v13)),
        rule(Pending(v14), Copied(v14)),
        rule(Pending(v15), Copied(v15)),
        rule(Pending(v16), Copied(v16)),
        rule(Pending(v17), Copied(v17)),
        rule(Pending(v18), Copied(v18)),
        rule(Pending(v19), Copied(v19)),
        rule(Pending(v20), Copied(v20)),
        rule(Pending(v21), Copied(v21)),
        rule(Pending(v22), Copied(v22)),
        rule(Pending(v23), Copied(v23)),
        rule(Pending(v24), Copied(v24)),
        rule(Pending(v25), Copied(v25)),
        rule(Pending(v26), Copied(v26)),
        rule(Pending(v27), Copied(v27)),
        rule(Pending(v28), Copied(v28)),
        rule(Pending(v29), Copied(v29)),
        rule(Pending(v30), Copied(v30)),
        rule(Pending(v31), Copied(v31)),
    ]
}

#[test]
fn attribute_supports_thirty_two_parameters() {
    assert_eq!(thirty_two.len(), 32);
}

macro_rules! wide_ruleset_test {
    ($test:ident, $group:ident; $($value:ident:$index:literal),+) => {
        #[ruleset]
        fn $group($($value: &I64),+) -> Vec<Rule> {
            vec![rule(vec![$(eq($value, $index)),+], vec![$(Copied($value)),+])]
        }

        #[test]
        fn $test() -> Result<(), TypedError> {
            let mut graph = EGraph::default();
            graph.run(&$group)?;
            assert!(graph.check(vec![$(Copied($index)),+])?);

            let mut previous: Option<Vec<I64>> = None;
            for _ in 0..2 {
                let mut invalid = None;
                let callback = ruleset(|$($value: &I64),+| {
                    let variables = vec![$($value.clone()),+];
                    let distinct = variables.iter().collect::<std::collections::HashSet<_>>();
                    assert_eq!(distinct.len(), variables.len());
                    if let Some(previous) = &previous {
                        assert_ne!(previous, &variables);
                        assert!(previous.iter().all(|value| !distinct.contains(value)));
                    }
                    previous = Some(variables);
                    invalid = Some(rule((), vec![$(Copied($value)),+]));
                    vec![rule(vec![$(eq($value, $index)),+], vec![$(Copied($value)),+])]
                });
                let mut graph = EGraph::default();
                assert!(matches!(
                    graph.run(ruleset(invalid.unwrap())),
                    Err(TypedError::Invalid(_))
                ));
                assert_eq!(graph.num_tuples()?, 0);
                graph.run(&callback)?;
                assert!(graph.check(vec![$(Copied($index)),+])?);
            }
            Ok(())
        }
    };
}

wide_ruleset_test!(thirty_three_parameters, thirty_three;
    v0:0, v1:1, v2:2, v3:3, v4:4, v5:5, v6:6, v7:7,
    v8:8, v9:9, v10:10, v11:11, v12:12, v13:13, v14:14, v15:15,
    v16:16, v17:17, v18:18, v19:19, v20:20, v21:21, v22:22, v23:23,
    v24:24, v25:25, v26:26, v27:27, v28:28, v29:29, v30:30, v31:31,
    v32:32
);
wide_ruleset_test!(forty_parameters, forty;
    v0:0, v1:1, v2:2, v3:3, v4:4, v5:5, v6:6, v7:7,
    v8:8, v9:9, v10:10, v11:11, v12:12, v13:13, v14:14, v15:15,
    v16:16, v17:17, v18:18, v19:19, v20:20, v21:21, v22:22, v23:23,
    v24:24, v25:25, v26:26, v27:27, v28:28, v29:29, v30:30, v31:31,
    v32:32, v33:33, v34:34, v35:35, v36:36, v37:37, v38:38, v39:39
);
wide_ruleset_test!(sixty_four_parameters, sixty_four;
    v0:0, v1:1, v2:2, v3:3, v4:4, v5:5, v6:6, v7:7,
    v8:8, v9:9, v10:10, v11:11, v12:12, v13:13, v14:14, v15:15,
    v16:16, v17:17, v18:18, v19:19, v20:20, v21:21, v22:22, v23:23,
    v24:24, v25:25, v26:26, v27:27, v28:28, v29:29, v30:30, v31:31,
    v32:32, v33:33, v34:34, v35:35, v36:36, v37:37, v38:38, v39:39,
    v40:40, v41:41, v42:42, v43:43, v44:44, v45:45, v46:46, v47:47,
    v48:48, v49:49, v50:50, v51:51, v52:52, v53:53, v54:54, v55:55,
    v56:56, v57:57, v58:58, v59:59, v60:60, v61:61, v62:62, v63:63
);

wide_ruleset_test!(one_hundred_twenty_eight_parameters, one_hundred_twenty_eight;
    v0:0, v1:1, v2:2, v3:3, v4:4, v5:5, v6:6, v7:7,
    v8:8, v9:9, v10:10, v11:11, v12:12, v13:13, v14:14, v15:15,
    v16:16, v17:17, v18:18, v19:19, v20:20, v21:21, v22:22, v23:23,
    v24:24, v25:25, v26:26, v27:27, v28:28, v29:29, v30:30, v31:31,
    v32:32, v33:33, v34:34, v35:35, v36:36, v37:37, v38:38, v39:39,
    v40:40, v41:41, v42:42, v43:43, v44:44, v45:45, v46:46, v47:47,
    v48:48, v49:49, v50:50, v51:51, v52:52, v53:53, v54:54, v55:55,
    v56:56, v57:57, v58:58, v59:59, v60:60, v61:61, v62:62, v63:63,
    v64:64, v65:65, v66:66, v67:67, v68:68, v69:69, v70:70, v71:71,
    v72:72, v73:73, v74:74, v75:75, v76:76, v77:77, v78:78, v79:79,
    v80:80, v81:81, v82:82, v83:83, v84:84, v85:85, v86:86, v87:87,
    v88:88, v89:89, v90:90, v91:91, v92:92, v93:93, v94:94, v95:95,
    v96:96, v97:97, v98:98, v99:99, v100:100, v101:101, v102:102, v103:103,
    v104:104, v105:105, v106:106, v107:107, v108:108, v109:109, v110:110, v111:111,
    v112:112, v113:113, v114:114, v115:115, v116:116, v117:117, v118:118, v119:119,
    v120:120, v121:121, v122:122, v123:123, v124:124, v125:125, v126:126, v127:127
);

#[ruleset]
fn independent_queries(key: &I64) -> Vec<Rule> {
    vec![
        rule(eq(key, 1), Copied(key)),
        rule(eq(key, 2), Finished(key)),
    ]
}

#[test]
fn borrowed_parameters_bind_independently_in_each_rule() -> Result<(), TypedError> {
    let mut graph = EGraph::default();
    graph.run(&independent_queries)?;
    assert!(graph.check((Copied(1), Finished(2)))?);
    assert!(!graph.check(Copied(2))?);
    assert!(!graph.check(Finished(1))?);
    Ok(())
}

#[ruleset]
fn inner_linted(key: &I64) -> Rule {
    //! Inner documentation describes the named item.
    #![expect(clippy::eq_op)]
    let _ = key == key;
    rule(Pending(key), Copied(key))
}

#[ruleset]
fn inner_disabled() -> Rule {
    #![cfg(any())]
    this_must_not_be_resolved()
}

fn inner_disabled() -> usize {
    7
}

#[test]
fn inner_attributes_apply_to_the_named_item() {
    assert_eq!(inner_linted.len(), 1);
    assert_eq!(inner_disabled(), 7);
}

#[ruleset]
fn invalid_rhs(key: &I64) -> Rule {
    rule((), Copied(key))
}

#[test]
fn attribute_keeps_validation_at_submission() {
    assert_eq!(invalid_rhs.len(), 1);
    let mut graph = EGraph::new(EGraphOptions::default());
    assert!(matches!(
        graph.run(&invalid_rhs),
        Err(TypedError::Invalid(_))
    ));
    assert_eq!(graph.num_tuples().unwrap(), 0);
}

#[test]
fn poisoned_graph_does_not_force_a_lazy_initializer() -> Result<(), TypedError> {
    static INITIALIZATIONS: AtomicUsize = AtomicUsize::new(0);
    #[ruleset]
    fn local_builder() -> Ruleset {
        INITIALIZATIONS.fetch_add(1, Ordering::SeqCst);
        struct NotClone(String);
        let mut labels = vec![NotClone("local callback".into())];
        ruleset(|key: &I64| {
            let NotClone(label) = labels.pop().unwrap();
            rule(Pending(key), Copied(key)).label(label)
        })
    }

    let mut graph = EGraph::new(EGraphOptions::default());
    graph.push()?;
    assert!(graph.register(panic("intentional native failure")).is_err());
    assert!(matches!(
        graph.run(&local_builder),
        Err(TypedError::NeedsRestore)
    ));
    assert_eq!(INITIALIZATIONS.load(Ordering::SeqCst), 0);
    graph.pop()?;
    graph.register(Pending(42))?;
    graph.run(&local_builder)?;
    assert!(graph.check(Copied(42))?);
    assert_eq!(INITIALIZATIONS.load(Ordering::SeqCst), 1);
    Ok(())
}

#[test]
fn ast_export_preserves_bindings_sharing_options_and_rule_order() -> Result<(), TypedError> {
    use egglog::ast::{Action as NativeAction, Command, Expr, Fact, RuleEvalMode};

    let build = || {
        ruleset(|x: &I64, y: &I64| {
            let shared = x.min(1);
            let first = rule(
                (Pair(&shared, &shared), Pair(x, y)),
                (Swapped(y, x), Pair(&shared, &shared)),
            )
            .naive()
            .no_decomp()
            .include_subsumed()
            .label("join \"first\"");
            [
                first.clone(),
                first,
                rule(Pending(y), Copied(y)).label("second"),
            ]
        })
        .label("export group")
    };
    let commands = build().to_ast()?;
    // Fresh callback identities and allocations do not affect generated names.
    assert_eq!(format!("{commands:?}"), format!("{:?}", build().to_ast()?));
    assert!(commands.iter().all(|command| matches!(
        command,
        Command::Relation { .. }
            | Command::AddRuleset(..)
            | Command::Rule { .. }
            | Command::UnstableCombinedRuleset(..)
    )));
    let rules: Vec<_> = commands
        .iter()
        .filter_map(|command| match command {
            Command::Rule { rule } => Some(rule),
            _ => None,
        })
        .collect();
    assert_eq!(rules.len(), 2, "cloned occurrences remain deduplicated");
    assert!(rules[0].name.contains("join \"first\""));
    assert!(rules[1].name.contains("second"));
    assert_eq!(rules[0].eval_mode, RuleEvalMode::Naive);
    assert!(rules[0].no_decomp && rules[0].include_subsumed);
    assert_eq!(rules[1].eval_mode, RuleEvalMode::Seminaive);
    assert!(!rules[1].no_decomp && !rules[1].include_subsumed);
    let Command::UnstableCombinedRuleset(_, name, members) = commands.last().unwrap() else {
        panic!("expected an ordered combined group");
    };
    assert!(name.contains("export group"));
    assert_eq!(
        members,
        &[rules[0].ruleset.clone(), rules[1].ruleset.clone()]
    );

    let shared_calls: Vec<_> = rules[0]
        .body
        .iter()
        .filter_map(|fact| match fact {
            Fact::Eq(_, Expr::Var(_, name), Expr::Call(_, head, _)) if head == "min" => Some(name),
            _ => None,
        })
        .collect();
    assert_eq!(shared_calls.len(), 1);
    assert!(rules[0].body.iter().any(|fact| matches!(
        fact,
        Fact::Eq(_, _, Expr::Call(_, _, args))
            if matches!(args.as_slice(), [Expr::Var(_, a), Expr::Var(_, b)]
                if a == shared_calls[0] && b == a)
    )));
    assert!(matches!(
        &rules[0].head.0[0],
        NativeAction::Let(_, _, Expr::Call(_, _, args))
            if matches!(args.as_slice(), [Expr::Var(_, y), Expr::Var(_, x)]
                if y == "@$typed_v_1" && x == "@$typed_v_")
    ));
    let NativeAction::Let(_, shared, Expr::Call(_, head, _)) = &rules[0].head.0[2] else {
        panic!("expected one shared RHS computation after the first action");
    };
    assert_eq!(head, "min");
    assert!(matches!(
        &rules[0].head.0[3],
        NativeAction::Let(_, _, Expr::Call(_, _, args))
            if matches!(args.as_slice(), [Expr::Var(_, a), Expr::Var(_, b)]
                if a == shared && b == shared)
    ));
    assert!(matches!(
        &rules[1].head.0[0],
        NativeAction::Let(_, _, Expr::Call(_, _, args))
            if matches!(args.as_slice(), [Expr::Var(_, y)] if y == "@$typed_v_2")
    ));
    Ok(())
}

#[test]
fn ast_export_retains_nominal_names_across_encounter_order() -> Result<(), TypedError> {
    use egglog::ast::{Command, Expr};
    use egglog_experimental::typed::builtins as egg;

    #[sort(name = "+")]
    struct Term;
    #[constructor(name = "nominal::i64", cost = 7)]
    fn number(value: I64) -> Term;
    #[constructor(name = "nominal::+")]
    fn add(left: Term, right: Term) -> Term;
    #[function(name = "stored", merge = |old: Term, new: Term| add(old, new))]
    fn stored(key: I64) -> Term;
    #[relation(name = "items")]
    fn items(values: egg::Vec<Term>);

    let build = |reverse| {
        ruleset(|key: &I64, value: &Term| {
            let mut facts = [
                Pending(key).into(),
                eq(value, number(key + 1)),
                eq(value, add(value, value)),
            ];
            if reverse {
                facts.reverse();
            }
            rule(facts, (set(stored(key), value), items(vec![value.clone()])))
        })
    };
    let mut orders = vec![];
    for reverse in [false, true] {
        let commands = build(reverse).to_ast()?;
        let constructors: Vec<_> = commands
            .iter()
            .filter_map(|command| match command {
                Command::Constructor { name, .. } => Some(name.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(constructors.len(), 2);
        orders.push(constructors);
        assert!(commands.iter().any(|command| matches!(command,
            Command::Constructor { name, schema, cost: Some(7), .. }
                if name == "nominal::i64" && schema.input == ["i64"]
                    && schema.output == "+"
        )));
        assert!(commands.iter().any(|command| matches!(command,
            Command::Sort { name, presort_and_args: Some((family, args)), .. }
                if name == "Vec<+>" && family == "Vec"
                    && matches!(args.as_slice(), [Expr::Var(_, sort)] if sort == "+")
        )));
        assert!(commands.iter().any(|command| matches!(command,
            Command::Relation { name, inputs, .. }
                if name == "items" && inputs == &["Vec<+>"]
        )));
        assert!(commands.iter().any(|command| matches!(command,
            Command::Function { name, schema, merge: Some(Expr::Call(_, head, args)), .. }
                if name == "stored" && schema.input == ["i64"]
                    && schema.output == "+" && head == "nominal::+"
                    && matches!(args.as_slice(), [Expr::Var(_, old), Expr::Var(_, new)]
                        if old == "old" && new == "new")
        )));
        let mut heads = std::collections::HashSet::new();
        for command in commands.clone() {
            command.map_symbols(
                &mut |head| {
                    heads.insert(head.clone());
                    head
                },
                &mut |leaf| leaf,
            );
        }
        for head in [
            "+",
            "vec-of",
            "nominal::+",
            "nominal::i64",
            "stored",
            "items",
        ] {
            assert!(heads.contains(head), "missing call head {head}");
        }
        // Separately typecheck this fixture: every nominal reference must resolve.
        egglog::EGraph::default().run_program(commands).unwrap();
    }
    assert_ne!(
        orders[0], orders[1],
        "the fixture changes declaration order"
    );
    orders[0].sort();
    orders[1].sort();
    assert_eq!(orders[0], orders[1]);
    Ok(())
}

#[test]
fn ast_export_does_not_evaluate_actions_or_lose_literal_payloads() -> Result<(), TypedError> {
    use egglog::ast::{Action as NativeAction, Command, Expr, Fact, Literal};
    use egglog_experimental::typed::builtins::F64;

    let bits = [(-0.0f64).to_bits(), 0x7ff8_0000_0000_1234];
    let group = ruleset(rule(
        bits.map(|bits| eq(F64::from(f64::from_bits(bits)), f64::from_bits(bits))),
        (Copied(I64::from(1) / 0), panic("not executed \"here\"")),
    ));
    let commands = group.to_ast()?;
    let rule = commands
        .iter()
        .find_map(|command| match command {
            Command::Rule { rule } => Some(rule),
            _ => None,
        })
        .unwrap();
    assert_eq!(rule.body.len(), bits.len());
    for (fact, expected) in rule.body.iter().zip(bits) {
        let Fact::Eq(_, Expr::Lit(_, Literal::Float(a)), Expr::Lit(_, Literal::Float(b))) = fact
        else {
            panic!("expected stored float literals");
        };
        assert_eq!(a.0.to_bits(), expected);
        assert_eq!(b.0.to_bits(), expected);
    }
    assert!(matches!(
        &rule.head.0[0],
        NativeAction::Let(_, _, Expr::Call(_, head, args))
            if head == "/" && matches!(args.as_slice(),
                [Expr::Lit(_, Literal::Int(1)), Expr::Lit(_, Literal::Int(0))])
    ));
    assert!(matches!(
        rule.head.0.last().unwrap(),
        NativeAction::Panic(_, message) if message == "not executed \"here\""
    ));
    Ok(())
}

#[test]
fn ast_export_reuses_submission_preflight() -> Result<(), TypedError> {
    assert!(matches!(invalid_rhs.to_ast(), Err(TypedError::Invalid(_))));
    let captured = let_("capture", I64::from(1));
    for group in [
        ruleset(rule(&captured, ())),
        ruleset(rule((), &captured)),
        ruleset(rule((), set(I64::from(1), 2))),
    ] {
        assert!(matches!(group.to_ast(), Err(TypedError::Invalid(_))));
    }
    let mut graph = EGraph::default();
    graph.register(&captured)?;
    let frozen = graph.freeze()?;
    let observed = frozen.lookup(&captured)?;
    let tuples = graph.num_tuples()?;
    assert!(matches!(
        ruleset(rule(eq(observed, 1), ())).to_ast(),
        Err(TypedError::Invalid(_))
    ));
    let too_many = vec![Fact::from(I64::from(1)); LoweringLimits::default().max_expanded_nodes + 1];
    assert!(matches!(
        ruleset(rule(too_many, ())).to_ast(),
        Err(TypedError::LoweringLimit(_))
    ));
    assert_eq!(graph.num_tuples()?, tuples);
    Ok(())
}
