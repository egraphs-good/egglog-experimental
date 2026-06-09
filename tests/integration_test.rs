use std::sync::Arc;

use egglog::{
    CommandOutput,
    ast::{Expr, Literal},
    prelude::{RustSpan, Span},
    span,
};

fn eval_get_size(egraph: &mut egglog::EGraph, names: &[&str]) -> i64 {
    let span = span!();
    let expr = Expr::Call(
        span.clone(),
        "get-size!".into(),
        names
            .iter()
            .map(|name| Expr::Lit(span.clone(), Literal::String((*name).into())))
            .collect(),
    );
    let (_, value) = egraph.eval_expr(&expr).unwrap();
    egraph.value_to_base::<i64>(value)
}

fn new_copy_egraph() -> egglog::EGraph {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    egraph
        .parse_and_run_program(
            None,
            r#"
        (ruleset copy)
        (relation R (i64))
        (relation S (i64))
        (R 0)
        (rule ((R x)) ((S x)) :ruleset copy :name "copy")
        "#,
        )
        .unwrap();
    egraph
}

fn let_backoff(egraph: &mut egglog::EGraph) {
    egraph
        .parse_and_run_program(
            None,
            "(let-scheduler bo (back-off :match-limit 2 :ban-length 2))",
        )
        .unwrap();
}

fn run_bo_copy(egraph: &mut egglog::EGraph) {
    egraph
        .parse_and_run_program(None, "(run-schedule (run-with bo copy))")
        .unwrap();
}

#[test]
fn test_extract() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let result = egraph
        .parse_and_run_program(
            None,
            "
        (with-dynamic-cost
            (datatype E (Add E E) (Sub E E :cost 200) (Num i64))
        )

        (union (Num 2) (Add (Num 1) (Num 1)))
        (set-cost (Num 2) 1000)
        (set-cost (Num 1) 100)
        (extract (Num 2))

        (push)
        (set-cost (Add (Num 1) (Num 1)) 800)
        (extract (Num 2))
        (pop)

        (push)
        (set-cost (Add (Num 1) (Num 1)) 798)
        (extract (Num 2))
        (pop)

        ;; 200 + 1 + 1 > 1 + 100 + 100
        (union (Num 2) (Sub (Num 5) (Num 3)))
        (extract (Num 2))
        (set-cost (Sub (Num 5) (Num 3)) 198)
        ;; 198 + 1 + 1 < 1 + 100 + 100
        (extract (Num 2))",
        )
        .unwrap();

    assert_eq!(result.len(), 5);
    assert_eq!(result[0].to_string(), "(Add (Num 1) (Num 1))\n");
    assert_eq!(result[1].to_string(), "(Num 2)\n");
    assert_eq!(result[2].to_string(), "(Add (Num 1) (Num 1))\n");
    assert_eq!(result[3].to_string(), "(Add (Num 1) (Num 1))\n");
    assert_eq!(result[4].to_string(), "(Sub (Num 5) (Num 3))\n");
}

#[test]
fn test_get_size_primitive() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let span = Span::Rust(Arc::new(RustSpan {
        file: "integration_test",
        line: 0,
        column: 0,
    }));

    let make_expr = |names: &[&str]| {
        Expr::Call(
            span.clone(),
            "get-size!".into(),
            names
                .iter()
                .map(|name| Expr::Lit(span.clone(), Literal::String((*name).into())))
                .collect(),
        )
    };

    let eval_size = |egraph: &mut egglog::EGraph, names: &[&str]| -> i64 {
        let expr = make_expr(names);
        let (_, value) = egraph.eval_expr(&expr).unwrap();
        egraph.value_to_base::<i64>(value)
    };

    assert_eq!(eval_size(&mut egraph, &[]), 0);
    assert_eq!(eval_size(&mut egraph, &["MkFoo"]), 0);
    assert_eq!(eval_size(&mut egraph, &["MkBar"]), 0);
    assert_eq!(eval_size(&mut egraph, &["MkFoo", "MkBar"]), 0);

    egraph
        .parse_and_run_program(
            None,
            "
            (datatype Foo (MkFoo i64))
            (datatype Bar (MkBar i64))
            (MkFoo 1)
            (MkFoo 2)
            (MkBar 10)
        ",
        )
        .unwrap();

    assert_eq!(eval_size(&mut egraph, &[]), 3);
    assert_eq!(eval_size(&mut egraph, &["MkFoo"]), 2);
    assert_eq!(eval_size(&mut egraph, &["MkBar"]), 1);
    assert_eq!(eval_size(&mut egraph, &["MkFoo", "MkBar"]), 3);
    assert_eq!(eval_size(&mut egraph, &["Unknown"]), 0);
}

#[test]
fn test_extract_set_cost_multiple_times_should_fail() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            "(with-dynamic-cost
                (datatype E (Add E E) (Sub E E :cost 200) (Num i64))
            )
            (set-cost (Num 2) 1000)",
        )
        .unwrap();

    egraph
        .parse_and_run_program(None, "(set-cost (Num 2) 1000)")
        .unwrap();

    let result = egraph.parse_and_run_program(None, "(set-cost (Num 2) 1)");
    assert!(result.is_err());
}

#[test]
fn test_extract_set_cost_decls() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            "(with-dynamic-cost
                (datatype E (Add E E) (Sub E E :cost 200) (Num i64))
                (constructor Mul (E E) E :cost 100)
                (datatype*
                  (E2 (Add2 E2 E2) (Sub2 E2 E2 :cost 200) (List VecE2) (Num2 i64))
                  (sort VecE2 (Vec E2))
                )
                (constructor Mul2 (E2 E2) E2)
            )
            (set-cost (Num 2) 1000)
            (set-cost (Num2 2) 1000)
            (set-cost (Mul (Num 2) (Num 2)) 1000)
            (set-cost (Sub2 (Num2 2) (Num2 2)) 1000)",
        )
        .unwrap();
}

#[test]
fn test_multi_extract_two_variants_two_terms() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let result = egraph
        .parse_and_run_program(
            None,
            "
        (with-dynamic-cost
            (datatype E (Add E E) (Mul E E) (Num i64))
        )

        (union (Num 2) (Add (Num 1) (Num 1)))
        (union (Num 2) (Mul (Num 1) (Num 2)))

        (union (Num 4) (Add (Num 2) (Num 2)))
        (union (Num 4) (Mul (Num 2) (Num 2)))

        (multi-extract 2 (Num 2) (Num 4))",
        )
        .unwrap();

    assert_eq!(result.len(), 1);
    let output = result[0].to_string();
    assert!(output.contains("(Num 2)"));
    assert!(output.contains("(Add (Num 1) (Num 1))") || output.contains("(Mul (Num 1) (Num 2))"));
    assert!(output.contains("(Num 4)"));
    assert!(output.contains("(Add (Num 2) (Num 2))") || output.contains("(Mul (Num 2) (Num 2))"));
}

#[test]
fn test_multi_extract_single_variant_minimal_cost() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let result = egraph
        .parse_and_run_program(
            None,
            "
        (with-dynamic-cost
            (datatype E (Add E E :cost 3) (Mul E E :cost 10) (Num i64 :cost 1))
        )

        (union (Num 5) (Add (Num 2) (Num 3)))
        (union (Num 5) (Mul (Num 1) (Num 5)))
        (union (Add (Num 5) (Num 5)) (Mul (Num 2) (Num 5)))

        (multi-extract 1 (Mul (Num 2) (Num 5)))",
        )
        .unwrap();

    assert_eq!(result.len(), 1);
    let output = result[0].to_string();
    assert!(output.contains("(Add (Num 5) (Num 5))"));
    assert!(!output.contains("Mul"));
}

#[test]
fn test_print_table_stats() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let result = egraph
        .parse_and_run_program(
            None,
            "
        (datatype E (Add E E) (Num i64))
        (Add (Num 1) (Num 2))
        (Add (Num 1) (Num 3))
        (print-table-stats Add)",
        )
        .unwrap();

    assert_eq!(result.len(), 1);
    let output = result[0].to_string();

    assert!(output.contains("Add"), "missing table name: {output}");
    assert!(output.contains("(size 2)"), "missing size: {output}");
    assert!(
        output.contains("(columns"),
        "missing columns section: {output}"
    );
    // Both rows share (Num 1) in column 0; col 1 and the output column each
    // have two distinct eclasses.
    assert!(output.contains("(0 E 1)"), "wrong col 0 stats: {output}");
    assert!(output.contains("(1 E 2)"), "wrong col 1 stats: {output}");
    assert!(
        output.contains("(2 E 2)"),
        "wrong output col stats: {output}"
    );
    assert!(
        output.contains("(out-degrees"),
        "missing out-degrees section: {output}"
    );
    // (output -> combined inputs) pair is only emitted when n_inputs >= 2,
    // which Add satisfies; its target is the tuple "(0 1)".
    assert!(
        output.contains("(2 (0 1)"),
        "missing combined-input out-degree: {output}"
    );
    assert!(output.contains("(median "), "missing median stat: {output}");
}

#[test]
fn test_print_table_stats_all_tables() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let result = egraph
        .parse_and_run_program(
            None,
            "
        (datatype E (Add E E) (Num i64))
        (Add (Num 1) (Num 2))
        (print-table-stats)",
        )
        .unwrap();

    assert_eq!(result.len(), 1);
    let output = result[0].to_string();
    assert!(output.contains("Add"), "missing Add: {output}");
    assert!(output.contains("Num"), "missing Num: {output}");
}

#[test]
fn test_print_table_stats_unknown_table_errors() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    let result = egraph.parse_and_run_program(None, "(print-table-stats DoesNotExist)");
    assert!(result.is_err());
}

#[test]
fn test_multi_extract_with_set_cost() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let result = egraph
        .parse_and_run_program(
            None,
            "
        (with-dynamic-cost
            (datatype E (Add E E) (Mul E E) (Num i64))
        )

        (union (Num 10) (Add (Num 5) (Num 5)))
        (union (Num 10) (Mul (Num 2) (Num 5)))

        (union (Num 6) (Add (Num 3) (Num 3)))
        (union (Num 6) (Mul (Num 2) (Num 3)))

        (set-cost (Add (Num 5) (Num 5)) 1)
        (set-cost (Add (Num 3) (Num 3)) 1)

        (set-cost (Mul (Num 2) (Num 5)) 1000)
        (set-cost (Mul (Num 2) (Num 3)) 1000)

        (multi-extract 2 (Num 10) (Num 6))",
        )
        .unwrap();

    assert_eq!(result.len(), 1);
    let output = result[0].to_string();
    assert!(output.contains("(Add (Num 5) (Num 5))"));
    assert!(output.contains("(Add (Num 3) (Num 3))"));
    assert!(!output.contains("Mul"));
}

#[test]
fn test_keep_best_basic() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            r#"
        (datatype Math (Num i64) (Add Math Math))
        (relation Target (Math))

        ; put two nodes in the same eclass
        (union (Num 2) (Add (Num 1) (Num 1)))

        ; record what we care about
        (Target (Num 2))
        "#,
        )
        .unwrap();

    // Before keep-best: both Num and Add tables have entries, Target has 1 row.
    assert_eq!(egraph.get_size("Num"), 2);
    assert_eq!(egraph.get_size("Add"), 1);
    assert_eq!(egraph.get_size("Target"), 1);

    // Run keep-best on the Target relation.
    egraph
        .parse_and_run_program(None, r#"(keep-best "Target")"#)
        .unwrap();

    // After keep-best: Target still has exactly 1 row,
    // and it contains a constructor term that can be extracted.
    assert_eq!(egraph.get_size("Target"), 1);
    assert_eq!(egraph.get_size("Num"), 1);

    let result = egraph
        .parse_and_run_program(None, "(print-function Target 100)")
        .unwrap();
    let output = result[0].to_string();
    assert!(output.contains("Num") && !output.contains("Add"));
}

#[test]
fn test_keep_best_clears_other_tables() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            r#"
        (datatype Math (Num i64) (Add Math Math))
        (relation Target (Math))
        (Num 42)
        (Add (Num 1) (Num 2))
        (Target (Num 42))
        "#,
        )
        .unwrap();

    let before_num = egraph.get_size("Num");
    let before_add = egraph.get_size("Add");
    assert!(before_num >= 3); // Num 42, Num 1, Num 2
    assert_eq!(before_add, 1);
    assert_eq!(egraph.get_size("Target"), 1);

    egraph
        .parse_and_run_program(None, r#"(keep-best "Target")"#)
        .unwrap();

    // After keep-best, Add table (not referenced by Target) should be empty.
    // The Num table entry for 42 should be re-inserted (it's reachable via Target).
    // Num 1 and Num 2 are not reachable from Target, so they should be gone.
    assert_eq!(egraph.get_size("Add"), 0);
    assert_eq!(egraph.get_size("Target"), 1);
    assert_eq!(egraph.get_size("Num"), 1); // only Num 42 is kept
}

#[test]
fn test_top_level_let_scheduler_persists_on_the_egraph() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            r#"
        (ruleset copy)
        (ruleset grow)
        (relation R (i64))
        (relation S (i64))
        (relation Seed ())
        (R 0)
        (R 1)
        (R 2)
        (Seed)
        (rule ((R x)) ((S x)) :ruleset copy :name "copy")
        (rule ((Seed)) ((R 3)) :ruleset grow :name "grow")
        "#,
        )
        .unwrap();

    let_backoff(&mut egraph);

    egraph
        .parse_and_run_program(
            None,
            r#"
        (run-schedule
          (seq
            (run-with bo copy)
            (run grow)
            (run-with bo copy)))
        "#,
        )
        .unwrap();

    assert_eq!(
        eval_get_size(&mut egraph, &["S"]),
        3,
        "ordinary back-off should replay the queued copy backlog and should not depend on fresh rematching"
    );
}

#[test]
fn test_top_level_let_scheduler_survives_egraph_clone() {
    let mut original = new_copy_egraph();
    let_backoff(&mut original);

    let mut cloned = original.clone();
    run_bo_copy(&mut cloned);
    run_bo_copy(&mut original);

    assert_eq!(eval_get_size(&mut cloned, &["S"]), 1);
    assert_eq!(eval_get_size(&mut original, &["S"]), 1);
}

#[test]
fn test_top_level_let_scheduler_redeclaration_returns_error() {
    let mut egraph = new_copy_egraph();
    let_backoff(&mut egraph);

    let err = egraph
        .parse_and_run_program(
            None,
            "(let-scheduler bo (back-off :match-limit 10 :ban-length 1))",
        )
        .unwrap_err();

    assert!(err.to_string().contains("Scheduler bo already exists"));

    run_bo_copy(&mut egraph);
    assert_eq!(eval_get_size(&mut egraph, &["S"]), 1);
}

#[test]
fn test_let_scheduler_unknown_scheduler_returns_error() {
    let mut egraph = new_copy_egraph();
    let err = egraph
        .parse_and_run_program(None, "(let-scheduler bo (missing-scheduler))")
        .unwrap_err();
    assert!(
        err.to_string()
            .contains("Unknown scheduler: missing-scheduler")
    );

    let mut egraph = new_copy_egraph();
    let err = egraph
        .parse_and_run_program(
            None,
            "(run-schedule (let-scheduler bo (missing-scheduler)))",
        )
        .unwrap_err();
    assert!(
        err.to_string()
            .contains("Unknown scheduler: missing-scheduler")
    );
}

#[test]
fn test_top_level_let_scheduler_invalidates_after_push_pop() {
    let mut egraph = new_copy_egraph();

    for _ in 0..2 {
        egraph.parse_and_run_program(None, "(push)").unwrap();
        let_backoff(&mut egraph);
        run_bo_copy(&mut egraph);
        assert_eq!(eval_get_size(&mut egraph, &["S"]), 1);
        egraph.parse_and_run_program(None, "(pop)").unwrap();
        assert_eq!(eval_get_size(&mut egraph, &["S"]), 0);

        let err = egraph
            .parse_and_run_program(None, "(run-schedule (run-with bo copy))")
            .unwrap_err();
        assert!(err.to_string().contains("Unknown scheduler: bo"));
    }
}

#[test]
fn test_top_level_let_scheduler_survives_pop_when_declared_before_push() {
    let mut egraph = new_copy_egraph();
    let_backoff(&mut egraph);
    egraph.parse_and_run_program(None, "(push)").unwrap();
    run_bo_copy(&mut egraph);
    assert_eq!(eval_get_size(&mut egraph, &["S"]), 1);

    egraph.parse_and_run_program(None, "(pop)").unwrap();
    assert_eq!(eval_get_size(&mut egraph, &["S"]), 0);

    run_bo_copy(&mut egraph);
    assert_eq!(eval_get_size(&mut egraph, &["S"]), 1);
}

#[test]
fn test_extract_missing_expression_returns_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let err = egraph.parse_and_run_program(None, "(extract)").unwrap_err();

    assert!(
        err.to_string()
            .contains("extract expects an expression and optional variant count")
    );
}

#[test]
fn test_extract_extra_arguments_return_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let err = egraph
        .parse_and_run_program(None, "(extract 0 1 2)")
        .unwrap_err();

    assert!(
        err.to_string()
            .contains("extract expects at most two arguments")
    );
}

#[test]
fn test_extract_negative_variants_returns_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(None, "(datatype E (Num i64))")
        .unwrap();

    let err = egraph
        .parse_and_run_program(None, "(extract (Num 1) -1)")
        .unwrap_err();

    assert!(err.to_string().contains("negative number of variants"));
}

#[test]
fn test_extract_zero_variants_preserves_best_extract_behavior() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let result = egraph
        .parse_and_run_program(
            None,
            "
        (with-dynamic-cost
            (datatype E (Add E E :cost 10) (Num i64 :cost 1))
        )
        (union (Num 2) (Add (Num 1) (Num 1)))
        (extract (Num 2) 0)",
        )
        .unwrap();

    assert_eq!(result.len(), 1);
    assert_eq!(result[0].to_string(), "(Num 2)\n");
}

#[test]
fn test_invalid_run_schedule_returns_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let err = egraph
        .parse_and_run_program(None, "(run-schedule (run 1))")
        .unwrap_err();

    assert!(
        err.to_string()
            .contains("Expected ruleset name or :until clause")
    );
}

#[test]
fn test_unknown_scheduler_returns_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let err = egraph
        .parse_and_run_program(None, "(run-schedule (let-scheduler bo (not-a-scheduler)))")
        .unwrap_err();

    assert!(err.to_string().contains("Unknown scheduler"));
}

#[test]
fn test_unknown_scheduler_binding_returns_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let err = egraph
        .parse_and_run_program(None, "(run-schedule (run-with bo))")
        .unwrap_err();

    assert!(err.to_string().contains("Unknown scheduler"));
}

#[test]
fn test_invalid_scheduler_tags_return_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let err = egraph
        .parse_and_run_program(
            None,
            r#"(run-schedule (let-scheduler bo (back-off "x" 1)))"#,
        )
        .unwrap_err();

    assert!(err.to_string().contains("Invalid scheduler tag name"));
}

#[test]
fn test_odd_scheduler_tags_return_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let err = egraph
        .parse_and_run_program(
            None,
            "(run-schedule (let-scheduler bo (back-off :match-limit)))",
        )
        .unwrap_err();

    assert!(err.to_string().contains("key/value pairs"));
}

#[test]
fn test_duplicate_scheduler_tags_return_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let err = egraph
        .parse_and_run_program(
            None,
            "(run-schedule (let-scheduler bo (back-off :match-limit 1 :match-limit 2)))",
        )
        .unwrap_err();

    assert!(err.to_string().contains("already exists"));
}

#[test]
fn test_invalid_scheduler_config_returns_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let err = egraph
        .parse_and_run_program(
            None,
            r#"(run-schedule (let-scheduler bo (back-off :match-limit "x")))"#,
        )
        .unwrap_err();

    assert!(err.to_string().contains(":match-limit"));
}

#[test]
fn test_negative_scheduler_config_returns_error_instead_of_panicking() {
    for tag in [":match-limit", ":ban-length"] {
        let mut egraph = egglog_experimental::new_experimental_egraph();
        let err = egraph
            .parse_and_run_program(
                None,
                &format!("(run-schedule (let-scheduler bo (back-off {tag} -1)))"),
            )
            .unwrap_err();

        assert!(err.to_string().contains("non-negative"));
    }
}

#[test]
fn test_multi_extract_bad_arity_returns_error_instead_of_panicking() {
    for program in ["(multi-extract)", "(multi-extract 1)"] {
        let mut egraph = egglog_experimental::new_experimental_egraph();

        let err = egraph.parse_and_run_program(None, program).unwrap_err();

        assert!(
            err.to_string()
                .contains("multi-extract expects at least a variant count and one expression"),
            "unexpected error for {program}: {err}"
        );
    }
}

fn add_copy_backoff_program(egraph: &mut egglog::EGraph) {
    egraph
        .parse_and_run_program(
            None,
            r#"
        (ruleset copy)
        (relation R (i64))
        (relation S (i64))
        (R 0)
        (R 1)
        (R 2)
        (R 3)
        (rule ((R x)) ((S x)) :ruleset copy :name "copy")
        "#,
        )
        .unwrap();
}

fn only_run_report(outputs: &[CommandOutput]) -> &egglog_reports::RunReport {
    match outputs {
        [CommandOutput::RunSchedule(report)] => report,
        other => panic!("expected one RunSchedule output, got {other:?}"),
    }
}

#[test]
fn test_multi_extract_negative_variants_returns_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(None, "(datatype E (Num i64))")
        .unwrap();

    let err = egraph
        .parse_and_run_program(None, "(multi-extract -1 (Num 1))")
        .unwrap_err();

    assert!(err.to_string().contains("negative number of variants"));
}

#[test]
fn test_multi_extract_zero_variants_returns_error_instead_of_extracting() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(None, "(datatype E (Num i64))")
        .unwrap();

    let err = egraph
        .parse_and_run_program(None, "(multi-extract 0 (Num 1))")
        .unwrap_err();

    assert!(err.to_string().contains("positive number of variants"));
}

#[test]
fn test_backoff_run_schedule_should_not_report_progress_without_egraph_updates() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    add_copy_backoff_program(&mut egraph);

    let outputs = egraph
        .parse_and_run_program(
            None,
            r#"
        (run-schedule
          (let-scheduler bo (back-off :match-limit 1 :ban-length 3))
          (run-with bo copy))
        "#,
        )
        .unwrap();

    let report = only_run_report(&outputs);
    assert_eq!(egraph.get_size("S"), 0);
    assert!(
        !report.updated,
        "banning work in the scheduler is not database progress"
    );
    assert!(
        !report.can_stop,
        "the scheduler still has deferred work after the ban"
    );
}

#[test]
fn test_saturate_continues_until_scheduler_can_stop_after_no_progress_ban() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    add_copy_backoff_program(&mut egraph);

    let outputs = egraph
        .parse_and_run_program(
            None,
            r#"
        (run-schedule
          (let-scheduler bo (back-off :match-limit 1 :ban-length 3))
          (saturate (run-with bo copy)))
        "#,
        )
        .unwrap();

    let report = only_run_report(&outputs);
    assert_eq!(
        egraph.get_size("S"),
        4,
        "saturate should keep running while the scheduler reports deferred work"
    );
    assert!(
        report.updated,
        "the eventual copy applications should be reported as database progress"
    );
}

#[test]
fn test_schedule_expr_eval() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            r#"
        (datatype Math (Num i64) (Add Math Math))
        (relation Target (Math))
        (union (Num 2) (Add (Num 1) (Num 1)))
        (Target (Num 2))
        "#,
        )
        .unwrap();

    // `(eval <expr>)` evaluates an expression as a schedule step in the full
    // read/write (FullState) context. Here it calls the `get-size!` reading
    // primitive, which is only admissible because of that full context.
    egraph
        .parse_and_run_program(
            None,
            r#"
        (run-schedule
          (eval (get-size!)))
        "#,
        )
        .unwrap();

    // `(eval <expr>)` also adds constructor terms to the e-graph, just like a
    // top-level expression would.
    let before = egraph.get_size("Add");
    egraph
        .parse_and_run_program(
            None,
            r#"
              (run-schedule
                (eval (Add (Num 3) (Num 4))))
              "#,
        )
        .unwrap();
    assert_eq!(
        egraph.get_size("Add"),
        before + 1,
        "(eval ...) should add the new Add term to the e-graph"
    );
}

#[test]
fn test_schedule_user_defined_command() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            r#"
        (datatype Math (Num i64) (Add Math Math))
        (relation Target (Math))
        (union (Num 2) (Add (Num 1) (Num 1)))
        (Target (Num 2))
        "#,
        )
        .unwrap();

    // keep-best as a step inside run-schedule
    egraph
        .parse_and_run_program(
            None,
            r#"
        (run-schedule
          (keep-best "Target"))
        "#,
        )
        .unwrap();

    assert_eq!(egraph.get_size("Target"), 1);
}

#[test]
fn test_schedule_repeat_push_pop_print_size() {
    use egglog::CommandOutput;
    let mut egraph = egglog_experimental::new_experimental_egraph();

    // Commutativity and both directions of associativity for Add.
    egraph
        .parse_and_run_program(
            None,
            r#"
        (datatype Math (Num i64) (Add Math Math))
        (ruleset math-rules)
        (rewrite (Add a b) (Add b a) :ruleset math-rules)
        (rewrite (Add (Add a b) c) (Add a (Add b c)) :ruleset math-rules)
        (rewrite (Add a (Add b c)) (Add (Add a b) c) :ruleset math-rules)
        "#,
        )
        .unwrap();

    // Each of 3 outer iterations:
    //   1. push the current (fact-free) state
    //   2. eval a sum-1-to-5 addition chain to add it to the e-graph
    //   3. repeat 5 times: run math-rules one step, then print-size
    //   4. pop back to the fact-free state
    //
    // print-size fires inside the inner repeat, so each outer iteration
    // emits 5 PrintAllFunctionsSize outputs — 15 total.
    let outputs = egraph
        .parse_and_run_program(
            None,
            r#"
        (run-schedule
          (repeat 3
            (push)
            (eval (Add (Add (Add (Add (Num 1) (Num 2)) (Num 3)) (Num 4)) (Num 5)))
            (repeat 5
              (run math-rules)
              (print-size))
            (pop)))
        "#,
        )
        .unwrap();

    // 3 outer iterations × 5 inner steps = 15 PrintAllFunctionsSize outputs,
    // followed by a single RunSchedule.
    let print_size_outputs: Vec<_> = outputs
        .iter()
        .filter(|o| matches!(o, CommandOutput::PrintAllFunctionsSize(_)))
        .collect();
    assert_eq!(
        print_size_outputs.len(),
        15,
        "expected 3 × 5 = 15 print-size outputs, got {}",
        print_size_outputs.len()
    );

    let add_sizes: Vec<usize> = print_size_outputs
        .into_iter()
        .map(|o| match o {
            CommandOutput::PrintAllFunctionsSize(v) => {
                let add = v.iter().find(|(n, _)| n == "Add").map(|(_, s)| *s).unwrap();
                let num = v.iter().find(|(n, _)| n == "Num").map(|(_, s)| *s).unwrap();
                // Num is always 5 (one per distinct literal, shared via e-class).
                assert_eq!(num, 5, "Num size should stay at 5");
                add
            }
            _ => unreachable!(),
        })
        .collect();

    // Expected Add sizes after each of the 5 rule steps, measured within a
    // single outer iteration (the push/pop makes all three groups identical).
    let expected = [14, 50, 137, 182, 180];
    for group in 0..3 {
        for step in 0..5 {
            assert_eq!(
                add_sizes[group * 5 + step],
                expected[step],
                "outer iteration {group}, inner step {step}: unexpected Add size"
            );
        }
    }

    // The last output is always the RunSchedule report.
    assert!(
        matches!(outputs.last().unwrap(), CommandOutput::RunSchedule(_)),
        "last output must be RunSchedule"
    );

    // After the repeat the pop has unwound all facts — the e-graph is back to
    // the state it had after defining the datatype (no concrete tuples).
    assert_eq!(egraph.get_size("Add"), 0);
    assert_eq!(egraph.get_size("Num"), 0);
}

#[test]
fn test_schedule_commands_and_actions() {
    use egglog::CommandOutput;
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            r#"
        (datatype Math (Num i64) (Add Math Math))
        (relation Target (Math))
        (union (Num 2) (Add (Num 1) (Num 1)))
        (Target (Num 2))
        "#,
        )
        .unwrap();

    // print-size inside run-schedule returns a CommandOutput::PrintFunctionSize
    let outputs = egraph
        .parse_and_run_program(
            None,
            r#"
        (run-schedule
          (print-size Target))
        "#,
        )
        .unwrap();

    // outputs should be: [PrintFunctionSize(...), RunSchedule(report)]
    assert!(
        outputs.len() >= 2,
        "expected at least 2 outputs, got {}",
        outputs.len()
    );
    assert!(matches!(outputs[0], CommandOutput::PrintFunctionSize(_)));
    assert!(matches!(
        outputs.last().unwrap(),
        CommandOutput::RunSchedule(_)
    ));

    // extract inside run-schedule
    let outputs = egraph
        .parse_and_run_program(
            None,
            r#"
        (run-schedule
          (extract (Num 2) 0))
        "#,
        )
        .unwrap();
    assert!(
        outputs
            .iter()
            .any(|o| matches!(o, CommandOutput::ExtractBest(..)))
    );

    // union as a schedule step
    egraph
        .parse_and_run_program(
            None,
            r#"
        (run-schedule
          (union (Num 1) (Num 2)))
        "#,
        )
        .unwrap();

    // push/pop as schedule steps
    egraph
        .parse_and_run_program(
            None,
            r#"
        (run-schedule
          (push)
          (pop))
        "#,
        )
        .unwrap();
}
