use std::sync::Arc;

use egglog::{
    CommandOutput,
    ast::{Expr, Literal},
    prelude::{RustSpan, Span},
    scheduler::{Matches, Scheduler},
};

#[derive(Clone, Default)]
struct DelayStopScheduler {
    can_stop_calls: usize,
}

impl Scheduler for DelayStopScheduler {
    fn can_stop(&mut self, _rules: &[&str], _ruleset: &str) -> bool {
        self.can_stop_calls += 1;
        self.can_stop_calls > 1
    }

    fn filter_matches(&mut self, _rule: &str, _ruleset: &str, _matches: &mut Matches) -> bool {
        false
    }
}

fn eval_get_size(egraph: &mut egglog::EGraph, names: &[&str]) -> i64 {
    let span = Span::Rust(Arc::new(RustSpan {
        file: "integration_test",
        line: 0,
        column: 0,
    }));
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

fn run_backoff_copy_grow(scheduler_name: &str) -> i64 {
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

    egraph
        .parse_and_run_program(
            None,
            &format!(
                r#"
        (run-schedule
          (let-scheduler bo ({scheduler_name} :match-limit 2 :ban-length 2))
          (seq
            (run-with bo copy)
            (run grow)
            (run-with bo copy)))
        "#
            ),
        )
        .unwrap();

    eval_get_size(&mut egraph, &["S"])
}

fn run_backoff_copy_grow_with_top_level_scheduler(scheduler_name: &str) -> i64 {
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

    egraph
        .parse_and_run_program(
            None,
            &format!("(let-scheduler bo ({scheduler_name} :match-limit 2 :ban-length 2))"),
        )
        .unwrap();

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

    eval_get_size(&mut egraph, &["S"])
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

    assert_eq!(eval_get_size(&mut egraph, &[]), 0);
    assert_eq!(eval_get_size(&mut egraph, &["MkFoo"]), 0);
    assert_eq!(eval_get_size(&mut egraph, &["MkBar"]), 0);
    assert_eq!(eval_get_size(&mut egraph, &["MkFoo", "MkBar"]), 0);

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

    assert_eq!(eval_get_size(&mut egraph, &[]), 3);
    assert_eq!(eval_get_size(&mut egraph, &["MkFoo"]), 2);
    assert_eq!(eval_get_size(&mut egraph, &["MkBar"]), 1);
    assert_eq!(eval_get_size(&mut egraph, &["MkFoo", "MkBar"]), 3);
    assert_eq!(eval_get_size(&mut egraph, &["Unknown"]), 0);
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
fn test_scheduler_should_not_report_progress_without_egraph_updates() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            r#"
        (ruleset test)
        (relation R (i64))
        (rule ((R x)) ((R x)) :ruleset test :name "noop")
        (R 1)
        (R 2)
        (R 3)
        (R 4)
        "#,
        )
        .unwrap();

    let before = egraph.get_size("R");
    let scheduler_id = egraph.add_scheduler(Box::new(DelayStopScheduler::default()));
    let report = egraph
        .step_rules_with_scheduler(scheduler_id, "test")
        .unwrap();
    let after = egraph.get_size("R");

    assert_eq!(
        before, after,
        "the scheduler chose no matches, so the e-graph should remain unchanged"
    );
    assert!(
        !report.updated,
        "scheduler state alone should not keep saturation alive when the e-graph did not change"
    );
    assert!(
        !report.can_stop,
        "the custom scheduler explicitly deferred work, so can_stop should remain false"
    );
}

#[test]
fn test_backoff_run_schedule_should_not_report_progress_without_egraph_updates() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            r#"
        (ruleset test)
        (relation R (i64))
        (rule ((R x)) ((R x)) :ruleset test :name "noop")
        (R 1)
        (R 2)
        (R 3)
        (R 4)
        "#,
        )
        .unwrap();
    let before = eval_get_size(&mut egraph, &["R"]);
    let outputs = egraph
        .parse_and_run_program(
            None,
            r#"
        (run-schedule
          (let-scheduler bo (back-off :match-limit 1 :ban-length 3))
          (run-with bo test))
        "#,
        )
        .unwrap();
    let after = eval_get_size(&mut egraph, &["R"]);

    let report = match &outputs[0] {
        CommandOutput::RunSchedule(report) => report,
        output => panic!("expected RunSchedule output, got {output:?}"),
    };

    assert_eq!(before, after);
    assert!(
        !report.updated,
        "the back-off scheduler banned the no-op rule without changing the e-graph, so the run should not report database progress"
    );
    assert!(
        !report.can_stop,
        "the back-off scheduler still has deferred work after banning the rule once"
    );
}

#[test]
fn test_backoff_replays_backlog_after_ban_expires() {
    assert_eq!(
        run_backoff_copy_grow("back-off"),
        3,
        "default back-off should replay the queued copy backlog and miss the newly added R 3 row on the next run"
    );
}

#[test]
fn test_backoff_egg_rematches_fresh_after_ban_expires() {
    assert_eq!(
        run_backoff_copy_grow("back-off-fresh"),
        4,
        "back-off-fresh should rematch the rebuilt graph and copy the newly added R 3 row as well"
    );
}

#[test]
fn test_backoff_does_not_match_subsumed_rows() {
    for scheduler_name in ["back-off", "back-off-fresh"] {
        let mut egraph = egglog_experimental::new_experimental_egraph();

        egraph
            .parse_and_run_program(
                None,
                r#"
            (ruleset analysis)
            (ruleset test)
            (datatype Math
              (Add Math Math)
              (Mul Math Math)
              (Num i64))
            (relation Hit (i64))
            (let expr (Add (Mul (Num 0) (Num 1)) (Num 2)))
            (rewrite (Mul (Num 0) x) (Num 0) :subsume :ruleset analysis)
            (rewrite (Add (Num 0) x) x :subsume :ruleset analysis)
            (rule ((= e (Add (Mul (Num a) x) (Num b)))) ((Hit a)) :ruleset test :name "hit-subsumed-affine")
            (run-schedule (saturate (run analysis)))
            "#,
            )
            .unwrap();

        egraph
            .parse_and_run_program(
                None,
                &format!(
                    r#"
            (run-schedule
              (let-scheduler bo ({scheduler_name} :match-limit 10 :ban-length 1))
              (run-with bo test))
            "#
                ),
            )
            .unwrap();

        assert_eq!(
            eval_get_size(&mut egraph, &["Hit"]),
            0,
            "{scheduler_name} should not fire on subsumed rows"
        );
    }
}

#[test]
fn test_top_level_let_scheduler_persists_on_the_egraph() {
    assert_eq!(
        run_backoff_copy_grow_with_top_level_scheduler("back-off-fresh"),
        4,
        "top-level let-scheduler should keep the scheduler in the egraph registry so later run-schedule calls can reuse it"
    );
}

#[test]
fn test_invalid_run_schedule_returns_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let err = egraph
        .parse_and_run_program(None, "(run-schedule (run 1))")
        .unwrap_err();

    assert!(err.to_string().contains("Invalid schedule"));
}

#[test]
fn test_invalid_scheduler_tags_return_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let err = egraph
        .parse_and_run_program(None, r#"(let-scheduler bo (back-off :match-limit "x"))"#)
        .unwrap_err();

    assert!(err.to_string().contains(":match-limit"));
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
