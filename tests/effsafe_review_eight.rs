//! Regression tests from the eighth review of the effect-safe extractor
//! (egglog-experimental PR 77): `set-effectful` in rules with wildcards and
//! `set-cost`, with long chains of shared lets, in `:unsafe-seminaive` and
//! non-seminaive e-graphs, and with head actions constraining body and
//! let-bound overloads.

use egglog_experimental::new_experimental_egraph;

const LANG: &str = r#"
  (datatype Expr (Arg) (State Expr) (Pair Expr Expr))
  (relation effsafe_effectful_Expr (Expr))
"#;

fn run(program: &str, seminaive: bool) {
    let mut eg = new_experimental_egraph();
    eg.seminaive = seminaive;
    eg.parse_and_run_program(None, &format!("{LANG}\n{program}"))
        .unwrap_or_else(|err| panic!("program failed: {err}"));
}

fn substitution_program(eval_mode: &str) -> String {
    format!(
        r#"
      (sort Replacements (Map Expr Expr))
      (rule ((= e (Arg)))
        ((let state (unstable-subst (State e) (map-empty)))
         (set-effectful Expr state))
        {eval_mode})
      (Arg)
      (run 1)
      (check (effsafe_effectful_Expr (State (Arg))))
    "#,
    )
}

#[test]
fn review8_unsafe_seminaive_head_has_full_context() {
    let program = substitution_program(":unsafe-seminaive");
    run(
        &program.replace(
            "(set-effectful Expr state)",
            "(effsafe_effectful_Expr state)",
        ),
        true,
    );
    run(&substitution_program(":naive"), true);
    run(&program, true);
}

#[test]
fn review8_global_nonseminaive_head_has_full_context() {
    let program = substitution_program("");
    run(
        &program.replace(
            "(set-effectful Expr state)",
            "(effsafe_effectful_Expr state)",
        ),
        false,
    );
    run(&program, false);
}

#[test]
fn review8_rule_head_can_constrain_body_overloads() {
    let program = r#"
      (sort Exprs (Vec Expr))
      (sort Ints (Vec i64))
      (constructor FromVec (Exprs) Expr)
      (rule ((= xs (vec-empty)))
        ((let state (FromVec xs))
         (set-effectful Expr state)))
      (run 1)
      (check (effsafe_effectful_Expr (FromVec (vec-empty))))
    "#;
    run(
        &program.replace(
            "(set-effectful Expr state)",
            "(effsafe_effectful_Expr state)",
        ),
        true,
    );
    run(program, true);
}

#[test]
fn review8_rule_body_accepts_wildcards() {
    let program = r#"
      (rule ((= state (State _))) ((set-effectful Expr state)))
      (State (Arg))
      (run 1)
      (check (effsafe_effectful_Expr (State (Arg))))
    "#;
    run(
        &program.replace(
            "(set-effectful Expr state)",
            "(effsafe_effectful_Expr state)",
        ),
        true,
    );
    run(program, true);
}

#[test]
fn review8_rule_accepts_set_cost_macro_bindings() {
    let program = r#"
      (with-dynamic-cost (constructor Costed (Expr) Expr))
      (rule ((= e (Arg)))
        ((set-cost (Costed e) 10)
         (set-effectful Expr (Costed e))))
      (Arg)
      (run 1)
      (check (effsafe_effectful_Expr (Costed (Arg))))
    "#;
    run(
        &program.replace(
            "(set-effectful Expr (Costed e))",
            "(effsafe_effectful_Expr (Costed e))",
        ),
        true,
    );
    run(program, true);
}

#[test]
#[cfg(target_os = "linux")]
fn review8_shared_lets_stay_compact() {
    const CHILD: &str = "EFFSAFE_REVIEW8_CHILD";
    if let Ok(mode) = std::env::var(CHILD) {
        let mut program = String::from("(rule ((= e (Arg))) ((let v0 e)\n");
        for i in 1..=22 {
            program.push_str(&format!("(let v{i} (Pair v{} v{}))\n", i - 1, i - 1));
        }
        // Runtime creates only 22 Pair nodes. Cover marking the chain itself
        // and an unrelated value; neither should require expanding the DAG.
        let mark = if mode.starts_with("control") {
            "effsafe_effectful_Expr"
        } else {
            "set-effectful Expr"
        };
        let value = if mode.ends_with("shared") { "v22" } else { "e" };
        program.push_str(&format!(
            "({mark} {value})))\n(Arg)\n(run 1)\n(check (effsafe_effectful_Expr marked))"
        ));
        run(&program, true);
        return;
    }

    let mut failures = Vec::new();
    for mode in [
        "control-unrelated",
        "control-shared",
        "marked-unrelated",
        "marked-shared",
    ] {
        // Keep a regression from exhausting the test host. Both the normal
        // action and marked action receive the same 1 GiB / 30 second limits.
        let output = std::process::Command::new("timeout")
            .args(["30s", "bash", "-c"])
            .arg("ulimit -v 1048576; ulimit -c 0; exec \"$@\"")
            .arg("effsafe-review8")
            .arg(std::env::current_exe().unwrap())
            .args(["--exact", "review8_shared_lets_stay_compact", "--nocapture"])
            .env(CHILD, mode)
            .output()
            .unwrap();
        let failure = format!(
            "{mode} shared-let rule failed under 1 GiB: {}\n{}\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        if mode.starts_with("control") {
            assert!(output.status.success(), "{failure}");
        } else if !output.status.success() {
            failures.push(failure);
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn review8_other_head_actions_constrain_shared_lets() {
    let program = r#"
      (sort Exprs (Vec Expr))
      (sort OtherExprs (Vec Expr))
      (constructor Save (Exprs) Expr)
      (rule ((= e (Arg)))
        ((let values (vec-of e))
         (Save values)
         (let state (vec-get values 0))
         (set-effectful Expr state)))
      (Arg)
      (run 1)
      (check (effsafe_effectful_Expr (Arg)))
    "#;
    run(
        &program.replace(
            "(set-effectful Expr state)",
            "(effsafe_effectful_Expr state)",
        ),
        true,
    );
    run(program, true);
}
