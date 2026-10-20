//! Typing independent overloads, many arguments, and nested writes.

use egglog_experimental::new_experimental_egraph;

const LANG: &str = r#"
  (datatype Expr (Arg) (Print Expr Expr))
  (rule ((= e (Arg))) ((set-effectful Expr e)))
  (rule ((= e (Print v s))) ((set-effectful Expr e)))
"#;

fn run(program: &str) {
    let mut eg = new_experimental_egraph();
    eg.parse_and_run_program(None, &format!("{LANG}\n{program}"))
        .unwrap_or_else(|err| panic!("program failed: {err}"));
}

#[test]
fn review7_identical_calls_can_have_different_sorts() {
    let program = r#"
      (sort Exprs (Vec Expr))
      (sort Ints (Vec i64))
      (constructor FromVec (Exprs) Expr)
      (primitive make-state (Exprs Ints) Expr (FromVec _0))
      (rule ((= e (Arg)))
        ((let state (make-state (vec-empty) (vec-empty)))
         (set-effectful Expr state)))
      (Arg)
      (run 3)
      (check (effsafe_effectful_Expr (FromVec (vec-empty))))
    "#;
    // Each call occurrence is resolved independently by the action typechecker.
    run(&program.replace(
        "(set-effectful Expr state)",
        "(effsafe_effectful_Expr state)",
    ));
    run(program);
}

#[test]
fn review7_distinct_arguments_are_constrained_before_cutoff() {
    let mut program = String::from(
        r#"
      (sort Exprs (Vec Expr))
      (sort Ints (Vec i64))
      (constructor FromVec (Exprs) Expr)
      (primitive make-state (Exprs Exprs Exprs Exprs Exprs Exprs Exprs Exprs Exprs)
        Expr (FromVec _0))
      (rule ((= e (Arg))) (
    "#,
    );
    for i in 0..9 {
        program.push_str(&format!("(let v{i} (vec-empty))\n"));
    }
    program.push_str(
        r#"
      (let state (make-state v0 v1 v2 v3 v4 v5 v6 v7 v8))
      (set-effectful Expr state)))
      (Arg)
      (run 3)
      (check (effsafe_effectful_Expr (FromVec (vec-empty))))
    "#,
    );
    run(&program.replace("(sort Ints (Vec i64))", ""));
    run(&program.replace(
        "(set-effectful Expr state)",
        "(effsafe_effectful_Expr state)",
    ));
    run(&program);
}

#[test]
fn review7_literal_constraint_with_nested_write() {
    let program = r#"
      (datatype Other (OtherArg))
      (sort ExprFn (UnstableFn () Expr))
      (sort OtherFn (UnstableFn () Other))
      (constructor Use (Expr) Expr)
      (constructor State (Expr) Expr)
      (primitive write (Expr) Expr (Use _0))
      (rule ((= e (Arg)))
        ((let f (unstable-fn "State" (write e)))
         (let state (unstable-app f))
         (set-effectful Expr state)))
      (Arg)
      (run 3)
      (check (effsafe_effectful_Expr (State (Use (Arg)))))
    "#;
    // Inline and let-bound partial arguments must resolve to the same sort.
    run(&program.replace(
        "(let f (unstable-fn \"State\" (write e)))",
        "(let partial (write e)) (let f (unstable-fn \"State\" partial))",
    ));
    run(&program.replace(
        "(set-effectful Expr state)",
        "(effsafe_effectful_Expr state)",
    ));
    run(program);
}
