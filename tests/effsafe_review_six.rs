//! Regression tests from the sixth review of the effect-safe extractor
//! (egglog-experimental PR 77): `set-effectful` typing with an unrelated
//! write primitive in the same rule, and a fixed-signature primitive applied
//! to one overloaded variable many times.

use egglog_experimental::new_experimental_egraph;

const LANG: &str = r#"
  (datatype Expr (Arg) (Print Expr Expr))
  (rule ((= e (Arg))) ((set-effectful e)))
  (rule ((= e (Print v s))) ((set-effectful e)))
"#;

fn run(program: &str) {
    let mut eg = new_experimental_egraph();
    eg.parse_and_run_program(None, &format!("{LANG}\n{program}"))
        .unwrap_or_else(|err| panic!("program failed: {err}"));
}

#[test]
fn review6_primitive_with_many_constrained_arguments() {
    let program = r#"
      (sort Exprs (Vec Expr))
      (sort Ints (Vec i64))
      (constructor FromVec (Exprs) Expr)
      (primitive make-state (Exprs Exprs Exprs Exprs Exprs Exprs Exprs Exprs Exprs)
        Expr (FromVec _0))
      (rule ((= e (Arg)))
        ((let values (vec-empty))
         (let state (make-state values values values values values values values values values))
         (set-effectful state)))
      (Arg)
      (run 3)
      (check (effsafe_effectful_Expr (FromVec (vec-empty))))
    "#;
    // A single vector sort avoids the fallback's combinatorial limit.
    run(&program.replace("(sort Ints (Vec i64))", ""));
    // Normal action typing handles both vector sorts and this fixed signature.
    run(&program.replace("(set-effectful state)", "(effsafe_effectful_Expr state)"));
    run(program);
}

#[test]
fn review6_primitive_inference_preserves_literal_arguments() {
    let program = r#"
      (datatype Other (OtherArg))
      (sort ExprFn (UnstableFn () Expr))
      (sort OtherFn (UnstableFn () Other))
      (constructor Use (Expr) Expr)
      (constructor State () Expr)
      (primitive write (Expr) Expr (Use _0))
      (rule ((= e (Arg)))
        ((let side (write e))
         (let f (unstable-fn "State"))
         (let state (unstable-app f))
         (set-effectful state)))
      (Arg)
      (run 3)
      (check (effsafe_effectful_Expr (State)))
    "#;
    // Without an unrelated write, query typing preserves the literal target.
    run(&program.replace("(let side (write e))", ""));
    run(&program.replace("(set-effectful state)", "(effsafe_effectful_Expr state)"));
    run(program);
}
