//! Typing shared overloaded variables and literal-sensitive primitives.

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
         (set-effectful Expr state)))
      (Arg)
      (run 3)
      (check (effsafe_effectful_Expr (FromVec (vec-empty))))
    "#;
    // Compare a single Vec sort with overloaded Vec sorts.
    run(&program.replace("(sort Ints (Vec i64))", ""));
    // Normal action typing handles both vector sorts and this fixed signature.
    run(&program.replace(
        "(set-effectful Expr state)",
        "(effsafe_effectful_Expr state)",
    ));
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
         (set-effectful Expr state)))
      (Arg)
      (run 3)
      (check (effsafe_effectful_Expr (State)))
    "#;
    // Adding an unrelated write must preserve the literal target.
    run(&program.replace("(let side (write e))", ""));
    run(&program.replace(
        "(set-effectful Expr state)",
        "(effsafe_effectful_Expr state)",
    ));
    run(program);
}
