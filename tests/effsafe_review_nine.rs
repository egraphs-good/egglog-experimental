//! Regression tests from the ninth review of the effect-safe extractor
//! (egglog-experimental PR 77): `set-effectful` after another macro's
//! generated declaration, in the real top-level and non-seminaive contexts,
//! and constraining an overloaded expression to eq sorts.
//! primitive contexts, and the eq-sort constraint on marked expressions.

use egglog::constraint::{SimpleTypeConstraint, TypeConstraint};
use egglog::{
    ArcSort, EGraph, Primitive, PurePrim, PureState, ReadPrim, ReadState, Value, WritePrim,
    WriteState,
};
use egglog_ast::span::Span;
use egglog_experimental::new_experimental_egraph;

#[derive(Clone)]
struct Constant {
    sort: ArcSort,
    value: Value,
}

impl Primitive for Constant {
    fn name(&self) -> &str {
        "choose-state"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        SimpleTypeConstraint::new(self.name(), vec![self.sort.clone()], span.clone()).into_box()
    }
}

impl PurePrim for Constant {
    fn apply<'a, 'db>(&self, _: PureState<'a, 'db>, _: &[Value]) -> Option<Value> {
        Some(self.value)
    }
}

impl ReadPrim for Constant {
    fn apply<'a, 'db>(&self, _: ReadState<'a, 'db>, _: &[Value]) -> Option<Value> {
        Some(self.value)
    }
}

impl WritePrim for Constant {
    fn apply<'a, 'db>(&self, _: WriteState<'a, 'db>, _: &[Value]) -> Option<Value> {
        Some(self.value)
    }
}

fn constant(eg: &mut EGraph, expr: &str) -> Constant {
    let expr = eg.parser.get_expr_from_string(None, expr).unwrap();
    let (sort, value) = eg.eval_expr(&expr).unwrap();
    Constant { sort, value }
}

fn with_context_overloads() -> EGraph {
    let mut eg = new_experimental_egraph();
    eg.parse_and_run_program(None, "(datatype Expr (Arg)) (datatype Other (OtherArg))")
        .unwrap();
    let write = constant(&mut eg, "(Arg)");
    let read = constant(&mut eg, "(OtherArg)");
    eg.add_write_primitive(write, None);
    eg.add_read_primitive(read, None);
    eg
}

#[test]
fn review9_mark_fresh_macro_result() {
    let program = r#"
      (datatype Expr (Arg))
      (relation effsafe_effectful_Expr (Expr))
      (relation Seen (Expr))
      (rule ((= e (Arg)))
        ((let state (unstable-fresh! Expr))
         (Seen state)
         (set-effectful state)))
      (Arg)
      (run 1)
      (check (Seen state) (effsafe_effectful_Expr state))
    "#;
    for text in [
        program.replace("(set-effectful state)", "(effsafe_effectful_Expr state)"),
        program.to_owned(),
    ] {
        new_experimental_egraph()
            .parse_and_run_program(None, &text)
            .unwrap_or_else(|err| panic!("program failed: {err}"));
    }
}

#[test]
fn review9_top_level_mark_does_not_choose_write_only_overload() {
    let mut eg = with_context_overloads();
    let expr = eg
        .parser
        .get_expr_from_string(None, "(choose-state)")
        .unwrap();
    // Full-context typing cannot choose between Expr and Other.
    let error = eg.eval_expr(&expr).unwrap_err();
    assert!(
        error.to_string().contains("Failed to infer a type"),
        "{error}"
    );
    let result = eg.parse_and_run_program(None, "(set-effectful (choose-state))");
    if result.is_ok() {
        eg.parse_and_run_program(None, "(check (effsafe_effectful_Expr (Arg)))")
            .unwrap();
    }
    assert!(
        result.is_err(),
        "an ambiguous top-level mark silently selected the Expr write overload"
    );
}

#[test]
fn review9_global_nonseminaive_mark_does_not_choose_write_only_overload() {
    let program = "(rule () ((set-effectful (choose-state))))";
    let mut explicit = with_context_overloads();
    assert!(
        explicit
            .parse_and_run_program(None, "(rule () ((set-effectful (choose-state))) :naive)")
            .is_err()
    );
    let mut eg = with_context_overloads();
    eg.seminaive = false;
    let result = eg.parse_and_run_program(None, program);
    if result.is_ok() {
        eg.parse_and_run_program(None, "(run 1) (check (effsafe_effectful_Expr (Arg)))")
            .unwrap();
    }
    assert!(
        result.is_err(),
        "a globally non-seminaive mark silently selected the Expr write overload"
    );
}

#[test]
fn review9_mark_constrains_an_overload_to_eq_sorts() {
    check_eq_constraint(false);
}

#[test]
fn review9_rule_mark_constrains_an_overload_to_eq_sorts() {
    check_eq_constraint(true);
}

fn check_eq_constraint(in_rule: bool) {
    for mark in ["effsafe_effectful_Expr", "set-effectful"] {
        let mut eg = new_experimental_egraph();
        eg.parse_and_run_program(
            None,
            "(datatype Expr (Arg)) (relation effsafe_effectful_Expr (Expr))",
        )
        .unwrap();
        let eq = constant(&mut eg, "(Arg)");
        let integer = constant(&mut eg, "0");
        eg.add_pure_primitive(eq, None);
        eg.add_pure_primitive(integer, None);
        let action = format!("({mark} (choose-state))");
        let command = if in_rule {
            format!("(rule () ({action})) (run 1)")
        } else {
            action
        };
        eg.parse_and_run_program(
            None,
            &format!("{command} (check (effsafe_effectful_Expr (Arg)))"),
        )
        .unwrap_or_else(|err| panic!("program failed: {err}"));
    }
}
