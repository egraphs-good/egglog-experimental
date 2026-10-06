//! Regression tests from the fourth review of the effect-safe extractor
//! (egglog-experimental PR 77): discounted boundary folds that close a cycle,
//! `:regions` children priced independently of in-region sharing, and
//! `set-effectful` on write primitives with any output sort or after lets of
//! base sorts.

use egglog::extract::{DefaultCost, TreeCostModel};
use egglog::{ArcSort, CommandOutput, EGraph, Enode, Function, Value};
use egglog_experimental::{DynamicCostModel, new_experimental_egraph, set_effsafe_cost_models};

const LANG: &str = r#"
  (datatype Expr (Arg) (Print Expr Expr))
  (rule ((= e (Arg))) ((set-effectful e)))
  (rule ((= e (Print v s))) ((set-effectful e)))
"#;

fn run(program: &str, setup: impl FnOnce(&mut EGraph)) -> Vec<CommandOutput> {
    let mut eg = new_experimental_egraph();
    setup(&mut eg);
    eg.parse_and_run_program(None, &format!("{LANG}\n{program}"))
        .unwrap_or_else(|err| panic!("program failed: {err}"))
}

fn extracted(outputs: Vec<CommandOutput>) -> (String, DefaultCost) {
    outputs
        .into_iter()
        .find_map(|out| match out {
            CommandOutput::ExtractBest(dag, cost, term) => Some((dag.to_string(term), cost)),
            _ => None,
        })
        .expect("an extraction")
}

#[test]
fn review4_primitive_result_sort_not_in_body() {
    let program = r#"
      (datatype Input (InputValue))
      (primitive make-state (Input) Expr (Arg))
      (rule ((= input (InputValue)))
         ((let state (make-state input))
          (set-effectful state)))
      (InputValue)
      (run 3)
      (check (effsafe_effectful_Expr (Arg)))
    "#;
    // The action typechecker knows the declared result sort of this primitive.
    run(
        &program.replace("(set-effectful state)", "(effsafe_effectful_Expr state)"),
        |_| {},
    );
    run(program, |_| {});
}

#[test]
fn review4_top_level_write_primitive_mark() {
    let program = r#"
      (constructor Next (Expr) Expr)
      (primitive make-state (Expr) Expr (Next _0))
      (set-effectful (make-state (Arg)))
      (check (effsafe_effectful_Expr (Next (Arg))))
    "#;
    run(
        &program.replace(
            "(set-effectful (make-state",
            "(effsafe_effectful_Expr (make-state",
        ),
        |_| {},
    );
    run(program, |_| {});
}

#[test]
fn review4_write_primitive_after_base_sort_let() {
    let program = r#"
      (constructor FromInt (i64) Expr)
      (primitive make-state (i64) Expr (FromInt _0))
      (rule ((= e (Arg)))
         ((let n 0)
          (let state (make-state n))
          (set-effectful state)))
      (Arg)
      (run 3)
      (check (effsafe_effectful_Expr (FromInt 0)))
    "#;
    run(
        &program.replace("(set-effectful state)", "(effsafe_effectful_Expr state)"),
        |_| {},
    );
    run(program, |_| {});
}

#[test]
fn review4_pure_boundary_reuse_is_not_free() {
    let program = r#"
      (constructor Big () Expr :cost 100)
      (constructor Wrap (Expr) Expr :regions (0))
      (constructor Alt () Expr :cost 50)
      (let $big (Big))
      (let $choice (Wrap $big))
      (union $choice (Alt))
      (let $s1 (Print $big (Arg)))
      (let $root (Print $choice $s1))
      (run 3)
      (extract $root :extractor effsafe)
    "#;
    // Without a boundary the Big value really can be reused for free.
    let ordinary = extracted(run(&program.replace(" :regions (0)", ""), |_| {}));
    assert_eq!(
        ordinary,
        ("(Print (Wrap (Big)) (Print (Big) (Arg)))".into(), 104)
    );
    // Across a boundary Wrap costs 101, even though Big was used earlier.
    let boundary = extracted(run(program, |_| {}));
    assert_eq!(boundary, ("(Print (Alt) (Print (Big) (Arg)))".into(), 153));
}

struct DiscountBoundary;
impl TreeCostModel<DefaultCost> for DiscountBoundary {
    type EnodeCost = DefaultCost;
    type ContainerCost = DefaultCost;
    fn base_value_cost(&self, _: &EGraph, _: &ArcSort, _: Value) -> DefaultCost {
        1
    }
    fn enode_cost(&self, eg: &EGraph, f: &Function, enode: &Enode<'_>) -> DefaultCost {
        use egglog::extract::DagCostModel;
        DynamicCostModel.enode_cost(eg, f, enode)
    }
    fn container_cost(&self, _: &EGraph, _: &ArcSort, _: Value) -> DefaultCost {
        1
    }
    fn fold_enode_cost(&self, own: DefaultCost, children: &[DefaultCost]) -> DefaultCost {
        children.iter().fold(own, |s, c| s.saturating_add(c / 4))
    }
    fn fold_container_cost(&self, own: DefaultCost, children: &[DefaultCost]) -> DefaultCost {
        children.iter().fold(own, |s, c| s.saturating_add(*c))
    }
}

#[test]
fn review4_discounted_pure_cycle_has_finite_alternative() {
    let program = r#"
      (constructor Big () Expr :cost 100)
      (constructor Wrap (Expr) Expr :regions (0))
      (let $v (Big))
      (union $v (Wrap $v))
      (let $root (Print $v (Arg)))
      (run 3)
      (extract $root :extractor effsafe)
    "#;
    // A finite effect-safe extraction exists regardless of the cost model.
    assert_eq!(extracted(run(program, |_| {})).0, "(Print (Big) (Arg))");
    let (_, cost) = extracted(run(program, |eg| {
        set_effsafe_cost_models(eg, DynamicCostModel, DiscountBoundary);
    }));
    assert!(cost <= 102);
}
