//! Regression tests from the fifth review of the effect-safe extractor
//! (egglog-experimental PR 77): ordinary picks closing a cycle through a
//! discounted boundary pick, consumer-constrained typing of overloaded
//! primitives under `set-effectful`, and synthetic mark names.

use egglog::extract::{DefaultCost, TreeCostModel};
use egglog::{ArcSort, CommandOutput, EGraph, Enode, Function, Value};
use egglog_experimental::{DynamicCostModel, new_experimental_egraph, set_effsafe_cost_models};

const LANG: &str = r#"
  (datatype Expr (Arg) (Print Expr Expr))
  (rule ((= e (Arg))) ((set-effectful Expr e)))
  (rule ((= e (Print v s))) ((set-effectful Expr e)))
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
fn review5_mixed_boundary_cycle_has_finite_alternative() {
    let program = r#"
      (constructor A () Expr :cost 200)
      (constructor B () Expr :cost 100)
      (constructor Wrap (Expr) Expr :regions (0))
      (constructor Plain (Expr) Expr)
      (let $a (A))
      (let $b (B))
      (union $a (Wrap $b))
      (union $b (Plain $a))
      (let $root (Print $a (Arg)))
      (run 3)
      (extract $root :extractor effsafe)
    "#;
    assert_eq!(
        extracted(run(program, |_| {})).0,
        "(Print (Wrap (B)) (Arg))"
    );
    let (_, cost) = extracted(run(program, |eg| {
        set_effsafe_cost_models(eg, DynamicCostModel, DiscountBoundary);
    }));
    assert!(cost <= 202);
}

#[test]
fn review5_write_primitive_context_types_empty_container() {
    let program = r#"
      (sort Exprs (Vec Expr))
      (sort Ints (Vec i64))
      (constructor FromVec (Exprs) Expr)
      (primitive make-state (Exprs) Expr (FromVec _0))
      (rule ((= e (Arg)))
        ((let values (vec-empty))
         (let state (make-state values))
         (set-effectful Expr state)))
      (Arg)
      (run 3)
      (check (effsafe_effectful_Expr (FromVec (vec-empty))))
    "#;
    // With only one Vec sort the fallback can guess its type.
    run(&program.replace("(sort Ints (Vec i64))", ""), |_| {});
    run(
        &program.replace(
            "(set-effectful Expr state)",
            "(effsafe_effectful_Expr state)",
        ),
        |_| {},
    );
    run(program, |_| {});
}

#[test]
fn review5_mark_names_do_not_capture_rule_variables() {
    let program = r#"
      (rule ((= e (Arg)) (= __effsafe_mark_0 0))
        ((set-effectful Expr e)))
      (Arg)
      (run 3)
      (check (effsafe_effectful_Expr (Arg)))
    "#;
    run(
        &program.replace("(set-effectful Expr e)", "(effsafe_effectful_Expr e)"),
        |_| {},
    );
    run(
        &program.replace("__effsafe_mark_0", "ordinary_name"),
        |_| {},
    );
    run(program, |_| {});
}
