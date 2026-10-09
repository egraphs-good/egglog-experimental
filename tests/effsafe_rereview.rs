//! Boundary pricing, deep pure terms, write primitives, and placeholder validation.

use egglog::ast::Expr;
use egglog::extract::{DefaultCost, TreeCostModel};
use egglog::{ArcSort, CommandOutput, EGraph, Enode, Function, Value, span};
use egglog_experimental::{
    DynamicCostModel, effsafe_state, new_experimental_egraph, set_effsafe_cost_models,
};

/// A small effectful language: `Print` and `Arg` carry the state, `Read`
/// is a pure value that depends on a state, `If` and `Loop` have subregions.
const LANG: &str = r#"
(datatype Expr
  (Arg)
  (Num i64)
  (Add Expr Expr)
  (Read Expr)
  (Print Expr Expr)
  (If Expr Expr Expr Expr :regions (2 3))
  (Loop Expr Expr :regions (1)))
(constructor Func (String Expr) Expr)
(rule ((= e (Arg))) ((set-effectful Expr e)))
(rule ((= e (Print v s))) ((set-effectful Expr e)))
(rule ((= e (If p s t els))) ((set-effectful Expr e)))
(rule ((= e (Loop s b))) ((set-effectful Expr e)))
(rule ((= e (Func n b))) ((set-effectful Expr e)))
"#;

/// Run `program` after the language prelude on an e-graph prepared by
/// `setup` and return the outputs.
fn run(program: &str, setup: impl FnOnce(&mut EGraph)) -> Vec<CommandOutput> {
    let mut egraph = new_experimental_egraph();
    setup(&mut egraph);
    egraph
        .parse_and_run_program(None, &format!("{LANG}\n{program}"))
        .unwrap_or_else(|err| panic!("program failed: {err}"))
}

fn terms_of(outputs: &[CommandOutput]) -> Vec<Vec<String>> {
    outputs
        .iter()
        .filter_map(|output| match output {
            CommandOutput::ExtractBest(termdag, _, term) => Some(vec![termdag.to_string(*term)]),
            CommandOutput::PrintFunction(_, termdag, terms, _) => {
                Some(terms.iter().map(|(t, _)| termdag.to_string(*t)).collect())
            }
            _ => None,
        })
        .collect()
}

/// Run `program` after the language prelude and return the terms of every
/// effsafe extraction, as strings.
fn extract(program: &str) -> Vec<Vec<String>> {
    terms_of(&run(program, |_| ()))
}

fn extract_one(program: &str) -> String {
    let mut all = extract(program);
    assert_eq!(all.len(), 1, "expected one extraction");
    let mut terms = all.pop().unwrap();
    assert_eq!(terms.len(), 1, "expected one root");
    terms.pop().unwrap()
}

fn extract_error_with(program: &str, setup: impl FnOnce(&mut EGraph)) -> String {
    let mut egraph = new_experimental_egraph();
    setup(&mut egraph);
    match egraph.parse_and_run_program(None, &format!("{LANG}\n{program}")) {
        Ok(outputs) => panic!("program should have failed, got {:?}", terms_of(&outputs)),
        Err(err) => err.to_string(),
    }
}

/// Stands in for every value of sort `sort`; see `EffsafeConfig::placeholders`.
fn placeholder(sort: &str, head: &str) -> impl FnOnce(&mut EGraph) {
    let (sort, head) = (sort.to_string(), head.to_string());
    move |egraph: &mut EGraph| {
        effsafe_state(egraph)
            .config
            .placeholders
            .insert(sort, Expr::Call(span!(), head, vec![]));
    }
}

/// A boundary cost model that does not charge `Loop` bodies at all, so that a
/// loop whose body leads back to the loop itself looks cheapest.
struct FreeLoops;

impl TreeCostModel<DefaultCost> for FreeLoops {
    type EnodeCost = (String, DefaultCost);
    type ContainerCost = DefaultCost;

    fn base_value_cost(&self, _: &EGraph, _: &ArcSort, _: Value) -> DefaultCost {
        1
    }

    fn enode_cost(&self, egraph: &EGraph, func: &Function, enode: &Enode<'_>) -> Self::EnodeCost {
        use egglog::extract::DagCostModel;
        (
            func.name().to_string(),
            DynamicCostModel.enode_cost(egraph, func, enode),
        )
    }

    fn container_cost(&self, _: &EGraph, _: &ArcSort, _: Value) -> DefaultCost {
        1
    }

    fn fold_enode_cost(
        &self,
        (name, own): Self::EnodeCost,
        child_costs: &[DefaultCost],
    ) -> DefaultCost {
        if name == "Loop" {
            own
        } else {
            child_costs
                .iter()
                .fold(own, |acc, c| acc.saturating_add(*c))
        }
    }

    fn fold_container_cost(&self, own: DefaultCost, element_costs: &[DefaultCost]) -> DefaultCost {
        element_costs
            .iter()
            .fold(own, |acc, c| acc.saturating_add(*c))
    }
}

#[test]
fn rereview_placeholder_requires_constructor() {
    let err = extract_error_with(
        r#"
      (datatype Ctx (NoCtx))
      (function MissingCtx () Ctx :merge old)
      (constructor Leaf (Ctx) Expr)
      (let $root (Print (Leaf (NoCtx)) (Arg)))
      (run 5)
      (extract $root :extractor effsafe)
    "#,
        placeholder("Ctx", "MissingCtx"),
    );
    assert!(err.contains("constructor"), "{err}");
}

#[test]
fn rereview_set_effectful_write_primitive_let() {
    let program = r#"
      (constructor Next (Expr) Expr)
      (primitive next (Expr) Expr (Next _0))
      (rule ((= e (Arg)))
         ((let b (next e))
          (set-effectful Expr b)))
      (let $s0 (Arg))
      (run 3)
      (extract $s0 :extractor effsafe)
    "#;
    // The ordinary action typechecker accepts this with the generated relation.
    assert_eq!(
        extract_one(&program.replace("(set-effectful Expr b)", "(effsafe_effectful_Expr b)")),
        "(Arg)"
    );
    assert_eq!(extract_one(program), "(Arg)");
}

#[test]
fn rereview_pure_boundary_stack_depth() {
    // Run the extraction in a separate process so stack overflow is a normal
    // failing assertion rather than aborting the entire regression suite.
    const CHILD: &str = "EFFSAFE_REVIEW_DEEP_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "rereview_pure_boundary_stack_depth",
                "--nocapture",
            ])
            .env(CHILD, "1")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "child failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        return;
    }
    let mut program =
        String::from("(constructor Box (Expr) Expr :regions (0))\n(let $v0 (Num 0))\n");
    for i in 1..=6000 {
        program.push_str(&format!("(let $v{i} (Box $v{}))\n", i - 1));
    }
    program.push_str(
        "(let $root (Print $v6000 (Arg)))\n(run 5)\n(extract $root :extractor effsafe)\n",
    );
    let outputs = run(&program, |_| ());
    assert!(
        outputs
            .iter()
            .any(|out| matches!(out, CommandOutput::ExtractBest(..)))
    );
}

struct ExpensiveChoose;
impl TreeCostModel<DefaultCost> for ExpensiveChoose {
    type EnodeCost = (String, DefaultCost);
    type ContainerCost = DefaultCost;
    fn base_value_cost(&self, eg: &EGraph, sort: &ArcSort, value: Value) -> DefaultCost {
        FreeLoops.base_value_cost(eg, sort, value)
    }
    fn enode_cost(&self, eg: &EGraph, func: &Function, enode: &Enode<'_>) -> Self::EnodeCost {
        FreeLoops.enode_cost(eg, func, enode)
    }
    fn container_cost(&self, eg: &EGraph, sort: &ArcSort, value: Value) -> DefaultCost {
        FreeLoops.container_cost(eg, sort, value)
    }
    fn fold_enode_cost(
        &self,
        (name, own): Self::EnodeCost,
        children: &[DefaultCost],
    ) -> DefaultCost {
        children
            .iter()
            .fold(if name == "Choose" { 1_000_000 } else { own }, |s, c| {
                s.saturating_add(*c)
            })
    }
    fn fold_container_cost(&self, own: DefaultCost, children: &[DefaultCost]) -> DefaultCost {
        FreeLoops.fold_container_cost(own, children)
    }
}

#[test]
fn rereview_pure_search_uses_boundary_model() {
    let program = r#"
       (constructor Choose (Expr) Expr :regions (0))
       (constructor Alt () Expr :cost 10)
       (let $v (Choose (Num 0)))
       (union $v (Alt))
       (let $root (Print $v (Arg)))
       (run 5)
       (extract $root :extractor effsafe)
    "#;
    // With the default cost model Choose really is cheaper.
    assert_eq!(extract_one(program), "(Print (Choose (Num 0)) (Arg))");
    // Under the custom model Choose costs one million; Alt still costs 10.
    let outputs = run(program, |eg| {
        set_effsafe_cost_models(eg, DynamicCostModel, ExpensiveChoose)
    });
    let (term, cost) = outputs
        .iter()
        .find_map(|out| match out {
            CommandOutput::ExtractBest(dag, cost, term) => Some((dag.to_string(*term), *cost)),
            _ => None,
        })
        .unwrap();
    assert_eq!(
        cost, 12,
        "selected {term}, ignoring the custom boundary cost"
    );
    assert_eq!(term, "(Print (Alt) (Arg))");
}
