//! Extraction regressions for saturated costs, region cycles, placeholders,
//! and primitive-bound effectful values.

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

/// Like [`extract_one`] but on an e-graph prepared by `setup`.
fn extract_one_with(program: &str, setup: impl FnOnce(&mut EGraph)) -> String {
    let mut all = terms_of(&run(program, setup));
    assert_eq!(all.len(), 1, "expected one extraction");
    let mut terms = all.pop().unwrap();
    assert_eq!(terms.len(), 1, "expected one root");
    terms.pop().unwrap()
}

/// The term and reported cost of the single `extract` in `program`.
fn extract_with_cost(program: &str) -> (String, DefaultCost) {
    let outputs = run(program, |_| ());
    let mut found = outputs.iter().filter_map(|output| match output {
        CommandOutput::ExtractBest(termdag, cost, term) => Some((termdag.to_string(*term), *cost)),
        _ => None,
    });
    let result = found.next().expect("an extraction");
    assert!(found.next().is_none(), "expected one extraction");
    result
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
fn review_region_before_state_with_read() {
    let term = extract_one(
        r#"
      (constructor BodyFirst (Expr Expr) Expr :regions (0))
      (rule ((= e (BodyFirst b s))) ((set-effectful Expr e)))
      (let $s (Print (Num 1) (Arg)))
      (let $l (BodyFirst (Print (Num 2) (Arg)) $s))
      (let $root (Print (Read $s) $l))
      (run 5)
      (extract $root :extractor effsafe)
    "#,
    );
    assert!(term.contains("BodyFirst"));
}

#[test]
fn review_pure_branch_reported_cost() {
    let (term, cost) = extract_with_cost(
        r#"
      (constructor Choose (Expr Expr Expr) Expr :regions (1 2))
      (constructor Big () Expr :cost 100)
      (let $root (Print (Choose (Num 0) (Big) (Big)) (Arg)))
      (run 5)
      (extract $root :extractor effsafe)
    "#,
    );
    assert_eq!(cost, 205, "{term}");
}

#[test]
fn review_saturated_pure_cost() {
    let term = extract_one(
        r#"
      (constructor Big (Expr) Expr :cost 9000000000000000000)
      (let $root (Print (Big (Big (Big (Num 1)))) (Arg)))
      (run 5)
      (extract $root :extractor effsafe)
    "#,
    );
    assert_eq!(term, "(Print (Big (Big (Big (Num 1)))) (Arg))");
}

#[test]
fn review_placeholder_arity_is_checked() {
    let err = extract_error_with(
        r#"
      (datatype Ctx (CtxNum i64))
      (constructor Leaf (Ctx) Expr)
      (let $root (Print (Leaf (CtxNum 1)) (Arg)))
      (run 5)
      (extract $root :extractor effsafe)
    "#,
        placeholder("Ctx", "CtxNum"),
    );
    assert!(!err.is_empty());
}

#[test]
fn review_set_effectful_primitive_let() {
    let term = extract_one(
        r#"
      (sort Exprs (Vec Expr))
      (constructor Next (Expr) Expr)
      (rule ((= e (Arg)))
         ((let v (vec-of (Next e)))
          (let b (vec-get v 0))
          (set-effectful Expr b)))
      (let $s0 (Arg))
      (run 3)
      (extract (Next $s0) :extractor effsafe)
    "#,
    );
    assert_eq!(term, "(Next (Arg))");
}

#[test]
fn review_cyclic_cache_across_roots() {
    use egglog_experimental::effsafe_extract::Roots;
    use egglog_experimental::{EffsafeConfig, extract_effsafe};
    let mut eg = new_experimental_egraph();
    eg.parse_and_run_program(
        None,
        &format!(
            "{LANG}\n{}",
            r#"
      (constructor Expensive (Expr Expr) Expr :cost 100)
      (rule ((= e (Expensive v s))) ((set-effectful Expr e)))
      (let $a (Expensive (Num 1) (Arg)))
      (let $b (Loop (Arg) $a))
      (union $a (Loop (Arg) $b))
      (run 5)
    "#
        ),
    )
    .unwrap();
    let a = eg.eval_expr(&Expr::Var(span!(), "$a".into())).unwrap();
    let b = eg.eval_expr(&Expr::Var(span!(), "$b".into())).unwrap();
    let config = EffsafeConfig {
        regions: [("Loop".into(), vec![1])].into(),
        ..Default::default()
    };
    // Both roots can be extracted individually from exactly the same graph.
    for root in [&a, &b] {
        let single = extract_effsafe(
            &eg,
            &Roots::Values(vec![root.clone()]),
            &config,
            &DynamicCostModel,
            &FreeLoops,
        )
        .unwrap();
        eprintln!(
            "individual root: {}",
            single.termdag.to_string(single.terms[0])
        );
    }
    let result = extract_effsafe(
        &eg,
        &Roots::Values(vec![a, b]),
        &config,
        &DynamicCostModel,
        &FreeLoops,
    )
    .unwrap();
    assert_eq!(result.terms.len(), 2);
}

#[test]
fn review_cyclic_cache_within_single_root() {
    let term = extract_one_with(
        r#"
      (constructor Expensive (Expr Expr) Expr :cost 100)
      (rule ((= e (Expensive v s))) ((set-effectful Expr e)))
      (let $a (Expensive (Num 1) (Arg)))
      (let $b (Loop (Arg) $a))
      (union $a (Loop (Arg) $b))
      (let $root (If (Num 0) (Arg) $a $b))
      (run 5)
      (extract $root :extractor effsafe)
    "#,
        |eg| set_effsafe_cost_models(eg, DynamicCostModel, FreeLoops),
    );
    assert!(term.contains("Expensive"));
}
