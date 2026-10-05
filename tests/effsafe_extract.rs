//! Effect-safe extraction (`extract :extractor effsafe`): the extracted terms are checked
//! against expected strings, which the `.egg` file harness cannot do.

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
(rule ((= e (Arg))) ((set-effectful e)))
(rule ((= e (Print v s))) ((set-effectful e)))
(rule ((= e (If p s t els))) ((set-effectful e)))
(rule ((= e (Loop s b))) ((set-effectful e)))
(rule ((= e (Func n b))) ((set-effectful e)))
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

fn extract_error(program: &str) -> String {
    extract_error_with(program, |_| ())
}

fn extract_error_with(program: &str, setup: impl FnOnce(&mut EGraph)) -> String {
    let mut egraph = new_experimental_egraph();
    setup(&mut egraph);
    match egraph.parse_and_run_program(None, &format!("{LANG}\n{program}")) {
        Ok(_) => panic!("program should have failed"),
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
fn picks_one_state_chain() {
    let term = extract_one(
        r#"
        (let $s0 (Arg))
        (let $p1 (Print (Num 1) $s0))
        (let $p2 (Print (Add (Num 1) (Num 0)) $s0))
        (union $p1 $p2)
        (let $p3 (Print (Add (Num 2) (Num 3)) $p1))
        (run 5)
        (extract $p3 :extractor effsafe)
        "#,
    );
    assert_eq!(term, "(Print (Add (Num 2) (Num 3)) (Print (Num 1) (Arg)))");
}

#[test]
fn reads_use_the_chosen_state() {
    // Two equivalent ways to produce the state s1. A pure Read of s1 must be
    // built from the very same e-node the statewalk chose, whichever it is.
    // Make the alternative Print cheaper than the original so a per-e-class
    // extractor would be tempted to mix them.
    let term = extract_one(
        r#"
        (with-dynamic-cost (datatype Marker (M)))
        (let $s0 (Arg))
        (let $s1 (Print (Add (Num 1) (Num 1)) $s0))
        (let $s1b (Print (Num 2) $s0))
        (union $s1 $s1b)
        (let $root (Print (Add (Read $s1) (Read $s1)) $s1))
        (run 5)
        (extract $root :extractor effsafe)
        "#,
    );
    // The cheaper (Num 2) print is chosen, and both Reads refer to it.
    assert_eq!(
        term,
        "(Print (Add (Read (Print (Num 2) (Arg))) (Read (Print (Num 2) (Arg)))) (Print (Num 2) (Arg)))"
    );
}

#[test]
fn nested_regions() {
    let term = extract_one(
        r#"
        (let $s0 (Arg))
        (let $inner (Loop $s0 (Print (Num 1) (Arg))))
        (let $branch (If (Num 0) $s0 (Print (Num 2) $inner) (Arg)))
        (let $outer (Loop $s0 $branch))
        (run 5)
        (extract $outer :extractor effsafe)
        "#,
    );
    assert_eq!(
        term,
        "(Loop (Arg) (If (Num 0) (Arg) (Print (Num 2) (Loop (Arg) (Print (Num 1) (Arg)))) (Arg)))"
    );
}

#[test]
fn subregion_shared_by_two_roots_is_extracted_once() {
    let terms = extract(
        r#"
        (let $body (Print (Add (Num 1) (Num 2)) (Arg)))
        (let $f (Func "f" (Loop (Arg) $body)))
        (let $g (Func "g" (Print (Num 9) (Loop (Arg) $body))))
        (run 5)
        (print-function Func :extractor effsafe)
        "#,
    );
    assert_eq!(terms.len(), 1);
    let [f, g] = &terms[0][..] else {
        panic!("expected two roots, got {terms:?}")
    };
    assert_eq!(
        f,
        "(Func \"f\" (Loop (Arg) (Print (Add (Num 1) (Num 2)) (Arg))))"
    );
    assert_eq!(
        g,
        "(Func \"g\" (Print (Num 9) (Loop (Arg) (Print (Add (Num 1) (Num 2)) (Arg)))))"
    );
}

#[test]
fn multiple_roots() {
    let terms = extract(
        r#"
        (let $s0 (Arg))
        (let $a (Print (Num 1) $s0))
        (let $b (Print (Num 2) $a))
        (run 5)
        (extract $a :extractor effsafe)
        (extract $b :extractor effsafe)
        "#,
    );
    assert_eq!(
        terms,
        vec![
            vec!["(Print (Num 1) (Arg))".to_string()],
            vec!["(Print (Num 2) (Print (Num 1) (Arg)))".to_string()],
        ]
    );
}

#[test]
fn dynamic_costs_steer_the_choice() {
    // Without set-cost the two prints tie and the extractor picks one of them;
    // make the Num-based one expensive and the Add-based one must win.
    let term = extract_one(
        r#"
        (with-dynamic-cost (constructor Big (i64) Expr))
        (let $s0 (Arg))
        (let $p (Print (Big 7) $s0))
        (let $q (Print (Add (Num 3) (Num 4)) $s0))
        (union $p $q)
        (set-cost (Big 7) 1000)
        (run 5)
        (extract $p :extractor effsafe)
        "#,
    );
    assert_eq!(term, "(Print (Add (Num 3) (Num 4)) (Arg))");
}

#[test]
fn placeholders_replace_a_sort() {
    // Placeholders are a Rust-side hook: the embedder names a constructor of
    // the sort that stands in for every value of it.
    let program = r#"
        (datatype Ctx (InLoop Expr) (NoCtx))
        (constructor Leaf (Ctx) Expr)
        (let $s0 (Arg))
        (let $l (Loop $s0 (Print (Leaf (InLoop (Arg))) (Arg))))
        (run 5)
        (extract $l :extractor effsafe)
    "#;
    let term = extract_one_with(program, placeholder("Ctx", "NoCtx"));
    assert_eq!(term, "(Loop (Arg) (Print (Leaf (NoCtx)) (Arg)))");

    // The replacement is checked: it must be a constructor of the sort.
    let err = extract_error_with(program, placeholder("Ctx", "Num"));
    assert!(
        err.contains("not a constructor application of that sort"),
        "unexpected error: {err}"
    );
    let err = extract_error_with(program, placeholder("Ctx", "Missing"));
    assert!(
        err.contains("not a constructor application of that sort"),
        "unexpected error: {err}"
    );
}

#[test]
fn cyclic_region_choices_are_avoided() {
    // The loop's body is the loop's own e-class. Under FreeLoops the loop
    // looks cheaper than the alternative, but placing its body leads back to
    // the region being extracted, so the extractor falls back to Expensive.
    let term = extract_one_with(
        r#"
        (constructor Expensive (Expr Expr) Expr :cost 100)
        (rule ((= e (Expensive v s))) ((set-effectful e)))
        (let $s0 (Arg))
        (let $r (Expensive (Num 1) $s0))
        (union $r (Loop $s0 $r))
        (run 5)
        (extract $r :extractor effsafe)
        "#,
        |egraph| set_effsafe_cost_models(egraph, DynamicCostModel, FreeLoops),
    );
    assert_eq!(term, "(Expensive (Num 1) (Arg))");

    // With no alternative at all the cycle is reported, not overflowed.
    let err = extract_error_with(
        r#"
        (let $s0 (Arg))
        (let $r (Print (Num 1) $s0))
        (union $r (Loop $s0 $r))
        (run 5)
        (subsume (Print (Num 1) $s0))
        (extract $r :extractor effsafe)
        "#,
        |egraph| set_effsafe_cost_models(egraph, DynamicCostModel, FreeLoops),
    );
    assert!(
        err.contains("leads back into") || err.contains("no finite term"),
        "unexpected error: {err}"
    );
}

#[test]
fn reported_cost_charges_each_region_occurrence() {
    // Both branches are the same region (cost 9 + 1 = 10). It is placed once
    // but charged once per occurrence: If 1 + 10 + 10 = 21, plus the
    // predicate (Num 1 + literal 1) and the state (1) in the enclosing
    // region: 24.
    let (term, cost) = extract_with_cost(
        r#"
        (constructor Big (Expr) Expr :cost 9)
        (rule ((= e (Big s))) ((set-effectful e)))
        (let $b (Big (Arg)))
        (let $if (If (Num 0) (Arg) $b $b))
        (run 5)
        (extract $if :extractor effsafe)
        "#,
    );
    assert_eq!(term, "(If (Num 0) (Arg) (Big (Arg)) (Big (Arg)))");
    assert_eq!(cost, 24);
}

#[test]
fn pure_children_at_region_positions_are_priced() {
    // A conditional that does not touch the state is pure, and so are its
    // branches: they are extracted within the enclosing region, but their
    // cost still counts (through the boundary fold), so the cheap sum wins
    // over a Choose whose branches are expensive.
    let term = extract_one(
        r#"
        (constructor Choose (Expr Expr Expr) Expr :regions (1 2))
        (constructor Big () Expr :cost 100)
        (let $s0 (Arg))
        (let $v (Choose (Num 0) (Big) (Big)))
        (union $v (Add (Num 1) (Num 2)))
        (let $p (Print $v $s0))
        (run 5)
        (extract $p :extractor effsafe)
        "#,
    );
    assert_eq!(term, "(Print (Add (Num 1) (Num 2)) (Arg))");
}

#[test]
fn set_effectful_accepts_let_bound_variables() {
    let term = extract_one(
        r#"
        (constructor Next (Expr) Expr)
        (rule ((= e (Arg))) ((let b (Next e)) (set-effectful b)))
        (let $s0 (Arg))
        (run 3)
        (extract (Next $s0) :extractor effsafe)
        "#,
    );
    assert_eq!(term, "(Next (Arg))");
}

#[test]
fn unrelated_invalid_enodes_do_not_block_extraction() {
    let term = extract_one(
        r#"
        (constructor Both (Expr Expr) Expr)
        (rule ((= e (Both a b))) ((set-effectful e)))
        (let $bad (Both (Arg) (Arg)))
        (let $good (Print (Num 1) (Arg)))
        (run 2)
        (extract $good :extractor effsafe)
        "#,
    );
    assert_eq!(term, "(Print (Num 1) (Arg))");
}

#[test]
fn include_subsumed_requires_effsafe() {
    for command in [
        "(extract $s0 :include-subsumed)",
        "(extract $s0 :extractor greedy-dag :include-subsumed)",
        "(print-function Func :include-subsumed)",
    ] {
        let err = extract_error(&format!("(let $s0 (Arg)) {command}"));
        assert!(
            err.contains("only supported with :extractor effsafe"),
            "unexpected error: {err}"
        );
    }
}

#[test]
fn containers_are_extracted_element_by_element() {
    let term = extract_one(
        r#"
        (sort Exprs (Vec Expr))
        (constructor Many (Exprs) Expr)
        (let $s0 (Arg))
        (let $p (Print (Many (vec-of (Num 1) (Add (Num 2) (Num 3)))) $s0))
        (run 5)
        (extract $p :extractor effsafe)
        "#,
    );
    assert_eq!(
        term,
        "(Print (Many (vec-of (Num 1) (Add (Num 2) (Num 3)))) (Arg))"
    );
}

#[test]
fn containers_carry_the_state() {
    // The state is passed to Call inside a Vec together with a value. The
    // container becomes effectful and the statewalk runs through it, so the
    // value is built from the chosen state chain.
    let term = extract_one(
        r#"
        (sort Exprs (Vec Expr))
        (constructor Call (String Exprs) Expr)
        (rule ((= e (Call n args))) ((set-effectful e)))
        (let $s0 (Arg))
        (let $s1 (Print (Num 1) $s0))
        (let $s1b (Print (Add (Num 0) (Num 1)) $s0))
        (union $s1 $s1b)
        (let $c (Call "f" (vec-of (Read $s1) $s1)))
        (run 5)
        (extract $c :extractor effsafe)
        "#,
    );
    assert_eq!(
        term,
        "(Call \"f\" (vec-of (Read (Print (Num 1) (Arg))) (Print (Num 1) (Arg))))"
    );
}

#[test]
fn subsumed_nodes_are_skipped_unless_included() {
    // Mark effectfulness first: subsumed e-nodes no longer match rules.
    let program = r#"
        (let $s0 (Arg))
        (let $p (Print (Num 1) $s0))
        (run 5)
        (subsume (Print (Num 1) $s0))
    "#;
    let err = extract_error(&format!("{program}\n(extract $p :extractor effsafe)"));
    assert!(
        err.contains("no extractable e-nodes") || err.contains("no finite term"),
        "unexpected error: {err}"
    );
    let term = extract_one(&format!(
        "{program}\n(extract $p :extractor effsafe :include-subsumed)"
    ));
    assert_eq!(term, "(Print (Num 1) (Arg))");
}

#[test]
fn errors_are_reported() {
    let err = extract_error("(let $n (Num 1)) (run 1) (extract $n :extractor effsafe)");
    assert!(err.contains("not effectful"), "unexpected error: {err}");

    let err = extract_error("(set-effectful 1)");
    assert!(err.contains("not an eq sort"), "unexpected error: {err}");

    let err = extract_error("(effsafe-regions Print 5)");
    assert!(err.contains("out of range"), "unexpected error: {err}");

    let err = extract_error(
        r#"
        (constructor Both (Expr Expr) Expr)
        (rule ((= e (Both a b))) ((set-effectful e)))
        (let $b (Both (Arg) (Arg)))
        (run 2)
        (extract $b :extractor effsafe)
        "#,
    );
    assert!(
        err.contains("no finite term") && err.contains("marked as regions"),
        "unexpected error: {err}"
    );
}
