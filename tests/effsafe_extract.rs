//! Effect-safe extraction (`effsafe-extract`): the extracted terms are checked
//! against expected strings, which the `.egg` file harness cannot do.

use egglog::CommandOutput;
use egglog_experimental::{EffsafeExtractOutput, new_experimental_egraph};

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
(relation Effectful (Expr))
(rule ((= e (Arg))) ((Effectful e)))
(rule ((= e (Print v s))) ((Effectful e)))
(rule ((= e (If p s t els))) ((Effectful e)))
(rule ((= e (Loop s b))) ((Effectful e)))
(rule ((= e (Func n b))) ((Effectful e)))
"#;

/// Run `program` after the language prelude and return the terms of every
/// effsafe extraction, as strings.
fn extract(program: &str) -> Vec<Vec<String>> {
    let mut egraph = new_experimental_egraph();
    let outputs = egraph
        .parse_and_run_program(None, &format!("{LANG}\n{program}"))
        .unwrap_or_else(|err| panic!("program failed: {err}"));
    outputs
        .iter()
        .filter_map(|output| match output {
            CommandOutput::UserDefined(out) => out
                .as_ref()
                .as_any()
                .downcast_ref::<EffsafeExtractOutput>()
                .map(|out| {
                    out.terms
                        .iter()
                        .map(|&t| out.termdag.to_string(t))
                        .collect()
                }),
            _ => None,
        })
        .collect()
}

fn extract_one(program: &str) -> String {
    let mut all = extract(program);
    assert_eq!(all.len(), 1, "expected one extraction");
    let mut terms = all.pop().unwrap();
    assert_eq!(terms.len(), 1, "expected one root");
    terms.pop().unwrap()
}

fn extract_error(program: &str) -> String {
    let mut egraph = new_experimental_egraph();
    match egraph.parse_and_run_program(None, &format!("{LANG}\n{program}")) {
        Ok(_) => panic!("program should have failed"),
        Err(err) => err.to_string(),
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
        (effsafe-extract Effectful $p3)
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
        (effsafe-extract Effectful $root)
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
        (effsafe-extract Effectful $outer)
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
        (effsafe-extract-all Effectful Func)
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
fn multiple_roots_in_one_call() {
    let terms = extract(
        r#"
        (let $s0 (Arg))
        (let $a (Print (Num 1) $s0))
        (let $b (Print (Num 2) $a))
        (run 5)
        (effsafe-extract Effectful $a $b)
        "#,
    );
    assert_eq!(
        terms,
        vec![vec![
            "(Print (Num 1) (Arg))".to_string(),
            "(Print (Num 2) (Print (Num 1) (Arg)))".to_string(),
        ]]
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
        (effsafe-extract Effectful $p)
        "#,
    );
    assert_eq!(term, "(Print (Add (Num 3) (Num 4)) (Arg))");
}

#[test]
fn placeholders_replace_a_sort() {
    let term = extract_one(
        r#"
        (datatype Ctx (InLoop Expr) (NoCtx))
        (constructor Leaf (Ctx) Expr)
        (let $s0 (Arg))
        (let $l (Loop $s0 (Print (Leaf (InLoop (Arg))) (Arg))))
        (effsafe-placeholder Ctx (NoCtx))
        (run 5)
        (effsafe-extract Effectful $l)
        "#,
    );
    assert_eq!(term, "(Loop (Arg) (Print (Leaf (NoCtx)) (Arg)))");
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
        (effsafe-extract Effectful $p)
        "#,
    );
    assert_eq!(
        term,
        "(Print (Many (vec-of (Num 1) (Add (Num 2) (Num 3)))) (Arg))"
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
    let err = extract_error(&format!("{program}\n(effsafe-extract Effectful $p)"));
    assert!(
        err.contains("no extractable e-nodes") || err.contains("no finite term"),
        "unexpected error: {err}"
    );
    let term = extract_one(&format!(
        "{program}\n(effsafe-extract Effectful $p :include-subsumed)"
    ));
    assert_eq!(term, "(Print (Num 1) (Arg))");
}

#[test]
fn errors_are_reported() {
    let err = extract_error("(let $n (Num 1)) (run 1) (effsafe-extract Effectful $n)");
    assert!(err.contains("not effectful"), "unexpected error: {err}");

    let err = extract_error("(let $s (Arg)) (run 1) (effsafe-extract Missing $s)");
    assert!(err.contains("not declared"), "unexpected error: {err}");

    let err = extract_error("(effsafe-regions Print 5)");
    assert!(err.contains("out of range"), "unexpected error: {err}");

    let err = extract_error(
        r#"
        (constructor Both (Expr Expr) Expr)
        (rule ((= e (Both a b))) ((Effectful e)))
        (let $b (Both (Arg) (Arg)))
        (run 2)
        (effsafe-extract Effectful $b)
        "#,
    );
    assert!(err.contains("marked as regions"), "unexpected error: {err}");
}
