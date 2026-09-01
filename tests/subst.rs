//! Tests for `unstable-subst` that need Rust: e-class identity, table sizes,
//! error variants, and failure atomicity. The language-level semantics are in
//! `tests/subst-basics.egg`.

use egglog::prelude::exprs::var;
use egglog::prelude::*;
use egglog::{EGraph, Error};
use egglog_experimental::new_experimental_egraph;

const MATH: &str = r#"
(datatype Math
  (Num i64)
  (Var String)
  (Add Math Math)
  (Mul Math Math))
(sort MathToMath (Map Math Math))
"#;

fn egraph(program: &str) -> EGraph {
    let mut eg = new_experimental_egraph();
    eg.parse_and_run_program(None, MATH).unwrap();
    eg.parse_and_run_program(None, program).unwrap();
    eg
}

#[test]
fn substituting_a_missing_key_returns_the_root_itself() {
    let mut eg = egraph(
        r#"
(let $x (Var "x"))
(let $e (Add $x (Num 1)))
(let $copy (unstable-subst $e (map-insert (map-empty) (Var "absent") (Num 0))))
"#,
    );
    assert_eq!(
        eg.eval_expr(&var("$e")).unwrap().1,
        eg.eval_expr(&var("$copy")).unwrap().1
    );
}

#[test]
fn an_empty_map_returns_the_root_itself() {
    let mut eg = egraph(
        r#"
(let $e (Add (Var "x") (Num 1)))
(let $copy (unstable-subst $e (map-empty)))
"#,
    );
    assert_eq!(
        eg.eval_expr(&var("$e")).unwrap().1,
        eg.eval_expr(&var("$copy")).unwrap().1
    );
}

#[test]
fn substituting_the_root_returns_its_replacement() {
    let mut eg = egraph(
        r#"
(let $x (Var "x"))
(let $y (Var "y"))
(let $copy (unstable-subst $x (map-insert (map-empty) $x $y)))
"#,
    );
    assert_eq!(
        eg.eval_expr(&var("$y")).unwrap().1,
        eg.eval_expr(&var("$copy")).unwrap().1
    );
}

/// Only the spine above a substituted class is copied; e-classes the
/// substitution cannot reach stay shared with the original.
#[test]
fn unaffected_subterms_are_shared_not_copied() {
    let mut eg = egraph(
        r#"
(let $x (Var "x"))
(let $untouched (Mul (Num 3) (Num 4)))
(let $e (Add $x $untouched))
(let $copy (unstable-subst $e (map-insert (map-empty) $x (Num 7))))
(check (= $copy (Add (Num 7) $untouched)))
"#,
    );
    // `Add` gained exactly one row: the copied root.
    let adds = eg.update(|fs| Ok(fs.table_size("Add"))).unwrap();
    assert_eq!(adds, Some(2));
    let muls = eg.update(|fs| Ok(fs.table_size("Mul"))).unwrap();
    assert_eq!(muls, Some(1));
    assert_ne!(
        eg.eval_expr(&var("$e")).unwrap().1,
        eg.eval_expr(&var("$copy")).unwrap().1
    );
}

/// A row an action has only just staged is not in the tables the walk reads, so
/// a term built in the same action is invisible when traversal is needed and
/// comes back unsubstituted — with no error. A root that is itself a map key is
/// replaced without a walk. Terms from earlier commands and rule iterations
/// are visible.
#[test]
fn does_not_see_terms_built_in_the_same_action() {
    let mut eg = egraph(
        r#"
(let $x (Var "x"))
(let $nine (Num 9))
(let $copy
  (unstable-subst
    (Mul $x (Num 5))
    (map-insert (map-empty) $x (Num 9))))
(let $unsubstituted (Mul $x (Num 5)))
(let $direct
  (unstable-subst
    (Mul $x (Num 6))
    (map-insert (map-empty) (Mul $x (Num 6)) $nine)))
"#,
    );
    assert_eq!(
        eg.eval_expr(&var("$copy")).unwrap().1,
        eg.eval_expr(&var("$unsubstituted")).unwrap().1
    );
    assert_eq!(
        eg.eval_expr(&var("$direct")).unwrap().1,
        eg.eval_expr(&var("$nine")).unwrap().1
    );
}

/// `$a = {Add (Num 0) x, Add $b x}` with `$b = Mul $a (Num 1)`: affected through
/// `x`, cyclic through `$b`. Subsuming the one e-node whose children lie outside
/// the cycle leaves no order that names the copy first.
const UNGROUNDED_CYCLE: &str = r#"
(let $x (Var "x"))
(let $a (Add (Num 0) $x))
(let $b (Mul $a (Num 1)))
(union $a (Add $b $x))
(subsume (Add (Num 0) $x))
(let $map (map-insert (map-empty) $x (Num 9)))
"#;

/// The same ungrounded cycle, with an acyclic affected branch beside it that
/// *is* copyable. The copyable part must not be written: egglog flushes an
/// action's staged writes even when it ends in an error, so a substitution that
/// copies its way up to a blockage cannot take those rows back.
const UNGROUNDED_CYCLE_WITH_SIDE_BRANCH: &str = r#"
(let $x (Var "x"))
(let $a (Add (Num 0) $x))
(let $b (Mul $a (Num 1)))
(union $a (Add $b $x))
(subsume (Add (Num 0) $x))
(let $side (Add $x (Num 7)))
(let $root (Mul $a $side))
(let $map (map-insert (map-empty) $x (Num 9)))
"#;

#[test]
fn a_failed_substitution_writes_no_constructor_copies() {
    let mut eg = egraph(UNGROUNDED_CYCLE_WITH_SIDE_BRANCH);
    let before = eg.update(|state| Ok(state.table_size("Add"))).unwrap();
    let err = eg
        .parse_and_run_program(None, "(let $copy (unstable-subst $root $map))")
        .unwrap_err();
    assert!(
        err.to_string().contains("panicked"),
        "expected a primitive panic, got {err}"
    );

    let after = eg.update(|state| Ok(state.table_size("Add"))).unwrap();
    assert_eq!(before, after, "a failed substitution wrote an Add copy");
}

/// A primitive cannot return an `Error`, and registering a custom panic message
/// needs the backend, which egglog does not expose to out-of-tree code. So the
/// same failure reaches an egglog program as a generic primitive panic, with
/// the reason in the log.
#[test]
fn an_ungrounded_cycle_panics_from_egglog() {
    let mut eg = egraph(UNGROUNDED_CYCLE);
    let err = eg
        .parse_and_run_program(None, "(let $copy (unstable-subst $a $map))")
        .unwrap_err();
    let message = err.to_string();
    assert!(
        message.contains("panicked"),
        "expected a primitive panic, got {message}"
    );
}

/// Subsumed e-nodes are excluded from extraction, so a copy must not bring
/// them back un-subsumed.
#[test]
fn skips_subsumed_enodes() {
    let mut eg = egraph(
        r#"
(let $x (Var "x"))
(let $keep (Add $x (Num 1)))
(let $drop (Mul $x (Num 1)))
(union $keep $drop)
(subsume (Mul $x (Num 1)))
(let $copy (unstable-subst $keep (map-insert (map-empty) $x (Num 6))))
(check (= $copy (Add (Num 6) (Num 1))))
"#,
    );
    // The one `Mul` row is the subsumed original; no copy was made.
    let muls = eg.update(|fs| Ok(fs.table_size("Mul"))).unwrap();
    assert_eq!(muls, Some(1));
}

/// Reads of live tables in a seminaive rule head would not re-fire when the
/// tables they read grow, so the typechecker rejects them.
#[test]
fn rejected_in_a_seminaive_rule_head() {
    let mut eg = new_experimental_egraph();
    eg.parse_and_run_program(None, MATH).unwrap();
    let err = eg
        .parse_and_run_program(
            None,
            r#"
(constructor Beta (Math Math Math) Math)
(rule ((= $lhs (Beta body from to)))
      ((union $lhs (unstable-subst body (map-insert (map-empty) from to)))))
"#,
        )
        .unwrap_err();
    assert!(
        matches!(err, Error::TypeError(_) | Error::TypeErrors(_)),
        "expected a type error, got {err}"
    );
}

/// The interface accepts exactly one map; multiple maps are not a mixed-sort
/// escape hatch.
#[test]
fn requires_exactly_one_map() {
    for call in [
        "(let $copy (unstable-subst $x))",
        "(let $copy (unstable-subst $x $map $map))",
    ] {
        let mut eg = egraph(
            r#"
(let $x (Var "x"))
(let $map (map-empty))
"#,
        );
        let err = eg.parse_and_run_program(None, call).unwrap_err();
        assert!(
            matches!(err, Error::TypeError(_) | Error::TypeErrors(_)),
            "expected a type error, got {err}"
        );
    }
}

/// A map from one eq-sort to another cannot be a substitution: the replacement
/// would not typecheck in the column where the key occurred.
#[test]
fn rejects_a_map_between_distinct_eq_sorts() {
    let mut eg = new_experimental_egraph();
    eg.parse_and_run_program(None, MATH).unwrap();
    let err = eg
        .parse_and_run_program(
            None,
            r#"
(datatype Ty (TVar String) (IntTy))
(sort MathToTy (Map Math Ty))
(let $x (Var "x"))
(let $a (TVar "a"))
(let $copy (unstable-subst $x (map-insert (map-empty) $x $a)))
"#,
        )
        .unwrap_err();
    assert!(
        matches!(err, Error::TypeError(_) | Error::TypeErrors(_)),
        "expected a type error, got {err}"
    );
}

#[test]
fn rejects_non_eq_roots_and_maps() {
    let mut eg = new_experimental_egraph();
    eg.parse_and_run_program(None, MATH).unwrap();
    for program in [
        "(let $copy (unstable-subst 1 (map-empty)))",
        r#"
(sort IntToInt (Map i64 i64))
(let $x (Var "x"))
(let $copy (unstable-subst $x (map-insert (map-empty) 1 2)))
"#,
    ] {
        let err = eg.parse_and_run_program(None, program).unwrap_err();
        assert!(
            matches!(err, Error::TypeError(_) | Error::TypeErrors(_)),
            "expected a type error, got {err}"
        );
    }
}

/// The walk keeps its own stack, so a deep term does not turn into deep
/// recursion. Depth is well past anything a program writes by hand while
/// staying cheap enough for CI.
#[test]
fn handles_a_deep_spine() {
    const DEPTH: usize = 5_000;
    let mut program = String::from("(let $x (Var \"x\"))\n(let $e0 $x)\n");
    for i in 1..=DEPTH {
        program.push_str(&format!("(let $e{i} (Add $x $e{}))\n", i - 1));
    }
    let mut eg = egraph(&program);
    eg.parse_and_run_program(
        None,
        &format!(
            "(let $copy (unstable-subst $e{DEPTH} \
             (map-insert (map-empty) $x (Num 0))))"
        ),
    )
    .unwrap();
    // Every one of the spine's `Add`s mentions `x`, so all of them are copied.
    let adds = eg.update(|fs| Ok(fs.table_size("Add"))).unwrap();
    assert_eq!(adds, Some(2 * DEPTH));
}
