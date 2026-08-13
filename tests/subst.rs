//! Tests for the `unstable-subst` primitive.

use egglog::prelude::exprs::var;
use egglog::prelude::*;
use egglog::{EGraph, Error, Value};
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

/// The value of a global, for the assertions that need to compare e-classes
/// rather than terms.
fn global(eg: &mut EGraph, name: &str) -> Value {
    eg.eval_expr(&var(&format!("${name}"))).unwrap().1
}

#[test]
fn replaces_a_variable_everywhere_it_occurs() {
    egraph(
        r#"
(let $x (Var "x"))
(let $y (Var "y"))
(let $e (Add $x (Mul $x (Num 2))))
(let $copy (unstable-subst $e (map-insert (map-empty) $x $y)))
(check (= $copy (Add $y (Mul $y (Num 2)))))
(fail (check (= $copy $e)))
"#,
    );
}

#[test]
fn substitutes_several_keys_at_once() {
    egraph(
        r#"
(let $x (Var "x"))
(let $y (Var "y"))
(let $e (Add $x $y))
(let $copy (unstable-subst $e (map-insert (map-insert (map-empty) $x $y) $y $x)))
(check (= $copy (Add $y $x)))
"#,
    );
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
    assert_eq!(global(&mut eg, "e"), global(&mut eg, "copy"));
}

#[test]
fn an_empty_map_returns_the_root_itself() {
    let mut eg = egraph(
        r#"
(let $e (Add (Var "x") (Num 1)))
(let $copy (unstable-subst $e (map-empty)))
"#,
    );
    assert_eq!(global(&mut eg, "e"), global(&mut eg, "copy"));
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
    assert_eq!(global(&mut eg, "y"), global(&mut eg, "copy"));
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
    assert_ne!(global(&mut eg, "e"), global(&mut eg, "copy"));
}

/// Copying an e-class copies every one of its e-nodes, so an equation between
/// two reachable terms is carried over to the copy. For an equation a rewrite
/// rule derived — one that holds for every value of the substituted class —
/// that is exactly right: `x * 0 = 0` stays `5 * 0 = 0`. The untouched `(Num 0)`
/// e-node copies to itself, which is what merges the copy back into that class.
#[test]
fn an_equation_that_holds_for_every_value_survives_substitution() {
    egraph(
        r#"
(rewrite (Mul a (Num 0)) (Num 0))
(let $x (Var "x"))
(let $e (Mul $x (Num 0)))
(run 1)
(check (= $e (Num 0)))
(let $copy (unstable-subst $e (map-insert (map-empty) $x (Num 5))))
(check (= $copy (Mul (Num 5) (Num 0))))
(check (= $copy (Num 0)))
"#,
    );
}

/// The same mechanism is unsound on a *ground* equation, which holds only for
/// the class it pins down: `(union (Add x (Num 1)) (Num 5))` says `x = 4`, and
/// substituting `x := 9` into it asserts `9 + 1 = 5`. Only substitute classes
/// that behave like universally quantified variables.
#[test]
fn a_ground_equation_about_a_key_is_substituted_too() {
    egraph(
        r#"
(let $x (Var "x"))
(let $e (Add $x (Num 1)))
(union $e (Num 5))
(let $copy (unstable-subst $e (map-insert (map-empty) $x (Num 9))))
(check (= $copy (Add (Num 9) (Num 1))))
(check (= $copy (Num 5)))
"#,
    );
}

/// A row an action has only just staged is not in the tables the walk reads,
/// so a term built in the same action is invisible to it and comes back
/// unsubstituted — with no error. Terms from earlier commands, and from
/// earlier rule iterations, are fine.
#[test]
fn does_not_see_terms_built_in_the_same_action() {
    let mut eg = egraph(
        r#"
(let $x (Var "x"))
(let $copy (unstable-subst (Mul $x (Num 5)) (map-insert (map-empty) $x (Num 9))))
(let $unsubstituted (Mul $x (Num 5)))
"#,
    );
    assert_eq!(global(&mut eg, "copy"), global(&mut eg, "unsubstituted"));
}

/// The staging limit is about the region being walked, not the replacements:
/// a map's values are spliced into the copy without being walked, so building
/// one in the same action is fine.
#[test]
fn a_replacement_built_in_the_same_action_is_fine() {
    egraph(
        r#"
(let $x (Var "x"))
(let $e (Add $x (Num 1)))
(let $copy (unstable-subst $e (map-insert (map-empty) $x (Mul (Num 2) (Num 3)))))
(check (= $copy (Add (Mul (Num 2) (Num 3)) (Num 1))))
"#,
    );
}

/// A cyclic e-class is copied as long as one of its e-nodes has all its
/// children outside the cycle: that e-node's `lookup_or_insert` names the copy,
/// and the cyclic e-node then unions into it. No e-class id is invented.
#[test]
fn a_grounded_cyclic_eclass_is_copied() {
    egraph(
        r#"
(let $x (Var "x"))
(let $loop (Add $x (Num 0)))
;; $loop now holds a grounded e-node and one referring to its own class.
(union $loop (Add $loop (Num 0)))
(let $copy (unstable-subst $loop (map-insert (map-empty) $x (Num 7))))
(check (= $copy (Add (Num 7) (Num 0))))
(check (= $copy (Add $copy (Num 0))))
"#,
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

/// The walk reports an ungrounded cycle instead of inventing an e-class id.
#[test]
fn an_ungrounded_cycle_is_an_error() {
    let mut eg = egraph(UNGROUNDED_CYCLE);
    let root = global(&mut eg, "a");
    let map = global(&mut eg, "map");
    let err = egglog_experimental::subst(&mut eg, root, map).unwrap_err();
    let message = err.to_string();
    assert!(
        message.contains("unstable-subst") && message.contains("no order copies e-class"),
        "expected an ungrounded-cycle error, got {message}"
    );
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

/// The root's sort is free: it need not be the map's key sort, because a
/// substitution reaches through every sort in the term structure.
#[test]
fn the_root_may_be_a_different_sort_than_the_keys() {
    egraph(
        r#"
(datatype MathList (Nil) (Cons Math MathList))
(let $x (Var "x"))
(let $list (Cons $x (Cons (Num 1) (Nil))))
(let $copy (unstable-subst $list (map-insert (map-empty) $x (Num 8))))
(check (= $copy (Cons (Num 8) (Cons (Num 1) (Nil)))))
"#,
    );
}

/// E-classes reached only through a container child are substituted too, and
/// the container is rebuilt around the replacements.
#[test]
fn substitutes_inside_container_children() {
    egraph(
        r#"
(sort MathVec (Vec Math))
(constructor Sum (MathVec) Math)
(let $x (Var "x"))
(let $e (Sum (vec-of $x (Num 1))))
(let $copy (unstable-subst $e (map-insert (map-empty) $x (Num 4))))
(check (= $copy (Sum (vec-of (Num 4) (Num 1)))))
"#,
    );
}

/// Container children with no e-classes inside are never walked into, so a
/// substitution leaves them alone.
#[test]
fn leaves_containers_without_eclasses_alone() {
    egraph(
        r#"
(sort Ints (Vec i64))
(constructor Tagged (Math Ints) Math)
(let $x (Var "x"))
(let $e (Tagged $x (vec-of 1 2)))
(let $copy (unstable-subst $e (map-insert (map-empty) $x (Num 5))))
(check (= $copy (Tagged (Num 5) (vec-of 1 2))))
"#,
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

#[test]
fn runs_in_a_naive_rule_head() {
    egraph(
        r#"
(constructor Beta (Math Math Math) Math)
(rule ((= $lhs (Beta body from to)))
      ((union $lhs (unstable-subst body (map-insert (map-empty) from to))))
      :naive)
(let $x (Var "x"))
(let $b (Beta (Add $x $x) $x (Num 3)))
(run 1)
(check (= $b (Add (Num 3) (Num 3))))
"#,
    );
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

/// A map from one sort to another cannot be a substitution: the replacement
/// would not typecheck in the column it is written to.
#[test]
fn rejects_a_map_between_different_sorts() {
    let mut eg = new_experimental_egraph();
    eg.parse_and_run_program(None, MATH).unwrap();
    let err = eg
        .parse_and_run_program(
            None,
            r#"
(sort MathToInt (Map Math i64))
(let $x (Var "x"))
(let $copy (unstable-subst $x (map-insert (map-empty) $x 3)))
"#,
        )
        .unwrap_err();
    assert!(
        matches!(err, Error::TypeError(_) | Error::TypeErrors(_)),
        "expected a type error, got {err}"
    );
}

/// Substitution is simultaneous, and a key's replacement is not itself
/// substituted — but a *reachable* class that happens to be a replacement is
/// still copied where it occurs on its own.
#[test]
fn a_replacement_that_is_itself_affected_is_copied_where_it_occurs() {
    egraph(
        r#"
(let $x (Var "x"))
(let $y (Add $x (Num 1)))
(let $e (Mul $x $y))
(let $copy (unstable-subst $e (map-insert (map-empty) $x $y)))
;; x |-> y, and y itself becomes (Add y 1) where it occurs as a child.
(check (= $copy (Mul $y (Add $y (Num 1)))))
"#,
    );
}

/// The walk uses an explicit stack, so depth is bounded by the heap rather than
/// by Rust's stack.
#[test]
fn handles_a_deep_spine() {
    const DEPTH: usize = 20_000;
    let mut program = String::from("(let $x (Var \"x\"))\n(let $e0 $x)\n");
    for i in 1..=DEPTH {
        program.push_str(&format!("(let $e{i} (Add $x $e{}))\n", i - 1));
    }
    let mut eg = egraph(&program);
    eg.parse_and_run_program(
        None,
        &format!("(let $copy (unstable-subst $e{DEPTH} (map-insert (map-empty) $x (Num 0))))"),
    )
    .unwrap();
    // Every one of the spine's `Add`s mentions `x`, so all of them are copied.
    let adds = eg.update(|fs| Ok(fs.table_size("Add"))).unwrap();
    assert_eq!(adds, Some(2 * DEPTH));
}

/// The Rust-level entry point, which takes the map as a container value.
#[test]
fn the_rust_api_substitutes() {
    let mut eg = egraph(
        r#"
(let $x (Var "x"))
(let $e (Add $x (Num 1)))
(let $map (map-insert (map-empty) $x (Num 2)))
(let $expected (Add (Num 2) (Num 1)))
"#,
    );
    let root = global(&mut eg, "e");
    let map = global(&mut eg, "map");
    let copy = egglog_experimental::subst(&mut eg, root, map).unwrap();
    assert_eq!(copy, global(&mut eg, "expected"));
}

#[test]
fn a_popped_constructor_is_not_walked() {
    egraph(
        r#"
(let $x (Var "x"))
(push)
(constructor Neg (Math) Math)
(let $inner (Neg $x))
(pop)
(let $e (Add $x (Num 1)))
(let $copy (unstable-subst $e (map-insert (map-empty) $x (Num 2))))
(check (= $copy (Add (Num 2) (Num 1))))
"#,
    );
}
