use std::{
    cell::Cell,
    fmt::Write as _,
    fs,
    panic::{AssertUnwindSafe, catch_unwind},
    process::Command,
    sync::Arc,
};

use egglog::{
    CommandOutput,
    ast::{Expr, Literal},
    prelude::{RustSpan, Span},
    span,
};

struct CountingDagCostModel<'a, M>(&'a Cell<usize>, M);

impl<C, M> egglog::extract::DagCostModel<C> for CountingDagCostModel<'_, M>
where
    C: egglog::extract::MonoidCost,
    M: egglog::extract::DagCostModel<C>,
{
    fn base_value_cost(
        &self,
        egraph: &egglog::EGraph,
        sort: &egglog::ArcSort,
        value: egglog::Value,
    ) -> C {
        self.0.set(self.0.get() + 1);
        self.1.base_value_cost(egraph, sort, value)
    }

    fn enode_cost(
        &self,
        egraph: &egglog::EGraph,
        func: &egglog::Function,
        enode: &egglog::Enode<'_>,
    ) -> C {
        self.0.set(self.0.get() + 1);
        self.1.enode_cost(egraph, func, enode)
    }

    fn container_cost(
        &self,
        egraph: &egglog::EGraph,
        sort: &egglog::ArcSort,
        value: egglog::Value,
    ) -> C {
        self.0.set(self.0.get() + 1);
        self.1.container_cost(egraph, sort, value)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct MaxCost(u64);

impl egglog::extract::MonoidCost for MaxCost {
    fn identity() -> Self {
        Self(0)
    }

    fn combine(self, other: &Self) -> Self {
        std::cmp::max(self, *other)
    }
}

struct MaxCostModel;

impl egglog::extract::DagCostModel<MaxCost> for MaxCostModel {
    fn base_value_cost(
        &self,
        _egraph: &egglog::EGraph,
        _sort: &egglog::ArcSort,
        _value: egglog::Value,
    ) -> MaxCost {
        MaxCost(1)
    }

    fn enode_cost(
        &self,
        _egraph: &egglog::EGraph,
        func: &egglog::Function,
        _enode: &egglog::Enode<'_>,
    ) -> MaxCost {
        MaxCost(match func.name() {
            "Cheap" => 2,
            "Pair" => 3,
            "Expensive" => 5,
            name => panic!("unexpected constructor {name}"),
        })
    }
}

fn eval_get_size(egraph: &mut egglog::EGraph, names: &[&str]) -> i64 {
    let span = span!();
    let expr = Expr::Call(
        span.clone(),
        "get-size!".into(),
        names
            .iter()
            .map(|name| Expr::Lit(span.clone(), Literal::String((*name).into())))
            .collect(),
    );
    let (_, value) = egraph.eval_expr(&expr).unwrap();
    egraph.value_to_base::<i64>(value)
}

fn new_copy_egraph() -> egglog::EGraph {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    egraph
        .parse_and_run_program(
            None,
            r#"
        (ruleset copy)
        (relation R (i64))
        (relation S (i64))
        (R 0)
        (rule ((R x)) ((S x)) :ruleset copy :name "copy")
        "#,
        )
        .unwrap();
    egraph
}

#[test]
fn invalid_higher_order_calls_report_the_unresolved_primitive() {
    let cases = [
        (
            r#"
            (sort IntMap (Map i64 i64))
            (sort IntBinary (UnstableFn (i64 i64) i64))
            (map-fold-kv (unstable-fn "+") 0 (map-empty))
            "#,
            "Failed to infer a type for: @map-fold-kv",
        ),
        (
            r#"
            (sort MaybeInt (Maybe i64))
            (sort IntToInt (UnstableFn (i64) i64))
            (unstable-catch (unstable-fn "+" 1))
            "#,
            "Failed to infer a type for: @unstable-catch",
        ),
        (
            r#"
            (sort MaybeInt (Maybe i64))
            (sort MaybeString (Maybe String))
            (let ambiguous (maybe-none))
            "#,
            "Failed to infer a type for: @maybe-none",
        ),
    ];

    for (program, expected) in cases {
        let mut egraph = egglog_experimental::new_experimental_egraph();
        let error = egraph.parse_and_run_program(None, program).unwrap_err();
        assert!(
            error.to_string().contains(expected),
            "unexpected diagnostic: {error}"
        );
    }
}

#[test]
fn f64_is_finite_rejects_nan_and_infinities() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    egraph
        .parse_and_run_program(
            None,
            r#"
            (check (f64-is-finite 1.0))
            (fail (check (f64-is-finite NaN)))
            (fail (check (f64-is-finite inf)))
            (fail (check (f64-is-finite -inf)))
            "#,
        )
        .unwrap();
}

#[test]
fn rational_primitives_cover_their_exact_domain() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    egraph
        .parse_and_run_program(
            None,
            r#"
            ; Construction canonicalizes signs and common factors.
            (check (= (rational 2 -4) (rational -1 2)))
            (check (= (numer (rational 6 -9)) -2))
            (check (= (denom (rational 6 -9)) 3))

            (check (= (neg (rational -3 2)) (rational 3 2)))
            (check (= (abs (rational -3 2)) (rational 3 2)))
            (check (= (floor (rational -9223372036854775808 1))
                      (rational -9223372036854775808 1)))
            (check (= (ceil (rational 9223372036854775807 1))
                      (rational 9223372036854775807 1)))
            (check (= (floor (rational -9223372036854775807 3))
                      (rational -3074457345618258603 1)))
            (check (= (ceil (rational 9223372036854775807 2))
                      (rational 4611686018427387904 1)))
            (check (= (round (rational -3 2)) (rational -2 1)))
            (check (= (round (rational 3 2)) (rational 2 1)))
            (check (= (round (rational -9223372036854775808 1))
                      (rational -9223372036854775808 1)))
            (check (= (round (rational 9223372036854775807 1))
                      (rational 9223372036854775807 1)))
            (check (= (min (rational -9223372036854775808 1)
                           (rational 9223372036854775807 1))
                      (rational -9223372036854775808 1)))
            (check (= (max (rational -9223372036854775808 1)
                           (rational 9223372036854775807 1))
                      (rational 9223372036854775807 1)))
            (check (< (rational -9223372036854775808 1)
                      (rational 9223372036854775807 1)))
            (check (> (rational 9223372036854775807 1)
                      (rational -9223372036854775808 1)))
            (check (<= (rational -9223372036854775808 1)
                       (rational -9223372036854775808 1)))
            (check (>= (rational 9223372036854775807 1)
                       (rational 9223372036854775807 1)))
            (check (= (+ (rational 9223372036854775807 2)
                         (rational 9223372036854775807 2))
                      (rational 9223372036854775807 1)))
            (check (= (- (rational 9223372036854775807 2)
                         (rational -9223372036854775807 2))
                      (rational 9223372036854775807 1)))
            (check (= (* (rational 2 3) (rational 3 4))
                      (rational 1 2)))
            (check (= (/ (rational 2 3) (rational 4 5))
                      (rational 5 6)))

            (check (= (pow (rational 2 3) (rational 3 1)) (rational 8 27)))
            (check (= (log (rational 1 1)) (rational 0 1)))
            (check (= (sqrt (rational 0 1)) (rational 0 1)))
            (check (= (sqrt (rational 4 9)) (rational 2 3)))
            (check (= (cbrt (rational 0 1)) (rational 0 1)))
            (check (= (cbrt (rational 8 27)) (rational 2 3)))
            (check (= (cbrt (rational -8 27)) (rational -2 3)))
            (check (= (cbrt (rational -9223372036854775808 1))
                      (rational -2097152 1)))
            (check (= (to-f64 (rational 1 2)) 0.5))
            "#,
        )
        .unwrap();
}

fn assert_rational_expr_undefined(expr: &str) {
    let result = catch_unwind(AssertUnwindSafe(|| {
        let mut egraph = egglog_experimental::new_experimental_egraph();
        egraph.parse_and_run_program(None, &format!("(let result {expr})"))
    }));
    let Ok(result) = result else {
        panic!("undefined Rational expression panicked: {expr}");
    };
    assert!(result.is_err(), "Rational expression was defined: {expr}");
}

#[test]
fn rational_partial_primitives_are_undefined_without_panicking() {
    for expr in [
        "(rational 1 0)",
        "(rational 1 -9223372036854775808)",
        "(rational -9223372036854775808 -1)",
        "(neg (rational -9223372036854775808 1))",
        "(abs (rational -9223372036854775808 1))",
        "(+ (rational 9223372036854775807 1) (rational 1 1))",
        "(- (rational -9223372036854775808 1) (rational 1 1))",
        "(* (rational 9223372036854775807 1) (rational 2 1))",
        "(/ (rational -9223372036854775808 1) (rational -1 1))",
        "(pow (rational 0 1) (rational 0 1))",
        "(pow (rational 0 1) (rational 1 2))",
        "(pow (rational 4 1) (rational 1 2))",
        "(pow (rational 2 1) (rational -1 1))",
        "(pow (rational 9223372036854775807 1) (rational 2 1))",
        "(log (rational 2 1))",
        "(sqrt (rational 2 1))",
        "(sqrt (rational -1 1))",
        "(cbrt (rational 2 1))",
    ] {
        assert_rational_expr_undefined(expr);
    }
}

#[test]
fn f64_is_finite_supports_proof_mode() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    let resolved = egraph
        .resolve_program(None, "(check (f64-is-finite 1.0))")
        .unwrap();
    assert!(egglog::program_supports_proofs(
        &resolved,
        egraph.type_info()
    ));
}

fn let_backoff(egraph: &mut egglog::EGraph) {
    egraph
        .parse_and_run_program(
            None,
            "(let-scheduler bo (back-off :match-limit 2 :ban-length 2))",
        )
        .unwrap();
}

fn run_bo_copy(egraph: &mut egglog::EGraph) {
    egraph
        .parse_and_run_program(None, "(run-schedule (run-with bo copy))")
        .unwrap();
}

const DYNAMIC_DAG_FIXTURE: &str = "
(with-dynamic-cost
    (datatype E
        (Pair E E :cost 1)
        (Wide E :cost 1)
        (Leaf i64 :cost 1))
)

(let shared (Wide (Leaf 0)))
(let daggy (Pair shared shared))
(let treeish (Pair (Leaf 1) (Leaf 2)))
(union daggy treeish)
";

const CYCLIC_DAG_FIXTURE: &str = "
(sort S)
(constructor S0 (S) S)
(constructor S3 (S S) S)
(constructor S5 (S) S)
(constructor S6 () S)

(let b (S6))
(let c (S0 b))
(let x (S0 (S3 (S5 b) b)))
(let y (S0 (S0 (S0 c))))
(union x y)
(let victim (S0 x))
";

fn run_dynamic_dag(commands: &str) -> Vec<CommandOutput> {
    egglog_experimental::new_experimental_egraph()
        .parse_and_run_program(None, &format!("{DYNAMIC_DAG_FIXTURE}\n{commands}"))
        .unwrap()
}

#[test]
fn test_extract() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let result = egraph
        .parse_and_run_program(
            None,
            "
        (with-dynamic-cost
            (datatype E (Add E E) (Sub E E :cost 200) (Num i64))
        )

        (union (Num 2) (Add (Num 1) (Num 1)))
        (set-cost (Num 2) 1000)
        (set-cost (Num 1) 100)
        (extract (Num 2))

        (push)
        (set-cost (Add (Num 1) (Num 1)) 800)
        (extract (Num 2))
        (pop)

        (push)
        (set-cost (Add (Num 1) (Num 1)) 798)
        (extract (Num 2))
        (pop)

        ;; 200 + 1 + 1 > 1 + 100 + 100
        (union (Num 2) (Sub (Num 5) (Num 3)))
        (extract (Num 2))
        (set-cost (Sub (Num 5) (Num 3)) 198)
        ;; 198 + 1 + 1 < 1 + 100 + 100
        (extract (Num 2))",
        )
        .unwrap();

    assert_eq!(result.len(), 5);
    assert_eq!(result[0].to_string(), "(Add (Num 1) (Num 1))\n");
    assert_eq!(result[1].to_string(), "(Num 2)\n");
    assert_eq!(result[2].to_string(), "(Add (Num 1) (Num 1))\n");
    assert_eq!(result[3].to_string(), "(Add (Num 1) (Num 1))\n");
    assert_eq!(result[4].to_string(), "(Sub (Num 5) (Num 3))\n");
}

#[test]
fn test_greedy_dag_extract_prefers_shared_subterms() {
    let result = run_dynamic_dag(
        "
        (extract daggy)
        (extract daggy :extractor greedy-dag)",
    );

    assert_eq!(result.len(), 2);
    assert_eq!(result[0].to_string(), "(Pair (Leaf 1) (Leaf 2))\n");
    assert_eq!(
        result[1].to_string(),
        "(Pair (Wide (Leaf 0)) (Wide (Leaf 0)))\n"
    );

    let CommandOutput::ExtractBest(_, tree_cost, _) = result[0].clone() else {
        panic!("expected tree extract output");
    };
    let CommandOutput::ExtractBest(_, dag_cost, _) = result[1].clone() else {
        panic!("expected greedy-dag extract output");
    };
    assert_eq!(tree_cost, 5);
    assert_eq!(dag_cost, 4);
}

#[test]
fn test_greedy_dag_cost_and_term_use_the_same_producer_snapshot() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    egraph
        .parse_and_run_program(
            None,
            r#"
            (with-dynamic-cost
              (datatype E
                (X :cost 10)
                (D :cost 4)
                (C E :cost 1)
                (Bx E :cost 1)
                (Bc E :cost 1)
                (A E E :cost 1)
                (Alt :cost 15)))
            (let $x (X))
            (let $d (D))
            (let $c (C $d))
            (let $b-old (Bx $x))
            (let $b-new (Bc $c))
            (union $b-old $b-new)
            (let $a (A $b-old $x))
            (union $a (Alt))
            "#,
        )
        .unwrap();

    let root_expr = egraph.parser.get_expr_from_string(None, "$a").unwrap();
    let (sort, value) = egraph.eval_expr(&root_expr).unwrap();
    let extracted = egglog_experimental::extract_best_greedy_dag(
        &egraph,
        vec![(sort.clone(), value)],
        egglog_experimental::DynamicCostModel,
    )
    .unwrap();
    let root = extracted.terms[0].as_ref().unwrap();
    let term = extracted.termdag.to_string(root.term);

    assert_eq!(root.cost, 12);
    assert_eq!(term, "(A (Bx (X)) (X))");
    let roundtrip = egraph.parser.get_expr_from_string(None, &term).unwrap();
    let (roundtrip_sort, roundtrip_value) = egraph.eval_expr(&roundtrip).unwrap();
    assert_eq!(roundtrip_sort.name(), sort.name());
    assert_eq!(roundtrip_value, value);

    let variants = egglog_experimental::extract_variants_greedy_dag(
        &egraph,
        vec![(sort, value)],
        1,
        egglog_experimental::DynamicCostModel,
    )
    .unwrap();
    assert_eq!(variants.variants[0][0].cost, 12);
    assert_eq!(
        variants.termdag.to_string(variants.variants[0][0].term),
        term
    );
}

#[test]
fn test_greedy_dag_reconciles_conflicting_child_snapshots() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    egraph
        .parse_and_run_program(
            None,
            r#"
            (with-dynamic-cost
              (datatype E
                (A :cost 5)
                (PAlt :cost 0)
                (OldOnly :cost 1)
                (UOnly :cost 1)
                (UOnly2 :cost 0)
                (C :cost 1)
                (B E :cost 1)
                (XOld E E E :cost 2)
                (XNew E :cost 1)
                (U E E E E E :cost 1)
                (V E E :cost 1)
                (P E E :cost 1)))
            (let $a (A))
            (let $p-alt (PAlt))
            (let $old-only (OldOnly))
            (let $u-only (UOnly))
            (let $u-only-2 (UOnly2))
            (let $c (C))
            (let $b (B $c))
            (let $x-old (XOld $p-alt $a $old-only))
            (let $x-new (XNew $b))
            (union $x-old $x-new)
            (let $u (U $x-old $b $c $u-only $u-only-2))
            (let $v (V $x-old $a))
            (let $p (P $u $v))
            (union $p $p-alt)
            "#,
        )
        .unwrap();

    let roots: Vec<_> = ["$p", "$u", "$v"]
        .into_iter()
        .map(|root| {
            let expr = egraph.parser.get_expr_from_string(None, root).unwrap();
            egraph.eval_expr(&expr).unwrap()
        })
        .collect();
    let best_calls = Cell::new(0);
    let extracted = egglog_experimental::extract_best_greedy_dag(
        &egraph,
        roots.clone(),
        CountingDagCostModel(&best_calls, egglog_experimental::DynamicCostModel),
    )
    .unwrap();
    let terms: Vec<_> = extracted
        .terms
        .iter()
        .map(|root| {
            let root = root.as_ref().unwrap();
            (root.cost, extracted.termdag.to_string(root.term))
        })
        .collect();

    assert_eq!(
        terms,
        [
            (0, "(PAlt)".to_owned(),),
            (
                5,
                "(U (XNew (B (C))) (B (C)) (C) (UOnly) (UOnly2))".to_owned(),
            ),
            (9, "(V (XOld (PAlt) (A) (OldOnly)) (A))".to_owned()),
        ]
    );
    for ((expected_sort, expected_value), (_, term)) in roots.iter().zip(&terms) {
        let expr = egraph.parser.get_expr_from_string(None, term).unwrap();
        let (actual_sort, actual_value) = egraph.eval_expr(&expr).unwrap();
        assert_eq!(actual_sort.name(), expected_sort.name());
        assert_eq!(actual_value, *expected_value);
    }
    // Twelve reachable constructor rows are costed during preparation. Exact
    // conflict rescoring reuses those costs instead of calling the model again.
    assert_eq!(best_calls.get(), 12);

    // The losing XOld snapshot reaches the root through PAlt, but the larger
    // sibling snapshot selects XNew. Reconciliation removes that apparent
    // cycle, so the finite P producer must remain available as a variant.
    let root_expr = egraph.parser.get_expr_from_string(None, "$p").unwrap();
    let root = egraph.eval_expr(&root_expr).unwrap();
    let variant_calls = Cell::new(0);
    let variants = egglog_experimental::extract_variants_greedy_dag(
        &egraph,
        vec![root],
        2,
        CountingDagCostModel(&variant_calls, egglog_experimental::DynamicCostModel),
    )
    .unwrap();
    let extracted_variants: Vec<_> = variants.variants[0]
        .iter()
        .map(|variant| (variant.cost, variants.termdag.to_string(variant.term)))
        .collect();
    assert_eq!(
        extracted_variants,
        [
            (0, "(PAlt)".to_owned()),
            (
                12,
                "(P (U (XNew (B (C))) (B (C)) (C) (UOnly) (UOnly2)) (V (XNew (B (C))) (A)))"
                    .to_owned(),
            ),
        ]
    );
    assert_eq!(variant_calls.get(), 12);
}

#[test]
fn test_greedy_dag_extract_respects_set_cost() {
    let result = run_dynamic_dag(
        "
        (extract daggy :extractor greedy-dag)
        (set-cost (Wide (Leaf 0)) 10)
        (extract daggy :extractor greedy-dag)",
    );

    assert_eq!(result.len(), 2);
    assert_eq!(
        result[0].to_string(),
        "(Pair (Wide (Leaf 0)) (Wide (Leaf 0)))\n"
    );
    assert_eq!(result[1].to_string(), "(Pair (Leaf 1) (Leaf 2))\n");
}

#[test]
fn test_greedy_dag_extract_avoids_cycle_from_python_issue_387() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let result = egraph
        .parse_and_run_program(
            None,
            &format!("{CYCLIC_DAG_FIXTURE}\n(extract victim :extractor greedy-dag)"),
        )
        .unwrap();

    assert_eq!(result.len(), 1);
    assert!(matches!(result[0], CommandOutput::ExtractBest(..)));
}

#[test]
fn test_greedy_dag_multi_extract_avoids_combined_root_cycle() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let result = egraph
        .parse_and_run_program(
            None,
            &format!("{CYCLIC_DAG_FIXTURE}\n(multi-extract 1 victim x :extractor greedy-dag)"),
        )
        .unwrap();

    assert!(matches!(result.as_slice(), [CommandOutput::UserDefined(_)]));
    assert_eq!(
        result[0].to_string(),
        "(\n   (\n      (S0 (S0 (S3 (S5 (S6)) (S6))))\n   )\n   (\n      (S0 (S3 (S5 (S6)) (S6)))\n   )\n)\n"
    );
}

#[test]
fn test_get_size_primitive() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let span = Span::Rust(Arc::new(RustSpan {
        file: "integration_test",
        line: 0,
        column: 0,
    }));

    let make_expr = |names: &[&str]| {
        Expr::Call(
            span.clone(),
            "get-size!".into(),
            names
                .iter()
                .map(|name| Expr::Lit(span.clone(), Literal::String((*name).into())))
                .collect(),
        )
    };

    let eval_size = |egraph: &mut egglog::EGraph, names: &[&str]| -> i64 {
        let expr = make_expr(names);
        let (_, value) = egraph.eval_expr(&expr).unwrap();
        egraph.value_to_base::<i64>(value)
    };

    assert_eq!(eval_size(&mut egraph, &[]), 0);
    assert_eq!(eval_size(&mut egraph, &["MkFoo"]), 0);
    assert_eq!(eval_size(&mut egraph, &["MkBar"]), 0);
    assert_eq!(eval_size(&mut egraph, &["MkFoo", "MkBar"]), 0);

    egraph
        .parse_and_run_program(
            None,
            "
            (datatype Foo (MkFoo i64))
            (datatype Bar (MkBar i64))
            (MkFoo 1)
            (MkFoo 2)
            (MkBar 10)
        ",
        )
        .unwrap();

    assert_eq!(eval_size(&mut egraph, &[]), 3);
    assert_eq!(eval_size(&mut egraph, &["MkFoo"]), 2);
    assert_eq!(eval_size(&mut egraph, &["MkBar"]), 1);
    assert_eq!(eval_size(&mut egraph, &["MkFoo", "MkBar"]), 3);
    assert_eq!(eval_size(&mut egraph, &["Unknown"]), 0);
}

#[test]
fn test_extract_set_cost_multiple_times_should_fail() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            "(with-dynamic-cost
                (datatype E (Add E E) (Sub E E :cost 200) (Num i64))
            )
            (set-cost (Num 2) 1000)",
        )
        .unwrap();

    egraph
        .parse_and_run_program(None, "(set-cost (Num 2) 1000)")
        .unwrap();

    let result = egraph.parse_and_run_program(None, "(set-cost (Num 2) 1)");
    assert!(result.is_err());
}

#[test]
fn test_extract_set_cost_decls() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            "(with-dynamic-cost
                (datatype E (Add E E) (Sub E E :cost 200) (Num i64))
                (constructor Mul (E E) E :cost 100)
                (datatype*
                  (E2 (Add2 E2 E2) (Sub2 E2 E2 :cost 200) (List VecE2) (Num2 i64))
                  (sort VecE2 (Vec E2))
                )
                (constructor Mul2 (E2 E2) E2)
            )
            (set-cost (Num 2) 1000)
            (set-cost (Num2 2) 1000)
            (set-cost (Mul (Num 2) (Num 2)) 1000)
            (set-cost (Sub2 (Num2 2) (Num2 2)) 1000)",
        )
        .unwrap();
}

#[test]
fn test_set_cost_rejects_negative_computed_values_without_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    egraph
        .parse_and_run_program(
            None,
            r#"
            (with-dynamic-cost (datatype E (Num i64)))
            (set-cost (Num 1) (+ 1 1))
            (extract (Num 1))
            "#,
        )
        .unwrap();

    let error = egraph
        .parse_and_run_program(None, "(set-cost (Num 2) (- 0 1))")
        .unwrap_err();
    assert!(
        error.to_string().contains("@validate-dynamic-cost"),
        "unexpected error: {error}"
    );

    egraph
        .parse_and_run_program(
            None,
            r#"
            (fail (check (= (cost_table_Num 2) -1)))
            (extract (Num 2))

            ; Direct cost-table writes are outside set-cost's validated
            ; protocol, but extraction must still remain panic-free.
            (set (cost_table_Num 3) -1)
            (extract (Num 3))
            "#,
        )
        .unwrap();
}

#[test]
fn test_multi_extract_two_variants_two_terms() {
    for extractor in ["", " :extractor greedy-dag"] {
        let mut egraph = egglog_experimental::new_experimental_egraph();
        let result = egraph
            .parse_and_run_program(
                None,
                &format!(
                    "
                    (with-dynamic-cost
                        (datatype E (Add E E) (Mul E E) (Num i64))
                    )

                    (union (Num 2) (Add (Num 1) (Num 1)))
                    (union (Num 2) (Mul (Num 1) (Num 2)))

                    (union (Num 4) (Add (Num 2) (Num 2)))
                    (union (Num 4) (Mul (Num 2) (Num 2)))

                    (multi-extract 2 (Num 2) (Num 4){extractor})"
                ),
            )
            .unwrap();

        let [CommandOutput::UserDefined(output)] = result.as_slice() else {
            panic!("expected one aggregate user-defined output, got {result:?}");
        };
        let output = output
            .as_ref()
            .as_any()
            .downcast_ref::<egglog_experimental::MultiExtractOutput>()
            .expect("user-defined output should retain its concrete multi-extract type");
        let terms: Vec<Vec<_>> = output
            .terms
            .iter()
            .map(|variants| {
                variants
                    .iter()
                    .map(|term| output.termdag.to_string(*term))
                    .collect()
            })
            .collect();

        assert_eq!(terms.iter().map(Vec::len).collect::<Vec<_>>(), [2, 2]);
        assert_eq!(terms[0][0], "(Num 2)");
        assert!(terms[0][1] == "(Add (Num 1) (Num 1))" || terms[0][1] == "(Mul (Num 1) (Num 2))");
        assert_eq!(terms[1][0], "(Num 4)");
        assert!(terms[1][1] == "(Add (Num 2) (Num 2))" || terms[1][1] == "(Mul (Num 2) (Num 2))");
    }
}

#[test]
fn test_multi_extract_returns_one_ordered_aggregate_including_empty_groups() {
    for extractor in ["", " :extractor greedy-dag"] {
        let mut egraph = egglog_experimental::new_experimental_egraph();
        let result = egraph
            .parse_and_run_program(
                None,
                &format!(
                    r#"
                    (datatype Math)
                    (constructor visible () Math)
                    (constructor hidden () Math :unextractable)
                    (multi-extract 1 (visible) 42 (hidden){extractor})
                    "#
                ),
            )
            .unwrap();

        let [CommandOutput::UserDefined(output)] = result.as_slice() else {
            panic!("expected one aggregate user-defined output, got {result:?}");
        };
        let output = output
            .as_ref()
            .as_any()
            .downcast_ref::<egglog_experimental::MultiExtractOutput>()
            .expect("user-defined output should retain its concrete multi-extract type");

        assert_eq!(
            output.terms.iter().map(Vec::len).collect::<Vec<_>>(),
            [1, 1, 0]
        );
        assert_eq!(output.termdag.to_string(output.terms[0][0]), "(visible)");
        assert_eq!(output.termdag.to_string(output.terms[1][0]), "42");
        assert_eq!(output.termdag.size(), 2);
    }
}

#[test]
fn test_multi_extract_single_variant_minimal_cost() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let result = egraph
        .parse_and_run_program(
            None,
            "
        (with-dynamic-cost
            (datatype E (Add E E :cost 3) (Mul E E :cost 10) (Num i64 :cost 1))
        )

        (union (Num 5) (Add (Num 2) (Num 3)))
        (union (Num 5) (Mul (Num 1) (Num 5)))
        (union (Add (Num 5) (Num 5)) (Mul (Num 2) (Num 5)))

        (multi-extract 1 (Mul (Num 2) (Num 5)))",
        )
        .unwrap();

    assert_eq!(result.len(), 1);
    let output = result[0].to_string();
    assert!(output.contains("(Add (Num 5) (Num 5))"));
    assert!(!output.contains("Mul"));
}

#[test]
fn test_print_table_stats() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let result = egraph
        .parse_and_run_program(
            None,
            "
        (datatype E (Add E E) (Num i64))
        (Add (Num 1) (Num 2))
        (Add (Num 1) (Num 3))
        (print-table-stats Add)",
        )
        .unwrap();

    assert_eq!(result.len(), 1);
    let output = result[0].to_string();

    assert!(output.contains("Add"), "missing table name: {output}");
    assert!(output.contains("(size 2)"), "missing size: {output}");
    assert!(
        output.contains("(columns"),
        "missing columns section: {output}"
    );
    // Both rows share (Num 1) in column 0; col 1 and the output column each
    // have two distinct eclasses.
    assert!(output.contains("(0 E 1)"), "wrong col 0 stats: {output}");
    assert!(output.contains("(1 E 2)"), "wrong col 1 stats: {output}");
    assert!(
        output.contains("(2 E 2)"),
        "wrong output col stats: {output}"
    );
    assert!(
        output.contains("(out-degrees"),
        "missing out-degrees section: {output}"
    );
    // (output -> combined inputs) pair is only emitted when n_inputs >= 2,
    // which Add satisfies; its target is the tuple "(0 1)".
    assert!(
        output.contains("(2 (0 1)"),
        "missing combined-input out-degree: {output}"
    );
    assert!(output.contains("(median "), "missing median stat: {output}");
}

#[test]
fn test_print_table_stats_all_tables() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let result = egraph
        .parse_and_run_program(
            None,
            "
        (datatype E (Add E E) (Num i64))
        (Add (Num 1) (Num 2))
        (print-table-stats)",
        )
        .unwrap();

    assert_eq!(result.len(), 1);
    let output = result[0].to_string();
    assert!(output.contains("Add"), "missing Add: {output}");
    assert!(output.contains("Num"), "missing Num: {output}");
}

#[test]
fn test_print_table_stats_unknown_table_errors() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    let result = egraph.parse_and_run_program(None, "(print-table-stats DoesNotExist)");
    assert!(result.is_err());
}

#[test]
fn test_multi_extract_with_set_cost() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let result = egraph
        .parse_and_run_program(
            None,
            "
        (with-dynamic-cost
            (datatype E (Add E E) (Mul E E) (Num i64))
        )

        (union (Num 10) (Add (Num 5) (Num 5)))
        (union (Num 10) (Mul (Num 2) (Num 5)))

        (union (Num 6) (Add (Num 3) (Num 3)))
        (union (Num 6) (Mul (Num 2) (Num 3)))

        (set-cost (Add (Num 5) (Num 5)) 1)
        (set-cost (Add (Num 3) (Num 3)) 1)

        (set-cost (Mul (Num 2) (Num 5)) 1000)
        (set-cost (Mul (Num 2) (Num 3)) 1000)

        (multi-extract 2 (Num 10) (Num 6))",
        )
        .unwrap();

    assert!(matches!(result.as_slice(), [CommandOutput::UserDefined(_)]));
    let output = result[0].to_string();
    assert!(output.contains("(Add (Num 5) (Num 5))"));
    assert!(output.contains("(Add (Num 3) (Num 3))"));
    assert!(!output.contains("Mul"));
}

#[test]
fn test_multi_extract_accepts_greedy_dag_extractor() {
    let result = run_dynamic_dag("(multi-extract 1 daggy :extractor greedy-dag)");

    assert_eq!(result.len(), 1);
    let output = result[0].to_string();
    assert!(
        output.contains("(Pair (Wide (Leaf 0)) (Wide (Leaf 0)))"),
        "expected shared DAG extraction: {output}"
    );
    assert!(
        !output.contains("(Pair (Leaf 1) (Leaf 2))"),
        "expected greedy DAG to prefer the shared term: {output}"
    );
}

#[test]
fn test_multi_extract_dag_accepts_greedy_dag_extractor() {
    let result = run_dynamic_dag("(multi-extract 1 :dag daggy :extractor greedy-dag)");

    assert_eq!(result.len(), 1);
    let output = result[0].to_string();
    let tokens: Vec<&str> = output.split_whitespace().collect();
    assert_eq!(
        tokens.join(" "),
        "(let ( (?t0 (Wide (Leaf 0))) ) ( ( (Pair ?t0 ?t0) ) ))"
    );
}

#[test]
fn test_keep_best_basic() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            r#"
        (datatype Math (Num i64) (Add Math Math))
        (relation Target (Math))

        ; put two nodes in the same eclass
        (union (Num 2) (Add (Num 1) (Num 1)))

        ; record what we care about
        (Target (Num 2))
        "#,
        )
        .unwrap();

    // Before keep-best: both Num and Add tables have entries, Target has 1 row.
    assert_eq!(egraph.get_size("Num"), 2);
    assert_eq!(egraph.get_size("Add"), 1);
    assert_eq!(egraph.get_size("Target"), 1);

    // Run keep-best on the Target relation.
    egraph
        .parse_and_run_program(None, r#"(keep-best "Target")"#)
        .unwrap();

    // After keep-best: Target still has exactly 1 row,
    // and it contains a constructor term that can be extracted.
    assert_eq!(egraph.get_size("Target"), 1);
    assert_eq!(egraph.get_size("Num"), 1);

    let result = egraph
        .parse_and_run_program(None, "(print-function Target 100)")
        .unwrap();
    let output = result[0].to_string();
    assert!(output.contains("Num") && !output.contains("Add"));
}

#[test]
fn test_keep_best_without_targets_fails_before_mutation() {
    for command in ["(keep-best)", "(keep-best :extractor greedy-dag)"] {
        let mut egraph = egglog_experimental::new_experimental_egraph();
        egraph
            .parse_and_run_program(None, "(relation R (i64)) (R 1)")
            .unwrap();

        let err = egraph.parse_and_run_program(None, command).unwrap_err();

        assert!(
            err.to_string()
                .contains("keep-best expects at least one table name"),
            "unexpected error for {command}: {err}"
        );
        assert_eq!(
            egraph.get_size("R"),
            1,
            "{command} mutated the e-graph before failing"
        );
    }
}

#[test]
fn test_keep_best_respects_set_cost() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            r#"
        (with-dynamic-cost
          (datatype Math (Num i64) (Add Math Math)))
        (relation Target (Math))

        (union (Num 2) (Add (Num 1) (Num 1)))
        (set-cost (Num 2) 100)
        (Target (Num 2))
        "#,
        )
        .unwrap();

    egraph
        .parse_and_run_program(None, r#"(keep-best "Target")"#)
        .unwrap();

    let result = egraph
        .parse_and_run_program(None, "(print-function Target 100)")
        .unwrap();
    let output = result[0].to_string();
    assert!(
        output.contains("(Add (Num 1) (Num 1))"),
        "expected dynamic cost model to prefer Add: {output}"
    );
    assert!(
        !output.contains("(Num 2)"),
        "expected high-cost Num representative to be removed: {output}"
    );
}

#[test]
fn test_keep_best_accepts_greedy_dag_extractor() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            &format!(
                "{DYNAMIC_DAG_FIXTURE}
        (relation Target (E))
        (Target daggy)"
            ),
        )
        .unwrap();

    egraph
        .parse_and_run_program(None, r#"(keep-best "Target" :extractor greedy-dag)"#)
        .unwrap();

    let result = egraph
        .parse_and_run_program(None, "(print-function Target 10)")
        .unwrap();
    let output = result[0].to_string();
    assert!(
        output.contains("(Pair (Wide (Leaf 0)) (Wide (Leaf 0)))"),
        "expected shared DAG extraction: {output}"
    );
    assert!(
        !output.contains("(Pair (Leaf 1) (Leaf 2))"),
        "expected keep-best to retain the greedy DAG representative: {output}"
    );
}

#[test]
fn test_keep_best_clears_other_tables() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            r#"
        (datatype Math (Num i64) (Add Math Math))
        (relation Target (Math))
        (Num 42)
        (Add (Num 1) (Num 2))
        (Target (Num 42))
        "#,
        )
        .unwrap();

    let before_num = egraph.get_size("Num");
    let before_add = egraph.get_size("Add");
    assert!(before_num >= 3); // Num 42, Num 1, Num 2
    assert_eq!(before_add, 1);
    assert_eq!(egraph.get_size("Target"), 1);

    egraph
        .parse_and_run_program(None, r#"(keep-best "Target")"#)
        .unwrap();

    // After keep-best, Add table (not referenced by Target) should be empty.
    // The Num table entry for 42 should be re-inserted (it's reachable via Target).
    // Num 1 and Num 2 are not reachable from Target, so they should be gone.
    assert_eq!(egraph.get_size("Add"), 0);
    assert_eq!(egraph.get_size("Target"), 1);
    assert_eq!(egraph.get_size("Num"), 1); // only Num 42 is kept
}

#[test]
fn test_keep_best_function_table() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            r#"
        (datatype Math (Num i64) (Add Math Math))
        (function Best (Math) i64 :no-merge)

        ; two nodes in one eclass, so extraction has to pick the cheaper term
        (union (Num 2) (Add (Num 1) (Num 1)))

        (set (Best (Num 2)) 7)
        "#,
        )
        .unwrap();

    assert_eq!(egraph.get_size("Best"), 1);
    assert_eq!(egraph.get_size("Add"), 1);

    // A `function` table re-inserts via `set`, unlike the constructor and
    // relation cases above, and carries a non-eq-sort output column.
    egraph
        .parse_and_run_program(None, r#"(keep-best "Best")"#)
        .unwrap();

    assert_eq!(egraph.get_size("Best"), 1);
    assert_eq!(egraph.get_size("Add"), 0);

    // The key comes back as the cheapest term for its eclass, and the output
    // column survives the round trip.
    let result = egraph
        .parse_and_run_program(None, "(print-function Best 100)")
        .unwrap();
    let output = result[0].to_string();
    assert!(output.contains("(Num 2)"), "unexpected output: {output}");
    assert!(output.contains("7"), "unexpected output: {output}");
    assert!(!output.contains("Add"), "unexpected output: {output}");
}

#[test]
fn test_keep_best_mixed_function_and_relation() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            r#"
        (datatype Math (Num i64) (Add Math Math))
        (relation Target (Math))
        (function Best (Math) i64 :no-merge)

        (union (Num 2) (Add (Num 1) (Num 1)))
        (union (Num 3) (Add (Num 1) (Num 2)))

        (Target (Num 3))
        (set (Best (Num 2)) 7)
        "#,
        )
        .unwrap();

    // One keep-best call spanning both subtypes, so each table has to be
    // dispatched independently on the way back in.
    egraph
        .parse_and_run_program(None, r#"(keep-best "Target" "Best")"#)
        .unwrap();

    assert_eq!(egraph.get_size("Target"), 1);
    assert_eq!(egraph.get_size("Best"), 1);
    assert_eq!(egraph.get_size("Add"), 0);

    let target = egraph
        .parse_and_run_program(None, "(print-function Target 100)")
        .unwrap()[0]
        .to_string();
    assert!(target.contains("(Num 3)"), "unexpected output: {target}");

    let best = egraph
        .parse_and_run_program(None, "(print-function Best 100)")
        .unwrap()[0]
        .to_string();
    assert!(best.contains("(Num 2)"), "unexpected output: {best}");
    assert!(best.contains("7"), "unexpected output: {best}");
}

#[test]
fn test_top_level_let_scheduler_persists_on_the_egraph() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            r#"
        (ruleset copy)
        (ruleset grow)
        (relation R (i64))
        (relation S (i64))
        (relation Seed ())
        (R 0)
        (R 1)
        (R 2)
        (Seed)
        (rule ((R x)) ((S x)) :ruleset copy :name "copy")
        (rule ((Seed)) ((R 3)) :ruleset grow :name "grow")
        "#,
        )
        .unwrap();

    let_backoff(&mut egraph);

    egraph
        .parse_and_run_program(
            None,
            r#"
        (run-schedule
          (seq
            (run-with bo copy)
            (run grow)
            (run-with bo copy)))
        "#,
        )
        .unwrap();

    assert_eq!(
        eval_get_size(&mut egraph, &["S"]),
        3,
        "ordinary back-off should replay the queued copy backlog and should not depend on fresh rematching"
    );
}

#[test]
fn test_top_level_let_scheduler_survives_egraph_clone() {
    let mut original = new_copy_egraph();
    let_backoff(&mut original);

    let mut cloned = original.clone();
    run_bo_copy(&mut cloned);
    run_bo_copy(&mut original);

    assert_eq!(eval_get_size(&mut cloned, &["S"]), 1);
    assert_eq!(eval_get_size(&mut original, &["S"]), 1);
}

#[test]
fn test_top_level_let_scheduler_redeclaration_returns_error() {
    let mut egraph = new_copy_egraph();
    let_backoff(&mut egraph);

    let err = egraph
        .parse_and_run_program(
            None,
            "(let-scheduler bo (back-off :match-limit 10 :ban-length 1))",
        )
        .unwrap_err();

    assert!(err.to_string().contains("Scheduler bo already exists"));

    run_bo_copy(&mut egraph);
    assert_eq!(eval_get_size(&mut egraph, &["S"]), 1);
}

#[test]
fn test_let_scheduler_unknown_scheduler_returns_error() {
    let mut egraph = new_copy_egraph();
    let err = egraph
        .parse_and_run_program(None, "(let-scheduler bo (missing-scheduler))")
        .unwrap_err();
    assert!(
        err.to_string()
            .contains("Unknown scheduler: missing-scheduler")
    );

    let mut egraph = new_copy_egraph();
    let err = egraph
        .parse_and_run_program(
            None,
            "(run-schedule (let-scheduler bo (missing-scheduler)))",
        )
        .unwrap_err();
    assert!(
        err.to_string()
            .contains("Unknown scheduler: missing-scheduler")
    );
}

#[test]
fn test_top_level_let_scheduler_invalidates_after_push_pop() {
    let mut egraph = new_copy_egraph();

    for _ in 0..2 {
        egraph.parse_and_run_program(None, "(push)").unwrap();
        let_backoff(&mut egraph);
        run_bo_copy(&mut egraph);
        assert_eq!(eval_get_size(&mut egraph, &["S"]), 1);
        egraph.parse_and_run_program(None, "(pop)").unwrap();
        assert_eq!(eval_get_size(&mut egraph, &["S"]), 0);

        let err = egraph
            .parse_and_run_program(None, "(run-schedule (run-with bo copy))")
            .unwrap_err();
        assert!(err.to_string().contains("Unknown scheduler: bo"));
    }
}

#[test]
fn test_top_level_let_scheduler_survives_pop_when_declared_before_push() {
    let mut egraph = new_copy_egraph();
    let_backoff(&mut egraph);
    egraph.parse_and_run_program(None, "(push)").unwrap();
    run_bo_copy(&mut egraph);
    assert_eq!(eval_get_size(&mut egraph, &["S"]), 1);

    egraph.parse_and_run_program(None, "(pop)").unwrap();
    assert_eq!(eval_get_size(&mut egraph, &["S"]), 0);

    run_bo_copy(&mut egraph);
    assert_eq!(eval_get_size(&mut egraph, &["S"]), 1);
}

#[test]
fn test_extract_missing_expression_returns_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let err = egraph.parse_and_run_program(None, "(extract)").unwrap_err();

    assert!(
        err.to_string()
            .contains("extract expects an expression and optional variant count")
    );
}

#[test]
fn test_extract_extra_arguments_return_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let err = egraph
        .parse_and_run_program(None, "(extract 0 1 2)")
        .unwrap_err();

    assert!(err.to_string().contains(
        "extract expects an expression, optional variant count, and optional :extractor"
    ));
}

#[test]
fn test_extract_negative_variants_returns_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(None, "(datatype E (Num i64))")
        .unwrap();

    let err = egraph
        .parse_and_run_program(None, "(extract (Num 1) -1)")
        .unwrap_err();

    assert!(err.to_string().contains("negative number of variants"));
}

#[test]
fn test_extract_zero_variants_preserves_best_extract_behavior() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let result = egraph
        .parse_and_run_program(
            None,
            "
        (with-dynamic-cost
            (datatype E (Add E E :cost 10) (Num i64 :cost 1))
        )
        (union (Num 2) (Add (Num 1) (Num 1)))
        (extract (Num 2) 0)",
        )
        .unwrap();

    assert_eq!(result.len(), 1);
    assert_eq!(result[0].to_string(), "(Num 2)\n");
}

#[test]
fn test_greedy_dag_extract_zero_variants_returns_empty_for_all_root_kinds() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    egraph
        .parse_and_run_program(None, "(datatype E (Num i64)) (sort IntVec (Vec i64))")
        .unwrap();
    let roots = ["1", "(vec-of 1)", "(Num 1)"]
        .into_iter()
        .map(|source| {
            let expr = egraph.parser.get_expr_from_string(None, source).unwrap();
            egraph.eval_expr(&expr).unwrap()
        })
        .collect();

    let calls = Cell::new(0);
    let extracted = egglog_experimental::extract_variants_greedy_dag(
        &egraph,
        roots,
        0,
        CountingDagCostModel(&calls, egglog::extract::AdditiveCostModel::default()),
    )
    .unwrap();

    assert_eq!(extracted.variants.len(), 3);
    assert!(extracted.variants.iter().all(Vec::is_empty));
    assert_eq!(calls.get(), 0);
}

#[test]
fn test_greedy_dag_tracks_eq_dependencies_nested_in_containers() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    egraph
        .parse_and_run_program(
            None,
            "(datatype* (E (Leaf) (List VecE)) (sort VecE (Vec E)))",
        )
        .unwrap();
    let expr = egraph
        .parser
        .get_expr_from_string(None, "(List (vec-of (Leaf)))")
        .unwrap();
    let (sort, value) = egraph.eval_expr(&expr).unwrap();

    // Discovery records the List producer before Leaf. Reaching List therefore
    // requires the reverse worklist index to include the E value inside VecE.
    let calls = Cell::new(0);
    let extracted = egglog_experimental::extract_best_greedy_dag(
        &egraph,
        vec![(sort, value)],
        CountingDagCostModel(&calls, egglog::extract::AdditiveCostModel::default()),
    )
    .unwrap();
    let root = extracted.terms[0].as_ref().unwrap();

    assert_eq!(root.cost, 2);
    assert_eq!(
        extracted.termdag.to_string(root.term),
        "(List (vec-of (Leaf)))"
    );
    assert_eq!(calls.get(), 3);
}

#[test]
fn test_greedy_dag_accepts_non_additive_monoid_cost() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    egraph
        .parse_and_run_program(
            None,
            "(datatype E (Cheap) (Expensive) (Pair E E))
             (let $child (Cheap))
             (union $child (Expensive))
             (let $root (Pair $child $child))",
        )
        .unwrap();
    let root_expr = egraph.parser.get_expr_from_string(None, "$root").unwrap();
    let root = egraph.eval_expr(&root_expr).unwrap();

    let extracted =
        egglog_experimental::extract_best_greedy_dag(&egraph, vec![root], MaxCostModel).unwrap();
    let root = extracted.terms[0].as_ref().unwrap();

    // `max` combines the Pair cost (3) and Cheap cost (2); addition would be 5.
    assert_eq!(root.cost, MaxCost(3));
    assert_eq!(
        extracted.termdag.to_string(root.term),
        "(Pair (Cheap) (Cheap))"
    );
}

#[test]
fn test_greedy_dag_costs_each_reachable_node_once_for_variants() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    egraph
        .parse_and_run_program(
            None,
            "(datatype E (Leaf i64))
             (let $root (Leaf 1))
             (union $root (Leaf 2))",
        )
        .unwrap();
    let root_expr = egraph.parser.get_expr_from_string(None, "$root").unwrap();
    let root = egraph.eval_expr(&root_expr).unwrap();

    let calls = Cell::new(0);
    let extracted = egglog_experimental::extract_variants_greedy_dag(
        &egraph,
        vec![root.clone(), root],
        2,
        CountingDagCostModel(&calls, egglog::extract::AdditiveCostModel::default()),
    )
    .unwrap();

    assert_eq!(
        extracted.variants.iter().map(Vec::len).collect::<Vec<_>>(),
        [2, 2]
    );
    // Two producer rows and their two primitive children are each costed once,
    // including during variant rescoring and debug fixed-point validation.
    assert_eq!(calls.get(), 4);
}

#[test]
fn test_greedy_dag_extract_variants_rank_root_alternatives() {
    let result = run_dynamic_dag("(extract daggy 2 :extractor greedy-dag)");

    assert_eq!(
        result[0].to_string(),
        "(\n   (Pair (Wide (Leaf 0)) (Wide (Leaf 0)))\n   (Pair (Leaf 1) (Leaf 2))\n)\n"
    );
}

#[test]
fn test_invalid_run_schedule_returns_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let err = egraph
        .parse_and_run_program(None, "(run-schedule (run 1))")
        .unwrap_err();

    assert!(
        err.to_string()
            .contains("Expected ruleset name or :until clause")
    );
}

#[test]
fn test_unknown_scheduler_returns_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let err = egraph
        .parse_and_run_program(None, "(run-schedule (let-scheduler bo (not-a-scheduler)))")
        .unwrap_err();

    assert!(err.to_string().contains("Unknown scheduler"));
}

#[test]
fn test_unknown_scheduler_binding_returns_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let err = egraph
        .parse_and_run_program(None, "(run-schedule (run-with bo))")
        .unwrap_err();

    assert!(err.to_string().contains("Unknown scheduler"));
}

#[test]
fn test_invalid_scheduler_tags_return_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let err = egraph
        .parse_and_run_program(
            None,
            r#"(run-schedule (let-scheduler bo (back-off "x" 1)))"#,
        )
        .unwrap_err();

    assert!(err.to_string().contains("Invalid scheduler tag name"));
}

#[test]
fn test_odd_scheduler_tags_return_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let err = egraph
        .parse_and_run_program(
            None,
            "(run-schedule (let-scheduler bo (back-off :match-limit)))",
        )
        .unwrap_err();

    assert!(err.to_string().contains("key/value pairs"));
}

#[test]
fn test_duplicate_scheduler_tags_return_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let err = egraph
        .parse_and_run_program(
            None,
            "(run-schedule (let-scheduler bo (back-off :match-limit 1 :match-limit 2)))",
        )
        .unwrap_err();

    assert!(err.to_string().contains("already exists"));
}

#[test]
fn test_invalid_scheduler_config_returns_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let err = egraph
        .parse_and_run_program(
            None,
            r#"(run-schedule (let-scheduler bo (back-off :match-limit "x")))"#,
        )
        .unwrap_err();

    assert!(err.to_string().contains(":match-limit"));
}

#[test]
fn test_unknown_backoff_tag_returns_error() {
    for tag in [":node-limt", ":eager-apply"] {
        let mut egraph = egglog_experimental::new_experimental_egraph();
        let err = egraph
            .parse_and_run_program(
                None,
                &format!("(run-schedule (let-scheduler bo (back-off {tag} 10)))"),
            )
            .unwrap_err();

        assert!(err.to_string().contains("Unknown back-off scheduler tag"));
        assert!(err.to_string().contains(tag));
    }
}

#[test]
fn test_negative_scheduler_config_returns_error_instead_of_panicking() {
    for tag in [":match-limit", ":ban-length", ":node-limit"] {
        let mut egraph = egglog_experimental::new_experimental_egraph();
        let err = egraph
            .parse_and_run_program(
                None,
                &format!("(run-schedule (let-scheduler bo (back-off {tag} -1)))"),
            )
            .unwrap_err();

        assert!(err.to_string().contains("non-negative"));
    }
}

#[test]
fn test_multi_extract_bad_arity_returns_error_instead_of_panicking() {
    for program in [
        "(multi-extract)",
        "(multi-extract 1)",
        "(multi-extract 1 :dag)",
    ] {
        let mut egraph = egglog_experimental::new_experimental_egraph();

        let err = egraph.parse_and_run_program(None, program).unwrap_err();

        assert!(
            err.to_string()
                .contains("multi-extract expects at least a variant count and one expression"),
            "unexpected error for {program}: {err}"
        );
    }
}

#[test]
fn test_multi_extract_dag_only_in_documented_position() {
    for program in ["(multi-extract 1 a :dag)", "(multi-extract 1 :dag :dag a)"] {
        let mut egraph = egglog_experimental::new_experimental_egraph();
        let err = egraph
            .parse_and_run_program(
                None,
                &format!("(datatype Math (Num i64)) (let a (Num 1)) {program}"),
            )
            .unwrap_err();
        assert!(
            err.to_string().contains(":dag"),
            "unexpected error for {program}: {err}"
        );
    }
}

fn add_copy_backoff_program(egraph: &mut egglog::EGraph) {
    egraph
        .parse_and_run_program(
            None,
            r#"
        (ruleset copy)
        (relation R (i64))
        (relation S (i64))
        (R 0)
        (R 1)
        (R 2)
        (R 3)
        (rule ((R x)) ((S x)) :ruleset copy :name "copy")
        "#,
        )
        .unwrap();
}

fn only_run_report(outputs: &[CommandOutput]) -> &egglog_reports::RunReport {
    match outputs {
        [CommandOutput::RunSchedule(report)] => report,
        other => panic!("expected one RunSchedule output, got {other:?}"),
    }
}

#[test]
fn test_multi_extract_negative_variants_returns_error_instead_of_panicking() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(None, "(datatype E (Num i64))")
        .unwrap();

    let err = egraph
        .parse_and_run_program(None, "(multi-extract -1 (Num 1))")
        .unwrap_err();

    assert!(err.to_string().contains("negative number of variants"));
}

#[test]
fn test_multi_extract_zero_variants_returns_error_instead_of_extracting() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(None, "(datatype E (Num i64))")
        .unwrap();

    let err = egraph
        .parse_and_run_program(None, "(multi-extract 0 (Num 1))")
        .unwrap_err();

    assert!(err.to_string().contains("positive number of variants"));
}

#[test]
fn test_backoff_run_schedule_should_not_report_progress_without_egraph_updates() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    add_copy_backoff_program(&mut egraph);

    let outputs = egraph
        .parse_and_run_program(
            None,
            r#"
        (run-schedule
          (let-scheduler bo (back-off :match-limit 1 :ban-length 3))
          (run-with bo copy))
        "#,
        )
        .unwrap();

    let report = only_run_report(&outputs);
    assert_eq!(egraph.get_size("S"), 0);
    assert!(
        !report.updated,
        "banning work in the scheduler is not database progress"
    );
    assert!(
        !report.can_stop,
        "the scheduler still has deferred work after the ban"
    );
}

#[test]
fn test_saturate_continues_until_scheduler_can_stop_after_no_progress_ban() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    add_copy_backoff_program(&mut egraph);

    let outputs = egraph
        .parse_and_run_program(
            None,
            r#"
        (run-schedule
          (let-scheduler bo (back-off :match-limit 1 :ban-length 3))
          (saturate (run-with bo copy)))
        "#,
        )
        .unwrap();

    let report = only_run_report(&outputs);
    assert_eq!(
        egraph.get_size("S"),
        4,
        "saturate should keep running while the scheduler reports deferred work"
    );
    assert!(
        report.updated,
        "the eventual copy applications should be reported as database progress"
    );
}

#[test]
fn test_schedule_expr_eval() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            r#"
        (datatype Math (Num i64) (Add Math Math))
        (relation Target (Math))
        (union (Num 2) (Add (Num 1) (Num 1)))
        (Target (Num 2))
        "#,
        )
        .unwrap();

    // `(eval <expr>)` evaluates an expression as a schedule step in the full
    // read/write (FullState) context. Here it calls the `get-size!` reading
    // primitive, which is only admissible because of that full context.
    egraph
        .parse_and_run_program(
            None,
            r#"
        (run-schedule
          (eval (get-size!)))
        "#,
        )
        .unwrap();

    // `(eval <expr>)` also adds constructor terms to the e-graph, just like a
    // top-level expression would.
    let before = egraph.get_size("Add");
    egraph
        .parse_and_run_program(
            None,
            r#"
              (run-schedule
                (eval (Add (Num 3) (Num 4))))
              "#,
        )
        .unwrap();
    assert_eq!(
        egraph.get_size("Add"),
        before + 1,
        "(eval ...) should add the new Add term to the e-graph"
    );
}

#[test]
fn test_schedule_user_defined_command() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            r#"
        (datatype Math (Num i64) (Add Math Math))
        (relation Target (Math))
        (union (Num 2) (Add (Num 1) (Num 1)))
        (Target (Num 2))
        "#,
        )
        .unwrap();

    // keep-best as a step inside run-schedule
    egraph
        .parse_and_run_program(
            None,
            r#"
        (run-schedule
          (keep-best "Target"))
        "#,
        )
        .unwrap();

    assert_eq!(egraph.get_size("Target"), 1);
}

#[test]
fn test_schedule_preserves_aggregate_multi_extract_output() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    let outputs = egraph
        .parse_and_run_program(
            None,
            r#"
            (datatype Math (Num i64))
            (run-schedule
              (multi-extract 1 (Num 1) 2))
            "#,
        )
        .unwrap();

    assert_eq!(outputs.len(), 2);
    assert!(matches!(outputs[0], CommandOutput::UserDefined(_)));
    assert!(matches!(outputs[1], CommandOutput::RunSchedule(..)));
}

#[test]
fn test_schedule_repeat_push_pop_print_size() {
    use egglog::CommandOutput;
    let mut egraph = egglog_experimental::new_experimental_egraph();

    // Commutativity and both directions of associativity for Add.
    egraph
        .parse_and_run_program(
            None,
            r#"
        (datatype Math (Num i64) (Add Math Math))
        (ruleset math-rules)
        (rewrite (Add a b) (Add b a) :ruleset math-rules)
        (rewrite (Add (Add a b) c) (Add a (Add b c)) :ruleset math-rules)
        (rewrite (Add a (Add b c)) (Add (Add a b) c) :ruleset math-rules)
        "#,
        )
        .unwrap();

    // Each of 3 outer iterations:
    //   1. push the current (fact-free) state
    //   2. eval a sum-1-to-5 addition chain to add it to the e-graph
    //   3. repeat 5 times: run math-rules one step, then print-size
    //   4. pop back to the fact-free state
    //
    // print-size fires inside the inner repeat, so each outer iteration
    // emits 5 PrintAllFunctionsSize outputs — 15 total.
    let outputs = egraph
        .parse_and_run_program(
            None,
            r#"
        (run-schedule
          (repeat 3
            (push)
            (eval (Add (Add (Add (Add (Num 1) (Num 2)) (Num 3)) (Num 4)) (Num 5)))
            (repeat 5
              (run math-rules)
              (print-size))
            (pop)))
        "#,
        )
        .unwrap();

    // 3 outer iterations × 5 inner steps = 15 PrintAllFunctionsSize outputs,
    // followed by a single RunSchedule.
    let print_size_outputs: Vec<_> = outputs
        .iter()
        .filter(|o| matches!(o, CommandOutput::PrintAllFunctionsSize(_)))
        .collect();
    assert_eq!(
        print_size_outputs.len(),
        15,
        "expected 3 × 5 = 15 print-size outputs, got {}",
        print_size_outputs.len()
    );

    let add_sizes: Vec<usize> = print_size_outputs
        .into_iter()
        .map(|o| match o {
            CommandOutput::PrintAllFunctionsSize(v) => {
                let add = v.iter().find(|(n, _)| n == "Add").map(|(_, s)| *s).unwrap();
                let num = v.iter().find(|(n, _)| n == "Num").map(|(_, s)| *s).unwrap();
                // Num is always 5 (one per distinct literal, shared via e-class).
                assert_eq!(num, 5, "Num size should stay at 5");
                add
            }
            _ => unreachable!(),
        })
        .collect();

    // Expected Add sizes after each of the 5 rule steps, measured within a
    // single outer iteration (the push/pop makes all three groups identical).
    let expected = [14, 50, 137, 182, 180];
    for group in 0..3 {
        for step in 0..5 {
            assert_eq!(
                add_sizes[group * 5 + step],
                expected[step],
                "outer iteration {group}, inner step {step}: unexpected Add size"
            );
        }
    }

    // The last output is always the RunSchedule report.
    assert!(
        matches!(outputs.last().unwrap(), CommandOutput::RunSchedule(_)),
        "last output must be RunSchedule"
    );

    // After the repeat the pop has unwound all facts — the e-graph is back to
    // the state it had after defining the datatype (no concrete tuples).
    assert_eq!(egraph.get_size("Add"), 0);
    assert_eq!(egraph.get_size("Num"), 0);
}

#[test]
fn test_schedule_commands_and_actions() {
    use egglog::CommandOutput;
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            r#"
        (datatype Math (Num i64) (Add Math Math))
        (relation Target (Math))
        (union (Num 2) (Add (Num 1) (Num 1)))
        (Target (Num 2))
        "#,
        )
        .unwrap();

    // print-size inside run-schedule returns a CommandOutput::PrintFunctionSize
    let outputs = egraph
        .parse_and_run_program(
            None,
            r#"
        (run-schedule
          (print-size Target))
        "#,
        )
        .unwrap();

    // outputs should be: [PrintFunctionSize(...), RunSchedule(report)]
    assert!(
        outputs.len() >= 2,
        "expected at least 2 outputs, got {}",
        outputs.len()
    );
    assert!(matches!(outputs[0], CommandOutput::PrintFunctionSize(_)));
    assert!(matches!(
        outputs.last().unwrap(),
        CommandOutput::RunSchedule(_)
    ));

    // extract inside run-schedule
    let outputs = egraph
        .parse_and_run_program(
            None,
            r#"
        (run-schedule
          (extract (Num 2) 0))
        "#,
        )
        .unwrap();
    assert!(
        outputs
            .iter()
            .any(|o| matches!(o, CommandOutput::ExtractBest(..)))
    );

    // union as a schedule step
    egraph
        .parse_and_run_program(
            None,
            r#"
        (run-schedule
          (union (Num 1) (Num 2)))
        "#,
        )
        .unwrap();

    // push/pop as schedule steps
    egraph
        .parse_and_run_program(
            None,
            r#"
        (run-schedule
          (push)
          (pop))
        "#,
        )
        .unwrap();
}

#[test]
fn test_backoff_node_limit() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    // "count" grows one Num per iteration; "pair" is quadratic in the number
    // of Nums. Without a node limit this saturates at 201 Nums and ~40k Adds.
    egraph
        .parse_and_run_program(
            None,
            r#"
        (ruleset explode)
        (datatype Math (Num i64) (Add Math Math))
        (Num 0)
        (rule ((= e (Num i)) (< i 200)) ((Num (+ i 1))) :ruleset explode :name "count")
        (rule ((= a (Num x)) (= b (Num y))) ((Add a b)) :ruleset explode :name "pair")
        (run-schedule
          (let-scheduler bo (back-off :node-limit 500))
          (saturate (run-with bo explode)))
        "#,
        )
        .unwrap();

    let nodes = egraph.num_nodes();
    // This program has no node-producing merge callbacks: it reaches the soft
    // threshold and remains within the expected final rule batch.
    assert!(
        (500..=600).contains(&nodes),
        "unexpected final size: {nodes}"
    );

    // (get-node-size!) agrees with EGraph::num_nodes and, since this program
    // has no analysis tables, with (get-size!).
    let span = span!();
    let expr = Expr::Call(span.clone(), "get-node-size!".into(), vec![]);
    let (_, value) = egraph.eval_expr(&expr).unwrap();
    assert_eq!(egraph.value_to_base::<i64>(value), nodes as i64);
    assert_eq!(eval_get_size(&mut egraph, &[]), nodes as i64);
}

#[test]
fn test_get_node_size_excludes_analysis_tables() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    egraph
        .parse_and_run_program(
            None,
            r#"
        (datatype Math (Num i64))
        (function depth (Math) i64 :no-merge)
        (relation seen (Math))
        (Num 0)
        (Num 1)
        (set (depth (Num 0)) 0)
        (seen (Num 0))
        (seen (Num 1))
        "#,
        )
        .unwrap();

    let span = span!();
    let expr = Expr::Call(span.clone(), "get-node-size!".into(), vec![]);
    let (_, value) = egraph.eval_expr(&expr).unwrap();
    // Two Num nodes; the depth analysis row and the two relation rows (a
    // constructor over a non-unionable sort) are excluded.
    assert_eq!(egraph.value_to_base::<i64>(value), 2);
    // ... but included by (get-size!).
    assert_eq!(eval_get_size(&mut egraph, &[]), 5);
    assert_eq!(egraph.num_nodes(), 2);
}

#[test]
fn test_get_node_size_excludes_custom_let_and_hidden_tables() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    egraph
        .parse_and_run_program(
            None,
            r#"
        (sort S)
        (constructor C () S)
        (constructor Hidden () S :internal-hidden)
        (function analysis () S :merge old)
        (relation seen ())
        (C)
        (Hidden)
        (set (analysis) (C))
        (let root (C))
        (seen)
        "#,
        )
        .unwrap();

    let expr = Expr::Call(span!(), "get-node-size!".into(), vec![]);
    let (_, value) = egraph.eval_expr(&expr).unwrap();
    assert_eq!(egraph.value_to_base::<i64>(value), 1);
    assert_eq!(egraph.num_nodes(), 1);
}

#[test]
fn test_multi_extract_dag() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    let outputs = egraph
        .parse_and_run_program(
            None,
            r#"
        (datatype Math (Num i64) (Add Math Math) (Neg Math))
        (let a (Add (Num 1) (Num 2)))
        (let b (Neg (Add (Num 1) (Num 2))))
        (multi-extract 1 :dag a b)
        "#,
        )
        .unwrap();
    let printed = outputs.last().unwrap().to_string();
    let tokens: Vec<&str> = printed.split_whitespace().collect();
    // The shared (Add (Num 1) (Num 2)) is bound once; leaves stay inline.
    assert_eq!(
        tokens.join(" "),
        "(let ( (?t0 (Add (Num 1) (Num 2))) ) ( ( ?t0 ) ( (Neg ?t0) ) ))"
    );

    // :dag output must expand to exactly the non-dag output.
    let plain = egraph
        .parse_and_run_program(None, "(multi-extract 1 a b)")
        .unwrap()
        .last()
        .unwrap()
        .to_string();
    let plain_tokens: Vec<&str> = plain.split_whitespace().collect();
    assert_eq!(
        plain_tokens.join(" "),
        "( ( (Add (Num 1) (Num 2)) ) ( (Neg (Add (Num 1) (Num 2))) ) )"
    );
}

#[test]
fn test_extractor_keyword_does_not_shadow_a_value_named_extractor() {
    // `:extractor` is a legal identifier, so a value may be bound to it.
    let mut egraph = egglog_experimental::new_experimental_egraph();
    let result = egraph
        .parse_and_run_program(
            None,
            r#"
            (relation table1 (i64))
            (relation table2 (i64))
            (table1 1)
            (table2 2)
            (let :extractor "table1")
            (keep-best :extractor "table2")"#,
        )
        .expect("a table name bound to `:extractor` is positional, not the selector");
    assert!(result.is_empty(), "unexpected output: {result:?}");
}

#[test]
fn test_extractor_keyword_does_not_shadow_a_term_named_extractor() {
    let result =
        run_dynamic_dag("(let :extractor (Leaf 1))\n(multi-extract 1 :extractor (Leaf 2))");
    assert!(matches!(result.as_slice(), [CommandOutput::UserDefined(_)]));
    let output = result[0].to_string();
    assert!(output.contains("(Leaf 1)"));
    assert!(output.contains("(Leaf 2)"));
}

/// A trailing `<symbol> <symbol>` pair is genuinely ambiguous: it is
/// indistinguishable from the selector without changing the surface syntax.
/// The selector wins, so a value named `:extractor` cannot be the
/// second-to-last argument when the last one is also a bare symbol.
#[test]
fn test_extractor_keyword_wins_against_a_trailing_symbol_pair() {
    let err = egglog_experimental::new_experimental_egraph()
        .parse_and_run_program(
            None,
            &format!("{DYNAMIC_DAG_FIXTURE}\n(let :extractor (Leaf 1))\n(multi-extract 1 :extractor daggy)"),
        )
        .expect_err("documented limitation");
    assert!(
        err.to_string().contains("unknown extractor: daggy"),
        "unexpected error: {err}"
    );
}

#[test]
fn test_extractor_keyword_does_not_shadow_a_variant_count_named_extractor() {
    let result = run_dynamic_dag("(let :extractor 2)\n(extract daggy :extractor)");
    assert_eq!(result.len(), 1);
}

#[test]
fn test_unknown_trailing_extractor_is_still_rejected() {
    let err = egglog_experimental::new_experimental_egraph()
        .parse_and_run_program(
            None,
            &format!("{DYNAMIC_DAG_FIXTURE}\n(extract daggy :extractor greedy-dg)"),
        )
        .expect_err("a misspelled extractor name must not be treated as positional");
    assert!(
        err.to_string().contains("unknown extractor: greedy-dg"),
        "unexpected error: {err}"
    );
}

fn run_deep_greedy_dag_chain(
    depth: usize,
    bottom_options: &str,
    label: &str,
) -> std::process::Output {
    let mut program = format!(
        "(sort E)\n(constructor Bottom () E {bottom_options})\n(constructor Next (E) E)\n(let $x0 (Bottom))\n"
    );
    for depth in 1..depth {
        writeln!(program, "(let $x{depth} (Next $x{}))", depth - 1).unwrap();
    }
    writeln!(program, "(extract $x{} :extractor greedy-dag)", depth - 1).unwrap();

    let path = std::env::temp_dir().join(format!(
        "egglog-greedy-dag-deep-{label}-{}.egg",
        std::process::id()
    ));
    fs::write(&path, program).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_egglog-experimental"))
        .arg(&path)
        .output()
        .unwrap();
    fs::remove_file(path).unwrap();
    output
}

#[test]
fn test_greedy_dag_discovery_handles_deep_constructor_chains() {
    // The unextractable leaf prevents reconstruction, isolating the discovery
    // traversal. Run the CLI as a child process so a stack-overflow regression
    // is reported as a test failure instead of aborting this test process.
    let output = run_deep_greedy_dag_chain(20_000, ":unextractable", "discovery");
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert_eq!(output.status.code(), Some(1), "unexpected status: {stderr}");
    assert!(
        stderr.contains("Unable to find any valid extraction"),
        "unexpected error: {stderr}"
    );
}

#[test]
fn test_greedy_dag_reconstruction_handles_deep_constructor_chains() {
    let output = run_deep_greedy_dag_chain(10_000, "", "reconstruction");
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(output.status.success(), "unexpected status: {stderr}");
}
