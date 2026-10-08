use egglog::extract::{DagCostModel, DefaultCost, TreeCostModel};
use egglog::{ArcSort, CommandOutput, EGraph, Enode, Error, Function, Value};
use egglog_experimental::{
    DynamicCostModel, effsafe_state, new_experimental_egraph, set_effsafe_cost_models,
};

fn extracted(outputs: Vec<CommandOutput>) -> (String, DefaultCost) {
    let [CommandOutput::ExtractBest(dag, cost, term)] = outputs.as_slice() else {
        panic!("expected one extraction, got {outputs:?}");
    };
    (dag.to_string(*term), *cost)
}

struct WeightedRegions;

impl TreeCostModel<DefaultCost> for WeightedRegions {
    type EnodeCost = DefaultCost;
    type ContainerCost = DefaultCost;

    fn base_value_cost(&self, _: &EGraph, _: &ArcSort, _: Value) -> DefaultCost {
        1
    }

    fn enode_cost(&self, eg: &EGraph, func: &Function, enode: &Enode<'_>) -> DefaultCost {
        DynamicCostModel.enode_cost(eg, func, enode)
    }

    fn container_cost(&self, _: &EGraph, _: &ArcSort, _: Value) -> DefaultCost {
        1
    }

    fn fold_enode_cost(&self, own: DefaultCost, children: &[DefaultCost]) -> DefaultCost {
        children.iter().enumerate().fold(own, |cost, (i, child)| {
            cost.saturating_add(child.saturating_mul(i as DefaultCost + 2))
        })
    }

    fn fold_container_cost(&self, own: DefaultCost, children: &[DefaultCost]) -> DefaultCost {
        children
            .iter()
            .fold(own, |cost, child| cost.saturating_add(*child))
    }
}

#[test]
fn rust_region_positions_are_an_unordered_set() {
    for positions in [vec![1, 2], vec![2, 1], vec![2, 1, 2, 1]] {
        let mut eg = new_experimental_egraph();
        eg.parse_and_run_program(
            None,
            r#"
            (datatype E (A) (B E) (C E) (If E E E))
            (let a (A))
            (let b (B a))
            (let c (C a))
            (let root (If a b c))
            (set-effectful E a)
            (set-effectful E b)
            (set-effectful E c)
            (set-effectful E root)
            "#,
        )
        .unwrap();
        effsafe_state(&mut eg)
            .config
            .regions
            .insert("If".into(), positions);
        set_effsafe_cost_models(&mut eg, DynamicCostModel, WeightedRegions);
        assert_eq!(
            extracted(
                eg.parse_and_run_program(None, "(extract root :extractor effsafe)")
                    .unwrap()
            ),
            ("(If (A) (B (A)) (C (A)))".into(), 16)
        );
    }
}

#[test]
fn pure_nodes_can_start_effectful_subregions() {
    for body in ["(A)", "(B)"] {
        let program = format!(
            r#"
            (datatype E (A) (B) (Read E :regions (0)) (Step E E))
            (let a (A))
            (let b {body})
            (let root (Step a (Read b)))
            (set-effectful E a)
            (set-effectful E b)
            (set-effectful E root)
            (extract root :extractor effsafe)
            "#
        );
        assert_eq!(
            extracted(
                new_experimental_egraph()
                    .parse_and_run_program(None, &program)
                    .unwrap()
            ),
            (format!("(Step (A) (Read {body}))"), 4)
        );
    }
}

#[test]
fn pure_dependencies_still_require_their_regions_statewalk() {
    for nested in [false, true] {
        let value = if nested {
            "(Wrap (Step b (Read a)))"
        } else {
            "(Read b)"
        };
        let program = format!(
            r#"
            (datatype E (A) (B) (Read E) (Wrap E :regions (0)) (Step E E))
            (let a (A))
            (let b (B))
            (let root (Step a {value}))
            (set-effectful E a)
            (set-effectful E b)
            (set-effectful E root)
            (set-effectful E (Step b (Read a)))
            (extract root :extractor effsafe)
            "#
        );
        let error = new_experimental_egraph()
            .parse_and_run_program(None, &program)
            .unwrap_err();
        assert!(matches!(error, Error::ExtractError(_)), "{error}");
        assert!(error.to_string().contains("outside the region"), "{error}");
    }
}

#[test]
fn pure_subregion_costs_steer_the_choice() {
    let program = r#"
        (datatype E (A) (B :cost 100) (Read E :regions (0)) (Alt :cost 50) (Step E E))
        (let a (A))
        (let b (B))
        (let value (Read b))
        (union value (Alt))
        (let root (Step a value))
        (set-effectful E a)
        (set-effectful E b)
        (set-effectful E root)
        (extract root :extractor effsafe)
    "#;
    assert_eq!(
        extracted(
            new_experimental_egraph()
                .parse_and_run_program(None, program)
                .unwrap()
        ),
        ("(Step (A) (Alt))".into(), 52)
    );
}

#[test]
fn mixed_pure_and_effectful_boundaries_keep_their_cost_positions() {
    for (value, term, cost) in [
        ("(Mixed b (Small))", "(Step (A) (Mixed (B) (Small)))", 233),
        ("(Mixed (Small) b)", "(Step (A) (Mixed (Small) (B)))", 323),
    ] {
        for alternative in [50, 500] {
            let program = format!(
                r#"
            (datatype E (A) (B :cost 100) (Small :cost 10)
                (Mixed E E :regions (0 1)) (Alt :cost {alternative}) (Step E E))
            (let a (A))
            (let b (B))
            (let value {value})
            (union value (Alt))
            (let root (Step a value))
            (set-effectful E a)
            (set-effectful E b)
            (set-effectful E root)
            (extract root :extractor effsafe)
            "#
            );
            let mut eg = new_experimental_egraph();
            set_effsafe_cost_models(&mut eg, DynamicCostModel, WeightedRegions);
            let expected = if alternative == 50 {
                ("(Step (A) (Alt))".into(), 52)
            } else {
                (term.into(), cost)
            };
            assert_eq!(
                extracted(eg.parse_and_run_program(None, &program).unwrap()),
                expected
            );
        }
    }
}

#[test]
fn entry_alternatives_in_one_class_are_supported() {
    let program = r#"
        (datatype E (A :cost 10) (B :cost 2) (Step E))
        (let a (A))
        (union a (B))
        (set-effectful E a)
        (let root (Step a))
        (set-effectful E root)
        (extract root :extractor effsafe)
    "#;
    assert_eq!(
        extracted(
            new_experimental_egraph()
                .parse_and_run_program(None, program)
                .unwrap()
        ),
        ("(Step (B))".into(), 3)
    );
}

#[test]
fn multiple_entry_classes_return_an_extraction_error() {
    let program = r#"
            (datatype E (A) (B) (Step E))
            (let a (A))
            (let root (Step a))
            (union root (Step (B)))
            (set-effectful E a)
            (set-effectful E (B))
            (set-effectful E root)
            (extract root :extractor effsafe)
            "#;
    let error = new_experimental_egraph()
        .parse_and_run_program(None, program)
        .unwrap_err();
    assert!(matches!(error, Error::ExtractError(_)), "{error}");
    assert!(
        error.to_string().contains("multiple entry e-classes"),
        "{error}"
    );
}

#[test]
fn invalid_subregions_below_pure_nodes_allow_an_alternative() {
    let program = r#"
        (datatype E (A) (B) (C) (Next E) (Read E :regions (0)) (Alt :cost 50) (Step E E))
        (let a (A))
        (let b (B))
        (let bad (Next b))
        (union bad (Next (C)))
        (let value (Read bad))
        (union value (Alt))
        (let root (Step a value))
        (set-effectful E a)
        (set-effectful E b)
        (set-effectful E (C))
        (set-effectful E bad)
        (set-effectful E root)
        (extract root :extractor effsafe)
    "#;
    assert_eq!(
        extracted(
            new_experimental_egraph()
                .parse_and_run_program(None, program)
                .unwrap()
        ),
        ("(Step (A) (Alt))".into(), 52)
    );
}

#[test]
fn print_limit_is_applied_before_validating_roots() {
    for limit in [0, 1, 2] {
        let mut eg = new_experimental_egraph();
        eg.parse_and_run_program(
            None,
            r#"
            (datatype E (Arg i64))
            (let good (Arg 0))
            (set-effectful E good)
            (Arg 1)
        "#,
        )
        .unwrap();
        let result = eg.parse_and_run_program(
            None,
            &format!("(print-function Arg {limit} :extractor effsafe)"),
        );
        if limit == 2 {
            assert!(result.unwrap_err().to_string().contains("not effectful"));
        } else {
            let outputs = result.unwrap();
            let [CommandOutput::PrintFunction(_, dag, terms, _)] = outputs.as_slice() else {
                panic!("expected print-function output, got {outputs:?}");
            };
            let actual: Vec<_> = terms.iter().map(|(t, _)| dag.to_string(*t)).collect();
            let expected = if limit == 0 { vec![] } else { vec!["(Arg 0)"] };
            assert_eq!(actual, expected);
        }
    }
}
