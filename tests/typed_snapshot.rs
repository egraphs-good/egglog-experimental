#![cfg(feature = "typed")]

use egglog_experimental::typed::{builtins as egg, prelude::*};

#[sort]
struct Node;

#[declarations]
impl Node {
    #[constructor]
    fn Empty() -> Self;
    #[constructor]
    fn Number(value: egg::I64) -> Self;
    #[constructor]
    fn Link(child: Node) -> Self;
}

#[test]
fn observed_nullary_row_targets_cannot_mutate_live_state() -> Result<(), TypedError> {
    let root = let_("nullary", Node::Empty());
    let mut graph = EGraph::new()?;
    graph.register(&root)?;
    let count = graph.num_tuples()?;
    let snapshot = graph.freeze()?;
    let observed = snapshot.nodes(&snapshot.lookup(&root)?)?.next().unwrap();
    for action in [
        delete(&observed),
        subsume(observed.clone()),
        Action::from(&observed),
    ] {
        assert!(graph.register(action).is_err());
        assert_eq!(graph.num_tuples()?, count);
        assert!(graph.check(Node::Empty())?);
    }
    Ok(())
}

#[function(no_merge)]
fn length(node: Node) -> egg::I64;
#[function(no_merge)]
fn selected(node: Node) -> Node;
#[relation]
fn marked(node: Node, value: egg::I64);

#[test]
fn table_rows_keep_values_without_becoming_constructor_producers() -> Result<(), TypedError> {
    let root = let_("table-root", Node::Number(7));
    let mut graph = EGraph::new()?;
    graph.register(&root)?;
    graph.register((
        set(length(&root), 11),
        set(selected(&root), &root),
        marked(&root, 11),
    ))?;
    let before = graph.num_tuples()?;
    let snapshot = graph.freeze()?;
    let class = snapshot.class_of(&snapshot.lookup(&root)?)?;
    assert_eq!(class.nodes().len(), 1);
    let length = snapshot
        .rows()
        .find(|row| row.name().ends_with("::length"))
        .unwrap();
    assert_eq!(length.args().next().unwrap().class(), Some(class));
    assert_eq!(
        i64::try_from(&length.value().unwrap().try_typed::<egg::I64>()?)?,
        11
    );
    let selected = snapshot
        .rows()
        .find(|row| row.name().ends_with("::selected"))
        .unwrap();
    assert_eq!(selected.value().unwrap().class(), Some(class));
    let marked = snapshot
        .rows()
        .find(|row| row.name().ends_with("::marked"))
        .unwrap();
    assert!(marked.value().is_none());
    assert_eq!(marked.args().len(), 2);
    assert_eq!(marked.args().next().unwrap().class(), Some(class));
    assert!(
        graph
            .register(length.value().unwrap().try_typed::<egg::I64>()?)
            .is_err()
    );
    assert_eq!(graph.num_tuples()?, before);
    Ok(())
}

#[sort]
struct CostTerm;

#[declarations]
impl CostTerm {
    #[constructor(cost = 0)]
    fn Zero() -> Self;
    #[constructor(cost = egg::I64::from(37))]
    fn Costly() -> Self;
    #[constructor(unextractable)]
    fn Hidden() -> Self;
    #[constructor(cost = -1)]
    fn Negative() -> Self;
    #[constructor(cost = egg::I64::from(1) + egg::I64::from(2))]
    fn Symbolic() -> Self;
    #[constructor(cost = var::<egg::I64>("cost"))]
    fn Variable() -> Self;
    #[constructor(cost = let_("cost", egg::I64::from(2)))]
    fn Capture() -> Self;
    #[constructor(name = "conflicting-cost", cost = 1)]
    fn First() -> Self;
    #[constructor(name = "conflicting-cost", cost = 2)]
    fn Second() -> Self;
    #[constructor(name = "conflicting-extractability")]
    fn Extractable() -> Self;
    #[constructor(name = "conflicting-extractability", unextractable)]
    fn Unextractable() -> Self;
}

#[test]
fn static_constructor_options_survive_bytes_and_conflicts_remain_semantic() -> Result<(), TypedError>
{
    let root = let_("cost-root", CostTerm::Costly());
    let mut graph = EGraph::new()?;
    graph.register(&root)?;
    graph.register((
        union(&root, CostTerm::Zero()),
        union(&root, CostTerm::Hidden()),
    ))?;
    assert_eq!(graph.extract(&root)?, CostTerm::Zero());
    let snapshot = graph.freeze()?;
    assert!(
        snapshot
            .nodes(&snapshot.lookup(&root)?)?
            .any(|node| { get_args(&node, CostTerm::Costly).unwrap().is_some() })
    );
    let mut costs = snapshot
        .class_of(&snapshot.lookup(&root)?)?
        .nodes()
        .filter_map(|node| node.declared_cost())
        .map(|value| i64::try_from(&value.try_typed::<egg::I64>()?))
        .collect::<Result<Vec<_>, TypedError>>()?;
    costs.sort();
    assert_eq!(costs, [0, 37]);
    let mut hidden = EGraph::new()?;
    hidden.register(CostTerm::Hidden())?;
    assert!(hidden.extract(CostTerm::Hidden()).is_err());
    for invalid in [
        CostTerm::Negative(),
        CostTerm::Symbolic(),
        CostTerm::Variable(),
        CostTerm::Capture(),
    ] {
        assert!(EGraph::new()?.register(invalid).is_err());
    }
    assert!(
        EGraph::new()?
            .register((CostTerm::First(), CostTerm::Second()))
            .is_err()
    );
    assert!(
        EGraph::new()?
            .register((CostTerm::Extractable(), CostTerm::Unextractable()))
            .is_err()
    );
    Ok(())
}

#[test]
fn snapshot_keeps_cycles_empty_classes_and_observation_provenance() -> Result<(), TypedError> {
    let root = let_("root", Node::Number(7));
    let empty = let_("empty", Node::Number(9));
    let mut graph = EGraph::new()?;
    graph.register((&root, &empty))?;
    graph.register((union(&root, Node::Link(&root)), delete(Node::Number(9))))?;
    let before = graph.num_tuples()?;
    // A tiny native oracle measures the portable visible-table count policy.
    // Production typed observations remain exclusively byte-backed.
    let mut native = egglog_experimental::new_experimental_egraph();
    native
        .parse_and_run_program(
            None,
            "(datatype Node (Number i64) (Link Node))
        (function root () Node :no-merge) (function empty () Node :no-merge)
        (set (root) (Number 7)) (set (empty) (Number 9))
        (union (root) (Link (root))) (delete (Number 9))",
        )
        .unwrap();
    assert_eq!(before, native.num_tuples());
    let snapshot = graph.freeze()?;
    assert_eq!(graph.num_tuples()?, before);
    let observed = snapshot.lookup(&root)?;
    let class = snapshot.class_of(&observed)?;
    assert_eq!(class.nodes().len(), 2);
    assert_eq!(snapshot.nodes(&snapshot.lookup(&empty)?)?.len(), 0);
    let linked = snapshot
        .nodes(&observed)?
        .find(|node| {
            get_args(node, |child: &Node| Node::Link(child))
                .unwrap()
                .is_some()
        })
        .unwrap();
    let (child,) = get_args(&linked, |child: &Node| Node::Link(child))?.unwrap();
    assert_eq!(snapshot.class_of(&child)?, class);
    assert!(graph.register(&observed).is_err());
    assert!(graph.register(Action::from(&observed)).is_err());
    assert!(graph.register(Node::Link(&observed)).is_err());
    assert!(graph.freeze()?.class_of(&observed).is_err());
    drop(graph);
    assert_eq!(snapshot.class_of(&child)?, class);
    Ok(())
}

#[test]
fn composed_schedules_return_exact_reports_and_publish_zero_repeat() -> Result<(), TypedError> {
    let root = let_("root", Node::Number(3));
    let copy = ruleset(|value: &egg::I64| {
        rewrite(Node::Number(value), Node::Link(Node::Number(value))).label("copy")
    });
    let mut graph = EGraph::new()?;
    let empty = graph.run(copy.repeat(0))?;
    assert!(!empty.detail.updated);
    assert!(empty.detail.iterations.is_empty());
    graph.register(&root)?;
    let result = graph.run(sequence((&copy, &copy)).saturate())?;
    assert!(result.detail.updated);
    assert!(!result.detail.iterations.is_empty());
    assert!(
        result
            .rules
            .iter()
            .any(|rule| rule.name.as_deref() == Some("copy"))
    );
    assert!(!graph.run(&copy)?.detail.updated);
    let stats = graph.stats()?;
    assert!(
        stats
            .detail
            .num_matches_per_rule
            .iter()
            .any(|entry| entry.value > 0)
    );
    assert!(
        graph
            .freeze()?
            .nodes(&graph.freeze()?.lookup(&root)?)
            .is_err()
    );
    Ok(())
}

#[test]
fn diagnostic_labels_keep_shared_occurrences_and_consumed_cursors() -> Result<(), TypedError> {
    let shared = rule((), Node::Number(4));
    let first = ruleset((&shared, shared.clone().label("first presentation")));
    let later = ruleset(shared.label("later presentation"));
    let mut graph = EGraph::new()?;
    let report = graph.run(&first)?;
    assert_eq!(
        report
            .detail
            .num_matches_per_rule
            .iter()
            .map(|entry| entry.value)
            .sum::<u64>(),
        1
    );
    let report = graph.run(&later)?;
    assert_eq!(
        report
            .detail
            .num_matches_per_rule
            .iter()
            .map(|entry| entry.value)
            .sum::<u64>(),
        0
    );
    Ok(())
}
