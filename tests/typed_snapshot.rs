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
fn multiple_extraction_ranks_available_terms_and_rejects_zero_before_effects()
-> Result<(), TypedError> {
    let low = CostTerm::Zero();
    let high = CostTerm::Costly();
    let root = let_("multiple-root", &high);
    let mut graph = EGraph::with_recording(true)?;
    graph.register((&root, union(&root, &low)))?;
    assert_eq!(graph.extract_multiple(&root, 2)?, [low.clone(), high]);
    assert_eq!(graph.extract(&root)?, low);

    let fresh = let_("not-initialized", CostTerm::Costly());
    let before = graph.history()?;
    assert!(matches!(
        graph.extract_multiple(&fresh, 0),
        Err(TypedError::Invalid(_))
    ));
    assert_eq!(graph.history()?, before);
    assert!(graph.freeze()?.lookup(&fresh).is_err());
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
        (function root () Node :no-merge :internal-hidden) (function empty () Node :no-merge :internal-hidden)
        (set (root) (Number 7)) (set (empty) (Number 9))
        (union (root) (Link (root))) (delete (Number 9))",
        )
        .unwrap();
    let visible_rows = ["Number", "Link"]
        .into_iter()
        .map(|name| {
            let egglog::CommandOutput::PrintFunctionSize(rows) =
                native.print_size(Some(name)).unwrap()
            else {
                panic!("visible constructor rows")
            };
            rows
        })
        .sum::<usize>();
    assert_eq!(before, visible_rows);
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
fn composed_schedules_return_small_results_and_opt_in_diagnostics() -> Result<(), TypedError> {
    let root = let_("root", Node::Number(3));
    let copy = ruleset(|value: &egg::I64| {
        rewrite(Node::Number(value), Node::Link(Node::Number(value))).label("copy")
    });
    let mut graph = EGraph::new()?;
    let empty = graph.run(copy.repeat(0))?;
    assert!(!empty.updated);
    graph.register(&root)?;
    let (result, diagnostic) = graph.run_with_diagnostics(sequence((&copy, &copy)).saturate())?;
    assert!(result.updated);
    let report: serde_json::Value = serde_json::from_slice(&diagnostic.content).unwrap();
    assert!(!report["iterations"].as_array().unwrap().is_empty());
    assert!(!graph.run(&copy)?.updated);
    assert!(diagnostic_matches(&graph.stats()?) > 0);
    assert!(
        graph
            .freeze()?
            .nodes(&graph.freeze()?.lookup(&root)?)
            .is_err()
    );
    let earlier = binding::<egg::I64>("stream-earlier");
    let late = let_("stream-late", egg::I64::from(9));
    let schedule = sequence((sequence(set(&earlier, 1)).with_snapshots(), set(&late, 2)));
    let mut observed = 0;
    let result = graph.run_stream(schedule, |snapshot| {
        observed += 1;
        assert_eq!(
            i64::try_from(&snapshot.lookup(&earlier).unwrap()).unwrap(),
            1
        );
        std::ops::ControlFlow::Break(())
    });
    assert!(
        matches!(result, Err(TypedError::Invalid(message)) if message == "execution cancelled")
    );
    assert_eq!(observed, 1);
    assert!(graph.check(eq(&earlier, 1))?);
    assert!(!graph.check(eq(
        binding::<egg::I64>("stream-late"),
        binding::<egg::I64>("stream-late")
    ))?);
    graph.register(&late)?;
    assert_eq!(i64::try_from(&graph.extract(&late)?)?, 9);
    Ok(())
}

fn diagnostic_matches(diagnostic: &Diagnostic) -> u64 {
    assert_eq!(diagnostic.format, "application/vnd.egglog.run-report+json");
    let value: serde_json::Value = serde_json::from_slice(&diagnostic.content).unwrap();
    value["num_matches_per_rule"]
        .as_object()
        .unwrap()
        .values()
        .map(|value| value.as_u64().unwrap())
        .sum()
}

#[test]
fn diagnostic_labels_share_content_and_consumed_cursors() -> Result<(), TypedError> {
    let shared = rule((), Node::Number(4));
    let first = ruleset((&shared, shared.clone().label("first presentation")));
    let later = ruleset(shared.label("later presentation"));
    let mut graph = EGraph::new()?;
    let (_, diagnostic) = graph.run_with_diagnostics(&first)?;
    assert_eq!(diagnostic_matches(&diagnostic), 1);
    let (_, diagnostic) = graph.run_with_diagnostics(&later)?;
    assert_eq!(diagnostic_matches(&diagnostic), 0);
    Ok(())
}
