// Python Datalog tutorial: relations, functional dependencies, and equality.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[relation]
pub fn edge(source: egg::I64, target: egg::I64);
#[relation]
pub fn path(source: egg::I64, target: egg::I64);
#[function(no_merge)]
pub fn edge_length(source: egg::I64, target: egg::I64) -> egg::I64;
#[function(merge = |old: egg::I64, new: egg::I64| old.min(new))]
pub fn path_length(source: egg::I64, target: egg::I64) -> egg::I64;

#[sort]
pub struct Node;

#[declarations]
impl Node {
    #[constructor(from(i64, i32))]
    pub fn make(value: egg::I64) -> Node;
}
#[relation]
pub fn node_edge(source: Node, target: Node);
#[relation]
pub fn node_path(source: Node, target: Node);

#[ruleset]
fn reachability(x: &egg::I64, y: &egg::I64, z: &egg::I64) -> Vec<Rule> {
    vec![
        rule(edge(x, y), path(x, y)),
        rule((path(x, y), edge(y, z)), path(x, z)),
    ]
}

#[ruleset]
fn shortest_paths(
    a: &egg::I64,
    b: &egg::I64,
    distance: &egg::I64,
    c: &egg::I64,
    ab: &egg::I64,
    bc: &egg::I64,
) -> Vec<Rule> {
    vec![
        rule(
            eq(edge_length(a, b), distance),
            set(path_length(a, b), distance),
        ),
        rule(
            (eq(path_length(a, b), ab), eq(edge_length(b, c), bc)),
            set(path_length(a, c), ab + bc),
        ),
    ]
}

#[ruleset]
fn node_paths(x: &Node, y: &Node, z: &Node) -> Vec<Rule> {
    vec![
        rule(node_edge(x, y), node_path(x, y)),
        rule((node_path(x, y), node_edge(y, z)), node_path(x, z)),
    ]
}

#[ruleset]
fn collapse_cycles(x: &Node, y: &Node) -> Ruleset {
    // Composition retains node_paths' existing rule occurrences and cursors.
    ruleset((
        &node_paths,
        rule((node_path(x, y), node_path(y, x)), union(x, y)),
    ))
}

pub fn main() -> Result<(), TypedError> {
    // A relation records facts; a recursive rule computes transitive closure.
    let mut graph = EGraph::default();
    graph.register((edge(1, 2), edge(2, 3), edge(3, 4)))?;
    assert!(graph.check(edge(1, 2))?);
    assert!(!graph.check(path(1, 4))?);
    graph.run(reachability.repeat(10))?;
    assert!(graph.check(path(1, 4))?);
    graph.run(reachability.saturate())?;
    assert!(!graph.check(path(4, 1))?);

    // A table maps each input tuple to one value. min merges competing paths.
    let mut graph = EGraph::default();
    graph.register((
        set(edge_length(1, 2), 10),
        set(edge_length(2, 3), 10),
        set(edge_length(1, 3), 30),
    ))?;
    graph.run(shortest_paths.saturate())?;
    assert!(graph.check(eq(path_length(1, 3), 20))?);

    // Equality-sort vertices can be unioned. All relations observe that union.
    let mut graph = EGraph::default();
    graph.register((
        node_edge(1, 2),
        node_edge(2, 3),
        node_edge(3, 1),
        node_edge(5, 6),
        union(Node::make(3), 5),
    ))?;
    graph.run(node_paths.saturate())?;
    assert!(graph.check((node_edge(3, 6), node_path(1, 6),))?);
    graph.run(collapse_cycles.saturate())?;
    assert!(graph.check((
        eq(Node::make(1), 2),
        eq(Node::make(1), 3),
        eq(Node::make(2), 3),
    ))?);
    Ok(())
}
