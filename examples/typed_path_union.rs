// Core web-demo/path-union.egg: graph edges rebuild after equality-sort union.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Node;

#[declarations]
impl Node {
    #[constructor(from(i64, i32))]
    pub fn make(value: egg::I64) -> Node;
}
#[relation]
pub fn edge(source: Node, target: Node);
#[relation]
pub fn path(source: Node, target: Node);

#[ruleset]
fn paths(x: &Node, y: &Node, z: &Node) -> Vec<Rule> {
    vec![
        rule(edge(x, y), path(x, y)),
        rule((path(x, y), edge(y, z)), path(x, z)),
    ]
}

pub fn main() -> Result<(), TypedError> {
    let mut egraph = EGraph::default();
    egraph.register((edge(1, 2), edge(2, 3), edge(5, 6), union(Node::make(3), 5)))?;
    egraph.run(paths.repeat(10))?;
    assert!(egraph.check(edge(3, 6))?);
    assert!(egraph.check(path(1, 6))?);
    Ok(())
}
