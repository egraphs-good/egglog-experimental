// Core web-demo/path.egg: recursive reachability and nonmatching checks.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[relation]
pub fn edge(source: egg::I64, target: egg::I64);
#[relation]
pub fn path(source: egg::I64, target: egg::I64);

#[ruleset]
fn paths(x: &egg::I64, y: &egg::I64, z: &egg::I64) -> Vec<Rule> {
    vec![
        rule(edge(x, y), path(x, y)),
        rule((path(x, y), edge(y, z)), path(x, z)),
    ]
}

pub fn main() -> Result<(), TypedError> {
    let mut egraph = EGraph::default();
    egraph.register((edge(1, 2), edge(2, 3), edge(3, 4)))?;
    assert!(egraph.check(edge(1, 2))?);
    assert!(!egraph.check(path(1, 2))?);
    egraph.run(paths.repeat(3))?;
    assert!(egraph.check(path(1, 4))?);
    assert!(!egraph.check(path(4, 1))?);
    Ok(())
}
