// Core web-demo/pathproof.egg: proofs are ordinary data, not proof mode.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Proof;

#[declarations]
impl Proof {
    pub fn trans(source: egg::I64, rest: Proof) -> Proof;
    pub fn edge(source: egg::I64, target: egg::I64) -> Proof;
}
#[relation]
pub fn edge(source: egg::I64, target: egg::I64);
#[relation]
pub fn path(source: egg::I64, target: egg::I64, proof: Proof);

#[ruleset]
fn rules(
    x: &egg::I64,
    y: &egg::I64,
    z: &egg::I64,
    proof: &Proof,
    p: &Proof,
    q: &Proof,
) -> Vec<Rule> {
    vec![
        rule(edge(x, y), path(x, y, Proof::edge(x, y))),
        rule(
            (edge(x, y), path(y, z, proof)),
            path(x, z, Proof::trans(x, proof)),
        ),
        // Equate proofs with the same endpoints, so minimum-cost extraction can
        // choose a shortest path rather than whichever proof was discovered first.
        rule((path(x, y, p), path(x, y, q)), union(p, q)),
    ]
}

pub fn main() -> Result<(), TypedError> {
    let mut egraph = EGraph::default();
    egraph.register((edge(2, 1), edge(3, 2), edge(1, 3)))?;
    egraph.run(rules.repeat(3))?;
    assert!(egraph.check(path(3, 1, Proof::trans(3, Proof::edge(2, 1))))?);
    Ok(())
}
