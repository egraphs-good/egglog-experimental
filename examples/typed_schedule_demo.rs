// Core schedule-demo.egg and Python schedule_demo.py: alternate two rulesets.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[relation]
pub fn left(step: egg::I64);
#[relation]
pub fn right(step: egg::I64);

#[ruleset]
fn left_rules(x: &egg::I64) -> Vec<Rule> {
    vec![rule((left(x), right(x)), left(x + 1))]
}

#[ruleset]
fn right_rules(x: &egg::I64, y: &egg::I64) -> Vec<Rule> {
    vec![rule((left(x), right(y), eq(x, y + 1)), right(x))]
}

pub fn main() -> Result<(), TypedError> {
    let schedule = sequence((right_rules.saturate(), left_rules.saturate())).repeat(10);
    let mut egraph = EGraph::default();
    egraph.register((left(0), right(0)))?;
    egraph.run(schedule)?;
    // The first right pass cannot advance; it remains one step behind the left.
    assert!(egraph.check((left(10), right(9)))?);
    assert!(!egraph.check(left(11))?);
    assert!(!egraph.check(right(10))?);
    Ok(())
}
