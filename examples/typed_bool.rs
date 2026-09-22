// Python examples/bool.py: ground booleans are distinct from query facts.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[relation]
pub fn r(value: egg::I64);
#[function(no_merge)]
pub fn flag(value: egg::I64) -> egg::Bool;

#[ruleset]
fn boolean_facts(i: &egg::I64) -> Vec<Rule> {
    vec![rule(r(i), set(flag(i), true))]
}

pub fn main() -> Result<(), TypedError> {
    let mut egraph = EGraph::default();
    let t = egg::Bool::from(true);
    let f = egg::Bool::from(false);
    #[expect(
        clippy::eq_op,
        reason = "The source example checks Boolean idempotence."
    )]
    {
        assert!(egraph.check((
            eq(&t & &t, &t),
            eq(&t & &f, &f),
            eq(&t | &f, &t),
            ne(&t | &f, &f),
        ))?);
    }
    assert!(egraph.check((
        eq(egg::I64::from(1).bool_lt(2), &t),
        eq(egg::I64::from(1).bool_le(2), &t),
        eq(egg::I64::from(2).bool_lt(1), &f),
        eq(egg::I64::from(2).bool_le(1), &f),
        eq(egg::I64::from(1).bool_lt(1), f),
        eq(egg::I64::from(1).bool_le(1), &t),
    ))?);
    egraph.register(r(0))?;
    egraph.run(boolean_facts.repeat(3))?;
    assert!(egraph.check(eq(flag(0), t))?);
    Ok(())
}
