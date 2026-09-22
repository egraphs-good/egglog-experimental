// Core web-demo/push-pop.egg: a native scope restores a merged table value.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[function(merge = |old: egg::I64, new: egg::I64| old.max(new))]
pub fn foo() -> egg::I64;

pub fn main() -> Result<(), TypedError> {
    let mut egraph = EGraph::default();
    egraph.register(set(foo(), 1))?;
    assert!(egraph.check(eq(foo(), 1))?);
    egraph.push()?;
    egraph.register(set(foo(), 2))?;
    assert!(egraph.check(eq(foo(), 2))?);
    egraph.pop()?;
    assert!(egraph.check(eq(foo(), 1))?);
    Ok(())
}
