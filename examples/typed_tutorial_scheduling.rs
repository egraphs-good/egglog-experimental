// Python scheduling tutorial, lines 1–198. Shared analysis/optimization rules
// are ordinary immutable values; a sequence is different from a combined group.
#[path = "typed_support/arithmetic.rs"]
pub mod theory;
use egglog_experimental::typed::prelude::*;
use theory::*;

#[ruleset]
fn analysis() -> Ruleset {
    ruleset((&inequalities, &intervals))
}
#[ruleset]
fn optimizations() -> Ruleset {
    ruleset((&algebra, &guarded_optimizations))
}
#[ruleset]
#[expect(clippy::erasing_op, reason = "this authors symbolic multiplication")]
fn extended_optimizations(x: &Num) -> Ruleset {
    ruleset((&optimizations, rewrite(x * 0, 0)))
}

pub fn main() -> Result<(), TypedError> {
    let one = Num::constant(1);
    let mut chain = Num::var("f");
    for name in ["e", "d", "c", "b", "a"] {
        chain = Num::var(name) + chain;
    }
    let mut positive = Num::constant(2);
    for _ in 0..4 {
        positive = &one + positive;
    }
    let addition_chain = let_("addition_chain", &chain);
    let nonzero_expr = let_("nonzero_expr", positive);
    let expr = let_("expr", &nonzero_expr * (&addition_chain / &nonzero_expr));
    let mut egraph = EGraph::default();
    egraph.register((&addition_chain, &expr))?;
    assert!(!egraph.check(eq(&expr, &addition_chain))?);
    egraph.run(analysis.saturate())?;
    egraph.run(&optimizations)?;
    assert!(egraph.check(eq(expr, addition_chain))?);
    let schedule = sequence((analysis.saturate(), &optimizations));
    egraph.run(schedule.repeat(2))?;

    // This second input needs an optimization before its nonzero analysis can
    // finish. Building an extended group does not mutate the previous schedule.
    let schedule = sequence((analysis.saturate(), &extended_optimizations));
    let addition_chain = let_("addition_chain", chain);
    #[expect(clippy::erasing_op, reason = "this authors symbolic multiplication")]
    let mut positive = Num::var("x") * 0;
    for _ in 0..4 {
        positive = &one + positive;
    }
    let nonzero_expr = let_("nonzero_expr", positive);
    let expr = let_("expr", &nonzero_expr * (&addition_chain / &nonzero_expr));
    let mut egraph = EGraph::default();
    egraph.register((&addition_chain, &expr))?;
    egraph.push()?;
    egraph.run(&schedule)?;
    let once = egraph.extract(&expr)?;
    assert!(!egraph.check(eq(&expr, &addition_chain))?);
    egraph.pop()?;
    egraph.push()?;
    egraph.run(schedule.repeat(2))?;
    let twice = egraph.extract(&expr)?;
    assert!(egraph.check(eq(expr, addition_chain))?);
    assert_ne!(once, twice);
    egraph.pop()?;
    Ok(())
}
