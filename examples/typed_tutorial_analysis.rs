// Python analysis tutorial, computational portion through line 199.
#[path = "typed_support/arithmetic.rs"]
pub mod theory;
use egglog_experimental::typed::prelude::*;
use theory::*;

#[ruleset]
fn ordered_algebra() -> Ruleset {
    ruleset((&inequalities, &algebra))
}
#[ruleset]
fn analyzed_algebra() -> Ruleset {
    ruleset((&ordered_algebra, &intervals, &guarded_optimizations))
}

pub fn main() -> Result<(), TypedError> {
    let one = Num::constant(1);
    let two = Num::constant(2);
    let x = Num::var("x");
    let y = Num::var("y");
    let expr1 = let_("expr1", &y + (&two + &x));
    let expr2 = let_("expr2", &x + y + &one + &two);
    let mut egraph = EGraph::default();
    egraph.register((&expr1, &expr2))?;
    assert!(!egraph.check(expr1.less_equal(&expr2))?);
    egraph.run(ordered_algebra.saturate())?;
    assert!(egraph.check(expr1.less_equal(expr2))?);

    // Analysis facts guard division cancellation; no host callbacks run here.
    let expr3 = let_("expr3", &two * (&x / (&one + &two / 2)));
    let expr4 = let_("expr4", &x);
    egraph.register((&expr3, &expr4))?;
    assert!(!egraph.check(eq(&expr3, &expr4))?);
    egraph.run(analyzed_algebra.saturate())?;
    assert!(egraph.check(eq(expr3, expr4))?);

    let x_plus_one = x + &one;
    let expr5 = &x_plus_one * &x_plus_one + two;
    #[expect(
        clippy::eq_op,
        reason = "the source case exercises guarded division cancellation"
    )]
    let expr6 = let_("expr6", &expr5 / &expr5);
    egraph.register(&expr6)?;
    egraph.run(analyzed_algebra.saturate())?;
    assert!(egraph.check(eq(expr6, one))?);
    Ok(())
}
