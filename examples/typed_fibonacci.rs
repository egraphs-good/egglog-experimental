// Core web-demo/fibonacci.egg and Python examples/fib.py have different seeds.
// Both source cases run independently: F(7)=13 for 0,1 and F(7)=21 for 1,1.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[function(no_merge)]
pub fn fib(index: egg::I64) -> egg::I64;

#[ruleset]
fn recurrence(x: &egg::I64, f0: &egg::I64, f1: &egg::I64) -> Vec<Rule> {
    vec![rule(
        (eq(f0, fib(x)), eq(f1, fib(x + 1))),
        set(fib(x + 2), f0 + f1),
    )]
}

pub fn main() -> Result<(), TypedError> {
    for (first, expected) in [(0, 13), (1, 21)] {
        let mut egraph = EGraph::default();
        egraph.register((set(fib(0), first), set(fib(1), 1)))?;
        egraph.run(recurrence.repeat(7))?;
        assert!(egraph.check(eq(fib(7), expected))?);
    }
    Ok(())
}
