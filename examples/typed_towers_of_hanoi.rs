// Core web-demo/towers-of-hanoi.egg. These source rules allow any top disk to
// move: there is deliberately no disk-size restriction, so the answer is 5.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Stack;

#[declarations]
impl Stack {
    pub fn empty() -> Stack;
    pub fn cons(disk: egg::I64, rest: Stack) -> Stack;
}
#[function(merge = |old: egg::I64, new: egg::I64| old.min(new))]
pub fn config(first: Stack, second: Stack, third: Stack) -> egg::I64;

#[ruleset]
fn rules(x: &egg::I64, a: &Stack, b: &Stack, c: &Stack, length: &egg::I64) -> Vec<Rule> {
    vec![
        rule(
            eq(config(Stack::cons(x, a), b, c), length),
            (
                set(config(a, Stack::cons(x, b), c), length + 1),
                set(config(a, b, Stack::cons(x, c)), length + 1),
            ),
        ),
        rule(
            eq(config(a, Stack::cons(x, b), c), length),
            (
                set(config(Stack::cons(x, a), b, c), length + 1),
                set(config(a, b, Stack::cons(x, c)), length + 1),
            ),
        ),
        rule(
            eq(config(a, b, Stack::cons(x, c)), length),
            (
                set(config(Stack::cons(x, a), b, c), length + 1),
                set(config(a, Stack::cons(x, b), c), length + 1),
            ),
        ),
    ]
}

pub fn main() -> Result<(), TypedError> {
    let empty = Stack::empty();
    let disks = Stack::cons(1, Stack::cons(2, Stack::cons(3, &empty)));
    let mut egraph = EGraph::default();
    egraph.register(set(config(&disks, &empty, &empty), 0))?;
    egraph.run(rules.repeat(1_000_000))?;
    let target = config(&empty, &empty, disks);
    assert!(egraph.check(eq(&target, 5))?);
    assert_eq!(egraph.extract(&target)?, egg::I64::from(5));
    Ok(())
}
