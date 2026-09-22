use egglog_experimental::typed::{builtins::I64, prelude::*};

#[ruleset]
fn generic<T>(value: &I64) -> Rule {
    rule(value, ())
}

#[ruleset]
fn constrained(value: &I64) -> Rule
where
    I64: Clone,
{
    rule(value, ())
}

#[ruleset]
async fn asynchronous(value: &I64) -> Rule {
    rule(value, ())
}

#[ruleset]
const fn constant(value: &I64) -> Rule {
    rule(value, ())
}

#[ruleset]
unsafe fn unsafe_rules(value: &I64) -> Rule {
    rule(value, ())
}

#[ruleset]
extern "C" fn foreign(value: &I64) -> Rule {
    rule(value, ())
}

struct Owner;
impl Owner {
    #[ruleset]
    fn receiver(&self) -> Rule {
        rule((), ())
    }
}

#[ruleset]
fn owned(value: I64) -> Rule {
    rule(value, ())
}

#[ruleset]
fn mutable(value: &mut I64) -> Rule {
    rule(value, ())
}

#[ruleset]
fn pattern((left, right): &(I64, I64)) -> Rule {
    rule((left, right), ())
}

#[ruleset]
fn wildcard(_: &I64) -> Rule {
    rule((), ())
}

#[ruleset(label = "unsupported")]
fn option() -> Rule {
    rule((), ())
}

#[ruleset(name = "first", name = "second")]
fn duplicate() -> Rule {
    rule((), ())
}

#[ruleset(name("malformed"))]
fn malformed_name() -> Rule {
    rule((), ())
}

fn main() {}
