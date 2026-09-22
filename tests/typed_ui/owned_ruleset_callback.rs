use egglog_experimental::typed::{builtins::I64, prelude::*};

fn main() {
    let _ = ruleset(|value: I64| rule(eq(value, 1), ()));
}
