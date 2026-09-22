use egglog_experimental::typed::{builtins::I64, prelude::*};

fn main() {
    let mut escaped = None;
    let _ = ruleset(|value: &I64| {
        escaped = Some(value);
        rule(eq(value, 1), ())
    });
    let _ = escaped;
}
