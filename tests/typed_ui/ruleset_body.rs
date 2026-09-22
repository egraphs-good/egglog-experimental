use egglog_experimental::typed::prelude::*;

#[ruleset]
fn bad_body() -> Vec<Rule> {
    vec![42]
}

fn main() {}
