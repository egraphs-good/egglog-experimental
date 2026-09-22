use egglog_experimental::typed::{builtins as egg, prelude::*};

#[sort]
struct Term;

#[constructor(args = PairArgs)]
fn pair(left: egg::I64, right: egg::I64) -> Term;

fn main() {
    let _ = PairArgs {
        left: egg::String::from("wrong sort"),
        ..PairArgs::fresh()
    };
    let _ = PairArgs {
        missing: 1.into(),
        ..PairArgs::fresh()
    };
}
