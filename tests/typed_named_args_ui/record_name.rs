use egglog_experimental::typed::{builtins::I64, prelude::*};

#[sort]
pub struct Term;
#[constructor(args = nested::LeafArgs)]
fn leaf(value: I64) -> Term;

fn main() {}
