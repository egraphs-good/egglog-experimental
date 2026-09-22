use egglog_experimental::typed::{
    builtins::{I64, String},
    prelude::*,
};

#[sort]
pub struct Term;
#[constructor(args = LeafArgs)]
fn leaf(value: I64) -> Term;

fn main() {
    let _ = LeafArgs {
        value: String::from("wrong"),
    };
}
