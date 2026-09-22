use egglog_experimental::typed::{
    builtins::{I64, String},
    prelude::*,
};
#[function(no_merge)]
fn weight(x: I64) -> I64;
fn main() {
    let _ = set(weight(1), String::from("wrong"));
}
