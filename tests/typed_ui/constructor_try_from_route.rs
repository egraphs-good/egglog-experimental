use egglog_experimental::typed::{builtins as egg, prelude::*};
#[sort]
pub struct Num;
#[constructor(try_from(bool))]
fn number(value: egg::I64) -> Num;
#[sort]
pub struct Numbers;
#[constructor(try_from(Vec<i64>))]
fn numbers(value: egg::Vec<egg::I64>) -> Numbers;
fn main() {}
