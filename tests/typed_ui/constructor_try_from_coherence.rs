use egglog_experimental::typed::{builtins::I64, prelude::*};
#[sort]
pub struct Num;
#[declarations]
impl Num {
    #[constructor(try_from)]
    fn first(value: I64) -> Self;
    #[constructor(try_from)]
    fn second(value: I64) -> Self;
}
#[sort]
pub struct Alias;
type Integer = I64;
#[constructor(try_from(Integer))]
fn alias(value: I64) -> Alias;
fn main() {}
