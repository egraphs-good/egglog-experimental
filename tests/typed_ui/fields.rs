use egglog_experimental::typed::{builtins as eg, prelude::*};
#[sort]
pub struct A;
#[constructor]
pub fn Make(value: eg::I64) -> A;
fn main() {
    // Declarations do not add public argument-record names.
    let _ = MakeArgs { wrong: 1.into() };
}
