use egglog_experimental::typed::{builtins as eg, prelude::*};
#[sort]
pub struct A;
#[constructor]
pub fn Make(value: eg::I64) -> A;
fn main() {
    Make(1, 2);
}
