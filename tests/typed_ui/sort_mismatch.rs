use egglog_experimental::typed::{builtins as eg, prelude::*};
#[sort]
pub struct A;
#[sort]
pub struct B;
#[constructor]
pub fn Make(value: eg::I64) -> A;
fn main() {
    let _: B = Make(1);
}
