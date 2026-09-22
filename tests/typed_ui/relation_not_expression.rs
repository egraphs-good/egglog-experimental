use egglog_experimental::typed::{builtins as eg, prelude::*};
#[relation]
pub fn Seen(value: eg::I64);
#[sort]
pub struct A;
#[constructor]
pub fn Make(value: eg::Unit) -> A;
fn main() {
    Make(Seen(1));
}
