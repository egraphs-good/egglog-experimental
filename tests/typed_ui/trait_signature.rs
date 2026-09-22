use egglog_experimental::typed::{builtins::I64, prelude::*};
#[sort]
pub struct Num;
trait Read {
    fn read(&self, value: I64) -> I64;
}
#[declarations]
impl Read for Num {
    #[function(no_merge)]
    fn read(&self, value: &I64) -> I64;
}
fn main() {}
