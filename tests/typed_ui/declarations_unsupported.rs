use egglog_experimental::typed::prelude::*;
#[sort]
pub struct Num;
#[declarations]
impl Num {
    #[function(no_merge)]
    fn mutable(&mut self) -> egglog_experimental::typed::builtins::I64;
}
trait Rows {
    fn row(&self);
}
#[declarations]
impl Rows for Num {
    #[relation]
    fn row(&self);
}
fn main() {}
