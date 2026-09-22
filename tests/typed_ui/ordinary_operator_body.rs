use egglog_experimental::typed::prelude::*;
#[sort]
pub struct Num;
#[declarations]
impl std::ops::Neg for Num {
    type Output = Self;
    fn neg(self) -> Self::Output { self }
}
fn main() {
    let value = var::<Num>("value");
    let _ = -&value;
}
