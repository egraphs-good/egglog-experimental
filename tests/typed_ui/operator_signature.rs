use egglog_experimental::typed::{builtins::I64, prelude::*};
#[sort]
pub struct Num;
#[declarations]
impl std::ops::Add<I64> for Num {
    type Output = Num;
    #[constructor]
    fn add(self, rhs: &Num) -> Num;
}
#[declarations]
impl std::ops::Neg for Num {
    type Output = Num;
    #[function(no_merge)]
    fn neg(self) -> I64;
}
fn main() {}

#[sort]
pub struct BorrowedOutput;
#[declarations]
impl std::ops::Neg for &BorrowedOutput {
    type Output = Self;
    #[constructor]
    fn neg(self) -> Self::Output;
}

#[sort]
pub struct WrongOutput;
#[declarations]
impl std::ops::Mul for WrongOutput {
    type Output = WrongOutput;
    #[function(no_merge)]
    fn mul(self, rhs: Self) -> I64;
}

#[sort]
pub struct WrongMethod;
#[declarations]
impl std::ops::Sub for WrongMethod {
    type Output = WrongMethod;
    #[constructor]
    fn add(self, rhs: Self) -> Self;
}
