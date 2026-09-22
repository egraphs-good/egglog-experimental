use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Num;
#[sort]
pub struct Other;

#[declarations]
impl std::ops::Add for Num {
    type Output = Num;
    #[constructor]
    fn add(self, rhs: Self) -> Self;
}

#[declarations]
impl std::ops::Add<Other> for Num {
    type Output = Num;
    #[constructor]
    fn add(self, rhs: Other) -> Self;
}

fn main() {}
