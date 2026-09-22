use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Term;
#[declarations]
impl Term {
    #[constructor(args = PairArgs)]
    fn pair(&self, receiver: Self) -> Self;
}

fn main() {}
