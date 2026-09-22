use egglog_experimental::typed::{builtins::I64, prelude::*};
#[sort]
pub struct Num;
#[declarations]
impl Num {
    #[constructor(try_from)]
    fn nullary() -> Self;
}
#[declarations]
impl Num {
    #[constructor(try_from)]
    fn binary(left: I64, right: I64) -> Self;
}
#[declarations]
impl Num {
    #[constructor(try_from)]
    fn receiver(&self) -> Self;
}
#[declarations]
impl Num {
    #[constructor(try_from)]
    fn identity(value: Self) -> Self;
}
#[declarations]
impl Num {
    #[constructor(try_from(I64))]
    fn duplicate_input(value: I64) -> Self;
}
#[declarations]
impl Num {
    #[constructor(try_from(i64, i64))]
    fn duplicate_target(value: I64) -> Self;
}
#[declarations]
impl Num {
    #[constructor(try_from, try_from)]
    fn duplicate_option(value: I64) -> Self;
}
#[declarations]
impl Num {
    #[constructor(try_from(&str))]
    fn borrowed_target(value: I64) -> Self;
}
#[declarations]
impl Num {
    #[constructor(try_from = i64)]
    fn malformed(value: I64) -> Self;
}
#[declarations]
impl Num {
    #[function(no_merge, try_from)]
    fn function(value: I64) -> Self;
}
#[declarations]
impl Num {
    #[relation(try_from)]
    fn relation(value: I64);
}
fn main() {}
