use egglog_experimental::typed::{builtins::I64, prelude::*};
#[sort]
pub struct Duplicate;
#[declarations]
impl Duplicate {
    #[constructor(from)]
    fn first(value: I64) -> Self;
    #[constructor(from)]
    fn second(value: I64) -> Self;
}
#[sort]
pub struct Existing;
#[declarations]
impl Existing {
    #[constructor(from)]
    fn integer(value: I64) -> Self;
}
impl From<I64> for Existing {
    fn from(value: I64) -> Self { Self::integer(value) }
}
#[sort]
pub struct Identity;
type Alias = Identity;
#[constructor(from)]
fn identity(value: Alias) -> Identity;
#[sort]
pub struct MissingRoute;
#[constructor(from(bool))]
fn missing(value: I64) -> MissingRoute;
fn main() {}
