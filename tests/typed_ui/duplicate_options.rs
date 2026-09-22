use egglog_experimental::typed::prelude::*;

#[sort(name = "first", name = "second")]
pub struct DuplicateSort;

#[sort]
pub struct Term;

#[constructor(name = "first", name = "second")]
pub fn Named() -> Term;

#[constructor(cost = 1, cost = 2)]
pub fn Cost() -> Term;

#[constructor(unextractable, unextractable)]
pub fn Hidden() -> Term;

#[function(no_merge, name = "first", name = "second")]
pub fn Table() -> egglog_experimental::typed::builtins::I64;

#[relation(name = "first", name = "second")]
pub fn Row();

#[declarations]
impl Term {
    #[constructor(name = "first", name = "second")]
    fn duplicate_name() -> Self;
}

#[declarations]
impl Term {
    #[constructor(cost = 1)]
    #[constructor(cost = 2)]
    fn duplicate_attribute() -> Self;
}

#[declarations]
impl Term {
    #[constructor(unextractable, unextractable)]
    fn duplicate_flag() -> Self;
}

fn main() {}
