use egglog_experimental::typed::{
    builtins::{I64, Vec as EVec},
    prelude::*,
};

#[sort]
pub struct Item;
#[declarations]
impl Item {
    pub fn A() -> Self;
    pub fn B() -> Self;
}

fn main() -> Result<(), TypedError> {
    let values = EVec::<I64>::of([7_i64, 11, 7]);
    let mut graph = EGraph::default();
    assert_eq!(i64::try_from(&graph.extract(values.get(1_i64))?)?, 11);
    let items = EVec::<Item>::of([Item::A(), Item::B()]);
    let nested = EVec::<EVec<Item>>::of([&items, &EVec::<Item>::empty()]);
    let extracted = graph.extract(&nested)?;
    let children = Vec::<EVec<Item>>::try_from(&extracted)?;
    assert_eq!(Vec::<Item>::try_from(&children[0])?, [Item::A(), Item::B()]);
    assert!(Vec::<Item>::try_from(&children[1])?.is_empty());
    Ok(())
}
