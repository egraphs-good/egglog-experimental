// Core web-demo/birewrite.egg: one equality authors both rewrite directions.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Math;

#[declarations]
impl Math {
    pub fn lit(value: egg::I64) -> Math;
}

#[declarations]
impl std::ops::Add<&Math> for &Math {
    type Output = Math;
    fn add(self, rhs: &Math) -> Math;
}

#[ruleset]
fn associativity(x: &Math, y: &Math, z: &Math) -> Vec<Rule> {
    birewrite((x + y) + z, x + (y + z)).into()
}

pub fn main() -> Result<(), TypedError> {
    let [a, b, c, d, e, f] = [1, 2, 3, 4, 5, 6].map(Math::lit);
    let ex1 = let_("ex1", (&a + &b) + &c);
    let ex2 = let_("ex2", &d + (&e + &f));
    let mut egraph = EGraph::default();
    egraph.register((&ex1, &ex2))?;
    egraph.run(associativity.repeat(10))?;
    assert!(egraph.check((eq(ex1, a + (b + c)), eq(ex2, (d + e) + f),))?);
    Ok(())
}
