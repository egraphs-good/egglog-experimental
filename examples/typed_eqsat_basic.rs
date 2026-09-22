// Core eqsat-basic.egg and Python eqsat_basic.py: distributivity and folding.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Math;

#[declarations]
impl Math {
    #[constructor(from(i64, i32))]
    pub fn num(value: egg::I64) -> Math;
    #[constructor(from(&str, std::string::String))]
    pub fn var(name: egg::String) -> Math;
}

#[declarations]
impl std::ops::Add<&Math> for &Math {
    type Output = Math;
    fn add(self, rhs: &Math) -> Math;
}

#[declarations]
impl std::ops::Mul<&Math> for &Math {
    type Output = Math;
    fn mul(self, rhs: &Math) -> Math;
}

#[ruleset]
fn arithmetic(a: &Math, b: &Math, c: &Math, i: &egg::I64, j: &egg::I64) -> Vec<Rule> {
    vec![
        rewrite(a + b, b + a),
        rewrite(a * (b + c), a * b + a * c),
        rewrite(Math::num(i) + Math::num(j), i + j),
        rewrite(Math::num(i) * Math::num(j), i * j),
    ]
}

pub fn main() -> Result<(), TypedError> {
    let x = Math::var("x");
    let expr1 = let_("expr1", Math::num(2) * (&x + 3));
    let expr2 = let_("expr2", Math::num(6) + Math::num(2) * x);
    let mut egraph = EGraph::default();
    egraph.register((&expr1, &expr2))?;
    egraph.run(arithmetic.repeat(10))?;
    assert!(egraph.check(eq(expr1, expr2))?);
    Ok(())
}
