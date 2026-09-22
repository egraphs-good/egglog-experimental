// Core web-demo/unify.egg: injectivity of a user-defined product constructor.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Expr;

#[declarations]
impl Expr {
    #[constructor(from(&str, std::string::String))]
    pub fn var(name: egg::String) -> Expr;
    #[constructor(from(i64, i32))]
    pub fn lit(value: egg::I64) -> Expr;
}

#[declarations]
impl std::ops::Mul<&Expr> for &Expr {
    type Output = Expr;
    fn mul(self, rhs: &Expr) -> Expr;
}

#[ruleset]
fn rules(a: &Expr, b: &Expr, c: &Expr, d: &Expr, i: &egg::I64) -> Vec<Rule> {
    vec![
        rule(eq(a * b, c * d), (union(a, c), union(b, d))),
        rule(
            eq(Expr::lit(i), a * b),
            panic("Literal cannot be equal to a product"),
        ),
    ]
}

pub fn main() -> Result<(), TypedError> {
    let a = Expr::var("a");
    let mut egraph = EGraph::default();
    egraph.register(union(&a * &a, Expr::lit(1) * 2))?;
    egraph.run(rules.repeat(3))?;
    assert!(egraph.check((eq(a, 1), eq(Expr::lit(2), 1)))?);
    Ok(())
}
