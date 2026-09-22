// Core web-demo/antiunify.egg: AU nodes retain disagreement between inputs.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Expr;

#[declarations]
impl Expr {
    #[constructor(from(i64, i32))]
    pub fn num(value: egg::I64) -> Expr;
    #[constructor(from(&str, std::string::String))]
    pub fn var(name: egg::String) -> Expr;
}
#[constructor]
// A remaining AU node is a placeholder that can unify with either input.
pub fn au(lhs: Expr, rhs: Expr) -> Expr;

#[declarations]
impl std::ops::Add<&Expr> for &Expr {
    type Output = Expr;
    fn add(self, rhs: &Expr) -> Expr;
}

#[ruleset]
fn rules(a: &Expr, b: &Expr, c: &Expr, d: &Expr, i: &egg::I64, j: &egg::I64) -> Vec<Rule> {
    vec![
        rewrite(a + b, b + a),
        rewrite(Expr::num(i) + Expr::num(j), i + j),
        rewrite(au(a, a), a),
        rewrite(au(a + b, c + d), au(a, c) + au(b, d)),
    ]
}

pub fn main() -> Result<(), TypedError> {
    let output = let_(
        "output",
        au(Expr::var("x") + (Expr::num(1) + 2), Expr::num(3) + "y"),
    );
    let mut egraph = EGraph::default();
    egraph.register(&output)?;
    egraph.run(rules.repeat(4))?;
    assert!(egraph.check(eq(&output, Expr::num(3) + au("x", "y")))?);
    let extracted = egraph.extract(&output)?;
    assert!(egraph.check(eq(output, extracted))?);
    Ok(())
}
