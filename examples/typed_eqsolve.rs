// Core web-demo/eqsolve.egg: equations are represented by unions of syntax.
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

#[declarations]
impl std::ops::Add<&Expr> for &Expr {
    type Output = Expr;
    fn add(self, rhs: &Expr) -> Expr;
}

#[declarations]
impl std::ops::Neg for &Expr {
    type Output = Expr;
    fn neg(self) -> Expr;
}

#[declarations]
impl std::ops::Mul<&Expr> for &Expr {
    type Output = Expr;
    fn mul(self, rhs: &Expr) -> Expr;
}

#[ruleset]
fn rules(
    x: &Expr,
    y: &Expr,
    z: &Expr,
    x_num: &egg::I64,
    y_num: &egg::I64,
    n: &egg::I64,
    name: &egg::String,
    a: &Expr,
    b: &Expr,
    z_num: &egg::I64,
) -> Vec<Rule> {
    vec![
        rewrite(x + y, y + x),
        rewrite((x + y) + z, x + (y + z)),
        rewrite(Expr::num(x_num) + Expr::num(y_num), x_num + y_num),
        rule(eq(x + y, z), union(z + (-y), x)),
        rewrite(-(-x), x),
        rewrite(-Expr::num(n), egg::I64::from(0) - n),
        rule(eq(x, Expr::var(name)), union(Expr::num(1) * x, x)),
        rule(eq(x, a + b), union(Expr::num(1) * x, x)),
        rewrite((y * x) + (z * x), (y + z) * x),
        rewrite(x * y, y * x),
        rule(
            (
                eq(Expr::num(x_num) * y, Expr::num(z_num)),
                eq(z_num % x_num, 0),
            ),
            union(y, Expr::num(z_num / x_num)),
        ),
    ]
}

pub fn main() -> Result<(), TypedError> {
    let x = Expr::var("x");
    let y = Expr::var("y");
    let z = Expr::var("z");
    let mut egraph = EGraph::default();
    egraph.register((union(&x + 2, 7), union(&z + &y, 6), union(&z + &z, &y)))?;
    egraph.run(rules.repeat(5))?;
    for value in [&x, &y, &z] {
        let _ = egraph.extract(value)?;
    }
    let six_minus_y = Expr::num(6) + (-&y);
    let twelve_minus_y = Expr::num(12) + (-&y);
    assert!(egraph.check((
        eq(z, &six_minus_y),
        eq(&y, &six_minus_y + &six_minus_y),
        eq(&y, &twelve_minus_y + (-&y)),
        eq(&y + &y, twelve_minus_y),
        eq((&y + &y) + &y, 12),
        eq((Expr::num(2) * &y) + &y, 12),
        eq(Expr::num(3) * y, 12),
    ))?);
    Ok(())
}
