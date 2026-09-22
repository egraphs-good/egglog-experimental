// Python basics tutorial: authoring is separate from registration and running.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Num;

#[declarations]
impl Num {
    #[constructor(from(i64, i32))]
    pub fn constant(value: egg::I64) -> Num;
    #[constructor(from(&str, std::string::String))]
    pub fn var(name: egg::String) -> Num;
}

// One annotated borrowed implementation also accepts RHS values convertible to Num.
#[declarations]
impl std::ops::Add<&Num> for &Num {
    type Output = Num;
    fn add(self, rhs: &Num) -> Num;
}

#[declarations]
impl std::ops::Mul<&Num> for &Num {
    type Output = Num;
    fn mul(self, rhs: &Num) -> Num;
}

#[ruleset]
pub(crate) fn arithmetic(x: &Num, y: &Num, z: &Num, a: &egg::I64, b: &egg::I64) -> Vec<Rule> {
    vec![
        rewrite(x + y, y + x),
        rewrite(x + (y + z), (x + y) + z),
        rewrite(x * y, y * x),
        rewrite(x * (y * z), (x * y) * z),
        rewrite(Num::constant(a) + Num::constant(b), a + b),
        rewrite(Num::constant(a) * Num::constant(b), a * b),
    ]
}

pub fn main() -> Result<(), TypedError> {
    let x = &Num::var("x");
    // These are the actual Python lesson's multiplication expressions. The
    // separate eqsat_basic example covers the distributivity example.
    let expr1 = let_("expr1", Num::constant(2) * (x * 3));
    let expr2 = let_("expr2", Num::constant(6) * x);
    let mut egraph = EGraph::default();
    egraph.register((&expr1, &expr2))?;
    assert_eq!(
        egraph.extract(&egg::String::from("Hello, world!"))?,
        egg::String::from("Hello, world!")
    );
    assert_eq!(egraph.extract(&egg::I64::from(42))?, egg::I64::from(42));
    egraph.extract(&expr1)?;
    egraph.extract(&expr2)?;

    // Distinct named variables bind independently; checking does not insert terms.
    let left = &var::<Num>("left");
    let right = &var::<Num>("right");
    assert!(egraph.check(eq(&expr1, left * right))?);
    assert!(!egraph.check(eq(&expr1, left + right))?);

    let query_x = &var::<Num>("query_x");
    assert!(!egraph.check(eq(query_x + 3, Num::constant(3) + query_x))?);
    assert!(!egraph.check(eq(Num::constant(-2) + 2, Num::constant(2) + -2))?);
    assert_eq!(egraph.extract(&(egg::I64::from(1) + 2))?, egg::I64::from(3));
    assert_eq!(
        egraph.extract(&(egg::String::from("1") + "2"))?,
        egg::String::from("12")
    );
    assert_eq!(
        egraph.extract(&(egg::F64::from(1.0) + 2.0))?,
        egg::F64::from(3.0)
    );
    egraph.run(arithmetic.repeat(10))?;
    assert!(egraph.check(eq(expr1, expr2))?);
    Ok(())
}
