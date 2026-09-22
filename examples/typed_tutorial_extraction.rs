// Python extraction tutorial, lines 1–99: static costs and best-tree extraction.
// Per-node dynamic costs in the second half are explicitly outside this lesson.
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

#[declarations]
impl std::ops::Add<&Num> for &Num {
    type Output = Num;
    #[constructor(cost = 2)]
    fn add(self, rhs: &Num) -> Num;
}

#[declarations]
impl std::ops::Mul<&Num> for &Num {
    type Output = Num;
    #[constructor(cost = 10)]
    fn mul(self, rhs: &Num) -> Num;
}

#[ruleset]
pub(crate) fn strength_reduction(x: &Num) -> Vec<Rule> {
    vec![rewrite(x * 2, x + x)]
}

pub fn main() -> Result<(), TypedError> {
    let x = Num::var("x");
    let expr = let_("expr", &x * 2 + 1);
    let mut egraph = EGraph::default();
    egraph.register(&expr)?;
    let (_, before) = egraph.extract_with_cost(&expr)?;
    // Costs include ground leaves. x costs 2, each integer constant costs 2.
    assert_eq!(before, 18);
    egraph.run(&strength_reduction)?;
    let (best, after) = egraph.extract_with_cost(&expr)?;
    assert_eq!(after, 10);
    assert!(egraph.check(eq(&best, (&x + &x) + 1))?);
    let (left, _) = get_args(&best, |left: &Num, right: &Num| left + right)?
        .expect("the cheapest root is addition");
    assert!(get_args(&left, |left: &Num, right: &Num| left + right)?.is_some());
    // A query variable leaves the right child unconstrained while retaining left.
    let right = var::<Num>("right");
    assert!(egraph.check(eq(&best, &left + right))?);
    // Extraction selects a native best tree. Equal-cost ties are not ordered.
    let forest = egraph.extract_many(&[&expr, &expr])?;
    assert_eq!(forest.len(), 2);
    assert_eq!(forest[0], forest[1]);
    Ok(())
}
