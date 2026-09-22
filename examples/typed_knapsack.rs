// Core web-demo/knapsack.egg: dynamic programming as equality saturation.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Expr;

#[declarations]
impl Expr {
    #[constructor(from(i64, i32))]
    pub fn num(value: egg::I64) -> Expr;
    pub fn max(left: Expr, right: Expr) -> Expr;
}
#[sort]
pub struct Objects;

#[declarations]
impl Objects {
    pub fn nil() -> Objects;
    pub fn cons(weight: egg::I64, value: egg::I64, rest: Objects) -> Objects;
}
#[constructor]
pub fn knap(capacity: egg::I64, objects: Objects) -> Expr;
#[function(no_merge)]
pub fn unwrap(value: Expr) -> egg::I64;

#[declarations]
impl std::ops::Add<&Expr> for &Expr {
    type Output = Expr;
    fn add(self, rhs: &Expr) -> Expr;
}

#[ruleset]
fn rules(
    a: &egg::I64,
    b: &egg::I64,
    capacity: &egg::I64,
    weight: &egg::I64,
    value: &egg::I64,
    rest: &Objects,
    n: &egg::I64,
) -> Vec<Rule> {
    let number = Expr::num(n);
    vec![
        rewrite(Expr::num(a) + Expr::num(b), a + b),
        rewrite(Expr::max(Expr::num(a), Expr::num(b)), a.max(b)),
        rewrite(
            knap(capacity, Objects::cons(weight, value, rest)),
            Expr::max(
                Expr::num(value) + knap(capacity - weight, rest),
                knap(capacity, rest),
            ),
        )
        .when(weight.le(capacity)),
        rewrite(
            knap(capacity, Objects::cons(weight, value, rest)),
            knap(capacity, rest),
        )
        .when(weight.gt(capacity)),
        rewrite(knap(capacity, Objects::nil()), 0),
        rule(&number, set(unwrap(&number), n)),
    ]
}

pub fn main() -> Result<(), TypedError> {
    type Case = (i64, &'static [(i64, i64)], i64);
    let cases: [Case; 4] = [
        (13, &[(5, 5), (3, 3), (12, 12), (5, 5)], 13),
        (5, &[(6, 6)], 0),
        (5, &[(1, 1), (1, 1), (1, 1)], 3),
        (15, &[(12, 40), (2, 20), (1, 20), (1, 10), (4, 100)], 150),
    ];
    let outputs: std::vec::Vec<_> = cases
        .iter()
        .enumerate()
        .map(|(i, (capacity, items, _))| {
            let objects = items
                .iter()
                .rev()
                .fold(Objects::nil(), |rest, &(weight, value)| {
                    Objects::cons(weight, value, rest)
                });
            let_(format!("test{i}"), knap(*capacity, objects))
        })
        .collect();
    let mut egraph = EGraph::default();
    egraph.register(outputs.as_slice())?;
    egraph.run(rules.repeat(100))?;
    for (output, (_, _, expected)) in outputs.into_iter().zip(cases) {
        assert!(egraph.check(eq(output, expected))?);
    }
    Ok(())
}
