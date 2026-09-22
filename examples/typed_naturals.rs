// Core web-demo/naturals.egg: recursive terms and staged addition/multiplication.
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct N;

#[declarations]
impl N {
    pub fn z() -> N;
    pub fn s(predecessor: N) -> N;
}

#[declarations]
impl std::ops::Add<&N> for &N {
    type Output = N;
    fn add(self, rhs: &N) -> N;
}

#[declarations]
impl std::ops::Mul<&N> for &N {
    type Output = N;
    fn mul(self, rhs: &N) -> N;
}

#[ruleset]
fn addition(n: &N, m: &N) -> Vec<Rule> {
    vec![rewrite(N::z() + n, n), rewrite(N::s(m) + n, N::s(m + n))]
}

#[ruleset]
fn multiplication(n: &N, m: &N) -> Vec<Rule> {
    vec![
        rewrite(N::z() * n, N::z()),
        rewrite(N::s(m) * n, n + (m * n)),
    ]
}

#[ruleset]
fn arithmetic() -> Ruleset {
    ruleset((&addition, &multiplication))
}

pub fn main() -> Result<(), TypedError> {
    let zero = N::z();
    let one = N::s(&zero);
    let two = N::s(&one);
    let three = N::s(&two);
    let four1 = let_("four1", N::s(&three));
    let four2 = let_("four2", &two + &two);
    let mut egraph = EGraph::default();
    egraph.register((zero, one, &two, &three, &four1, &four2))?;
    assert!(!egraph.check(eq(&four1, &four2))?);
    egraph.run(addition.saturate())?;
    assert!(egraph.check(eq(four1, four2))?);

    let six1 = let_("six1", &two * three);
    let six2 = let_("six2", &two + (&two + &two));
    egraph.register((&six1, &six2))?;
    assert!(!egraph.check(eq(&six1, &six2))?);
    egraph.run(arithmetic.saturate())?;
    assert!(egraph.check(eq(six1, six2))?);
    Ok(())
}
