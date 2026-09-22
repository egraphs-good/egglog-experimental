// Core web-demo/bdd.egg: all Boolean BDD operations and source checks.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Bdd;

#[declarations]
impl Bdd {
    pub fn ite(index: egg::I64, yes: Bdd, no: Bdd) -> Bdd;
    pub fn truth() -> Bdd;
    pub fn falsity() -> Bdd;
}

impl From<bool> for Bdd {
    fn from(value: bool) -> Self {
        if value {
            Self::truth()
        } else {
            Self::falsity()
        }
    }
}

#[declarations]
impl std::ops::BitAnd<&Bdd> for &Bdd {
    type Output = Bdd;
    fn bitand(self, rhs: &Bdd) -> Bdd;
}

#[declarations]
impl std::ops::BitOr<&Bdd> for &Bdd {
    type Output = Bdd;
    fn bitor(self, rhs: &Bdd) -> Bdd;
}

#[declarations]
impl std::ops::Not for &Bdd {
    type Output = Bdd;
    fn not(self) -> Bdd;
}

#[declarations]
impl std::ops::BitXor<&Bdd> for &Bdd {
    type Output = Bdd;
    fn bitxor(self, rhs: &Bdd) -> Bdd;
}

#[ruleset]
fn theory(
    n: &egg::I64,
    m: &egg::I64,
    a: &Bdd,
    b: &Bdd,
    c: &Bdd,
    d: &Bdd,
    x: &Bdd,
    y: &Bdd,
) -> Vec<Rule> {
    // Smaller variable indices belong higher in the decision tree.
    // The n < m guards preserve this ordering when combining different roots.
    let left = Bdd::ite(n, a, b);
    let right = Bdd::ite(m, c, d);
    let same = Bdd::ite(n, c, d);
    vec![
        // A test whose two branches agree needs no decision node.
        rewrite(Bdd::ite(n, a, a), a),
        rewrite(x & y, y & x),
        rewrite(Bdd::falsity() & x, false),
        rewrite(Bdd::truth() & x, x),
        rewrite(&left & &right, Bdd::ite(n, a & &right, b & &right)).when(n.lt(m)),
        rewrite(&left & &same, Bdd::ite(n, a & c, b & d)),
        rewrite(x | y, y | x),
        rewrite(Bdd::truth() | x, true),
        rewrite(Bdd::falsity() | x, x),
        rewrite(&left | &right, Bdd::ite(n, a | &right, b | &right)).when(n.lt(m)),
        rewrite(&left | &same, Bdd::ite(n, a | c, b | d)),
        rewrite(!Bdd::truth(), false),
        rewrite(!Bdd::falsity(), true),
        rewrite(!&left, Bdd::ite(n, !a, !b)),
        rewrite(x ^ y, y ^ x),
        rewrite(Bdd::truth() ^ x, !x),
        rewrite(Bdd::falsity() ^ x, x),
        rewrite(&left ^ &right, Bdd::ite(n, a ^ &right, b ^ right)).when(n.lt(m)),
        rewrite(left ^ same, Bdd::ite(n, a ^ c, b ^ d)),
    ]
}

#[expect(clippy::eq_op, reason = "the source checks Boolean idempotence")]
pub fn main() -> Result<(), TypedError> {
    let mut egraph = EGraph::default();
    egraph.push()?;
    let [v0, v1, v2] = [0, 1, 2].map(|i| Bdd::ite(i, true, false));
    let xor_left = !&v0 ^ &v1;
    let xor_right = &v0 ^ !&v1;
    let xor_not = !(&v0 ^ &v1);
    let cases = [
        (!!&v0, v0.clone()),
        (&v0 | !&v0, Bdd::truth()),
        (&v0 & !&v0, Bdd::falsity()),
        (&v0 & &v0, v0.clone()),
        (&v0 | &v0, v0.clone()),
        (!&v0 ^ &v0, Bdd::truth()),
        ((&v1 | &v2) & &v2, v2.clone()),
        (xor_left.clone(), xor_right.clone()),
        (xor_right, xor_not.clone()),
        (xor_not, xor_left),
        (&v1 & &v2, Bdd::ite(1, Bdd::ite(2, true, false), false)),
        (!&v1 & (!&v0 & (&v0 ^ &v1)), Bdd::falsity()),
        (!&v1 | (!&v0 | (v0 ^ !v1)), Bdd::truth()),
    ]
    .into_iter()
    .enumerate()
    .map(|(i, (actual, expected))| (let_(format!("t{i}"), actual), expected))
    .collect::<Vec<_>>();
    egraph.register(cases.iter().map(|(actual, _)| actual).collect::<Vec<_>>())?;
    egraph.run(theory.repeat(30))?;
    for (actual, expected) in cases {
        assert!(egraph.check(eq(actual, expected))?);
    }
    egraph.pop()?;
    Ok(())
}
