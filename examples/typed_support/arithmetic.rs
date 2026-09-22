// Shared executable theory from Python tutorials 3 and 4. The scheduling
// lesson imports the analysis lesson's schema; these fixed rulesets preserve
// that reuse without duplicating the theory in two runnable examples.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Num;

#[declarations]
impl Num {
    #[constructor(from(i64, i32))]
    pub fn constant(value: egg::BigRat) -> Num;
    #[constructor(from(&str, std::string::String))]
    pub fn var(name: egg::String) -> Num;
    pub fn less_equal(&self, right: Num);
    pub fn non_zero(&self);
    #[function(merge = |old: egg::BigRat, new: egg::BigRat| old.min(new))]
    pub fn upper(&self) -> egg::BigRat;
    #[function(merge = |old: egg::BigRat, new: egg::BigRat| old.max(new))]
    pub fn lower(&self) -> egg::BigRat;
}

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

#[declarations]
impl std::ops::Div<&Num> for &Num {
    type Output = Num;
    fn div(self, rhs: &Num) -> Num;
}

#[ruleset]
pub fn inequalities(
    a: &Num,
    b: &Num,
    c: &Num,
    n: &egg::BigRat,
    m: &egg::BigRat,
    name: &egg::String,
    d: &Num,
) -> Vec<Rule> {
    let left = a + b;
    let right = c + d;
    vec![
        rule((a.less_equal(b), b.less_equal(c)), a.less_equal(c)),
        rule(
            (eq(a, Num::constant(n)), eq(b, Num::constant(m)), n.le(m)),
            a.less_equal(b),
        ),
        rule(eq(a, Num::var(name)), a.less_equal(a)),
        rule(
            (&left, &right, a.less_equal(c), b.less_equal(d)),
            left.less_equal(&right),
        ),
    ]
}

#[ruleset]
pub fn algebra(x: &Num, y: &Num, z: &Num, a: &egg::BigRat, b: &egg::BigRat) -> Vec<Rule> {
    vec![
        rewrite(x + (y + z), x + y + z),
        rewrite(x + y + z, x + (y + z)),
        rewrite(x * (y * z), x * y * z),
        rewrite(x * y * z, x * (y * z)),
        rewrite(x + y, y + x),
        rewrite(x * y, y * x),
        rewrite(x * (y + z), x * y + x * z),
        rewrite(x + 0, x),
        rewrite(x * 1, x),
        rewrite(Num::constant(a) + Num::constant(b), a + b),
        rewrite(Num::constant(a) * Num::constant(b), a * b),
    ]
}

#[ruleset]
pub fn intervals(
    e: &Num,
    n: &egg::BigRat,
    a: &Num,
    b: &Num,
    u: &egg::BigRat,
    v: &egg::BigRat,
    la: &egg::BigRat,
    lb: &egg::BigRat,
    ua: &egg::BigRat,
    ub: &egg::BigRat,
) -> Vec<Rule> {
    let p00 = la * lb;
    let p01 = la * ub;
    let p10 = ua * lb;
    let p11 = ua * ub;
    vec![
        rule(e.less_equal(Num::constant(n)), set(e.upper(), n)),
        rule(Num::constant(n).less_equal(e), set(e.lower(), n)),
        rule(
            (eq(e, a + b), eq(a.upper(), u), eq(b.upper(), v)),
            set(e.upper(), u + v),
        ),
        rule(
            (eq(e, a + b), eq(a.lower(), u), eq(b.lower(), v)),
            set(e.lower(), u + v),
        ),
        rule(
            (
                eq(e, a * b),
                eq(a.lower(), la),
                eq(b.lower(), lb),
                eq(a.upper(), ua),
                eq(b.upper(), ub),
            ),
            (
                set(e.lower(), p00.min(p01.min(p10.min(&p11)))),
                set(e.upper(), p00.max(p01.max(p10.max(p11)))),
            ),
        ),
        rule(eq(e, a * a), set(e.lower(), 0)),
        rule(e.lower().gt(0), e.non_zero()),
        rule(e.upper().lt(0), e.non_zero()),
    ]
}

#[expect(
    clippy::eq_op,
    reason = "the source theory deliberately rewrites nonzero e/e to one"
)]
#[ruleset]
pub fn guarded_optimizations(e: &Num, x: &Num) -> Vec<Rule> {
    vec![
        rewrite(e / e, 1).when(e.non_zero()),
        rewrite(e * (x / e), x).when(e.non_zero()),
    ]
}
