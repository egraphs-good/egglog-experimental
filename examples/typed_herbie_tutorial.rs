// Core web-demo/herbie-tutorial.egg. These are ordinary analysis tables, not
// dynamic extraction costs. In particular the source's upper-bound product
// uses min (not max); this port preserves that instructional program exactly.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;
#[sort]
pub struct Math;

#[declarations]
impl Math {
    #[constructor(from(i64, i32))]
    pub fn num(value: egg::BigRat) -> Math;
    #[constructor(from(&str, std::string::String))]
    pub fn var(name: egg::String) -> Math;
}
#[function(merge = |old: egg::BigRat, new: egg::BigRat| old.max(new))]
pub fn lower(expr: Math) -> egg::BigRat;
#[function(merge = |old: egg::BigRat, new: egg::BigRat| old.min(new))]
pub fn upper(expr: Math) -> egg::BigRat;
#[function(no_merge)]
pub fn true_value(expr: Math) -> egg::F64;
#[function(merge = |_old: egg::F64, new: egg::F64| new)]
pub fn best_error(expr: Math) -> egg::F64;

#[declarations]
impl std::ops::Add<&Math> for &Math {
    type Output = Math;
    fn add(self, rhs: &Math) -> Math;
}

#[declarations]
impl std::ops::Div<&Math> for &Math {
    type Output = Math;
    fn div(self, rhs: &Math) -> Math;
}

#[declarations]
impl std::ops::Mul<&Math> for &Math {
    type Output = Math;
    fn mul(self, rhs: &Math) -> Math;
}

#[ruleset]
fn basic(a: &Math, b: &Math, r1: &egg::BigRat, r2: &egg::BigRat) -> Vec<Rule> {
    vec![
        rewrite(a + b, b + a),
        rewrite(a + 0, a),
        rewrite(Math::num(r1) + Math::num(r2), r1 + r2),
    ]
}

#[ruleset]
fn unsafe_division(r: &egg::BigRat) -> Vec<Rule> {
    let one = Math::num(1);

    vec![rule(Math::num(r), union(&one, Math::num(r) / Math::num(r)))]
}

#[expect(
    clippy::eq_op,
    reason = "the source theory guards division cancellation"
)]
#[ruleset]
fn intervals(
    r: &egg::BigRat,
    e: &Math,
    a: &Math,
    b: &Math,
    x: &egg::BigRat,
    y: &egg::BigRat,
    la: &egg::BigRat,
    lb: &egg::BigRat,
    ua: &egg::BigRat,
    ub: &egg::BigRat,
) -> Vec<Rule> {
    let one = Math::num(1);
    let number = Math::num(r);
    let add = a + b;
    let bound = (la * lb).min((la * ub).min((ua * lb).min(ua * ub)));

    vec![
        rule(&number, (set(lower(&number), r), set(upper(&number), r))),
        rule(
            (eq(e, &add), eq(x, lower(a)), eq(y, lower(b))),
            set(lower(e), x + y),
        ),
        rule(
            (eq(e, &add), eq(x, upper(a)), eq(y, upper(b))),
            set(upper(e), x + y),
        ),
        rule(
            (
                eq(e, a * b),
                eq(la, lower(a)),
                eq(lb, lower(b)),
                eq(ua, upper(a)),
                eq(ub, upper(b)),
            ),
            (set(lower(e), &bound), set(upper(e), bound)),
        ),
        rule((eq(e, &add), lower(e).gt(0)), union(&one, &add / &add)),
    ]
}

#[ruleset]
fn truth(e: &Math, lb: &egg::BigRat) -> Vec<Rule> {
    vec![rule(
        (eq(lower(e).to_f64(), upper(e).to_f64()), eq(lb, lower(e))),
        set(true_value(e), lb.to_f64()),
    )]
}

#[ruleset]
fn error(
    n: &egg::BigRat,
    a: &Math,
    b: &Math,
    va: &egg::F64,
    vb: &egg::F64,
    true_v: &egg::F64,
    computed: &egg::F64,
) -> Vec<Rule> {
    let number = Math::num(n);
    let add = a + b;
    vec![
        rule(&number, set(best_error(&number), n.to_f64())),
        rule(
            &add,
            set(best_error(&add), egg::BigRat::new(10000, 1).to_f64()),
        ),
        rule(
            (
                &add,
                eq(best_error(a), va),
                eq(best_error(b), vb),
                eq(true_v, true_value(&add)),
                eq(computed, va + vb),
                (computed - true_v).abs().lt(best_error(&add)),
            ),
            set(best_error(&add), computed),
        ),
    ]
}

#[ruleset]
fn bounds() -> Ruleset {
    ruleset((&basic, &intervals))
}

#[ruleset]
fn with_truth() -> Ruleset {
    ruleset((&bounds, &truth))
}

#[ruleset]
fn all() -> Ruleset {
    ruleset((&with_truth, &error))
}

#[expect(
    clippy::eq_op,
    reason = "the source checks guarded division cancellation"
)]
pub fn main() -> Result<(), TypedError> {
    let zero = egg::BigRat::new(0, 1);
    let one = Math::num(1);
    let two = Math::num(2);
    let mut egraph = EGraph::default();
    let one_two = let_("one_two", &one + &two);
    egraph.register((&one_two, Math::num(&zero)))?;
    egraph.push()?;
    egraph.run(&basic)?;
    assert!(egraph.check((eq(&one_two, 3), eq(two + &one, one_two)))?);
    egraph.pop()?;
    egraph.push()?;
    // Unguarded cancellation incorrectly proves 1 = 0/0; keep the counterexample scoped.
    egraph.run(ruleset((basic.clone(), &unsafe_division)))?;
    assert!(egraph.check(eq(&one, Math::num(&zero) / Math::num(&zero)))?);
    egraph.pop()?;
    let x = Math::var("x");
    let x1 = let_("x1", &x + one);
    egraph.register(&x1)?;
    egraph.push()?;
    egraph.register((set(lower(&x), zero), set(upper(&x), 1)))?;
    egraph.run(bounds.repeat(3))?;
    egraph.extract(&lower(&x1))?;
    egraph.extract(&upper(&x1))?;
    assert!(egraph.check(eq(Math::num(1), &x1 / &x1))?);
    egraph.pop()?;
    let exact = egg::BigRat::new(200, 201);
    egraph.register((set(lower(&x), &exact), set(upper(x), exact)))?;
    egraph.run(bounds.repeat(3))?;
    egraph.extract(&lower(&x1))?;
    egraph.extract(&upper(&x1))?;
    egraph.run(&with_truth)?;
    egraph.extract(&true_value(x1))?;
    egraph.push()?;
    let hundredth = Math::num(egg::BigRat::new(1, 100));
    let target = let_(
        "target",
        (&hundredth + &hundredth) + egg::BigRat::new(-2, 100),
    );
    egraph.register(&target)?;
    egraph.run(&all)?;
    // Start with a poor error estimate; later runs allow constant folding to improve it.
    egraph.register(set(
        best_error(&target),
        egg::BigRat::new(10000, 1).to_f64(),
    ))?;
    egraph.extract(&best_error(&target))?;
    egraph.run(&all)?;
    egraph.extract(&best_error(target))?;
    egraph.pop()?;
    Ok(())
}
