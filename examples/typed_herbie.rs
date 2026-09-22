// Complete core web-demo/herbie.egg: 196 analysis/simplification rules and
// fourteen source scopes. This intentionally preserves the source's capital
// "Exp", tan(-x) -> -cos(x), and unguarded interval division; it is a faithful
// example port, not a corrected or universally sound numerical theory.
// Source-only constant aliases are ordinary Rust DAG bindings (not captures
// inside rules). All executable input below is typed Rust, with no text parser.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;
#[sort]
pub struct Math;

#[declarations]
impl Math {
    #[constructor(from(i64, i32))]
    pub fn num(value: egg::BigRat) -> Math;
    pub fn var(name: egg::String) -> Math;
    pub fn constant(name: egg::String) -> Math;
    pub fn unary(operator: egg::String, argument: Math) -> Math;
    pub fn pow(left: Math, right: Math) -> Math;
    pub fn sqrt(expression: Math) -> Math;
    pub fn cbrt(expression: Math) -> Math;
    pub fn fabs(expression: Math) -> Math;
    pub fn ceil(expression: Math) -> Math;
    pub fn floor(expression: Math) -> Math;
    pub fn round(expression: Math) -> Math;
    pub fn log(expression: Math) -> Math;
}
#[function(merge = |old: egg::BigRat, new: egg::BigRat| old.min(new))]
pub fn upper(expression: Math) -> egg::BigRat;
#[function(merge = |old: egg::BigRat, new: egg::BigRat| old.max(new))]
pub fn lower(expression: Math) -> egg::BigRat;
#[relation]
pub fn non_zero(expression: Math);

#[declarations]
impl std::ops::Add<&Math> for &Math {
    type Output = Math;
    fn add(self, rhs: &Math) -> Math;
}

#[declarations]
impl std::ops::Sub<&Math> for &Math {
    type Output = Math;
    fn sub(self, rhs: &Math) -> Math;
}

#[declarations]
impl std::ops::Mul<&Math> for &Math {
    type Output = Math;
    fn mul(self, rhs: &Math) -> Math;
}

#[declarations]
impl std::ops::Div<&Math> for &Math {
    type Output = Math;
    fn div(self, rhs: &Math) -> Math;
}

#[declarations]
impl std::ops::Neg for &Math {
    type Output = Math;
    fn neg(self) -> Math;
}

#[expect(
    clippy::eq_op,
    reason = "the source theory includes x-x and guarded x/x"
)]
#[ruleset(name = "herbie")]
fn theory(
    r_a: &egg::BigRat,
    r_b: &egg::BigRat,
    m_denom: &Math,
    r_res: &egg::BigRat,
    r_l: &egg::BigRat,
    m_e: &Math,
    r_h: &egg::BigRat,
    r_ve: &egg::BigRat,
    m_a: &Math,
    m_b: &Math,
    r_la: &egg::BigRat,
    r_lb: &egg::BigRat,
    r_ha: &egg::BigRat,
    r_hb: &egg::BigRat,
    m_c: &Math,
    m_x: &Math,
    m_y: &Math,
    s_x: &egg::String,
    m_d: &Math,
) -> Vec<Rule> {
    let zero = Math::num(0);
    let one = Math::num(1);
    let two = Math::num(2);
    let three = Math::num(3);
    let neg_one = -&one;
    let exp_a = &Math::unary("exp", m_a);
    let exp_b = &Math::unary("exp", m_b);
    let sin_a = &Math::unary("sin", m_a);
    let sin_b = &Math::unary("sin", m_b);
    let cos_a = &Math::unary("cos", m_a);
    let cos_b = &Math::unary("cos", m_b);
    let sin_a_squared = &(sin_a * sin_a);
    let cos_a_squared = &(cos_a * cos_a);
    let pi = &Math::constant("PI");
    let sin_x = &Math::unary("sin", m_x);
    let cos_x = &Math::unary("cos", m_x);
    let tan_x = &Math::unary("tan", m_x);
    let exp_x = &Math::unary("exp", m_x);
    let exp_neg_x = &Math::unary("exp", -m_x);
    let cosh_x = &Math::unary("cosh", m_x);
    let sinh_x = &Math::unary("sinh", m_x);

    vec![
        rewrite(Math::num(r_a) + Math::num(r_b), r_a + r_b),
        rewrite(Math::num(r_a) - Math::num(r_b), r_a - r_b),
        rewrite(Math::num(r_a) * Math::num(r_b), r_a * r_b),
        rewrite(Math::num(r_a) / m_denom, r_a / r_b)
            .when((eq(m_denom, Math::num(r_b)), non_zero(m_denom))),
        rewrite(Math::pow(Math::num(r_a), Math::num(r_b)), r_res).when(eq(r_res, r_a.pow(r_b))),
        rewrite(-Math::num(r_a), -r_a),
        rewrite(Math::fabs(Math::num(r_a)), r_a.abs()),
        rewrite(Math::ceil(Math::num(r_a)), r_a.ceil()),
        rewrite(Math::floor(Math::num(r_a)), r_a.floor()),
        rewrite(Math::round(Math::num(r_a)), r_a.round()),
        rewrite(Math::log(Math::num(r_a)), r_res).when(eq(r_res, r_a.log())),
        // Either one-sided bound can exclude zero, even without constant evaluation.
        // As in the source, this assumes well-formed intervals: lower <= upper.
        rule((eq(r_l, lower(m_e)), r_l.gt(0)), non_zero(m_e)),
        rule((eq(r_h, upper(m_e)), r_h.lt(0)), non_zero(m_e)),
        rule(
            eq(m_e, Math::num(r_ve)),
            (set(lower(m_e), r_ve), set(upper(m_e), r_ve)),
        ),
        rule(
            (
                eq(m_e, m_a + m_b),
                eq(r_la, lower(m_a)),
                eq(r_lb, lower(m_b)),
            ),
            set(lower(m_e), r_la + r_lb),
        ),
        rule(
            (
                eq(m_e, m_a + m_b),
                eq(r_ha, upper(m_a)),
                eq(r_hb, upper(m_b)),
            ),
            set(upper(m_e), r_ha + r_hb),
        ),
        rule(
            (
                eq(m_e, m_a - m_b),
                eq(r_la, lower(m_a)),
                eq(r_ha, upper(m_a)),
                eq(r_lb, lower(m_b)),
                eq(r_hb, upper(m_b)),
            ),
            (
                set(
                    lower(m_e),
                    (r_la - r_lb)
                        .min(r_la - r_hb)
                        .min((r_ha - r_lb).min(r_ha - r_hb)),
                ),
                set(
                    upper(m_e),
                    (r_la - r_lb)
                        .max(r_la - r_hb)
                        .max((r_ha - r_lb).max(r_ha - r_hb)),
                ),
            ),
        ),
        rule(
            (
                eq(m_e, m_a * m_b),
                eq(r_la, lower(m_a)),
                eq(r_ha, upper(m_a)),
                eq(r_lb, lower(m_b)),
                eq(r_hb, upper(m_b)),
            ),
            (
                set(
                    lower(m_e),
                    (r_la * r_lb)
                        .min(r_la * r_hb)
                        .min((r_ha * r_lb).min(r_ha * r_hb)),
                ),
                set(
                    upper(m_e),
                    (r_la * r_lb)
                        .max(r_la * r_hb)
                        .max((r_ha * r_lb).max(r_ha * r_hb)),
                ),
            ),
        ),
        rule(
            (
                eq(m_e, m_a / m_b),
                eq(r_la, lower(m_a)),
                eq(r_ha, upper(m_a)),
                eq(r_lb, lower(m_b)),
                eq(r_hb, upper(m_b)),
            ),
            (
                set(
                    lower(m_e),
                    (r_la / r_lb)
                        .min(r_la / r_hb)
                        .min((r_ha / r_lb).min(r_ha / r_hb)),
                ),
                set(
                    upper(m_e),
                    (r_la / r_lb)
                        .max(r_la / r_hb)
                        .max((r_ha / r_lb).max(r_ha / r_hb)),
                ),
            ),
        ),
        rule(
            (eq(m_e, -m_a), eq(r_la, lower(m_a)), eq(r_ha, upper(m_a))),
            (set(lower(m_e), -r_ha), set(upper(m_e), -r_la)),
        ),
        rule(
            (
                eq(m_e, Math::fabs(m_a)),
                eq(r_la, lower(m_a)),
                eq(r_ha, upper(m_a)),
            ),
            (
                set(lower(m_e), r_la.abs().min(r_ha.abs())),
                set(upper(m_e), r_la.abs().max(r_ha.abs())),
            ),
        ),
        rule(
            (eq(m_e, Math::ceil(m_a)), eq(r_la, lower(m_a))),
            set(lower(m_e), r_la.ceil()),
        ),
        rule(
            (eq(m_e, Math::ceil(m_a)), eq(r_ha, upper(m_a))),
            set(upper(m_e), r_ha.ceil()),
        ),
        rule(
            (eq(m_e, Math::floor(m_a)), eq(r_la, lower(m_a))),
            set(lower(m_e), r_la.floor()),
        ),
        rule(
            (eq(m_e, Math::floor(m_a)), eq(r_ha, upper(m_a))),
            set(upper(m_e), r_ha.floor()),
        ),
        rule(
            (eq(m_e, Math::round(m_a)), eq(r_la, lower(m_a))),
            set(lower(m_e), r_la.round()),
        ),
        rule(
            (eq(m_e, Math::round(m_a)), eq(r_ha, upper(m_a))),
            set(upper(m_e), r_ha.round()),
        ),
        rewrite(m_a + m_b, m_b + m_a),
        rewrite(m_a * m_b, m_b * m_a),
        rewrite(m_a + (m_b + m_c), (m_a + m_b) + m_c),
        rewrite((m_a + m_b) + m_c, m_a + (m_b + m_c)),
        rewrite(m_a + (m_b - m_c), (m_a + m_b) - m_c),
        rewrite((m_a - m_b) + m_c, m_a - (m_b - m_c)),
        rewrite(m_a - (m_b + m_c), (m_a - m_b) - m_c),
        rewrite((m_a + m_b) - m_c, m_a + (m_b - m_c)),
        rewrite((m_a - m_b) - m_c, m_a - (m_b + m_c)),
        rewrite(m_a - (m_b - m_c), (m_a - m_b) + m_c),
        rewrite(m_a * (m_b * m_c), (m_a * m_b) * m_c),
        rewrite((m_a * m_b) * m_c, m_a * (m_b * m_c)),
        rewrite(m_a * (m_b / m_c), (m_a * m_b) / m_c),
        rewrite((m_a / m_b) * m_c, (m_a * m_c) / m_b),
        rewrite(m_a / (m_b * m_c), (m_a / m_b) / m_c),
        rewrite((m_b * m_c) / m_a, m_b / (m_a / m_c)).when(non_zero(m_c)),
        rewrite(m_a / (m_b / m_c), (m_a / m_b) * m_c).when(non_zero(m_c)),
        rewrite((m_b / m_c) / m_a, m_b / (m_a * m_c)).when(non_zero(m_a)),
        rewrite(m_x + m_x, &two * m_x),
        rewrite(m_a * (m_b + m_c), (m_a * m_b) + (m_a * m_c)),
        rewrite(m_a * (m_b + m_c), (m_b * m_a) + (m_c * m_a)),
        rewrite((m_a * m_b) + (m_a * m_c), m_a * (m_b + m_c)),
        rewrite((m_a * m_b) - (m_a * m_c), m_a * (m_b - m_c)),
        rewrite((m_b * m_a) + (m_c * m_a), m_a * (m_b + m_c)),
        rewrite((m_b * m_a) - (m_c * m_a), m_a * (m_b - m_c)),
        rewrite((m_b * m_a) + m_a, (m_b + &one) * m_a),
        rewrite(m_a + (m_c * m_a), (m_c + &one) * m_a),
        rewrite(-(m_a * m_b), (-m_a) * m_b),
        rewrite(-(m_a * m_b), m_a * (-m_b)),
        rewrite((-m_a) * m_b, -(m_a * m_b)),
        rewrite(m_a * (-m_b), -(m_a * m_b)),
        rewrite(-(m_a + m_b), (-m_a) + (-m_b)),
        rewrite((-m_a) + (-m_b), -(m_a + m_b)),
        rewrite((-m_a) / m_b, -(m_a / m_b)),
        rewrite(-(m_a / m_b), (-m_a) / m_b),
        rewrite(m_a - ((-m_b) * m_c), m_a + (m_b * m_c)),
        rewrite(m_a - (m_b * m_c), m_a + ((-m_b) * m_c)),
        rewrite((m_a * m_b) * (m_a * m_b), (m_a * m_a) * (m_b * m_b)),
        rewrite((m_a * m_a) * (m_b * m_b), (m_a * m_b) * (m_a * m_b)),
        rewrite((m_a * m_a) - (m_b * m_b), (m_a + m_b) * (m_a - m_b)),
        rewrite((m_a * m_a) - &one, (m_a + &one) * (m_a - &one)),
        rewrite((m_a * m_a) + (-&one), (m_a + &one) * (m_a - &one)),
        rewrite(
            Math::pow(m_a, m_b),
            Math::pow(m_a, m_b / &two) * Math::pow(m_a, m_b / &two),
        ),
        rewrite(
            Math::pow(m_a, m_b) * Math::pow(m_a, m_b),
            Math::pow(m_a, &two * m_b),
        ),
        // These identities also apply when x cannot be constant-folded.
        rewrite(&one / (&one / m_x), m_x).when(non_zero(m_x)),
        rewrite(m_x * (&one / m_x), &one).when(non_zero(m_x)),
        rewrite((&one / m_x) * m_x, &one).when(non_zero(m_x)),
        rewrite(m_x - m_x, &zero),
        rewrite(m_x / m_x, &one).when(non_zero(m_x)),
        rewrite(&zero / m_x, &zero).when(non_zero(m_x)),
        rewrite(&zero * m_x, &zero),
        rewrite(m_x * &zero, &zero),
        rewrite(&zero + m_x, m_x),
        rewrite(m_x + &zero, m_x),
        rewrite(&zero - m_x, -m_x),
        rewrite(m_x - &zero, m_x),
        rewrite(-(-m_x), m_x),
        rewrite(&one * m_x, m_x),
        rewrite(m_x * &one, m_x),
        rewrite(m_x / &one, m_x),
        rewrite(&neg_one * m_x, -m_x),
        rewrite(m_a - m_b, m_a + (-m_b)),
        rewrite(m_a + (-m_b), m_a - m_b),
        rewrite(-m_x, &zero - m_x),
        rewrite(-m_x, &neg_one * m_x),
        rewrite(m_x / m_y, m_x * (&one / m_y)),
        rewrite(m_x * (&one / m_y), m_x / m_y),
        rewrite(m_x / m_y, &one / (m_y / m_x)).when((non_zero(m_x), non_zero(m_y))),
        // The source restricts this generative identity to Var roots, not all Math.
        rewrite(Math::var(s_x), &one * Math::var(s_x)),
        rewrite((m_a - m_b) / m_c, (m_a / m_c) - (m_b / m_c)),
        rewrite((m_a * m_b) / (m_c * m_d), (m_a / m_c) * (m_b / m_d)),
        rewrite(Math::sqrt(m_x) * Math::sqrt(m_x), m_x),
        rewrite(Math::sqrt(m_x * m_x), Math::fabs(m_x)),
        rewrite((-m_x) * (-m_x), m_x * m_x),
        rewrite(Math::fabs(m_x) * Math::fabs(m_x), m_x * m_x),
        rewrite(Math::fabs(Math::fabs(m_x)), Math::fabs(m_x)),
        rewrite(Math::fabs(m_a - m_b), Math::fabs(m_b - m_a)),
        rewrite(Math::fabs(-m_x), Math::fabs(m_x)),
        rewrite(Math::fabs(m_x * m_x), m_x * m_x),
        rewrite(Math::fabs(m_a * m_b), Math::fabs(m_a) * Math::fabs(m_b)),
        rewrite(Math::fabs(m_a / m_b), Math::fabs(m_a) / Math::fabs(m_b)),
        rewrite(Math::pow(Math::cbrt(m_x), &three), m_x),
        rewrite(Math::cbrt(Math::pow(m_x, &three)), m_x),
        rewrite((Math::cbrt(m_x) * Math::cbrt(m_x)) * Math::cbrt(m_x), m_x),
        rewrite(Math::cbrt(m_x) * (Math::cbrt(m_x) * Math::cbrt(m_x)), m_x),
        rewrite(Math::pow(-m_x, &three), -Math::pow(m_x, &three)),
        rewrite(
            Math::pow(m_x * m_y, &three),
            Math::pow(m_x, &three) * Math::pow(m_y, &three),
        ),
        rewrite(
            Math::pow(m_x / m_y, &three),
            Math::pow(m_x, &three) / Math::pow(m_y, &three),
        ),
        rewrite(Math::pow(m_x, &three), m_x * (m_x * m_x)),
        // The source warns that this direction can cycle with difference-of-squares
        // and identity expansions, causing substantial e-graph growth.
        rewrite(m_x * (m_x * m_x), Math::pow(m_x, &three)),
        rewrite(Math::unary("exp", Math::log(m_x)), m_x),
        rewrite(Math::log(Math::unary("exp", m_x)), m_x),
        rewrite(Math::unary("exp", &zero), &one),
        rewrite(Math::unary("exp", &one), Math::constant("E")),
        rewrite(Math::constant("E"), Math::unary("exp", &one)),
        rewrite(Math::unary("exp", m_a + m_b), exp_a * exp_b),
        rewrite(Math::unary("exp", m_a - m_b), exp_a / exp_b),
        rewrite(Math::unary("exp", -m_a), &one / exp_a),
        rewrite(exp_a * exp_b, Math::unary("exp", m_a + m_b)),
        rewrite(&one / exp_a, Math::unary("exp", -m_a)),
        rewrite(exp_a / exp_b, Math::unary("exp", m_a - m_b)),
        rewrite(Math::unary("exp", m_a * m_b), Math::pow(exp_a, m_b)),
        rewrite(Math::unary("exp", m_a / &two), Math::sqrt(exp_a)),
        rewrite(Math::unary("exp", m_a / &three), Math::cbrt(exp_a)),
        rewrite(Math::unary("exp", m_a * &two), exp_a * exp_a),
        rewrite(Math::unary("exp", m_a * &three), Math::pow(exp_a, &three)),
        rewrite(Math::pow(m_a, &neg_one), &one / m_a),
        rewrite(Math::pow(m_a, &one), m_a),
        // Exclude 0^0 in both zero-exponent and zero-base identities.
        rewrite(Math::pow(m_a, &zero), &one).when(non_zero(m_a)),
        rewrite(Math::pow(&one, m_a), &one),
        rewrite(
            Math::unary("Exp", Math::log(m_a) * m_b),
            Math::pow(m_a, m_b),
        ),
        rewrite(Math::pow(m_a, m_b) * m_a, Math::pow(m_a, m_b + &one)),
        rewrite(Math::pow(m_a, egg::BigRat::new(1, 2)), Math::sqrt(m_a)),
        rewrite(Math::pow(m_a, &two), m_a * m_a),
        rewrite(Math::pow(m_a, egg::BigRat::new(1, 3)), Math::cbrt(m_a)),
        rewrite(Math::pow(m_a, &three), (m_a * m_a) * m_a),
        // Again, the nonzero guard excludes 0^0.
        rewrite(Math::pow(&zero, m_a), &zero).when(non_zero(m_a)),
        rewrite(Math::log(m_a * m_b), Math::log(m_a) + Math::log(m_b)),
        rewrite(Math::log(m_a / m_b), Math::log(m_a) - Math::log(m_b)),
        rewrite(Math::log(&one / m_a), -Math::log(m_a)),
        rewrite(Math::log(Math::pow(m_a, m_b)), m_b * Math::log(m_a)),
        rewrite(Math::log(Math::constant("E")), &one),
        rewrite(cos_a_squared + sin_a_squared, &one),
        rewrite(&one - cos_a_squared, sin_a_squared),
        rewrite(&one - sin_a_squared, cos_a_squared),
        rewrite(cos_a_squared + -1, -sin_a_squared),
        rewrite(sin_a_squared + -1, -cos_a_squared),
        rewrite(cos_a_squared - &one, -sin_a_squared),
        rewrite(sin_a_squared - &one, -cos_a_squared),
        rewrite(Math::unary("sin", pi / 6), egg::BigRat::new(1, 2)),
        rewrite(Math::unary("sin", pi / 4), Math::sqrt(&two) / &two),
        rewrite(Math::unary("sin", pi / &three), Math::sqrt(&three) / &two),
        rewrite(Math::unary("sin", pi / &two), &one),
        rewrite(Math::unary("sin", pi), &zero),
        rewrite(Math::unary("sin", m_x + pi), -sin_x),
        rewrite(Math::unary("sin", m_x + (pi / &two)), cos_x),
        rewrite(Math::unary("cos", pi / 6), Math::sqrt(&three) / &two),
        rewrite(Math::unary("cos", pi / 4), Math::sqrt(&two) / &two),
        rewrite(Math::unary("cos", pi / &three), egg::BigRat::new(1, 2)),
        rewrite(Math::unary("cos", pi / &two), &zero),
        rewrite(Math::unary("cos", pi), -1),
        rewrite(Math::unary("cos", m_x + pi), -cos_x),
        rewrite(Math::unary("cos", m_x + (pi / &two)), -sin_x),
        rewrite(Math::unary("tan", pi / 6), &one / Math::sqrt(&three)),
        rewrite(Math::unary("tan", pi / 4), &one),
        rewrite(Math::unary("tan", pi / &three), Math::sqrt(&three)),
        rewrite(Math::unary("tan", pi), &zero),
        rewrite(Math::unary("tan", m_x + pi), tan_x),
        rewrite(Math::unary("tan", m_x + (pi / &two)), &neg_one / tan_x),
        rewrite(sin_a / (&one + cos_a), Math::unary("tan", m_a / &two)),
        rewrite((-sin_a) / (&one + cos_a), Math::unary("tan", (-m_a) / &two)),
        rewrite((&one - cos_a) / sin_a, Math::unary("tan", m_a / &two)),
        rewrite((&one - cos_a) / (-sin_a), Math::unary("tan", (-m_a) / &two)),
        rewrite(
            (sin_a + sin_b) / (cos_a + cos_b),
            Math::unary("tan", (m_a + m_b) / &two),
        ),
        rewrite(
            (sin_a - sin_b) / (cos_a + cos_b),
            Math::unary("tan", (m_a - m_b) / &two),
        ),
        rewrite(Math::unary("sin", &zero), &zero),
        rewrite(Math::unary("cos", &zero), &one),
        rewrite(Math::unary("tan", &zero), &zero),
        rewrite(Math::unary("sin", -m_x), -sin_x),
        rewrite(Math::unary("cos", -m_x), cos_x),
        rewrite(Math::unary("tan", -m_x), -cos_x),
        rewrite(sinh_x, (exp_x - exp_neg_x) / &two),
        rewrite(cosh_x, (exp_x + exp_neg_x) / &two),
        rewrite(
            Math::unary("tanh", m_x),
            (exp_x - exp_neg_x) / (exp_x + exp_neg_x),
        ),
        rewrite(
            Math::unary("tanh", m_x),
            (Math::unary("exp", &two * m_x) - &one) / (Math::unary("exp", &two * m_x) + &one),
        ),
        rewrite(
            Math::unary("tanh", m_x),
            (&one - Math::unary("exp", Math::num(-2) * m_x))
                / (&one + Math::unary("exp", Math::num(-2) * m_x)),
        ),
        rewrite((cosh_x * cosh_x) - (sinh_x * sinh_x), &one),
        rewrite(cosh_x + sinh_x, exp_x),
        rewrite(cosh_x - sinh_x, exp_neg_x),
    ]
}

pub fn main() -> Result<(), TypedError> {
    let mut egraph = EGraph::default();
    let r_zero = egg::BigRat::new(0, 1);
    egraph.register(&r_zero)?;
    let r_one = egg::BigRat::new(1, 1);
    egraph.register(&r_one)?;
    let r_two = egg::BigRat::new(2, 1);
    egraph.register(&r_two)?;
    let zero = Math::num(&r_zero);
    egraph.register(&zero)?;
    let one = Math::num(&r_one);
    egraph.register(&one)?;
    let two = Math::num(&r_two);
    egraph.register(&two)?;
    let three = Math::num(3);
    egraph.register(&three)?;
    let neg_one = -&one;
    egraph.register(&neg_one)?;
    {
        egraph.push()?;
        let e = let_("e", &one + &zero);
        egraph.register(&e)?;
        egraph.run(theory.repeat(1))?;
        assert!(egraph.check(eq(&e, &one))?);
        egraph.pop()?;
    }
    {
        egraph.push()?;
        let five = Math::num(5);
        egraph.register(&five)?;
        let six = Math::num(6);
        egraph.register(&six)?;
        let e2 = let_("e2", &one + &five);
        egraph.register(&e2)?;
        egraph.run(theory.repeat(1))?;
        assert!(egraph.check(eq(&e2, &six))?);
        egraph.pop()?;
    }
    let x = Math::var("x");
    egraph.register(&x)?;
    {
        egraph.push()?;
        let e3 = let_("e3", &x + &zero);
        egraph.register(&e3)?;
        egraph.run(theory.repeat(1))?;
        assert!(egraph.check(eq(&e3, &x))?);
        egraph.pop()?;
    }
    {
        egraph.push()?;
        let e4 = let_("e4", &x - &zero);
        egraph.register(&e4)?;
        egraph.run(theory.repeat(1))?;
        assert!(egraph.check(eq(&e4, &x))?);
        egraph.pop()?;
    }
    {
        egraph.push()?;
        let e5 = let_("e5", &x * &one);
        egraph.register(&e5)?;
        egraph.run(theory.repeat(1))?;
        assert!(egraph.check(eq(&e5, &x))?);
        egraph.pop()?;
    }
    {
        egraph.push()?;
        let e6 = let_("e6", &x / &one);
        egraph.register(&e6)?;
        egraph.run(theory.repeat(1))?;
        assert!(egraph.check(eq(&e6, &x))?);
        egraph.pop()?;
    }
    {
        egraph.push()?;
        let e7 = let_("e7", (&one * &x) - ((&x + &one) * &one));
        egraph.register(&e7)?;
        egraph.run(theory.repeat(3))?;
        assert!(egraph.check(eq(&e7, -1))?);
        egraph.pop()?;
    }
    {
        egraph.push()?;
        let e8 = let_("e8", (&x + &one) - &x);
        egraph.register(&e8)?;
        egraph.run(theory.repeat(4))?;
        assert!(egraph.check(eq(&e8, &one))?);
        egraph.pop()?;
    }
    {
        egraph.push()?;
        let e9 = let_("e9", (&x + &one) - &one);
        egraph.register(&e9)?;
        egraph.run(theory.repeat(4))?;
        assert!(egraph.check(eq(&e9, &x))?);
        egraph.pop()?;
    }
    {
        egraph.push()?;
        egraph.register(set(lower(&x), &r_one))?;
        let e10 = let_("e10", (&x * &three) / &x);
        egraph.register(&e10)?;
        egraph.run(theory.repeat(3))?;
        assert!(egraph.check(eq(&e10, &three))?);
        egraph.pop()?;
    }
    {
        egraph.push()?;
        let e11 = let_(
            "e11",
            (Math::sqrt(&x + &one) * Math::sqrt(&x + &one)) - (Math::sqrt(&x) * Math::sqrt(&x)),
        );
        egraph.register(&e11)?;
        egraph.run(theory.repeat(5))?;
        assert!(egraph.check(eq(&one, &e11))?);
        egraph.pop()?;
    }
    {
        egraph.push()?;
        let e12: Math = let_(
            "e12",
            Math::num(egg::BigRat::new(1, 5)) + egg::BigRat::new(3, 10),
        );
        egraph.register(&e12)?;
        egraph.run(theory.repeat(1))?;
        assert!(egraph.check(eq(&e12, egg::BigRat::new(1, 2)))?);
        egraph.pop()?;
    }
    {
        egraph.push()?;
        let e13 = let_("e13", Math::unary("cos", Math::constant("PI")));
        egraph.register(&e13)?;
        egraph.run(theory.repeat(1))?;
        assert!(egraph.check(eq(&e13, -1))?);
        egraph.pop()?;
    }
    {
        egraph.push()?;
        let sqrt5 = Math::sqrt(5);
        egraph.register(&sqrt5)?;
        let e14 = let_(
            "e14",
            &one / (((&one + &sqrt5) / &two) - ((&one - &sqrt5) / &two)),
        );
        egraph.register(&e14)?;
        let tgt = let_("tgt", &one / &sqrt5);
        egraph.register(&tgt)?;
        egraph.run(theory.repeat(6))?;
        assert!(egraph.check(eq(&e14, &tgt))?);
        egraph.pop()?;
    }
    Ok(())
}
