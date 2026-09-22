// Core web-demo/math.egg: the full differentiation/integration theory and
// all 21 scoped cases, including pruning, a negative check and a seeded goal.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Math;

#[declarations]
impl Math {
    #[constructor(cost = 100)]
    pub fn diff(&self, variable: Math) -> Math;
    #[constructor(cost = 100)]
    pub fn integral(&self, variable: Math) -> Math;
    pub fn pow(&self, exponent: Math) -> Math;
    pub fn ln(&self) -> Math;
    pub fn sqrt(&self) -> Math;
    pub fn sin(&self) -> Math;
    pub fn cos(&self) -> Math;
    #[constructor(from(f64))]
    pub fn constant(value: egg::F64) -> Math;
    #[constructor(from(&str, std::string::String))]
    pub fn var(name: egg::String) -> Math;
    // Table all math expressions so rules can bind their variables.
    pub fn universe(&self);
    pub fn is_not_zero(&self);
    pub fn is_const_or_distinct_var_demand(&self, variable: egg::String);
    pub fn is_const_or_distinct_var(&self, variable: egg::String);
}

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

// Pruning remains a separate run; this group follows the source rule order.
#[expect(
    clippy::eq_op,
    reason = "the source theory deliberately rewrites a-a and nonzero a/a"
)]
#[ruleset]
pub(crate) fn math(
    e: &Math,
    x: &Math,
    y: &Math,
    a: &Math,
    b: &Math,
    c: &Math,
    f: &Math,
    g: &Math,
    n: &egg::F64,
    m: &egg::F64,
    name: &egg::String,
    v: &egg::String,
    w: &egg::String,
) -> Vec<Rule> {
    let zero = &Math::constant(0.0);
    let one = &Math::constant(1.0);
    let minus_one = &Math::constant(-1.0);
    let constant_n = &Math::constant(n);
    let constant_m = &Math::constant(m);
    let variable_v = &Math::var(v);
    let variable_w = &Math::var(w);
    let variable_derivative = &c.diff(variable_v);
    let next_exponent = &(constant_n + one);
    let integral_b = &b.integral(x);
    vec![
        // Table all math expressions so rules can bind their variables.
        rule(eq(e, y.diff(x)), e.universe()),
        rule(eq(e, x.integral(y)), e.universe()),
        rule(eq(e, x + y), e.universe()),
        rule(eq(e, x - y), e.universe()),
        rule(eq(e, x * y), e.universe()),
        rule(eq(e, x / y), e.universe()),
        rule(eq(e, x.pow(y)), e.universe()),
        rule(eq(e, x.ln()), e.universe()),
        rule(eq(e, x.sqrt()), e.universe()),
        rule(eq(e, x.sin()), e.universe()),
        rule(eq(e, x.cos()), e.universe()),
        rule(eq(e, constant_n), e.universe()),
        rule(eq(e, Math::var(name)), e.universe()),
        // Constant folding unions with constant nodes, like the source egg analysis.
        rewrite(constant_n + constant_m, n + m),
        rewrite(constant_n - constant_m, n - m),
        rewrite(constant_n * constant_m, n * m),
        rewrite(constant_n / constant_m, n / m).when(ne(m, 0.0)),
        // Mark every expression except zero; remove the fact if it later becomes zero.
        rule((x.universe(), ne(x, zero)), x.is_not_zero()),
        rule((x.is_not_zero(), eq(x, zero)), delete(x.is_not_zero())),
        // Constants and distinct variables are independent of the differentiation variable.
        rule(
            (variable_w.is_const_or_distinct_var_demand(v), ne(v, w)),
            variable_w.is_const_or_distinct_var(v),
        ),
        rule(
            constant_n.is_const_or_distinct_var_demand(v),
            constant_n.is_const_or_distinct_var(v),
        ),
        // Commutativity, associativity, identities, and distribution.
        rewrite(a + b, b + a),
        rewrite(a * b, b * a),
        rewrite(a + (b + c), a + b + c),
        rewrite(a * (b * c), a * b * c),
        rewrite(a - b, a + minus_one * b),
        rewrite(a / b, a * b.pow(minus_one)).when(b.is_not_zero()),
        rewrite(a + zero, a),
        rewrite(a * zero, zero),
        rewrite(a * one, a),
        rule(a.universe(), union(a, a + zero)),
        rule(a.universe(), union(a, a * one)),
        rewrite(a - a, zero),
        rewrite(a / a, one).when(a.is_not_zero()),
        rewrite(a * (b + c), a * b + a * c),
        rewrite(a * b + a * c, a * (b + c)),
        // Powers and reciprocals.
        rewrite(a.pow(b) * a.pow(c), a.pow(b + c)),
        rewrite(x.pow(zero), one).when(x.is_not_zero()),
        rewrite(x.pow(one), x),
        rewrite(x.pow(2.0), x * x),
        rewrite(x.pow(minus_one), one / x).when(x.is_not_zero()),
        rewrite(x * (one / x), one).when(x.is_not_zero()),
        // Differentiate variables, sums, products, and elementary functions.
        rewrite(variable_v.diff(variable_v), one),
        rule(variable_derivative, c.is_const_or_distinct_var_demand(v)),
        rewrite(variable_derivative, zero).when(c.is_const_or_distinct_var(v)),
        rewrite((a + b).diff(x), a.diff(x) + b.diff(x)),
        rewrite((a * b).diff(x), a * b.diff(x) + b * a.diff(x)),
        rewrite(x.sin().diff(x), x.cos()),
        rewrite(x.cos().diff(x), minus_one * x.sin()),
        rewrite(x.ln().diff(x), one / x).when(x.is_not_zero()),
        rewrite(
            f.pow(g).diff(x),
            f.pow(g) * (f.diff(x) * (g / f) + g.diff(x) * f.ln()),
        )
        .when((f.is_not_zero(), g.is_not_zero())),
        // Integrate constants, powers, sums, and products by parts.
        rewrite(one.integral(x), x),
        rewrite(
            x.pow(constant_n).integral(x),
            x.pow(next_exponent) / next_exponent,
        ),
        rewrite(x.cos().integral(x), x.sin()),
        rewrite(x.sin().integral(x), minus_one * x.cos()),
        rewrite((f + g).integral(x), f.integral(x) + g.integral(x)),
        rewrite((f - g).integral(x), f.integral(x) - g.integral(x)),
        rewrite(
            (a * b).integral(x),
            a * integral_b - (a.diff(x) * integral_b).integral(x),
        ),
    ]
}

// Prune with subsumption, allowing saturation instead of repeatedly recreating nodes.
#[ruleset]
pub(crate) fn prune(x: &Math, y: &Math, constant: &egg::F64) -> Vec<Rule> {
    vec![
        rule(eq(Math::constant(constant), y.diff(x)), subsume(y.diff(x))),
        rule(
            eq(Math::constant(constant), x.integral(y)),
            subsume(x.integral(y)),
        ),
        rule(eq(Math::constant(constant), x + y), subsume(x + y)),
        rule(eq(Math::constant(constant), x - y), subsume(x - y)),
        rule(eq(Math::constant(constant), x * y), subsume(x * y)),
        rule(eq(Math::constant(constant), x / y), subsume(x / y)),
        rule(eq(Math::constant(constant), x.pow(y)), subsume(x.pow(y))),
        rule(eq(Math::constant(constant), x.ln()), subsume(x.ln())),
        rule(eq(Math::constant(constant), x.sqrt()), subsume(x.sqrt())),
        rule(eq(Math::constant(constant), x.sin()), subsume(x.sin())),
        rule(eq(Math::constant(constant), x.cos()), subsume(x.cos())),
    ]
}

// Only these two rules run in the first, scoped source case.
#[ruleset]
fn add_ac(a: &Math, b: &Math, c: &Math) -> Vec<Rule> {
    vec![rewrite(a + b, b + a), rewrite(a + (b + c), a + b + c)]
}

// The common source schedule: capture in a fresh scope, search until the
// equality holds while pruning constants, then check and restore the scope.
fn prove_case(
    egraph: &mut EGraph,
    name: &str,
    expression: Math,
    expected: &Math,
) -> Result<(), TypedError> {
    egraph.push()?;
    let root = let_(name, expression);
    egraph.register(&root)?;
    let goal = eq(root, expected);
    egraph.run(sequence((math.until(goal.clone()), &prune)).saturate())?;
    assert!(egraph.check(goal)?, "{name}");
    egraph.pop()
}

pub fn main() -> Result<(), TypedError> {
    let one = &Math::constant(1.0);
    let two = &Math::constant(2.0);
    let mut egraph = EGraph::default();
    let x = &Math::var("x");
    let y = &Math::var("y");
    let a = &Math::var("a");
    let three = &Math::constant(3.0);
    let four = &Math::constant(4.0);

    egraph.push()?;
    let ascending = (1..=7)
        .rev()
        .map(|n| Math::from(f64::from(n)))
        .reduce(|rest, next| next + rest)
        .unwrap();
    let descending = (1..=7)
        .map(|n| Math::from(f64::from(n)))
        .reduce(|rest, next| next + rest)
        .unwrap();
    let root = let_("math_associate_adds", ascending);
    egraph.register(&root)?;
    egraph.run(add_ac.repeat(7))?;
    assert!(egraph.check(eq(root, descending))?);
    egraph.pop()?;

    egraph.push()?;
    let root = let_("math_fail", x + y);
    egraph.register(&root)?;
    egraph.run(sequence((&math, &prune)).saturate())?;
    assert!(!egraph.check(eq(root, x / y))?);
    egraph.pop()?;

    let five_root = &Math::var("five").sqrt();
    prove_case(&mut egraph, "math_simplify_add", x + x + x + x, &(four * x))?;
    prove_case(
        &mut egraph,
        "math_powers",
        two.pow(x) * two.pow(y),
        &two.pow(x + y),
    )?;
    prove_case(
        &mut egraph,
        "math_simplify_const",
        one + (a - (two - one) * a),
        one,
    )?;
    prove_case(
        &mut egraph,
        "math_simplify_root",
        one / ((one + five_root) / two - (one - five_root) / two),
        &(one / five_root),
    )?;
    prove_case(
        &mut egraph,
        "math_simplify_factor",
        (x + three) * (x + one),
        &(x * x + four * x + three),
    )?;
    prove_case(&mut egraph, "math_diff_same", x.diff(x), one)?;
    prove_case(
        &mut egraph,
        "math_diff_different",
        y.diff(x),
        &Math::constant(0.0),
    )?;
    prove_case(
        &mut egraph,
        "math_diff_simple1",
        (one + two * x).diff(x),
        two,
    )?;
    prove_case(&mut egraph, "math_diff_simple2", (one + y * x).diff(x), y)?;
    prove_case(&mut egraph, "math_diff_ln", x.ln().diff(x), &(one / x))?;
    prove_case(
        &mut egraph,
        "diff_power_simple",
        x.pow(three).diff(x),
        &(three * x.pow(two)),
    )?;

    // The source deliberately seeds the harder target and repeats 60 times.
    egraph.push()?;
    let root = let_(
        "diff_power_harder",
        (x.pow(three) - Math::constant(7.0) * x.pow(two)).diff(x),
    );
    let expected = x * (three * x - 14.0);
    egraph.register((&root, &expected))?;
    let goal = eq(root, expected);
    egraph.run(sequence((math.until(goal.clone()), &prune)).repeat(60))?;
    assert!(egraph.check(goal)?);
    egraph.pop()?;

    let by_parts = &(x * x.sin() + x.cos());
    prove_case(&mut egraph, "integ_one", one.integral(x), x)?;
    prove_case(&mut egraph, "integ_sin", x.cos().integral(x), &x.sin())?;
    prove_case(
        &mut egraph,
        "integ_x",
        x.pow(one).integral(x),
        &(x.pow(two) / two),
    )?;
    prove_case(
        &mut egraph,
        "integ_part1",
        (x * x.cos()).integral(x),
        by_parts,
    )?;
    prove_case(
        &mut egraph,
        "integ_part2",
        (x.cos() * x).integral(x),
        by_parts,
    )?;
    prove_case(
        &mut egraph,
        "integ_part3",
        x.ln().integral(x),
        &(x * x.ln() - x),
    )?;
    egraph.push()?;
    egraph.register(x * one)?;
    egraph.run(sequence((&math, &prune)).saturate())?;
    egraph.pop()?;
    Ok(())
}
