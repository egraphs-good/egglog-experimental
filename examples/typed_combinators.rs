// Core web-demo/combinators.egg: substitution through S/K/I combinators.
// This retains the full conversion and abstraction-elimination theory, not
// just the final beta-reduction case. The source's nullary constant aliases
// become ordinary Rust DAG bindings; only the result needs a captured value.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Expr;

#[declarations]
impl Expr {
    #[constructor(cost = 100, from(&str, std::string::String))]
    pub fn var(name: egg::String) -> Expr;
    pub fn abs(name: egg::String, body: Expr) -> Expr;
    pub fn if_(condition: Expr, then_: Expr, else_: Expr) -> Expr;
    #[constructor(from(i64, i32))]
    pub fn n(value: egg::I64) -> Expr;
    pub fn app(function: Expr, argument: Expr) -> Expr;
    pub fn t_const() -> Expr;
    pub fn f_const() -> Expr;
    pub fn uncomb(combinator: CExpr) -> Expr;
}

#[sort]
pub struct CExpr;

#[declarations]
impl CExpr {
    #[constructor(cost = 10_000)]
    pub fn c_var(name: egg::String) -> CExpr;
    #[constructor(cost = 10_000)]
    pub fn c_abs(name: egg::String, body: CExpr) -> CExpr;
    pub fn cn(value: egg::I64) -> CExpr;
    pub fn c_app(function: CExpr, argument: CExpr) -> CExpr;
    pub fn ct_const() -> CExpr;
    pub fn cf_const() -> CExpr;
    pub fn c_if_const() -> CExpr;
    pub fn c_add_const() -> CExpr;
    pub fn s_const() -> CExpr;
    pub fn k_const() -> CExpr;
    pub fn i_const() -> CExpr;
    #[constructor(cost = 1_000_000)]
    pub fn comb(expression: Expr) -> CExpr;
}

impl From<bool> for Expr {
    fn from(value: bool) -> Self {
        if value {
            Self::t_const()
        } else {
            Self::f_const()
        }
    }
}

#[declarations]
impl std::ops::Add<&Expr> for &Expr {
    type Output = Expr;
    fn add(self, rhs: &Expr) -> Expr;
}

#[ruleset]
fn theory(
    x: &Expr,
    cx: &CExpr,
    n: &egg::I64,
    m: &egg::I64,
    condition: &Expr,
    then_: &Expr,
    else_: &Expr,
    left: &Expr,
    right: &Expr,
    fun: &Expr,
    arg: &Expr,
    cc: &CExpr,
    cthen: &CExpr,
    celse: &CExpr,
    cleft: &CExpr,
    cright: &CExpr,
    body: &Expr,
    v: &egg::String,
    v2: &egg::String,
    cy: &CExpr,
    cz: &CExpr,
) -> Vec<Rule> {
    let truth = Expr::t_const();
    let falsehood = Expr::f_const();
    let ct = CExpr::ct_const();
    let cf = CExpr::cf_const();
    let cif = CExpr::c_if_const();
    let cadd = CExpr::c_add_const();
    let s = CExpr::s_const();
    let k = CExpr::k_const();
    let i = CExpr::i_const();
    let if_condition = CExpr::c_app(&cif, CExpr::comb(condition));
    let if_then = CExpr::c_app(if_condition, CExpr::comb(then_));

    vec![
        // Round trips, without inventing surface syntax for S/K/I.
        rewrite(CExpr::comb(Expr::uncomb(cx)), cx),
        rewrite(Expr::uncomb(CExpr::comb(x)), x),
        // These are generative rules: a conversion row need not exist yet.
        rule(eq(x, Expr::n(n)), union(CExpr::comb(x), CExpr::cn(n))),
        rule(eq(cx, CExpr::cn(n)), union(Expr::uncomb(cx), Expr::n(n))),
        rule(eq(x, &truth), union(CExpr::comb(x), &ct)),
        rule(eq(cx, &ct), union(Expr::uncomb(cx), &truth)),
        rule(eq(x, &falsehood), union(CExpr::comb(x), &cf)),
        rule(eq(cx, &cf), union(Expr::uncomb(cx), &falsehood)),
        rule(
            eq(x, Expr::if_(condition, then_, else_)),
            union(CExpr::comb(x), CExpr::c_app(if_then, CExpr::comb(else_))),
        ),
        rule(
            eq(
                cx,
                CExpr::c_app(CExpr::c_app(CExpr::c_app(&cif, cc), cthen), celse),
            ),
            union(
                Expr::uncomb(cx),
                Expr::if_(Expr::uncomb(cc), Expr::uncomb(cthen), Expr::uncomb(celse)),
            ),
        ),
        rule(
            eq(x, left + right),
            union(
                CExpr::comb(x),
                CExpr::c_app(CExpr::c_app(&cadd, CExpr::comb(left)), CExpr::comb(right)),
            ),
        ),
        rule(
            eq(cx, CExpr::c_app(CExpr::c_app(&cadd, cleft), cright)),
            union(Expr::uncomb(cx), Expr::uncomb(cleft) + Expr::uncomb(cright)),
        ),
        rule(
            eq(x, Expr::app(fun, arg)),
            union(
                CExpr::comb(x),
                CExpr::c_app(CExpr::comb(fun), CExpr::comb(arg)),
            ),
        ),
        rule(eq(x, Expr::var(v)), union(CExpr::comb(x), CExpr::c_var(v))),
        rule(
            eq(x, Expr::abs(v, body)),
            union(CExpr::comb(x), CExpr::c_abs(v, CExpr::comb(body))),
        ),
        // Abstraction elimination. The deliberately simple source theory
        // introduces S without computing free-variable sets first.
        rewrite(CExpr::c_abs(v, CExpr::c_var(v)), &i),
        rewrite(
            CExpr::c_abs(v, CExpr::c_var(v2)),
            CExpr::c_app(&k, CExpr::c_var(v2)),
        )
        .when(ne(v, v2)),
        rewrite(
            CExpr::c_abs(v, CExpr::cn(n)),
            CExpr::c_app(&k, CExpr::cn(n)),
        ),
        rewrite(CExpr::c_abs(v, &ct), CExpr::c_app(&k, &ct)),
        rewrite(CExpr::c_abs(v, &cf), CExpr::c_app(&k, &cf)),
        rewrite(CExpr::c_abs(v, &cif), CExpr::c_app(&k, &cif)),
        rewrite(CExpr::c_abs(v, &cadd), CExpr::c_app(&k, &cadd)),
        rewrite(
            CExpr::c_abs(v, CExpr::c_app(cx, cy)),
            CExpr::c_app(CExpr::c_app(&s, CExpr::c_abs(v, cx)), CExpr::c_abs(v, cy)),
        ),
        rewrite(CExpr::c_abs(v, CExpr::c_app(&k, CExpr::c_var(v))), &k),
        // Evaluation stays on the surface representation.
        rewrite(Expr::if_(true, then_, else_), then_),
        rewrite(Expr::if_(false, then_, else_), else_),
        rewrite(Expr::n(n) + Expr::n(m), Expr::n(n + m)),
        // Substitution stays on the combinator representation.
        rewrite(CExpr::c_app(&i, cx), cx),
        rewrite(CExpr::c_app(CExpr::c_app(&k, cx), cy), cx),
        // Without demand control, S expansion can cause the database to grow rapidly.
        rewrite(
            CExpr::c_app(CExpr::c_app(CExpr::c_app(&s, cx), cy), cz),
            CExpr::c_app(CExpr::c_app(cx, cz), CExpr::c_app(cy, cz)),
        ),
    ]
}

pub fn main() -> Result<(), TypedError> {
    let truth = Expr::t_const();
    let falsehood = Expr::f_const();
    let ct = CExpr::ct_const();
    let cf = CExpr::cf_const();
    let cif = CExpr::c_if_const();
    let cadd = CExpr::c_add_const();
    let s = CExpr::s_const();
    let k = CExpr::k_const();
    let i = CExpr::i_const();

    // (\x. (if x then 0 else 1) + 2) false
    let test = let_(
        "test",
        Expr::app(Expr::abs("x", Expr::if_("x", 0, 1) + 2), &falsehood),
    );

    let mut graph = EGraph::default();
    graph.register((&truth, &falsehood, &test, &ct, &cf, &cif, &cadd, &s, &k, &i))?;
    graph.run(theory.repeat(11))?;
    let converted = CExpr::comb(&test);
    let best: CExpr = graph.extract(&converted)?;
    assert!(graph.check(eq(converted, best))?);
    assert!(graph.check(eq(test, 3))?);
    Ok(())
}
