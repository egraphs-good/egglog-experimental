// Core web-demo/typecheck.egg: demand-driven simply typed lambda calculus.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;
#[sort]
pub struct Type;

#[declarations]
impl Type {
    pub fn arrow(input: Type, output: Type) -> Type;
    pub fn unit() -> Type;
}
#[sort]
pub struct Expr;

#[declarations]
impl Expr {
    pub fn lam(name: egg::String, ty: Type, body: Expr) -> Expr;
    pub fn app(function: Expr, argument: Expr) -> Expr;
    #[constructor(from(&str, std::string::String))]
    pub fn var(name: egg::String) -> Expr;
    pub fn unit() -> Expr;
}
#[sort]
pub struct Context;

#[declarations]
impl Context {
    pub fn cons(name: egg::String, ty: Type, rest: Context) -> Context;
    pub fn nil() -> Context;
}
#[constructor]
pub fn type_of(context: Context, expr: Expr) -> Type;

impl From<()> for Expr {
    fn from(_: ()) -> Self {
        Self::unit()
    }
}

#[ruleset]
fn theory(
    ctx: &Context,
    f: &Expr,
    e: &Expr,
    t1: &Type,
    t2: &Type,
    x: &egg::String,
    y: &egg::String,
    t: &Type,
    ty: &Type,
) -> Vec<Rule> {
    vec![
        rewrite(type_of(ctx, ()), Type::unit()),
        rewrite(type_of(Context::cons(x, t, ctx), Expr::var(x)), t),
        // Skip a context entry only when it binds a different variable.
        rewrite(
            type_of(Context::cons(y, ty, ctx), Expr::var(x)),
            type_of(ctx, Expr::var(x)),
        )
        .when(ne(x, y)),
        rewrite(
            type_of(ctx, Expr::lam(x, t, e)),
            Type::arrow(t, type_of(Context::cons(x, t, ctx), e)),
        ),
        // Typing an application creates demand for its function and argument.
        rule(
            type_of(ctx, Expr::app(f, e)),
            (type_of(ctx, f), type_of(ctx, e)),
        ),
        rule(
            (
                eq(type_of(ctx, Expr::app(f, e)), t1),
                eq(type_of(ctx, f), Type::arrow(type_of(ctx, e), t2)),
            ),
            union(t1, t2),
        ),
    ]
}

pub fn main() -> Result<(), TypedError> {
    let unit = Type::unit();
    let nil = Context::nil();
    let id = Expr::lam("x", &unit, "x");
    let free = Expr::lam("x", &unit, "y");
    let arrow = Type::arrow(&unit, &unit);
    let complex = Type::arrow(&arrow, &unit);
    let t_id = let_("id", type_of(&nil, &id));
    let t_app = let_(
        "app",
        type_of(
            &nil,
            Expr::app(
                Expr::app(
                    Expr::lam(
                        "x",
                        &unit,
                        Expr::lam("f", Type::arrow(&unit, &unit), Expr::app("f", "x")),
                    ),
                    (),
                ),
                id,
            ),
        ),
    );
    let ill = let_("free_ill", type_of(&nil, &free));
    let t_free1 = let_("free1", type_of(Context::cons("y", &unit, &nil), &free));
    let t_free2 = let_("free2", type_of(Context::cons("y", &complex, nil), free));
    let mut egraph = EGraph::default();
    egraph.register((&t_id, &t_app, &ill, &t_free1, &t_free2))?;
    egraph.run(theory.repeat(15))?;
    for (actual, expected) in [
        (t_id, arrow.clone()),
        (t_app, unit.clone()),
        (t_free1, arrow),
        (t_free2, Type::arrow(unit, complex)),
    ] {
        egraph.extract(&actual)?;
        assert!(egraph.check(eq(actual, expected))?);
    }
    // The source intentionally leaves the free variable without a typing rule.
    assert!(!egraph.check(eq(ill, Type::arrow(Type::unit(), Type::unit())))?);
    Ok(())
}
