// Core web-demo/typeinfer.egg: polymorphic inference, all eleven test programs,
// fresh-variable numbering, generalization, injectivity and occurs checks.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;
#[sort]
pub struct Ident;

#[declarations]
impl Ident {
    #[constructor(from(&str, std::string::String))]
    pub fn named(name: egg::String) -> Ident;
    pub fn fresh(base: Ident, index: egg::I64) -> Ident;
}
#[sort]
pub struct Expr;

#[declarations]
impl Expr {
    #[constructor(from)]
    pub fn var(name: Ident) -> Expr;
    pub fn app(function: Expr, argument: Expr) -> Expr;
    pub fn abs(name: Ident, body: Expr) -> Expr;
    pub fn let_(name: Ident, value: Expr, body: Expr) -> Expr;
    pub fn num(value: egg::I64) -> Expr;
    pub fn truth() -> Expr;
    pub fn falsity() -> Expr;
    pub fn unit() -> Expr;
}
#[sort]
pub struct Type;

#[declarations]
impl Type {
    #[constructor(cost = 3)]
    pub fn var(name: Ident) -> Type;
    pub fn arrow(input: Type, output: Type) -> Type;
    pub fn int() -> Type;
    pub fn bool() -> Type;
    pub fn unit() -> Type;
}
#[sort]
pub struct Scheme;

#[declarations]
impl Scheme {
    pub fn forall(variables: egg::Set<Ident>, ty: Type) -> Scheme;
}
#[sort]
pub struct Context;

#[declarations]
impl Context {
    pub fn nil() -> Context;
    pub fn cons(name: Ident, scheme: Scheme, rest: Context) -> Context;
}
#[relation]
pub fn ftv_context(context: Context, variables: egg::Set<Ident>);
#[relation]
pub fn ftv(ty: Type, variables: egg::Set<Ident>);
#[relation]
pub fn ftv_scheme(scheme: Scheme, variables: egg::Set<Ident>);
#[relation]
pub fn has_qs(context: Context, ty: Type, variables: egg::Set<Ident>);
#[relation]
pub fn qs_demand(context: Context, ty: Type);
#[relation]
pub fn expr_size(expr: Expr, size: egg::I64);
#[relation]
pub fn occurs(name: Ident, ty: Type);
#[relation]
pub fn base_type(ty: Type);
#[constructor(cost = 1000)]
pub fn lookup(context: Context, name: Ident) -> Scheme;
#[constructor(cost = 1000)]
pub fn generalize(context: Context, ty: Type) -> Scheme;
#[constructor(cost = 1000)]
pub fn instantiate(scheme: Scheme, index: egg::I64) -> Type;
#[constructor(cost = 1000)]
pub fn subst_fresh(variables: egg::Set<Ident>, ty: Type, index: egg::I64) -> Type;
#[constructor(cost = 1000)]
pub fn type_of(context: Context, expr: Expr, index: egg::I64) -> Type;
#[constructor]
pub fn errors() -> Ident;

impl From<bool> for Expr {
    fn from(value: bool) -> Self {
        if value {
            Self::truth()
        } else {
            Self::falsity()
        }
    }
}

impl From<()> for Expr {
    fn from(_: ()) -> Self {
        Self::unit()
    }
}

#[ruleset]
fn theory(
    e: &Expr,
    n: &egg::I64,
    x: &Ident,
    a: &Expr,
    b: &Expr,
    sa: &egg::I64,
    sb: &egg::I64,
    ty: &Type,
    fr: &Type,
    to: &Type,
    s1: &egg::Set<Ident>,
    s2: &egg::Set<Ident>,
    ctx: &Context,
    scheme: &Scheme,
    qs: &egg::Set<Ident>,
    fv: &egg::Set<Ident>,
    rest: &Context,
    y: &Ident,
    q1: &egg::Set<Ident>,
    q2: &egg::Set<Ident>,
    keys: &egg::Set<Ident>,
    t: &Type,
    vs: &egg::Set<Ident>,
    c: &egg::I64,
    f1: &Type,
    t1: &Type,
    f2: &Type,
    t2: &Type,
    e1: &Expr,
    e2: &Expr,
    c1: &egg::I64,
    c2: &egg::I64,
    sz: &egg::I64,
    cc: &egg::I64,
) -> Vec<Rule> {
    let fresh = Type::var(Ident::fresh(x, c));
    let monomorphic = Scheme::forall(egg::Set::<Ident>::empty(), &fresh);
    let abstraction_context = Context::cons(x, monomorphic, ctx);
    let let_context = Context::cons(x, generalize(ctx, type_of(ctx, e1, c1)), ctx);
    vec![
        // Expression sizes.
        rule(eq(e, Expr::num(n)), expr_size(e, 1)),
        rule(eq(e, Expr::var(x)), expr_size(e, 1)),
        // Asserted facts are cleared between test scopes, so define these as rules.
        rule(eq(e, Expr::truth()), expr_size(e, 1)),
        rule(eq(e, Expr::falsity()), expr_size(e, 1)),
        rule(eq(e, Expr::unit()), expr_size(e, 1)),
        rule(
            (eq(e, Expr::app(a, b)), expr_size(a, sa), expr_size(b, sb)),
            expr_size(e, sa + sb + 1),
        ),
        rule(
            (
                eq(e, Expr::let_(x, a, b)),
                expr_size(a, sa),
                expr_size(b, sb),
            ),
            expr_size(e, sa + sb + 1),
        ),
        rule(
            (eq(e, Expr::abs(x, a)), expr_size(a, sa)),
            expr_size(e, sa + 1),
        ),
        // Scheme and context free variables.
        rule(eq(ty, Type::bool()), ftv(ty, egg::Set::<Ident>::empty())),
        rule(eq(ty, Type::unit()), ftv(ty, egg::Set::<Ident>::empty())),
        rule(eq(ty, Type::int()), ftv(ty, egg::Set::<Ident>::empty())),
        rule(
            eq(ty, Type::var(x)),
            ftv(ty, egg::Set::<Ident>::empty().insert(x)),
        ),
        rule(
            (eq(ty, Type::arrow(fr, to)), ftv(fr, s1), ftv(to, s2)),
            ftv(ty, s1.union(s2)),
        ),
        rule(
            eq(ctx, Context::nil()),
            ftv_context(ctx, egg::Set::<Ident>::empty()),
        ),
        rule(
            (eq(scheme, Scheme::forall(qs, ty)), ftv(ty, fv)),
            ftv_scheme(scheme, fv.difference(qs)),
        ),
        rule(
            (
                eq(ctx, Context::cons(x, scheme, rest)),
                ftv_context(rest, s1),
                ftv_scheme(scheme, s2),
            ),
            ftv_context(ctx, s1.union(s2)),
        ),
        // Lookup.
        rewrite(lookup(Context::cons(x, scheme, ctx), x), scheme),
        rewrite(lookup(Context::cons(y, scheme, rest), x), lookup(rest, x)).when(ne(x, y)),
        // Generalization and instantiation.
        rule(
            qs_demand(ctx, Type::int()),
            has_qs(ctx, Type::int(), egg::Set::<Ident>::empty()),
        ),
        rule(
            qs_demand(ctx, Type::bool()),
            has_qs(ctx, Type::bool(), egg::Set::<Ident>::empty()),
        ),
        rule(
            qs_demand(ctx, Type::unit()),
            has_qs(ctx, Type::unit(), egg::Set::<Ident>::empty()),
        ),
        rule(
            qs_demand(ctx, Type::arrow(fr, to)),
            (qs_demand(ctx, fr), qs_demand(ctx, to)),
        ),
        rule(
            (
                qs_demand(ctx, Type::arrow(fr, to)),
                has_qs(ctx, fr, q1),
                has_qs(ctx, to, q2),
            ),
            has_qs(ctx, Type::arrow(fr, to), q1.union(q2)),
        ),
        rule(
            (
                qs_demand(ctx, Type::var(x)),
                ftv_context(ctx, keys),
                keys.contains(x),
            ),
            has_qs(ctx, Type::var(x), egg::Set::<Ident>::empty()),
        ),
        rule(
            (
                qs_demand(ctx, Type::var(x)),
                ftv_context(ctx, keys),
                keys.not_contains(x),
            ),
            has_qs(ctx, Type::var(x), egg::Set::<Ident>::empty().insert(x)),
        ),
        rule(generalize(ctx, t), qs_demand(ctx, t)),
        rewrite(generalize(ctx, t), Scheme::forall(vs, t)).when(has_qs(ctx, t, vs)),
        // Substitution.
        rewrite(subst_fresh(vs, Type::int(), c), Type::int()),
        rewrite(subst_fresh(vs, Type::bool(), c), Type::bool()),
        rewrite(subst_fresh(vs, Type::unit(), c), Type::unit()),
        rewrite(
            subst_fresh(vs, Type::arrow(fr, to), c),
            Type::arrow(subst_fresh(vs, fr, c), subst_fresh(vs, to, c)),
        ),
        rewrite(
            subst_fresh(vs, Type::var(x), c),
            Type::var(Ident::fresh(x, c)),
        )
        .when(vs.contains(x)),
        rewrite(subst_fresh(vs, Type::var(x), c), Type::var(x)).when(vs.not_contains(x)),
        rewrite(instantiate(Scheme::forall(vs, t), c), subst_fresh(vs, t, c)),
        // Injectivity.
        rule(
            eq(Type::arrow(f1, t1), Type::arrow(f2, t2)),
            (union(f1, f2), union(t1, t2)),
        ),
        // Type inference.
        rewrite(type_of(ctx, Expr::num(n), c), Type::int()),
        rewrite(type_of(ctx, true, c), Type::bool()),
        rewrite(type_of(ctx, false, c), Type::bool()),
        rewrite(type_of(ctx, (), c), Type::unit()),
        rewrite(
            type_of(ctx, Expr::var(x), c),
            instantiate(lookup(ctx, x), c),
        ),
        rewrite(
            type_of(ctx, Expr::abs(x, e), c),
            Type::arrow(&fresh, type_of(abstraction_context, e, cc)),
        )
        .when(eq(cc, c + 1)),
        rule(
            (
                eq(to, type_of(ctx, Expr::app(e1, e2), c)),
                eq(c1, c + 1),
                expr_size(e1, sz),
                eq(c2, c + sz + 1),
            ),
            union(type_of(ctx, e1, c1), Type::arrow(type_of(ctx, e2, c2), to)),
        ),
        rewrite(
            type_of(ctx, Expr::let_(x, e1, e2), c),
            type_of(let_context, e2, c2),
        )
        .when((eq(c1, c + 1), expr_size(e1, sz), eq(c2, c + sz + 1))),
        // Occurs checks.
        rule(
            eq(Type::var(x), Type::arrow(fr, to)),
            (occurs(x, fr), occurs(x, to)),
        ),
        rule(occurs(x, Type::var(x)), panic("occurs check fail")),
        rule(
            occurs(x, Type::arrow(fr, to)),
            (occurs(x, fr), occurs(x, to)),
        ),
        rule(
            (base_type(t), eq(t, Type::arrow(fr, to))),
            panic("Unifying base types with functions"),
        ),
        rule(eq(Type::int(), Type::bool()), panic("Unifying base types")),
        rule(eq(Type::int(), Type::unit()), panic("Unifying base types")),
        rule(eq(Type::bool(), Type::unit()), panic("Unifying base types")),
    ]
}

pub fn main() -> Result<(), TypedError> {
    let [x, y, z, id, iid, f, a] = ["x", "y", "z", "id", "iid", "f", "a"].map(Ident::named);
    let identity = Expr::abs(&x, &x);
    let tx = Type::var(Ident::fresh(&x, 0));
    let ty = Type::var(Ident::fresh(&y, 3));
    let tz = Type::var(Ident::fresh(Ident::fresh(&z, 2), 4));
    let nested = Type::var(Ident::fresh(Ident::fresh(Ident::fresh(&x, 1), 5), 7));
    let cases = [
        (identity.clone(), Type::arrow(&tx, &tx)),
        (
            Expr::let_(
                &id,
                &identity,
                Expr::app(Expr::app(&id, &id), Expr::app(&id, true)),
            ),
            Type::bool(),
        ),
        (
            Expr::app(&identity, Expr::abs(&y, &y)),
            Type::arrow(&ty, &ty),
        ),
        (Expr::let_(&x, true, true), Type::bool()),
        (Expr::let_(&x, true, &x), Type::bool()),
        (
            Expr::abs(&x, Expr::let_(&y, Expr::abs(&z, &z), &y)),
            Type::arrow(tx, Type::arrow(&tz, &tz)),
        ),
        (
            Expr::let_(
                &x,
                true,
                Expr::let_(&f, Expr::abs(&a, &a), Expr::let_(&x, (), Expr::app(&f, &x))),
            ),
            Type::unit(),
        ),
        (
            Expr::let_(
                &x,
                (),
                Expr::let_(
                    &f,
                    Expr::abs(&y, &x),
                    Expr::let_(&x, true, Expr::app(&f, &x)),
                ),
            ),
            Type::unit(),
        ),
        (
            Expr::app(
                Expr::abs(
                    &x,
                    Expr::let_(
                        &f,
                        Expr::abs(&y, &x),
                        Expr::let_(&x, true, Expr::app(&f, &x)),
                    ),
                ),
                (),
            ),
            Type::unit(),
        ),
        (
            Expr::app(
                Expr::abs(
                    &x,
                    Expr::app(
                        Expr::abs(&f, Expr::app(Expr::abs(&x, Expr::app(&f, &x)), true)),
                        Expr::abs(&y, &x),
                    ),
                ),
                (),
            ),
            Type::unit(),
        ),
        (
            Expr::let_(
                &id,
                identity,
                Expr::let_(
                    &iid,
                    Expr::abs(y, &id),
                    Expr::app(&iid, Expr::app(&id, true)),
                ),
            ),
            Type::arrow(&nested, &nested),
        ),
    ];
    let mut egraph = EGraph::default();
    egraph.register([Type::int(), Type::bool(), Type::unit()].map(|t| base_type(t)))?;
    for (i, (expr, expected)) in cases.into_iter().enumerate() {
        egraph.push()?;
        let output = let_(format!("{i}"), type_of(Context::nil(), expr, 0));
        egraph.register(&output)?;
        egraph.run(theory.repeat(100))?;
        assert!(egraph.check(eq(output, expected))?, "typeinfer case {i}");
        egraph.pop()?;
    }
    Ok(())
}
