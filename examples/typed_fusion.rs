// Core web-demo/fusion.egg: free-variable analysis, capture-avoiding beta
// reduction and pushdown fuse the recursive sum/map definitions symbolically.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;
#[sort]
pub struct Variable;

#[declarations]
impl Variable {
    #[constructor(from(&str, std::string::String))]
    pub fn named(name: egg::String) -> Variable;
    pub fn from_term(term: Term) -> Variable;
}
#[sort]
pub struct Term;

#[declarations]
impl Term {
    pub fn app(function: Term, argument: Term) -> Term;
    pub fn lam(variable: Variable, body: Term) -> Term;
    #[constructor(from)]
    pub fn var(variable: Variable) -> Term;
    pub fn let_(variable: Variable, value: Term, body: Term) -> Term;
    #[constructor(from(i64, i32))]
    pub fn num(value: egg::I64) -> Term;
    pub fn case(list: Term, nil: Term, cons: Term) -> Term;
    pub fn cons(head: Term, tail: Term) -> Term;
    pub fn nil() -> Term;
}
#[function(merge = |old: egg::Set<Variable>, new: egg::Set<Variable>| old.intersection(new))]
pub fn freer(term: Term) -> egg::Set<Variable>;
#[constructor(cost = 10000)]
pub fn pushdown(function: Term, body: Term) -> Term;
#[constructor(cost = 1000)]
pub fn sum() -> Term;
#[constructor(cost = 1000)]
pub fn map_f() -> Term;
#[constructor]
pub fn sum_map_f() -> Term;
#[relation]
pub fn tail(term: Term);

#[declarations]
impl std::ops::Add<&Term> for &Term {
    type Output = Term;
    fn add(self, rhs: &Term) -> Term;
}

#[ruleset]
fn theory(
    e: &Term,
    v: &Variable,
    body: &Term,
    fv: &egg::Set<Variable>,
    a: &Term,
    b: &Term,
    fa: &egg::Set<Variable>,
    fb: &egg::Set<Variable>,
    n: &egg::I64,
    c: &Term,
    fc: &egg::Set<Variable>,
    expr: &Term,
    v1: &Variable,
    v2: &Variable,
    f: &Term,
    x: &Variable,
    w: &Variable,
    xs: &Variable,
    e1: &Term,
    e2: &Term,
) -> Vec<Rule> {
    let fresh = Variable::from_term(expr);
    vec![
        // Free variables.
        rule(
            (eq(e, Term::app(a, b)), eq(freer(a), fa), eq(freer(b), fb)),
            set(freer(e), fa.union(fb)),
        ),
        rule(
            (eq(e, Term::lam(v, body)), eq(freer(body), fv)),
            set(freer(e), fv.remove(v)),
        ),
        rule(
            eq(e, Term::var(v)),
            set(freer(e), egg::Set::<Variable>::empty().insert(v)),
        ),
        rule(
            (
                eq(e, Term::let_(v, a, b)),
                eq(freer(a), fa),
                eq(freer(b), fb),
            ),
            set(freer(e), fa.union(fb.remove(v))),
        ),
        rule(
            (eq(e, a + b), eq(freer(a), fa), eq(freer(b), fb)),
            set(freer(e), fa.union(fb)),
        ),
        rule(
            eq(e, Term::num(n)),
            set(freer(e), egg::Set::<Variable>::empty()),
        ),
        rule(
            (
                eq(e, Term::case(a, b, c)),
                eq(freer(a), fa),
                eq(freer(b), fb),
                eq(freer(c), fc),
            ),
            set(freer(e), fa.union(fb).union(fc)),
        ),
        rule(
            (eq(e, Term::cons(a, b)), eq(freer(a), fa), eq(freer(b), fb)),
            set(freer(e), fa.union(fb)),
        ),
        rule(
            eq(e, Term::nil()),
            set(freer(e), egg::Set::<Variable>::empty()),
        ),
        // Capture-avoiding substitution.
        rewrite(Term::app(Term::lam(v, b), e), Term::let_(v, e, b)),
        rewrite(Term::case(Term::nil(), a, b), a),
        rewrite(
            Term::case(Term::cons(a, b), c, e),
            Term::app(Term::app(e, a), b),
        ),
        rewrite(Term::let_(v, e, Term::num(n)), Term::num(n)),
        rewrite(Term::let_(v, e, Term::nil()), Term::nil()),
        rewrite(Term::let_(v, e, Term::var(v)), e),
        rewrite(Term::let_(v, e, Term::var(w)), Term::var(w)).when(ne(v, w)),
        rewrite(Term::let_(v, e, a), a).when(freer(a).not_contains(v)),
        rewrite(
            Term::let_(v, e, expr),
            Term::app(Term::let_(v, e, a), Term::let_(v, e, b)),
        )
        .when((eq(expr, Term::app(a, b)), freer(expr).contains(v))),
        rewrite(
            Term::let_(v, e, expr),
            Term::let_(v, e, a) + Term::let_(v, e, b),
        )
        .when((eq(expr, a + b), freer(expr).contains(v))),
        rewrite(
            Term::let_(v, e, expr),
            Term::cons(Term::let_(v, e, a), Term::let_(v, e, b)),
        )
        .when((eq(expr, Term::cons(a, b)), freer(expr).contains(v))),
        rewrite(
            Term::let_(v, e, Term::case(a, b, c)),
            Term::case(
                Term::let_(v, e, a),
                Term::let_(v, e, b),
                Term::let_(v, e, c),
            ),
        )
        .when(freer(Term::case(a, b, c)).contains(v)),
        rewrite(Term::let_(v, e, Term::lam(v, b)), Term::lam(v, b)),
        rewrite(
            Term::let_(v, e, Term::lam(w, b)),
            Term::lam(w, Term::let_(v, e, b)),
        )
        .when((
            freer(b).contains(v),
            ne(v, w),
            eq(fv, freer(e)),
            fv.not_contains(w),
        )),
        rule(
            (
                eq(expr, Term::let_(v1, e, Term::lam(v2, body))),
                freer(body).contains(v1),
                ne(v1, v2),
                eq(fv, freer(e)),
                fv.contains(v2),
            ),
            union(
                expr,
                Term::lam(
                    &fresh,
                    Term::let_(v1, e, Term::let_(v2, Term::var(&fresh), body)),
                ),
            ),
        ),
        // Pushdown and fusion.
        rewrite(
            Term::app(f, Term::app(Term::lam(x, e), e2)),
            Term::app(Term::lam(x, pushdown(f, e)), e2),
        ),
        rewrite(
            pushdown(f, Term::case(e, e1, Term::lam(x, Term::lam(xs, e2)))),
            Term::case(
                e,
                Term::app(f, e1),
                Term::lam(x, Term::lam(xs, Term::app(f, e2))),
            ),
        ),
        rule((pushdown(f, e), eq(e, Term::app(a, b))), tail(e)),
        rule((pushdown(f, e), eq(e, Term::lam(x, e))), tail(e)),
        rule((pushdown(f, e), eq(e, Term::var(x))), tail(e)),
        rule((pushdown(f, e), eq(e, Term::cons(a, b))), tail(e)),
        rule((pushdown(f, e), eq(e, Term::nil())), tail(e)),
        rule((pushdown(f, e), eq(e, a + b)), tail(e)),
        rule((pushdown(f, e), eq(e, Term::num(n))), tail(e)),
        rewrite(pushdown(f, e), Term::app(f, e)).when(tail(e)),
        rewrite(
            Term::app(sum(), Term::app(map_f(), e)),
            Term::app(sum_map_f(), e),
        ),
    ]
}

pub fn main() -> Result<(), TypedError> {
    let [xs, x, tail, input] = ["xs", "x", "xs'", "expr"].map(Variable::named);
    let vx = Term::var(&x);
    let vtail = Term::var(&tail);
    let vinput = Term::var(input);
    let mut egraph = EGraph::default();
    egraph.register((
        union(
            sum(),
            Term::lam(
                &xs,
                Term::case(
                    &xs,
                    0,
                    Term::lam(&x, Term::lam(&tail, &vx + Term::app(sum(), &vtail))),
                ),
            ),
        ),
        union(
            map_f(),
            Term::lam(
                &xs,
                Term::case(
                    &xs,
                    Term::nil(),
                    Term::lam(
                        &x,
                        Term::lam(&tail, Term::cons(&vx + 1, Term::app(map_f(), &vtail))),
                    ),
                ),
            ),
        ),
        set(freer(sum()), egg::Set::<Variable>::empty()),
        set(freer(map_f()), egg::Set::<Variable>::empty()),
    ))?;
    let expr = let_("expr", Term::app(sum(), Term::app(map_f(), &vinput)));
    egraph.register(&expr)?;
    egraph.run(theory.repeat(100))?;
    egraph.extract(&freer(expr))?;
    let output = Term::case(
        &vinput,
        0,
        Term::lam(x, Term::lam(tail, (vx + 1) + Term::app(sum_map_f(), vtail))),
    );
    let retained = let_("my_output", &output);
    egraph.register(&retained)?;
    assert!(egraph.check(eq(Term::app(sum_map_f(), vinput), output))?);
    Ok(())
}
