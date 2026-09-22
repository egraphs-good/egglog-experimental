// Core lambda.egg and Python lambda_.py. Their evaluation storage and the
// freer(Let) formula differ; run each actual theory instead of conflating them.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;
#[sort]
pub struct Value;

#[declarations]
impl Value {
    #[constructor(from(i64, i32))]
    pub fn num(value: egg::I64) -> Value;
    pub fn truth() -> Value;
    pub fn falsity() -> Value;
}
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
    pub fn val(value: Value) -> Term;
    #[constructor(from)]
    pub fn var(variable: Variable) -> Term;
    pub fn equal(left: Term, right: Term) -> Term;
    pub fn app(function: Term, argument: Term) -> Term;
    pub fn lam(variable: Variable, body: Term) -> Term;
    pub fn let_(variable: Variable, value: Term, body: Term) -> Term;
    pub fn fix(variable: Variable, body: Term) -> Term;
    pub fn if_(condition: Term, yes: Term, no: Term) -> Term;
}
#[function(merge = |old: egg::Set<Variable>, new: egg::Set<Variable>| old.intersection(new))]
// Track variables that can affect evaluation, not every syntactically free variable.
pub fn freer(term: Term) -> egg::Set<Variable>;
#[function(no_merge)]
pub fn evaluates(term: Term) -> Value;
#[constructor]
pub fn python_eval(term: Term) -> Value;
#[relation]
pub fn result_found();

#[declarations]
impl std::ops::Add<&Term> for &Term {
    type Output = Term;
    fn add(self, rhs: &Term) -> Term;
}

// Fixed occurrences are shared across the core and Python theory factories.
static REWRITES: std::sync::LazyLock<[Rule; 13]> = std::sync::LazyLock::new(|| {
    let [a, b, c, e] = &["a", "b", "c", "e"].map(var::<Term>);
    let [v, w] = &["v", "w"].map(var::<Variable>);
    let fv = &var::<egg::Set<Variable>>("fv");
    [
        rewrite(Term::if_(true, a, b), a),
        rewrite(Term::if_(false, a, b), b),
        rewrite(Term::if_(Term::equal(Term::var(v), e), a, b), b)
            .when(eq(Term::let_(v, e, a), Term::let_(v, e, b))),
        rewrite(a + b, b + a),
        rewrite((a + b) + c, a + (b + c)),
        rewrite(Term::equal(a, b), Term::equal(b, a)),
        rewrite(Term::fix(v, e), Term::let_(v, Term::fix(v, e), e)),
        rewrite(Term::app(Term::lam(v, b), e), Term::let_(v, e, b)),
        rewrite(
            Term::let_(v, e, Term::if_(c, a, b)),
            Term::if_(
                Term::let_(v, e, c),
                Term::let_(v, e, a),
                Term::let_(v, e, b),
            ),
        ),
        rewrite(Term::let_(v, e, Term::var(v)), e),
        rewrite(Term::let_(v, e, Term::var(w)), Term::var(w)).when(ne(v, w)),
        rewrite(Term::let_(v, e, Term::lam(v, b)), Term::lam(v, b)),
        rewrite(
            Term::let_(v, e, Term::lam(w, b)),
            Term::lam(w, Term::let_(v, e, b)),
        )
        .when((ne(v, w), eq(fv, freer(e)), fv.not_contains(w))),
    ]
});

fn theory(python: bool) -> Ruleset {
    let eval: fn(&Term) -> Value = if python {
        |x| python_eval(x)
    } else {
        |x| evaluates(x)
    };
    ruleset(
        |e: &Term,
         v: &Value,
         variable: &Variable,
         a: &Term,
         b: &Term,
         fa: &egg::Set<Variable>,
         fb: &egg::Set<Variable>,
         c: &Term,
         fc: &egg::Set<Variable>,
         va: &egg::I64,
         vb: &egg::I64,
         left_value: &Value,
         right_value: &Value,
         x: &Variable,
         yes: &Term,
         no: &Term,
         expr: &Term,
         v1: &Variable,
         v2: &Variable,
         body: &Term,
         fv: &egg::Set<Variable>| {
            let free = if python {
                fa.remove(variable).union(fb)
            } else {
                fa.union(fb.remove(variable))
            };
            let renamed = Variable::from_term(expr);
            vec![
                // Free variables.
                rule(
                    eq(e, Term::val(v)),
                    set(freer(e), egg::Set::<Variable>::empty()),
                ),
                rule(
                    eq(e, Term::var(variable)),
                    set(freer(e), egg::Set::<Variable>::empty().insert(variable)),
                ),
                rule(
                    (eq(e, a + b), eq(freer(a), fa), eq(freer(b), fb)),
                    set(freer(e), fa.union(fb)),
                ),
                rule(
                    (eq(e, Term::equal(a, b)), eq(freer(a), fa), eq(freer(b), fb)),
                    set(freer(e), fa.union(fb)),
                ),
                rule(
                    (eq(e, Term::app(a, b)), eq(freer(a), fa), eq(freer(b), fb)),
                    set(freer(e), fa.union(fb)),
                ),
                rule(
                    (eq(e, Term::lam(variable, b)), eq(freer(b), fv)),
                    set(freer(e), fv.remove(variable)),
                ),
                rule(
                    (
                        eq(e, Term::let_(variable, a, b)),
                        eq(freer(a), fa),
                        eq(freer(b), fb),
                    ),
                    set(freer(e), free),
                ),
                rule(
                    (eq(e, Term::fix(variable, b)), eq(freer(b), fv)),
                    set(freer(e), fv.remove(variable)),
                ),
                rule(
                    (
                        eq(e, Term::if_(c, a, b)),
                        eq(freer(c), fc),
                        eq(freer(a), fa),
                        eq(freer(b), fb),
                    ),
                    set(freer(e), fc.union(fa.union(fb))),
                ),
                // Evaluation.
                rule(
                    eq(e, Term::val(v)),
                    if python {
                        union(eval(e), v)
                    } else {
                        set(evaluates(e), v)
                    },
                ),
                rule(
                    (
                        eq(e, a + b),
                        eq(Value::num(va), eval(a)),
                        eq(Value::num(vb), eval(b)),
                    ),
                    if python {
                        union(eval(e), Value::num(va + vb))
                    } else {
                        set(evaluates(e), Value::num(va + vb))
                    },
                ),
                rule(
                    (eq(e, Term::equal(a, b)), eq(eval(b), eval(a))),
                    if python {
                        union(eval(e), true)
                    } else {
                        set(evaluates(e), Value::truth())
                    },
                ),
                rule(
                    (
                        eq(e, Term::equal(a, b)),
                        eq(left_value, eval(a)),
                        eq(right_value, eval(b)),
                        ne(left_value, right_value),
                    ),
                    if python {
                        union(eval(e), false)
                    } else {
                        set(evaluates(e), Value::falsity())
                    },
                ),
                rule(eq(v, eval(e)), union(e, Term::val(v))),
                // Conditionals and algebra.
                REWRITES[0].clone(),
                REWRITES[1].clone(),
                rule(
                    Term::if_(Term::equal(Term::var(x), e), yes, no),
                    (Term::let_(x, e, yes), Term::let_(x, e, no)),
                ),
                REWRITES[2].clone(),
                REWRITES[3].clone(),
                REWRITES[4].clone(),
                REWRITES[5].clone(),
                // Capture-avoiding substitution.
                REWRITES[6].clone(),
                REWRITES[7].clone(),
                rewrite(
                    Term::let_(variable, e, Term::app(a, b)),
                    Term::app(Term::let_(variable, e, a), Term::let_(variable, e, b)),
                ),
                rewrite(
                    Term::let_(variable, e, a + b),
                    Term::let_(variable, e, a) + Term::let_(variable, e, b),
                ),
                rewrite(
                    Term::let_(variable, e, Term::equal(a, b)),
                    Term::equal(Term::let_(variable, e, a), Term::let_(variable, e, b)),
                ),
                if python {
                    let constant = Term::val(v);
                    rewrite(Term::let_(variable, e, &constant), constant)
                } else {
                    rewrite(Term::let_(variable, e, c), c).when(eval(c))
                },
                REWRITES[8].clone(),
                REWRITES[9].clone(),
                REWRITES[10].clone(),
                REWRITES[11].clone(),
                REWRITES[12].clone(),
                rule(
                    (
                        eq(expr, Term::let_(v1, e, Term::lam(v2, body))),
                        ne(v1, v2),
                        eq(fv, freer(e)),
                        fv.contains(v2),
                    ),
                    union(
                        expr,
                        Term::lam(
                            &renamed,
                            Term::let_(v1, e, Term::let_(v2, Term::var(&renamed), body)),
                        ),
                    ),
                ),
            ]
        },
    )
}

impl From<i64> for Term {
    fn from(value: i64) -> Self {
        Self::val(Value::num(value))
    }
}

impl From<i32> for Term {
    fn from(value: i32) -> Self {
        Self::val(Value::num(value))
    }
}

impl From<egg::I64> for Term {
    fn from(value: egg::I64) -> Self {
        Self::val(Value::num(value))
    }
}

impl From<&egg::I64> for Term {
    fn from(value: &egg::I64) -> Self {
        Self::val(Value::num(value))
    }
}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        if value {
            Self::truth()
        } else {
            Self::falsity()
        }
    }
}

impl From<bool> for Term {
    fn from(value: bool) -> Self {
        Self::val(Value::from(value))
    }
}

pub fn main() -> Result<(), TypedError> {
    for python in [false, true] {
        let theory = theory(python);
        let [x, y, a, b, f, g, five, add_five, compose, add1, zeroone] = [
            "x", "y", "a", "b", "f", "g", "five", "add-five", "compose", "add1", "zeroone",
        ]
        .map(Variable::named);
        let [n0, n1, n2, n4, n5, n6, n7, n8, n9, n10] =
            [0, 1, 2, 4, 5, 6, 7, 8, 9, 10].map(Term::from);
        let vx = Term::var(&x);
        let vy = Term::var(&y);
        let va = Term::var(a);
        let vb = Term::var(b);
        let compose_body = Term::lam(
            &f,
            Term::lam(&g, Term::lam(&x, Term::app(&f, Term::app(&g, &vx)))),
        );
        let increment = Term::lam(&y, &vy + &n1);
        let mut cases = vec![
            (
                Term::lam(&x, &n4 + Term::app(Term::lam(&y, &vy), &n4)),
                Term::lam(&x, n8),
                10,
                true,
            ),
            (
                Term::if_(Term::equal(&va, &vb), &va + &va, &va + &vb),
                va + vb,
                10,
                true,
            ),
            (
                Term::let_(&x, &n0, Term::let_(&y, &n1, &vx + &vy)),
                n1.clone(),
                10,
                true,
            ),
            (
                Term::let_(&x, &n1, Term::lam(&x, &vx)),
                Term::lam(&x, &n1),
                10,
                false,
            ),
            (
                Term::let_(&y, &vx + &vx, Term::lam(&x, &vy)),
                Term::lam(&x, &vx + &vx),
                10,
                false,
            ),
            (
                Term::let_(
                    &five,
                    n5,
                    Term::let_(
                        &add_five,
                        Term::lam(&x, &vx + &five),
                        Term::let_(&five, &n6, Term::app(&add_five, &n1)),
                    ),
                ),
                n6,
                10,
                true,
            ),
            (
                Term::if_(Term::equal(&n1, &n1), &n7, n9),
                n7.clone(),
                4,
                true,
            ),
            (
                Term::let_(
                    &zeroone,
                    Term::lam(&x, Term::if_(Term::equal(&vx, &n0), &n0, &n1)),
                    Term::app(&zeroone, n0) + Term::app(&zeroone, n10),
                ),
                n1.clone(),
                20,
                true,
            ),
        ];
        for (count, expected, steps) in [(1, n2, 20), (6, n7.clone(), 30)] {
            let mut body = Term::var(&add1);
            for _ in 0..count {
                body = Term::app(Term::app(&compose, &add1), body);
            }
            cases.push((
                Term::let_(&compose, &compose_body, Term::let_(&add1, &increment, body)),
                Term::lam(&x, &vx + expected),
                steps,
                true,
            ));
        }
        for (index, (input, expected, steps, positive)) in cases.into_iter().enumerate() {
            let mut egraph = EGraph::default();
            let output = let_(format!("{python}::{index}"), input);
            egraph.register(&output)?;
            egraph.run(theory.repeat(if python && ![4, 5, 8].contains(&index) {
                30
            } else {
                steps
            }))?;
            assert_eq!(
                egraph.check(eq(&output, expected))?,
                positive,
                "lambda source={python} case={index}"
            );
            if index == 3 && python {
                assert!(egraph.check(eq(&output, Term::lam(&x, &vx)))?);
            }
            if index == 4 {
                assert!(egraph.check(freer(Term::lam(&x, &vy)).contains(&y))?);
            }
            if index == 5 {
                assert!(!egraph.check(eq(output, &n7))?);
            }
            if index == 8 && python {
                let presence = ruleset(rule(
                    (
                        Term::lam(&x, &n1 + Term::app(Term::lam(&y, &n1 + &vy), &vx)),
                        Term::lam(&x, &vx + 2),
                    ),
                    result_found(),
                ));
                egraph.run(&presence)?;
                assert!(egraph.check(result_found())?);
            }
        }
        if python {
            let mut egraph = EGraph::default();
            let tests = [
                (python_eval(&n1), Value::num(1)),
                (python_eval(n1 + 2), Value::num(3)),
            ];
            for (input, expected) in tests {
                egraph.register(&input)?;
                egraph.run(theory.repeat(30))?;
                assert!(egraph.check(eq(input, expected))?);
            }
        }
    }
    Ok(())
}
