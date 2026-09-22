// Core resolution.egg and Python examples/resolution.py use different final
// clauses. Run both, including the core's additional unit-propagation rewrite.
// This encoding handles ground atoms modulo equality, not clause-local
// first-order unification. The source warns that encoding clause sets with
// associativity/commutativity is inefficient.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;
#[sort]
pub struct Formula;

#[declarations]
impl Formula {
    pub fn truth() -> Formula;
    pub fn falsity() -> Formula;
    #[constructor(from(i64, i32))]
    pub fn p(index: egg::I64) -> Formula;
}

#[declarations]
impl std::ops::BitOr<&Formula> for &Formula {
    type Output = Formula;
    fn bitor(self, rhs: &Formula) -> Formula;
}

#[declarations]
impl std::ops::Not for &Formula {
    type Output = Formula;
    fn not(self) -> Formula;
}

#[ruleset]
fn simplification(a: &Formula, b: &Formula, c: &Formula) -> Vec<Rule> {
    // Clauses are right-associated disjunctions ending in false.
    let t = Formula::truth();
    let f = Formula::falsity();
    vec![
        rewrite((a | b) | c, a | (b | c)),
        rewrite(a | (b | c), b | (a | c)),
        rewrite(a | (a | b), a | b),
        rewrite(a | ((!a) | b), &t),
        rewrite(&f | a, a),
        rewrite(a | f, a),
        rewrite(&t | a, &t),
        rewrite(a | &t, t),
    ]
}

fn resolution_case(python: bool) -> Result<(), TypedError> {
    let clauses = ruleset(
        |p: &Formula, a: &Formula, rest_a: &Formula, rest_b: &Formula| {
            let mut clauses = vec![
                rule(eq(!p, true), union(p, false)),
                rule(eq(!p, false), union(p, true)),
                rule(eq(Formula::truth(), p | false), union(p, true)),
                // Commutativity brings each complementary literal to the head
                // of its clause, where this join performs resolution.
                rule(
                    (
                        eq(Formula::truth(), a | rest_a),
                        eq(Formula::truth(), (!a) | rest_b),
                    ),
                    union(rest_a | rest_b, true),
                ),
            ];
            if !python {
                clauses.push(rule((p, eq(Formula::truth(), p | false)), union(p, true)));
            }
            clauses
        },
    );
    let theory = ruleset((&simplification, clauses));
    let mut egraph = EGraph::default();
    let t = Formula::truth();
    let f = Formula::falsity();
    let [p0, p1, p2] = [0, 1, 2].map(Formula::p);
    let last_middle = if python { !&p1 } else { p1.clone() };
    egraph.register((
        union(!&f, &t),
        union(!&t, &f),
        union(&p1 | ((!&p2) | &f), &t),
        union(&p2 | ((!&p0) | &f), &t),
        union(&p0 | ((!&p1) | &f), &t),
        union(p1, &f),
        union((!&p0) | (last_middle | (&p2 | &f)), &t),
    ))?;
    egraph.run(theory.repeat(10))?;
    assert!(egraph.check((ne(t, &f), eq(p0, &f), eq(p2, f)))?);
    Ok(())
}
impl From<bool> for Formula {
    fn from(value: bool) -> Self {
        if value {
            Self::truth()
        } else {
            Self::falsity()
        }
    }
}

pub fn main() -> Result<(), TypedError> {
    resolution_case(false)?;
    resolution_case(true)
}
