// Core web-demo/set.egg: set primitives and demand-driven reified indexing.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct IntSet;

#[declarations]
impl IntSet {
    pub fn wrap(values: egg::Set<egg::I64>) -> IntSet;
}
#[function(no_merge)]
pub fn get(set: IntSet, index: egg::I64) -> egg::I64;

#[ruleset]
fn rules(values: &egg::Set<egg::I64>, j: &egg::I64) -> Vec<Rule> {
    let value = IntSet::wrap(values);
    let index = j + 1;
    vec![
        rule(
            (&value, values.len().gt(0)),
            set(get(&value, 0), values.get(0)),
        ),
        rule(
            (get(&value, j), index.lt(values.len())),
            set(get(value, &index), values.get(&index)),
        ),
    ]
}

pub fn main() -> Result<(), TypedError> {
    let mut egraph = EGraph::default();
    let a = egg::Set::<egg::I64>::of([1, 2]);
    assert!(egraph.check((
        eq(&a, egg::Set::<egg::I64>::empty().insert(1).insert(2)),
        eq(&a, egg::Set::<egg::I64>::empty().insert(2).insert(1)),
        eq(a.union(egg::Set::of([3, 4])), egg::Set::of([1, 2, 3, 4])),
        eq(egg::Set::<egg::I64>::empty().len(), 0),
        eq(egg::Set::<egg::I64>::of([1, 1, 1]).len(), 1),
        eq(egg::Set::<egg::I64>::of([1, -1, 1, 1]).len(), 2),
        eq(
            egg::Set::<egg::I64>::of([1, 2, 3]).remove(3),
            egg::Set::of([1, 2])
        ),
    ))?);
    let values = egg::Set::<egg::I64>::of([1, -1, 2, 4, 1]);
    // Native i64 base-value ordering places negative values after positives.
    for (index, expected) in [1, 2, 4, -1].into_iter().enumerate() {
        assert!(egraph.check(eq(values.get(index as i64), expected))?);
    }
    let root = let_(
        "root",
        IntSet::wrap(egg::Set::<egg::I64>::of([2, 4, 1, 4, -1])),
    );
    egraph.register(&root)?;
    egraph.run(rules.repeat(100))?;
    for (index, expected) in [1, 2, 4, -1].into_iter().enumerate() {
        assert!(egraph.check(eq(get(&root, index as i64), expected))?);
    }
    Ok(())
}
