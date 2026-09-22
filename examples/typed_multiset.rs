// Core multiset.egg's admitted non-higher-order sections. See the exact line
// ranges in docs/typed-example-coverage.md; no map/reduce behavior is simulated.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Math;

#[declarations]
impl Math {
    #[constructor(from(i64, i32))]
    pub fn num(value: egg::I64) -> Math;
}

pub fn main() -> Result<(), TypedError> {
    let [one, two, three, four] = [1, 2, 3, 4].map(Math::num);
    let xs = let_("xs", egg::MultiSet::<Math>::of([1, 2, 3]));
    let mut egraph = EGraph::default();
    egraph.register((&xs, &four))?;
    assert!(
        egraph.check((
            eq(
                egg::MultiSet::<Math>::of([&one, &one]),
                egg::MultiSet::<Math>::single(&one, 2)
            ),
            eq(egg::MultiSet::<Math>::of([&three, &two, &one]), &xs),
            ne(egg::MultiSet::<Math>::of([&three, &two, &one, &one]), &xs),
            eq(
                xs.insert(&four),
                egg::MultiSet::<Math>::of([&one, &two, &three, &four])
            ),
            eq(
                xs.subtract(egg::MultiSet::<Math>::of([&three])),
                egg::MultiSet::<Math>::of([&one, &two])
            ),
            eq(
                egg::MultiSet::<Math>::of([&three, &three, &one]).pick_max(),
                &three
            ),
            eq(
                egg::MultiSet::<Math>::of([&one, &two, &two, &three])
                    .intersection(egg::MultiSet::<Math>::of([&two, &two, &three, &four])),
                egg::MultiSet::<Math>::of([&two, &two, &three])
            ),
            eq(
                egg::MultiSet::<Math>::of([&three]).subtract_swapped(&xs),
                egg::MultiSet::<Math>::of([&one, &two])
            ),
            xs.contains(&one),
            xs.not_contains(&four),
            eq(xs.remove(&two), egg::MultiSet::<Math>::of([&one, &three])),
            eq(
                egg::MultiSet::<Math>::of([&one, &one]).remove(&one),
                egg::MultiSet::<Math>::of([&one])
            ),
            eq(xs.len(), 3),
            eq(egg::MultiSet::<Math>::of([&one, &one, &one]).len(), 3),
            eq(xs.count(&one), 1),
            eq(egg::MultiSet::<Math>::of([&one]).pick(), &one),
        ))?
    );
    // The source expects these partial operations to fail. Restore a healthy
    // native scope after each failure instead of continuing a poisoned session.
    for invalid in [
        xs.subtract(egg::MultiSet::<Math>::of([&three, &three])),
        xs.subtract(egg::MultiSet::<Math>::of([&four])),
        xs.remove(&four),
    ] {
        egraph.push()?;
        assert!(egraph.register(invalid).is_err());
        egraph.pop()?;
        assert!(egraph.check(eq(xs.len(), 3))?);
    }
    let summed =
        egg::MultiSet::of([&one, &two, &three]).sum(egg::MultiSet::of([&one, &two, &four]));
    assert!(egraph.check((
        eq(
            &summed,
            egg::MultiSet::<Math>::of([&one, &four, &two, &three, &two, &one])
        ),
        eq(summed.len(), 6),
    ))?);

    egraph.push()?;
    let nested = let_(
        "nested",
        egg::MultiSet::<egg::MultiSet<Math>>::of([
            egg::MultiSet::<Math>::of([1, 2, 3]),
            egg::MultiSet::<Math>::of([1, 2, 3]),
        ]),
    );
    egraph.register(&nested)?;
    egraph.register(union(&one, &two))?;
    assert!(egraph.check(eq(
        &nested,
        egg::MultiSet::<egg::MultiSet<Math>>::of([
            egg::MultiSet::<Math>::of([&two, &two, &three]),
            egg::MultiSet::<Math>::of([&two, &two, &three]),
        ])
    ))?);
    assert!(egraph.check(eq(
        nested.sum_multisets(),
        egg::MultiSet::<Math>::of([&two, &two, &two, &two, &three, &three])
    ))?);
    egraph.pop()?;

    egraph.push()?;
    egraph.register(xs.union_values())?;
    assert!(egraph.check(eq(one, two))?);
    egraph.pop()?;
    Ok(())
}
