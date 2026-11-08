use egglog_experimental::typed::{builtins::I64, prelude::*};

#[sort(name = "Math")]
pub(crate) struct Math;

#[declarations]
impl Math {
    #[constructor(name = "Num")]
    fn num(value: I64) -> Self;
    #[function(name = "value", no_merge)]
    fn value(&self) -> I64;
}

#[declarations]
impl std::ops::Add for Math {
    type Output = Math;
    #[constructor(name = "Add")]
    fn add(self, rhs: Math) -> Math;
}

#[ruleset(name = "")]
fn fold(e: &Math, a: &I64, b: &I64) -> Rule {
    rule(
        eq(e, Math::num(a) + Math::num(b)),
        (
            union(e, Math::num(a + b)),
            set(e.value(), a + b),
            subsume(Math::num(a) + Math::num(b)),
        ),
    )
    .label("fold")
}

pub(crate) fn run_example(graph: &mut EGraph) -> Result<(), TypedError> {
    let sum = let_("sum", Math::num(2) + Math::num(3));
    graph.register(&sum)?;
    graph.run(&fold)?;
    assert!(graph.check((eq(&sum, Math::num(5)), eq(sum.value(), 5)))?);
    assert_eq!(graph.extract(&sum)?, Math::num(5));
    Ok(())
}

fn main() -> Result<(), TypedError> {
    let mut graph = EGraph::new()?;
    run_example(&mut graph)?;
    graph.freeze()?;
    Ok(())
}
