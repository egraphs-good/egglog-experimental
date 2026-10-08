use egglog_experimental::typed::{
    builtins::{F64, I64},
    prelude::*,
};

#[sort]
struct Math;
#[declarations]
impl Math {
    #[constructor(try_from)]
    fn Num(value: I64) -> Self;
    fn Add(a: Math, b: Math) -> Self;
}

fn main() -> Result<(), TypedError> {
    let fold = ruleset(|i: &I64, j: &I64| {
        rewrite(Math::Add(Math::Num(i), Math::Num(j)), Math::Num(i + j))
    });
    let term = Math::Add(Math::Num(2_i64), Math::Num(3_i64));
    let mut graph = EGraph::default();
    graph.register(&term)?;
    graph.run(&fold)?;
    let result = I64::try_from(graph.extract(&term)?)?;
    assert_eq!(i64::try_from(&result)?, 5);
    assert_eq!(
        f64::try_from(&graph.extract(F64::from(1.25) + F64::from(2.5))?)?,
        3.75
    );
    Ok(())
}
