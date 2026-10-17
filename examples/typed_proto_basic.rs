use egglog_experimental::typed::prelude::*;

#[sort]
struct Math;
#[declarations]
impl Math {
    fn Leaf() -> Self;
    fn Pair(left: Math, right: Math) -> Self;
}

fn main() -> Result<(), TypedError> {
    let leaf = Math::Leaf();
    let root = Math::Pair(&leaf, &leaf);
    let collapse = ruleset(|x: &Math| rewrite(Math::Pair(x, x), x));
    let mut graph = EGraph::default();
    graph.register(&root)?;
    graph.run(&collapse)?;
    assert!(graph.check(eq(&root, &leaf))?);
    assert_eq!(graph.extract(&root)?, leaf);
    Ok(())
}
