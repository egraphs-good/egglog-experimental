use egglog_experimental::typed::{builtins as egg, prelude::*};
fn main() {
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register(eq(egg::I64::from(1), 1));
    graph.register(rule((), ()));
    graph.register(ruleset(()));
    graph.register(ruleset(()).repeat(1));
}
