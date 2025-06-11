use egglog::prelude::add_leaf_sort;
pub use egglog::*;
use std::sync::Arc;

mod rational;
pub use rational::*;
mod sugar;
pub use sugar::*;
mod scheduling;
pub use scheduling::*;

mod set_cost;
pub use set_cost::*;

pub fn new_experimental_egraph() -> EGraph {
    let mut egraph = EGraph::default();
    add_leaf_sort(&mut egraph, RationalSort, span!()).unwrap();
    egraph.parser.add_command_macro(Arc::new(For));
    egraph.parser.add_command_macro(Arc::new(WithRuleset));

    add_set_cost(&mut egraph);

    egraph
        .add_command("run-schedule".into(), Arc::new(RunExtendedSchedule))
        .unwrap();
    egraph
}
