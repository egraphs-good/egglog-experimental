use egglog::prelude::{RustSpan, Span, add_base_sort};
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
mod size;
pub use size::*;

mod smt;
mod smt_bitvec;
mod smt_real;
pub use smt::*;
pub use smt_bitvec::*;
pub use smt_real::*;

pub fn new_experimental_egraph() -> EGraph {
    let mut egraph = EGraph::default();
    add_base_sort(&mut egraph, RationalSort, span!()).unwrap();
    egraph.parser.add_command_macro(Arc::new(For));
    egraph.parser.add_command_macro(Arc::new(WithRuleset));

    add_set_cost(&mut egraph);
    egraph.add_primitive(GetSizePrimitive);

    // Comment this out for now since the run-schedule in experimental doesn't support equality facts
    // egraph
    //     .add_command("run-schedule".into(), Arc::new(RunExtendedSchedule))
    //     .unwrap();

    add_smt(&mut egraph);
    egraph
}
