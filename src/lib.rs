pub use egglog::*;
use std::sync::Arc;

mod rational;
pub use rational::*;

pub fn new_experimental_egraph() -> EGraph {
    let mut egraph = EGraph::default();
    egraph.add_arcsort(Arc::new(RationalSort)).unwrap();
    egraph
}
