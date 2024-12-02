pub use egglog::*;
use std::sync::Arc;

mod rational;
pub use rational::*;

pub struct EGraph(pub egglog::EGraph);

impl Default for EGraph {
    fn default() -> EGraph {
        let mut inner = egglog::EGraph::default();
        inner.add_arcsort(Arc::new(RationalSort)).unwrap();
        EGraph(inner)
    }
}
