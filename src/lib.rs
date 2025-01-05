pub use egglog::*;
use std::sync::Arc;
use sugar::{For, WithRuleset};

mod rational;
mod sugar;
pub use rational::*;

pub fn new_experimental_egraph() -> EGraph {
    let mut egraph = EGraph::default();
    egraph.add_arcsort(Arc::new(RationalSort), span!()).unwrap();
    egraph.parser.add_command_macro(Arc::new(For));
    egraph.parser.add_command_macro(Arc::new(WithRuleset));
    egraph
}
