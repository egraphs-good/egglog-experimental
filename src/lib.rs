use egglog::ast::Parser;
use egglog::prelude::{RustSpan, Span, add_base_sort};
pub use egglog::*;
use std::sync::Arc;

mod rational;
pub use rational::*;
mod scheduling;
pub use scheduling::*;
mod fresh_macro;

mod set_cost;
pub use set_cost::*;
mod size;
pub use size::*;

// Sugar modules using parse-time macros
mod sugar;
pub use sugar::*;

pub fn new_experimental_egraph() -> EGraph {
    let mut egraph = EGraph::default();

    // Set up the parser with experimental parse-time macros
    egraph.parser = experimental_parser();

    add_base_sort(&mut egraph, RationalSort, span!()).unwrap();
    add_set_cost(&mut egraph);
    egraph.add_primitive(GetSizePrimitive);

    // Register the fresh! macro
    egraph
        .command_macros
        .register(Arc::new(fresh_macro::FreshMacro::new()));

    egraph
}

// Create a parser with experimental macros
pub fn experimental_parser() -> Parser {
    let mut parser = Parser::default();
    parser.add_command_macro(Arc::new(sugar::For));
    parser.add_command_macro(Arc::new(sugar::WithRuleset));
    parser
}
