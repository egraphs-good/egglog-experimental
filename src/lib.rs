//! # egglog-experimental
//!
//! This crate layers several experimental features on top of the core
//! [`egglog`](https://github.com/egraphs-good/egglog) language and runtime.
//! It can serve as a standard library when building equality
//! saturation workflows in Rust.
//!
//! ## Implemented extensions
//!
//! - Language and values: exact rationals, one-shot `for` rules, grouped
//!   `with-ruleset` declarations, body-defined primitives, and fresh values in
//!   rule actions.
//! - Scheduling and extraction: extended schedules, named back-off schedulers,
//!   dynamic costs, multi-extraction, and `keep-best` compaction.
//! - Inspection: table-size queries and per-table column and out-degree
//!   statistics.
//!
//! The [feature guide](https://github.com/egraphs-good/egglog-experimental#features)
//! gives concise syntax and runnable examples. This crate's modules document
//! the Rust APIs behind the extensions.
//!
use egglog::ast::Parser;
use egglog::prelude::add_base_sort;
pub use egglog::*;
use std::sync::Arc;

pub mod rational;
pub use rational::*;
pub mod scheduling;
pub use scheduling::*;
mod fresh_macro;

mod set_cost;
pub use set_cost::*;
mod multi_extract;
pub use multi_extract::*;
mod size;
pub use size::*;
mod primitive;
mod table_rows;
mod table_stats;
pub use table_stats::*;

// Sugar modules using parse-time macros
mod sugar;
pub use sugar::*;

mod keep_best;
pub use keep_best::KeepBestCommand;

/// Creates an [`EGraph`] with every egglog-experimental extension registered.
pub fn new_experimental_egraph() -> EGraph {
    let mut egraph = EGraph::default();

    // Set up the parser with experimental parse-time macros
    egraph.parser = experimental_parser();

    // Rational support
    add_base_sort(&mut egraph, RationalSort, span!()).unwrap();

    // Support for set cost
    add_set_cost(&mut egraph);
    egraph.add_read_primitive(GetSizePrimitive, None);

    // unstable-fresh! macro
    egraph
        .command_macros_mut()
        .register(Arc::new(fresh_macro::FreshMacro::new()));

    // scheduler support
    egraph
        .add_command("run-schedule".into(), Arc::new(RunExtendedSchedule))
        .unwrap();
    egraph
        .add_command("let-scheduler".into(), Arc::new(LetSchedulerCommand))
        .unwrap();

    egraph
        .add_command(
            "multi-extract".into(),
            Arc::new(MultiExtract::new(DynamicCostModel)),
        )
        .unwrap();

    egraph
        .add_command("keep-best".into(), Arc::new(KeepBestCommand))
        .unwrap();

    // Per-column statistics for function tables.
    egraph
        .add_command("print-table-stats".into(), Arc::new(PrintTableStatsCommand))
        .unwrap();
    egraph
        .add_command("primitive".into(), Arc::new(primitive::RegisterPrimitive))
        .unwrap();
    egraph
}

/// Creates a parser with the `for` and `with-ruleset` parse-time macros.
///
/// Use [`new_experimental_egraph`] to register all runtime extensions as well.
pub fn experimental_parser() -> Parser {
    let mut parser = Parser::default();
    parser.add_command_macro(Arc::new(sugar::For));
    parser.add_command_macro(Arc::new(sugar::WithRuleset));
    parser
}
