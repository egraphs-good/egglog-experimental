//! Ordinary Rust authoring backed directly by generated protobuf records.
//!
//! This initial subset supports equality sorts/constructors, exact selectors,
//! callback rewrites, named flat rulesets and byte-backed register/check/extract.
//! Scalar builtin APIs await engine-owned Rust catalog metadata. Foreign open
//! binders, arbitrary declarations, frozen graphs and general schedules are not
//! accepted yet; no source/AST execution fallback exists.
use egglog::proto as pb;
mod close;
mod decl;
mod expr;
mod rule;
mod selector;
mod session;
mod storage;

pub use decl::SortRef;
pub use egglog_experimental_typed_macros::{constructor, declarations, sort};
pub use expr::{EgglogValue, EqualitySort, var};
pub use rule::{Fact, Rule, Ruleset, eq, rewrite, ruleset};
pub use selector::get_args;
pub use session::EGraph;

/// Authoring, decoding or structured engine failure.
#[derive(Debug)]
pub enum TypedError {
    /// Invalid or currently unsupported authored program.
    Invalid(String),
    /// A result does not have the requested concrete representation.
    Decode(String),
    /// The byte engine returned its structured failure unchanged.
    Engine(Box<pb::Error>),
}
impl std::fmt::Display for TypedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Invalid(s) | Self::Decode(s) => f.write_str(s),
            Self::Engine(e) => write!(f, "engine error {}: {}", e.code, e.message),
        }
    }
}
impl std::error::Error for TypedError {}

/// Common authoring types, declaration macros and operations.
pub mod prelude {
    pub use super::{
        EGraph, EgglogValue, EqualitySort, Fact, Rule, Ruleset, TypedError, constructor,
        declarations, eq, get_args, rewrite, ruleset, sort, var,
    };
}

#[doc(hidden)]
pub mod __private {
    pub use super::{
        decl::Callable,
        expr::{Expr, ValueInput, fresh_scope, variable},
    };
}

#[cfg(test)]
mod tests;
