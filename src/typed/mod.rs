//! Typed, portable Rust expressions executed by egglog's ordinary AST frontend.
//!
//! Expressions describe computations. [`let_`] explicitly captures a result;
//! ordinary Rust clones preserve syntax sharing without capturing evaluation.
//! Ordinary free and inherent calls accept inputs through [`Into`]. Recognized
//! binary operator declarations also accept an RHS convertible to their declared
//! operand sort, for either owned or borrowed LHS values. Define concrete [`From`]
//! implementations to choose application constructors; conversions are not
//! automatically composed, and reverse primitive-left operators are not generated.
//! Unary constructors can opt into reverse [`TryFrom`] inspection with
//! `#[constructor(try_from)]` or `#[constructor(try_from(i64))]`. Conversion
//! unwraps that exact call; it never evaluates or chooses an e-class alternative.

macro_rules! for_arities {
    ($callback:ident $(; $($extra:ident:$marker:ident:$n:tt),+)? ) => {
        for_arities!(@ $callback []; A0:M0:0,A1:M1:1,A2:M2:2,A3:M3:3,A4:M4:4,A5:M5:5,A6:M6:6,A7:M7:7,A8:M8:8,A9:M9:9,A10:M10:10,A11:M11:11,A12:M12:12,A13:M13:13,A14:M14:14,A15:M15:15,A16:M16:16,A17:M17:17,A18:M18:18,A19:M19:19,A20:M20:20,A21:M21:21,A22:M22:22,A23:M23:23,A24:M24:24,A25:M25:25,A26:M26:26,A27:M27:27,A28:M28:28,A29:M29:29,A30:M30:30,A31:M31:31 $(,$($extra:$marker:$n),+)?);
    };
    (@ $callback:ident [$($done:ident:$marker:ident:$n:tt,)*]; $a:ident:$m:ident:$i:tt $(,$rest:ident:$r:ident:$j:tt)*) => {
        $callback!($($done:$marker:$n,)* $a:$m:$i);
        for_arities!(@ $callback [$($done:$marker:$n,)* $a:$m:$i,]; $($rest:$r:$j),*);
    };
    (@ $callback:ident [$($done:ident:$marker:ident:$n:tt,)*];) => {};
}

pub mod builtins;
mod decl;
mod expr;
mod freeze;
mod lower;
mod rule;
mod selector;
mod session;
pub mod tutorial;

pub(crate) use decl::CallableRef;
pub use decl::SortRef;
pub use egglog::extract::DefaultCost;
pub use egglog_experimental_typed_macros::{
    constructor, declarations, function, relation, ruleset, sort,
};
pub use egglog_reports::RunReport;
pub use expr::{EgglogValue, EqualitySort, let_, var};
pub use freeze::*;
pub use rule::*;
pub use selector::{CallRoot, SelectCall, SelectedArgs, get_args};
pub use session::*;

/// Imports the typed authoring and execution vocabulary.
pub mod prelude {
    pub use super::{
        Action, DecodeError, EGraph, EGraphOptions, EgglogValue, EqualitySort, Fact, FreezeLimits,
        FrozenEGraph, LoweringLimits, Relation, Rule, Ruleset, RunReport, Schedule, SortRef,
        TableRow, TableSnapshot, TypedError, birewrite, constructor, declarations, delete, eq,
        function, get_args, let_, ne, panic, relation, rewrite, rule, ruleset, sequence, set, sort,
        subsume, union, var,
    };
}

/// Macro expansion support, not an independent authoring or execution API.
#[doc(hidden)]
pub mod __private {
    pub use super::decl::{
        CallKind, CallSyntax, CallableDef, CallableRef, DefinitionSource, SortKind,
    };
    pub use super::expr::{Expr, Identity, NodeKind, ValueInput, variable};
    pub use egglog::ast::{Literal, RustSpan, Span};
    pub use std::any::TypeId;
    pub use std::sync::{Arc, OnceLock};
}

#[derive(Debug)]
/// A wrapper validation, native execution, or typed observation failure.
pub enum TypedError {
    /// An invalid portable authoring context, rejected before execution.
    Invalid(String),
    /// An explicit lowering or observation budget was exceeded.
    LoweringLimit(String),
    /// A previous native failure requires restoration of a healthy scope.
    NeedsRestore,
    /// The failing native command and its confirmed successful prefix.
    Core {
        /// Underlying native error, including its source span when available.
        source: egglog::Error,
        /// Zero-based emitted command index within this method.
        command: usize,
        /// Number of emitted commands confirmed successful before the failure.
        completed: usize,
    },
    /// An unexpected or unsupported native result representation.
    Decode(String),
    /// A requested root is not available in the observation domain.
    UnresolvedRoot {
        /// Ordered root index for a batch operation, if applicable.
        index: Option<usize>,
        /// Why the root could not be resolved.
        reason: String,
    },
}

impl std::fmt::Display for TypedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Invalid(s) | Self::LoweringLimit(s) | Self::Decode(s) => f.write_str(s),
            Self::NeedsRestore => {
                f.write_str("typed egraph needs restoration to a healthy pushed scope")
            }
            Self::Core {
                source,
                command,
                completed,
            } => write!(
                f,
                "command {command} failed after {completed} completed commands: {source}"
            ),
            Self::UnresolvedRoot { index, reason } => {
                write!(f, "unresolved root {index:?}: {reason}")
            }
        }
    }
}
impl std::error::Error for TypedError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Core { source, .. } => Some(source),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Explicit decoding failed for a portable expression or observed scalar/container.
pub struct DecodeError(#[doc = "Explanation of the unsupported or mismatched value."] pub String);
impl std::fmt::Display for DecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for DecodeError {}
impl From<DecodeError> for TypedError {
    fn from(error: DecodeError) -> Self {
        Self::Decode(error.0)
    }
}

#[track_caller]
pub(crate) fn origin() -> egglog::ast::Span {
    let caller = std::panic::Location::caller();
    egglog::ast::Span::Rust(std::sync::Arc::new(egglog::ast::RustSpan {
        file: caller.file(),
        line: caller.line(),
        column: caller.column(),
    }))
}
