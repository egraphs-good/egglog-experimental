//! Ordinary Rust authoring backed directly by generated protobuf records.
//!
//! This initial subset supports equality sorts/constructors, exact selectors,
//! callback rewrites, named flat rulesets and byte-backed register/check/extract.
//! I64/F64 literals/addition and generic Vec operations use engine-owned metadata.
//! Ordered Vec value decoding retains child expression ownership. Foreign open
//! binders, arbitrary declarations, frozen graphs and general schedules are not
//! accepted yet; no source/AST execution fallback exists.
//!
//! Scalar conversions and constructor arguments are checked by Rust. Calls
//! author symbolic expressions; they do not evaluate those expressions.
//!
//! ```
//! use egglog_experimental::typed::{builtins::{F64, I64}, prelude::*};
//!
//! #[sort]
//! pub struct Term;
//! #[declarations]
//! impl Term {
//!     pub fn Num(value: I64) -> Self;
//!     pub fn Pair(left: Term, right: Term) -> Self;
//! }
//!
//! let integer = I64::from(7_i64);
//! let _: I64 = &integer + I64::from(&11_i64);
//! let float = F64::from(1.5_f64);
//! let _: F64 = &float + F64::from(&2.5_f64);
//! let left = Term::Num(7_i64);
//! let right = Term::Num(&integer);
//! let _: Term = Term::Pair(&left, right);
//! ```
//!
//! Vector element and result types remain precise through generic functions,
//! borrowed elements, empty iterators, and nested vectors:
//!
//! ```
//! use egglog_experimental::typed::{builtins::{I64, Vec as EVec}, EgglogValue};
//!
//! fn singleton<T: EgglogValue>(value: impl Into<T>) -> EVec<T> {
//!     EVec::<T>::of([value])
//! }
//! fn first<T: EgglogValue>(values: &EVec<T>) -> T {
//!     values.get(0_i64)
//! }
//!
//! let integer = I64::from(7_i64);
//! let values = EVec::<I64>::of([7_i64, 11_i64]);
//! let _: EVec<I64> = EVec::<I64>::of([&integer, &integer]);
//! let _: EVec<I64> = singleton::<I64>(&integer);
//! let _: I64 = first(&values);
//! let _: EVec<EVec<I64>> = singleton::<EVec<I64>>(&values);
//! let _: EVec<I64> = EVec::<I64>::empty();
//! let _: EVec<I64> = EVec::<I64>::of(std::iter::empty::<I64>());
//! ```
//!
//! Integer and floating-point sorts cannot be mixed in arithmetic:
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64};
//! let _ = I64::from(1_i64) + F64::from(2.0_f64);
//! ```
//!
//! Literal conversion does not implicitly cast between host numeric types:
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::I64;
//! let _ = I64::from(1.5_f64);
//! ```
//!
//! A vector's element sort constrains every iterator item:
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64, Vec as EVec};
//! let _ = EVec::<I64>::of([F64::from(1.5_f64)]);
//! ```
//!
//! Lookup requires an integer index and returns the vector's element type:
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64, Vec as EVec};
//! let _ = EVec::<I64>::empty().get(F64::from(0.0_f64));
//! ```
//!
//! ```compile_fail,E0308
//! use egglog_experimental::typed::builtins::{F64, I64, Vec as EVec};
//! let _: F64 = EVec::<I64>::empty().get(0_i64);
//! ```
//!
//! `of` takes one iterable, rather than a Rust variadic argument list:
//!
//! ```compile_fail,E0061
//! use egglog_experimental::typed::builtins::{I64, Vec as EVec};
//! let _ = EVec::<I64>::of([1_i64], [2_i64]);
//! ```
//!
//! The declared `Num(I64)` constructor also enforces its input sort and arity:
//!
//! ```compile_fail,E0277
//! # use egglog_experimental::typed::{builtins::{F64, I64}, prelude::*};
//! # #[sort]
//! # pub struct Term;
//! # #[declarations]
//! # impl Term { pub fn Num(value: I64) -> Self; }
//! let _ = Term::Num(F64::from(1.5_f64));
//! ```
//!
//! ```compile_fail,E0061
//! # use egglog_experimental::typed::{builtins::I64, prelude::*};
//! # #[sort]
//! # pub struct Term;
//! # #[declarations]
//! # impl Term { pub fn Num(value: I64) -> Self; }
//! let _ = Term::Num();
//! ```
use egglog::proto as pb;
pub mod builtins;
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
