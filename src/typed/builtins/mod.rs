//! Catalog-generated scalar wrappers. Structural equality compares authored
//! payload bits/syntax, not the native engine's numeric equality relation.
//!
//! Higher-order methods use typed structural function values:
//!
//! ```
//! use egglog_experimental::typed::builtins::{Function, I64, Maybe, Vec};
//! let plus_one = Function::<(I64,), I64>::new(|x| x + I64::from(1))?;
//! let mapped: Vec<I64> = Vec::<I64>::of([1_i64, 2]).map(plus_one);
//! let caught: Maybe<I64> = Maybe::catch(Function::<(), I64>::new(|| I64::from(1) / I64::from(0))?);
//! # Ok::<(), egglog_experimental::typed::TypedError>(())
//! ```
//!
//! Callback input, output and accumulator sorts are checked by Rust:
//!
//! ```compile_fail,E0308
//! use egglog_experimental::typed::builtins::{F64, Function, I64, Vec};
//! Vec::<I64>::of([1_i64]).map(Function::<(F64,), I64>::new(|_| I64::from(1)).unwrap());
//! ```
//! ```compile_fail,E0308
//! use egglog_experimental::typed::builtins::{F64, Function, I64, Map};
//! let callback = Function::<(F64, I64, I64), F64>::new(|a, _, _| a.clone()).unwrap();
//! Map::<I64, I64>::of([(1_i64, 2_i64)]).fold_kv(callback, I64::from(0));
//! ```
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, Function, I64, Maybe};
//! Maybe::<I64>::catch(Function::<(), F64>::new(|| F64::from(1.0)).unwrap());
//! ```
//! ```compile_fail,E0308
//! use egglog_experimental::typed::builtins::{F64, Function, I64, Maybe};
//! let callback = Function::<(I64,), F64>::new(|_| F64::from(1.0)).unwrap();
//! Maybe::<I64>::some(1_i64).match_(callback, I64::from(0));
//! ```
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{bool_ne, F64, I64};
//! bool_ne(I64::from(1), F64::from(1.0));
//! ```
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{subst, I64, Map};
//! subst(I64::from(1), Map::<I64, I64>::empty());
//! ```
mod function;
use function::function_application;
pub use function::{Function, FunctionArgs};
include!("generated.rs");
