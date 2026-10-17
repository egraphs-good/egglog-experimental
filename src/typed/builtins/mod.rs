//! Catalog-generated scalar wrappers. Structural equality compares authored
//! payload bits/syntax, not the native engine's numeric equality relation.
mod function;
use function::function_application;
pub use function::{Function, FunctionArgs};
include!("generated.rs");
