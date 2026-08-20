//! Inspect e-graph table sizes from an egglog expression.
//!
//! `(get-size!)` returns the sum of all non-internal table sizes.
//! `(get-size! "A" "B")` returns the sum for the named tables. The primitive
//! is read-capable, so it can also be used in extended schedule guards and
//! `eval` steps.

use std::convert::TryFrom;

use egglog::{
    Core, Primitive, Read, ReadPrim, ReadState, Value,
    constraint::{AllEqualTypeConstraint, TypeConstraint},
    prelude::BaseSort,
    prelude::{I64Sort, Span, StringSort},
    sort::S,
    util::INTERNAL_SYMBOL_PREFIX,
};

/// Read primitive implementing `(get-size! "table"...)`.
///
/// With no arguments it sums all non-internal tables. String arguments limit
/// the sum to the named tables.
#[derive(Clone)]
pub struct GetSizePrimitive;

impl Primitive for GetSizePrimitive {
    fn name(&self) -> &str {
        "get-size!"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        AllEqualTypeConstraint::new(self.name(), span.clone())
            .with_output_sort(I64Sort.to_arcsort())
            .with_all_arguments_sort(StringSort.to_arcsort())
            .into_box()
    }
}

impl ReadPrim for GetSizePrimitive {
    fn apply<'a, 'db>(&self, state: ReadState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let size: usize = match args {
            [] => state
                .table_sizes()
                .into_iter()
                .filter_map(|(name, size)| {
                    (!name.starts_with(INTERNAL_SYMBOL_PREFIX)).then_some(size)
                })
                .sum(),
            tables => tables
                .iter()
                .map(|value| state.base_values().unwrap::<S>(*value).0)
                .filter_map(|name| state.table_size(&name))
                .sum(),
        };
        let size = i64::try_from(size).ok()?;
        Some(state.base_values().get::<i64>(size))
    }
}
