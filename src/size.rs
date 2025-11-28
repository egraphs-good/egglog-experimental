use std::convert::TryFrom;

use egglog::{
    ExecutionState, Primitive, Value,
    constraint::{SimpleTypeConstraint, TypeConstraint},
    prelude::BaseSort,
    prelude::{I64Sort, Span},
};

#[derive(Clone)]
pub struct GetSizePrimitive;

impl Primitive for GetSizePrimitive {
    fn name(&self) -> &str {
        "get-size!"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        SimpleTypeConstraint::new(self.name(), vec![I64Sort.to_arcsort()], span.clone()).into_box()
    }

    fn apply(&self, exec_state: &mut ExecutionState, args: &[Value]) -> Option<Value> {
        if !args.is_empty() {
            return None;
        }
        let total_size: usize = exec_state
            .table_ids()
            .map(|table_id| exec_state.get_table(table_id).len())
            .sum();
        let total_size = i64::try_from(total_size).ok()?;
        Some(exec_state.base_values().get::<i64>(total_size))
    }
}
