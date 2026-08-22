use std::any::TypeId;

use egglog::constraint::{Constraint, TypeConstraint};
use egglog::prelude::Span;
use egglog::sort::{FunctionContainer, FunctionSort, MapContainer};
use egglog::{ArcSort, AtomTerm, Core, Primitive, PurePrim, PureState, TypeInfo, Value};

use crate::type_constraints::exact_signatures;

#[derive(Clone, Copy)]
pub(crate) struct MapFoldKv;

impl Primitive for MapFoldKv {
    fn name(&self) -> &str {
        "map-fold-kv"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        Box::new(MapFoldKvTypeConstraint { span: span.clone() })
    }
}

impl PurePrim for MapFoldKv {
    fn apply<'a, 'db>(&self, mut state: PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let function = state
            .container_values()
            .get_val::<FunctionContainer>(args[0])?
            .clone();
        let map = state
            .container_values()
            .get_val::<MapContainer>(args[2])?
            .clone();

        let mut accumulator = args[1];
        // MapContainer orders opaque Values, not logical keys. This order is
        // stable only within the EGraph that owns those Values, so callers
        // should use an order-insensitive callback.
        for (key, value) in map.data {
            accumulator = state.apply_function(&function, &[accumulator, key, value])?;
        }
        Some(accumulator)
    }
}

struct MapFoldKvTypeConstraint {
    span: Span,
}

impl TypeConstraint for MapFoldKvTypeConstraint {
    fn get(
        &self,
        arguments: &[AtomTerm],
        typeinfo: &TypeInfo,
    ) -> Vec<Box<dyn Constraint<AtomTerm, ArcSort>>> {
        let maps = typeinfo
            .get_arcsorts_by(|sort| sort.value_type() == Some(TypeId::of::<MapContainer>()));
        let signatures = typeinfo
            .get_sorts::<FunctionSort>()
            .into_iter()
            .filter(|function| {
                function.inputs().len() == 3
                    && function.inputs()[0].name() == function.output().name()
            })
            .flat_map(|function| {
                let accumulator = function.output();
                let function_for_filter = function.clone();
                maps.iter()
                    .filter(move |map| {
                        let inner = map.inner_sorts();
                        inner.len() == 2
                            && inner[0].name() == function_for_filter.inputs()[1].name()
                            && inner[1].name() == function_for_filter.inputs()[2].name()
                    })
                    .cloned()
                    .map(move |map| {
                        vec![
                            function.clone() as ArcSort,
                            accumulator.clone(),
                            map,
                            accumulator.clone(),
                        ]
                    })
            });
        exact_signatures("map-fold-kv", &self.span, arguments, 4, signatures)
    }
}
