use std::any::TypeId;

use egglog::ast::Expr;
use egglog::constraint::{Constraint, TypeConstraint};
use egglog::prelude::{ContainerSort, Span};
use egglog::sort::{ContainerValues, FunctionContainer, FunctionSort, Presort, ValueRebuilder};
use egglog::{
    ArcSort, AtomTerm, ContainerValue, Core, EGraph, Primitive, PurePrim, PureState, TermDag,
    TermId, TypeError, TypeInfo, Value, add_primitive,
};

use crate::type_constraints::exact_signatures;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct MaybeContainer {
    do_rebuild: bool,
    data: Option<Value>,
}

impl ContainerValue for MaybeContainer {
    fn rebuild_contents(&mut self, rebuilder: &dyn ValueRebuilder) -> bool {
        if !self.do_rebuild {
            return false;
        }
        let Some(old) = self.data else {
            return false;
        };
        let new = rebuilder.rebuild_val(old);
        self.data = Some(new);
        old != new
    }

    fn iter(&self) -> impl Iterator<Item = Value> + '_ {
        self.data.iter().copied()
    }
}

#[derive(Clone, Debug)]
pub(crate) struct MaybeSort {
    name: String,
    element: ArcSort,
}

impl Presort for MaybeSort {
    fn presort_name() -> &'static str {
        "Maybe"
    }

    fn reserved_primitives() -> Vec<&'static str> {
        vec![
            "maybe-none",
            "maybe-some",
            "maybe-unwrap",
            "maybe-unwrap-or",
            "unstable-catch",
            "unstable-maybe-match",
        ]
    }

    fn make_sort(
        typeinfo: &mut TypeInfo,
        name: String,
        args: &[Expr],
        span: Span,
    ) -> Result<ArcSort, TypeError> {
        if let [Expr::Var(element_span, element)] = args {
            let element = typeinfo
                .get_sort_by_name(element)
                .ok_or_else(|| TypeError::UndefinedSort(element.clone(), element_span.clone()))?;
            Ok(Self {
                name,
                element: element.clone(),
            }
            .to_arcsort())
        } else {
            Err(TypeError::BadPresortArguments(
                Self::presort_name().to_owned(),
                span,
            ))
        }
    }
}

impl ContainerSort for MaybeSort {
    type Container = MaybeContainer;

    fn name(&self) -> &str {
        &self.name
    }

    fn is_eq_container_sort(&self) -> bool {
        self.element.is_eq_sort() || self.element.is_eq_container_sort()
    }

    fn inner_sorts(&self) -> Vec<ArcSort> {
        vec![self.element.clone()]
    }

    fn inner_values(
        &self,
        container_values: &ContainerValues,
        value: Value,
    ) -> Vec<(ArcSort, Value)> {
        container_values
            .get_val::<MaybeContainer>(value)
            .unwrap()
            .data
            .iter()
            .map(|value| (self.element.clone(), *value))
            .collect()
    }

    fn register_primitives(&self, egraph: &mut EGraph) {
        let maybe = self.clone().to_arcsort();

        add_primitive!(egraph, "maybe-some" = {self.clone(): MaybeSort} |value: # (self.element.clone())| -> @MaybeContainer (maybe) {
            MaybeContainer {
                do_rebuild: self.ctx.is_eq_container_sort(),
                data: Some(value),
            }
        });
        add_primitive!(egraph, "maybe-unwrap" = |value: @MaybeContainer (maybe)| -?> # (self.element.clone()) {
            value.data
        });
        add_primitive!(egraph, "maybe-unwrap-or" = |value: @MaybeContainer (maybe), default: # (self.element.clone())| -> # (self.element.clone()) {
            value.data.unwrap_or(default)
        });
    }

    fn reconstruct_termdag(
        &self,
        _container_values: &ContainerValues,
        _value: Value,
        termdag: &mut TermDag,
        element_terms: Vec<TermId>,
    ) -> TermId {
        match element_terms.as_slice() {
            [] => termdag.app("maybe-none".to_owned(), vec![]),
            [value] => termdag.app("maybe-some".to_owned(), vec![*value]),
            _ => unreachable!("Maybe containers contain at most one value"),
        }
    }

    fn serialized_name(&self, container_values: &ContainerValues, value: Value) -> String {
        if container_values
            .get_val::<MaybeContainer>(value)
            .unwrap()
            .data
            .is_some()
        {
            "maybe-some".to_owned()
        } else {
            "maybe-none".to_owned()
        }
    }
}

#[derive(Clone, Copy)]
struct MaybeNone;

impl Primitive for MaybeNone {
    fn name(&self) -> &str {
        "maybe-none"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        Box::new(MaybeNoneTypeConstraint { span: span.clone() })
    }
}

impl PurePrim for MaybeNone {
    fn apply<'a, 'db>(&self, mut state: PureState<'a, 'db>, _args: &[Value]) -> Option<Value> {
        Some(state.register_container(MaybeContainer {
            // Empty values have no contents to rebuild. Using one canonical
            // representation also makes `none` independent of its element sort.
            do_rebuild: false,
            data: None,
        }))
    }
}

struct MaybeNoneTypeConstraint {
    span: Span,
}

impl TypeConstraint for MaybeNoneTypeConstraint {
    fn get(
        &self,
        arguments: &[AtomTerm],
        typeinfo: &TypeInfo,
    ) -> Vec<Box<dyn Constraint<AtomTerm, ArcSort>>> {
        let signatures = typeinfo
            .get_arcsorts_by(|sort| sort.value_type() == Some(TypeId::of::<MaybeContainer>()))
            .into_iter()
            .map(|maybe| vec![maybe]);
        // `none` has no input from which to infer its nominal Maybe alias. If
        // multiple aliases remain compatible, surrounding context must select
        // one; picking the first would make unrelated sort declarations change
        // the meaning of a program.
        exact_signatures("maybe-none", &self.span, arguments, 1, signatures)
    }
}

#[derive(Clone, Copy)]
struct Catch {
    do_rebuild: bool,
}

impl Primitive for Catch {
    fn name(&self) -> &str {
        "unstable-catch"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        Box::new(CatchTypeConstraint {
            do_rebuild: self.do_rebuild,
            span: span.clone(),
        })
    }
}

impl PurePrim for Catch {
    fn apply<'a, 'db>(&self, mut state: PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let function = state
            .container_values()
            .get_val::<FunctionContainer>(args[0])?
            .clone();
        let data = state.apply_function(&function, &[]);
        Some(state.register_container(MaybeContainer {
            do_rebuild: self.do_rebuild && data.is_some(),
            data,
        }))
    }
}

struct CatchTypeConstraint {
    do_rebuild: bool,
    span: Span,
}

impl TypeConstraint for CatchTypeConstraint {
    fn get(
        &self,
        arguments: &[AtomTerm],
        typeinfo: &TypeInfo,
    ) -> Vec<Box<dyn Constraint<AtomTerm, ArcSort>>> {
        let functions = typeinfo.get_sorts::<FunctionSort>();
        let signatures = typeinfo
            .get_arcsorts_by(|sort| {
                sort.value_type() == Some(TypeId::of::<MaybeContainer>())
                    && sort.is_eq_container_sort() == self.do_rebuild
            })
            .into_iter()
            .flat_map(|maybe| {
                let element = maybe.inner_sorts()[0].clone();
                functions
                    .iter()
                    .filter(move |function| {
                        function.inputs().is_empty() && function.output().name() == element.name()
                    })
                    .cloned()
                    .map(move |function| vec![function as ArcSort, maybe.clone()])
            });
        exact_signatures("unstable-catch", &self.span, arguments, 2, signatures)
    }
}

#[derive(Clone, Copy)]
struct MaybeMatch;

impl Primitive for MaybeMatch {
    fn name(&self) -> &str {
        "unstable-maybe-match"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        Box::new(MaybeMatchTypeConstraint { span: span.clone() })
    }
}

impl PurePrim for MaybeMatch {
    fn apply<'a, 'db>(&self, mut state: PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let maybe = state
            .container_values()
            .get_val::<MaybeContainer>(args[0])?
            .clone();
        match maybe.data {
            Some(value) => {
                let function = state
                    .container_values()
                    .get_val::<FunctionContainer>(args[1])?
                    .clone();
                state.apply_function(&function, &[value])
            }
            None => Some(args[2]),
        }
    }
}

struct MaybeMatchTypeConstraint {
    span: Span,
}

impl TypeConstraint for MaybeMatchTypeConstraint {
    fn get(
        &self,
        arguments: &[AtomTerm],
        typeinfo: &TypeInfo,
    ) -> Vec<Box<dyn Constraint<AtomTerm, ArcSort>>> {
        let functions = typeinfo.get_sorts::<FunctionSort>();
        let signatures = typeinfo
            .get_arcsorts_by(|sort| sort.value_type() == Some(TypeId::of::<MaybeContainer>()))
            .into_iter()
            .flat_map(|maybe| {
                let element = maybe.inner_sorts()[0].clone();
                functions
                    .iter()
                    .filter(move |function| {
                        function.inputs().len() == 1
                            && function.inputs()[0].name() == element.name()
                    })
                    .cloned()
                    .map(move |function| {
                        let output = function.output();
                        vec![maybe.clone(), function as ArcSort, output.clone(), output]
                    })
            });
        exact_signatures("unstable-maybe-match", &self.span, arguments, 4, signatures)
    }
}

pub(crate) fn add_maybe(egraph: &mut EGraph) {
    egraph
        .type_info()
        .add_presort::<MaybeSort>(egglog::span!())
        .unwrap();
    egraph.add_pure_primitive(MaybeNone, None);
    egraph.add_pure_primitive(Catch { do_rebuild: false }, None);
    egraph.add_pure_primitive(Catch { do_rebuild: true }, None);
    egraph.add_pure_primitive(MaybeMatch, None);
}
