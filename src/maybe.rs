//! An optional-value container and control-flow primitives.
//!
//! `Maybe[T]` stores either no value or one value of `T`. This module provides
//! construction, partial unwrapping, defaulting, undefined-result capture, and
//! higher-order branching over those values.

use std::any::TypeId;

use egglog::ast::Expr;
use egglog::builtin::BuiltinInstance;
use egglog::constraint::{Constraint, TypeConstraint};
use egglog::prelude::{ContainerSort, Span};
use egglog::sort::{ContainerValues, FunctionContainer, FunctionSort, Presort, ValueRebuilder};
use egglog::{
    ArcSort, AtomTerm, ContainerValue, Core, EGraph, Primitive, PurePrim, PureState, TermDag,
    TermId, TypeError, TypeInfo, Value, add_primitive,
};

use crate::type_constraints::{exact_signatures, signature_definition};

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
    fn container_type() -> Option<TypeId> {
        Some(TypeId::of::<MaybeContainer>())
    }

    fn family_description() -> Option<egglog::builtin::FamilyDescription> {
        Some(egglog::builtin::FamilyDescription {
            name: "Maybe".into(),
            arity: 1,
        })
    }

    fn builtin_definitions() -> Vec<egglog::builtin::BuiltinDescription> {
        use egglog::builtin::SortPattern;
        let patterns = vec![
            SortPattern::Param(0),
            SortPattern::Family {
                name: "Maybe".into(),
                args: vec![SortPattern::Param(0)],
            },
        ];
        let mut definitions: Vec<_> = [
            ("none", "maybe-none", vec![], 1),
            ("some", "maybe-some", vec![("value", 0)], 1),
            ("unwrap", "maybe-unwrap", vec![("maybe", 1)], 0),
            (
                "unwrap_or",
                "maybe-unwrap-or",
                vec![("maybe", 1), ("default", 0)],
                0,
            ),
        ]
        .into_iter()
        .map(|(key, alias, inputs, output)| {
            signature_definition(
                &format!("egglog.experimental.maybe.{key}"),
                alias,
                patterns.clone(),
                &["T"],
                &inputs,
                output,
            )
        })
        .collect();
        definitions.push(signature_definition(
            "egglog.experimental.maybe.catch",
            "unstable-catch",
            vec![
                SortPattern::Param(0),
                SortPattern::Family {
                    name: "Maybe".into(),
                    args: vec![SortPattern::Param(0)],
                },
                SortPattern::Function {
                    inputs: vec![],
                    output: Box::new(SortPattern::Param(0)),
                },
            ],
            &["T"],
            &[("thunk", 2)],
            1,
        ));
        definitions.push(signature_definition(
            "egglog.experimental.maybe.match",
            "unstable-maybe-match",
            vec![
                SortPattern::Param(0),
                SortPattern::Param(1),
                SortPattern::Family {
                    name: "Maybe".into(),
                    args: vec![SortPattern::Param(0)],
                },
                SortPattern::Function {
                    inputs: vec![SortPattern::Param(0)],
                    output: Box::new(SortPattern::Param(1)),
                },
            ],
            &["T", "U"],
            &[("maybe", 2), ("on_some", 3), ("default", 1)],
            1,
        ));
        definitions
    }

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
        typeinfo: &TypeInfo,
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

    fn family_instance(&self) -> Option<egglog::builtin::NativeFamilyInstance> {
        Some(egglog::builtin::NativeFamilyInstance {
            family: "Maybe".into(),
            parameters: vec![self.element.clone()],
        })
    }

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
        let none = egraph
            .type_info()
            .instantiate_builtin("egglog.experimental.maybe.none", &maybe)
            .unwrap();
        let some = egraph
            .type_info()
            .instantiate_builtin("egglog.experimental.maybe.some", &maybe)
            .unwrap();
        let unwrap = egraph
            .type_info()
            .instantiate_builtin("egglog.experimental.maybe.unwrap", &maybe)
            .unwrap();
        let unwrap_or = egraph
            .type_info()
            .instantiate_builtin("egglog.experimental.maybe.unwrap_or", &maybe)
            .unwrap();
        egraph.add_pure_primitive(MaybeNone { instance: none }, None);

        add_primitive!(egraph, "maybe-some" [instance = some] = {self.clone(): MaybeSort} |value: #| -> @MaybeContainer {
            MaybeContainer {
                do_rebuild: self.ctx.is_eq_container_sort(),
                data: Some(value),
            }
        });
        add_primitive!(egraph, "maybe-unwrap" [instance = unwrap] = |value: @MaybeContainer| -?> # {
            value.data
        });
        add_primitive!(egraph, "maybe-unwrap-or" [instance = unwrap_or] = |value: @MaybeContainer, default: #| -> # {
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

#[derive(Clone)]
struct MaybeNone {
    instance: BuiltinInstance,
}

impl Primitive for MaybeNone {
    fn name(&self) -> &str {
        "maybe-none"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        self.instance.type_constraints(span)
    }

    fn builtin_instance(&self) -> Option<&BuiltinInstance> {
        Some(&self.instance)
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

/// `(unstable-catch thunk)` evaluates a zero-argument `UnstableFn`, returning
/// `maybe-some` when the application is defined and `maybe-none` otherwise.
#[derive(Clone)]
struct Catch {
    do_rebuild: bool,
    instance: BuiltinInstance,
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

    fn builtin_instance(&self) -> Option<&BuiltinInstance> {
        Some(&self.instance)
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

#[derive(Clone)]
struct MaybeMatch {
    instance: BuiltinInstance,
}

impl Primitive for MaybeMatch {
    fn name(&self) -> &str {
        "unstable-maybe-match"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        Box::new(MaybeMatchTypeConstraint { span: span.clone() })
    }

    fn builtin_instance(&self) -> Option<&BuiltinInstance> {
        Some(&self.instance)
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
    let catch = egraph
        .type_info()
        .instantiate_builtin_open("egglog.experimental.maybe.catch")
        .unwrap();
    for do_rebuild in [false, true] {
        egraph.add_pure_primitive(
            Catch {
                do_rebuild,
                instance: catch.clone(),
            },
            None,
        );
    }
    let instance = egraph
        .type_info()
        .instantiate_builtin_open("egglog.experimental.maybe.match")
        .unwrap();
    egraph.add_pure_primitive(MaybeMatch { instance }, None);
}
