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

    fn builtin_definitions() -> Vec<egglog::proto::Program> {
        use egglog::proto as pb;
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
            let receiver = matches!(key, "unwrap" | "unwrap_or");
            let parameters = inputs.iter().enumerate().skip(usize::from(receiver));
            pb::Program {
                ir_version: 1,
                sorts: vec![
                    pb::Sort {
                        kind: Some(pb::sort::Kind::Var(0)),
                        ..Default::default()
                    },
                    pb::Sort {
                        kind: Some(pb::sort::Kind::Family(pb::HostSort {
                            name: "Maybe".into(),
                            args: vec![0],
                        })),
                        ..Default::default()
                    },
                ],
                declarations: vec![
                    pb::Declaration {
                        kind: Some(pb::declaration::Kind::HostSortFamily(pb::HostSortFamily {
                            name: "Maybe".into(),
                            arity: 1,
                            bindings: Some(pb::SortBindings {
                                python: Some(pb::TypeBinding {
                                    path: vec!["egglog".into(), "builtins".into(), "Maybe".into()],
                                    type_params: vec!["T".into()],
                                }),
                                rust: Some(pb::TypeBinding {
                                    path: vec![
                                        "egglog_experimental".into(),
                                        "typed".into(),
                                        "builtins".into(),
                                        "Maybe".into(),
                                    ],
                                    type_params: vec!["T".into()],
                                }),
                                ..Default::default()
                            }),
                        })),
                        ..Default::default()
                    },
                    pb::Declaration {
                        kind: Some(pb::declaration::Kind::HostPrimitive(pb::HostPrimitive {
                            name: format!("egglog.experimental.maybe.{key}"),
                            typing: Some(pb::host_primitive::Typing::Signature(
                                pb::GenericSignature {
                                    type_params: vec!["T".into()],
                                    inputs: inputs
                                        .iter()
                                        .map(|(name, sort)| pb::Arg {
                                            name: (*name).into(),
                                            sort: *sort,
                                        })
                                        .collect(),
                                    output: Some(output),
                                    ..Default::default()
                                },
                            )),
                        })),
                        bindings: Some(pb::CallableBindings {
                            python: Some(pb::PythonBindings {
                                views: vec![pb::PythonCallable {
                                    kind: if receiver {
                                        pb::PythonCallKind::Method
                                    } else {
                                        pb::PythonCallKind::ClassMethod
                                    }
                                    .into(),
                                    path: vec![key.into()],
                                    owner: Some(pb::BindingOwner {
                                        kind: Some(pb::binding_owner::Kind::Sort(1)),
                                    }),
                                    receiver: receiver.then_some(0),
                                    params: parameters
                                        .clone()
                                        .map(|(i, (name, _))| pb::PythonParameter {
                                            core_input: Some(i as u32),
                                            name: (*name).into(),
                                            default_expr: None,
                                        })
                                        .collect(),
                                    ..Default::default()
                                }],
                            }),
                            rust: Some(pb::RustBindings {
                                views: vec![pb::RustCallable {
                                    path: vec![key.into()],
                                    owner: Some(pb::BindingOwner {
                                        kind: Some(pb::binding_owner::Kind::Sort(1)),
                                    }),
                                    receiver: receiver.then_some(pb::RustReceiver {
                                        core_input: Some(0),
                                        borrowed: true,
                                    }),
                                    params: parameters
                                        .map(|(i, (name, _))| pb::RustParameter {
                                            core_input: Some(i as u32),
                                            name: (*name).into(),
                                            borrowed: false,
                                        })
                                        .collect(),
                                    ..Default::default()
                                }],
                            }),
                            egglog: Some(pb::EgglogBindings {
                                views: vec![pb::EgglogCallable {
                                    symbol: alias.into(),
                                    datatype_member: false,
                                }],
                            }),
                        }),
                        ..Default::default()
                    },
                ],
                ..Default::default()
            }
        })
        .collect();
        definitions.push(signature_definition(
            "egglog.experimental.maybe.catch",
            "unstable-catch",
            vec![
                pb::Sort {
                    kind: Some(pb::sort::Kind::Var(0)),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "Maybe".into(),
                        args: vec![0],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Func(pb::FuncSort {
                        params: vec![],
                        result: 0,
                    })),
                    ..Default::default()
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
                pb::Sort {
                    kind: Some(pb::sort::Kind::Var(0)),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Var(1)),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "Maybe".into(),
                        args: vec![0],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Func(pb::FuncSort {
                        params: vec![0],
                        result: 1,
                    })),
                    ..Default::default()
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
        egraph
            .type_info()
            .register_builtin_sort("Maybe", maybe.clone(), vec![self.element.clone()])
            .unwrap();
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
