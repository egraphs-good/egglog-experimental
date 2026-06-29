use egglog::ast::{Expr, Literal};
use egglog::prelude::ContainerSort;
use egglog::sort::{ContainerValues, F, Presort, ValueRebuilder};
use egglog::{
    ArcSort, ContainerValue, EGraph, Term, TermDag, TermId, TypeError, TypeInfo, Value,
    add_primitive_with_validator,
};
use std::any::TypeId;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MaybeContainer {
    pub do_rebuild: bool,
    pub data: Option<Value>,
}

impl ContainerValue for MaybeContainer {
    fn rebuild_contents(&mut self, rebuilder: &dyn ValueRebuilder) -> bool {
        if self.do_rebuild {
            if let Some(old) = self.data {
                let new = rebuilder.rebuild_val(old);
                self.data = Some(new);
                old != new
            } else {
                false
            }
        } else {
            false
        }
    }

    fn iter(&self) -> impl Iterator<Item = Value> + '_ {
        self.data.iter().copied()
    }
}

#[derive(Clone, Debug)]
pub struct MaybeSort {
    name: String,
    element: ArcSort,
}

impl MaybeSort {
    pub fn element(&self) -> ArcSort {
        self.element.clone()
    }
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
            "maybe-f64-merge-with-tol",
        ]
    }

    fn make_sort(
        typeinfo: &mut TypeInfo,
        name: String,
        args: &[Expr],
    ) -> Result<ArcSort, TypeError> {
        if let [Expr::Var(span, element)] = args {
            let element = typeinfo
                .get_sort_by_name(element)
                .ok_or(TypeError::UndefinedSort(element.clone(), span.clone()))?;

            Ok(Self {
                name,
                element: element.clone(),
            }
            .to_arcsort())
        } else {
            panic!("Maybe sort requires exactly one argument")
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
        let val = container_values
            .get_val::<MaybeContainer>(value)
            .unwrap()
            .clone();
        val.data
            .iter()
            .map(|v| (self.element.clone(), *v))
            .collect()
    }

    fn register_primitives(&self, eg: &mut EGraph) {
        let arc = self.clone().to_arcsort();

        add_primitive_with_validator!(
            eg,
            "maybe-none" = {self.clone(): MaybeSort} || -> @MaybeContainer (arc) { MaybeContainer {
                do_rebuild: self.ctx.is_eq_container_sort(),
                data: None,
            } },
            |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
                if args.is_empty() {
                    Some(termdag.app("maybe-none".into(), vec![]))
                } else {
                    None
                }
            }
        );

        add_primitive_with_validator!(
            eg,
            "maybe-some" = {self.clone(): MaybeSort} |x: # (self.element())| -> @MaybeContainer (arc) { MaybeContainer {
                do_rebuild: self.ctx.is_eq_container_sort(),
                data: Some(x),
            } },
            |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
                if args.len() == 1 {
                    Some(termdag.app("maybe-some".into(), args.to_vec()))
                } else {
                    None
                }
            }
        );

        add_primitive_with_validator!(
            eg,
            "maybe-unwrap" = |xs: @MaybeContainer (arc)| -?> # (self.element()) { xs.data },
            |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
                let [maybe] = args else {
                    return None;
                };
                match termdag.get(*maybe) {
                    Term::App(head, children) if head == "maybe-some" && children.len() == 1 => {
                        Some(children[0])
                    }
                    _ => None,
                }
            }
        );

        add_primitive_with_validator!(
            eg,
            "maybe-unwrap-or" = |xs: @MaybeContainer (arc), default: # (self.element())| -> # (self.element()) {
                xs.data.unwrap_or(default)
            },
            |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
                let [maybe, default] = args else {
                    return None;
                };
                match termdag.get(*maybe) {
                    Term::App(head, children) if head == "maybe-some" && children.len() == 1 => {
                        Some(children[0])
                    }
                    Term::App(head, children) if head == "maybe-none" && children.is_empty() => {
                        Some(*default)
                    }
                    _ => None,
                }
            }
        );

        if self.element().name() == "f64" {
            add_primitive_with_validator!(
                eg,
                "maybe-f64-merge-with-tol" = |old: @MaybeContainer (arc), new: @MaybeContainer (arc), tol: F| -?> @MaybeContainer (arc) {{
                    match (old.data, new.data) {
                        (None, _) | (_, None) => Some(MaybeContainer { data: None, ..old }),
                        (Some(old_value), Some(new_value)) => {
                            let old_f = state.base_values().unwrap::<F>(old_value).0.0;
                            let new_f = state.base_values().unwrap::<F>(new_value).0.0;
                            let tolerance = tol.0.0.abs();
                            let merged =
                                old_f == new_f ||
                                (old_f == 0.0 && new_f == -0.0) ||
                                (old_f == -0.0 && new_f == 0.0) ||
                                (old_f - new_f).abs() <= tolerance;
                            merged.then_some(old)
                        }
                    }
                }},
                validate_maybe_f64_merge_with_tol
            );
        }
    }

    fn reconstruct_termdag(
        &self,
        _container_values: &ContainerValues,
        _value: Value,
        termdag: &mut TermDag,
        element_terms: Vec<TermId>,
    ) -> TermId {
        match element_terms.as_slice() {
            [] => termdag.app("maybe-none".into(), vec![]),
            [value] => termdag.app("maybe-some".into(), vec![*value]),
            _ => panic!("Maybe sort expected at most one element"),
        }
    }

    fn serialized_name(&self, container_values: &ContainerValues, value: Value) -> String {
        let maybe = container_values.get_val::<MaybeContainer>(value).unwrap();
        if maybe.data.is_some() {
            "maybe-some".to_owned()
        } else {
            "maybe-none".to_owned()
        }
    }
}

pub fn maybe_sorts(type_info: &TypeInfo) -> Vec<(ArcSort, ArcSort)> {
    type_info
        .get_arcsorts_by(|sort| sort.value_type() == Some(TypeId::of::<MaybeContainer>()))
        .into_iter()
        .filter_map(|sort| {
            let inner_sorts = sort.inner_sorts();
            let [element] = inner_sorts.as_slice() else {
                return None;
            };
            Some((sort, element.clone()))
        })
        .collect()
}

fn validate_maybe_f64_merge_with_tol(termdag: &mut TermDag, args: &[TermId]) -> Option<TermId> {
    let [old, new, tol] = args else {
        return None;
    };
    match (maybe_f64(termdag, *old)?, maybe_f64(termdag, *new)?) {
        (None, _) | (_, None) => Some(termdag.app("maybe-none".into(), vec![])),
        (Some(old_f), Some(new_f)) => {
            let Term::Lit(Literal::Float(tolerance)) = termdag.get(*tol) else {
                return None;
            };
            let tolerance = tolerance.0.abs();
            let merged = old_f == new_f
                || (old_f == 0.0 && new_f == -0.0)
                || (old_f == -0.0 && new_f == 0.0)
                || (old_f - new_f).abs() <= tolerance;
            merged.then_some(*old)
        }
    }
}

fn maybe_f64(termdag: &TermDag, term: TermId) -> Option<Option<f64>> {
    match termdag.get(term) {
        Term::App(head, children) if head == "maybe-none" && children.is_empty() => Some(None),
        Term::App(head, children) if head == "maybe-some" && children.len() == 1 => {
            match termdag.get(children[0]) {
                Term::Lit(Literal::Float(value)) => Some(Some(value.0)),
                _ => None,
            }
        }
        _ => None,
    }
}
