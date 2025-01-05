use egglog::ast::Symbol;
use egglog::sort::{FromSort, IntoSort, Sort};
use lazy_static::lazy_static;
use num::integer::Roots;
use num::rational::Rational64;
use num::traits::{CheckedAdd, CheckedDiv, CheckedMul, CheckedSub, One, Signed, ToPrimitive, Zero};
use std::any::Any;
use std::sync::{Arc, Mutex};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct R(Rational64); // orphan rule
use crate::{ast::Literal, util::IndexSet};

use super::*;

lazy_static! {
    static ref RATIONAL_SORT_NAME: Symbol = "Rational".into();
    static ref RATS: Mutex<IndexSet<R>> = Default::default();
}

#[derive(Debug)]
pub struct RationalSort;

impl Sort for RationalSort {
    fn name(&self) -> Symbol {
        *RATIONAL_SORT_NAME
    }

    fn as_arc_any(self: Arc<Self>) -> Arc<dyn Any + Send + Sync + 'static> {
        self
    }

    #[rustfmt::skip]
    fn register_primitives(self: Arc<Self>, eg: &mut TypeInfo) {
        type Opt<T=()> = Option<T>;

        // TODO we can't have primitives take borrows just yet, since it
        // requires returning a reference to the locked sort
        add_primitives!(eg, "+" = |a: R, b: R| -> Opt<R> { a.0.checked_add(&b.0).map(R) });
        add_primitives!(eg, "-" = |a: R, b: R| -> Opt<R> { a.0.checked_sub(&b.0).map(R) });
        add_primitives!(eg, "*" = |a: R, b: R| -> Opt<R> { a.0.checked_mul(&b.0).map(R) });
        add_primitives!(eg, "/" = |a: R, b: R| -> Opt<R> { a.0.checked_div(&b.0).map(R) });

        add_primitives!(eg, "min" = |a: R, b: R| -> R { R(a.0.min(b.0)) });
        add_primitives!(eg, "max" = |a: R, b: R| -> R { R(a.0.max(b.0)) });
        add_primitives!(eg, "neg" = |a: R| -> R { R(-a.0) });
        add_primitives!(eg, "abs" = |a: R| -> R { R(a.0.abs()) });
        add_primitives!(eg, "floor" = |a: R| -> R { R(a.0.floor()) });
        add_primitives!(eg, "ceil" = |a: R| -> R { R(a.0.ceil()) });
        add_primitives!(eg, "round" = |a: R| -> R { R(a.0.round()) });
        add_primitives!(eg, "rational" = |a: i64, b: i64| -> R { R(Rational64::new(a, b)) });
        add_primitives!(eg, "numer" = |a: R| -> i64 { *a.0.numer() });
        add_primitives!(eg, "denom" = |a: R| -> i64 { *a.0.denom() });

        add_primitives!(eg, "to-f64" = |a: R| -> f64 { a.0.to_f64().unwrap() });

        add_primitives!(eg, "pow" = |a: R, b: R| -> Option<R> {
            if a.0.is_zero() {
                if b.0.is_positive() {
                    Some(R(Rational64::zero()))
                } else {
                    None
                }
            } else if b.0.is_zero() {
                Some(R(Rational64::one()))
            } else if let Some(b) = b.0.to_i64() {
                if let Ok(b) = usize::try_from(b) {
                    num::traits::checked_pow(a.0, b).map(R)
                } else {
                    // TODO handle negative powers
                    None
                }
            } else {
                None
            }
        });
        add_primitives!(eg, "log" = |a: R| -> Option<R> {
            if a.0.is_one() {
                Some(R(Rational64::zero()))
            } else {
                todo!()
            }
        });
        add_primitives!(eg, "sqrt" = |a: R| -> Option<R> {
            if a.0.numer().is_positive() && a.0.denom().is_positive() {
                let s1 = a.0.numer().sqrt();
                let s2 = a.0.denom().sqrt();
                let is_perfect = &(s1 * s1) == a.0.numer() && &(s2 * s2) == a.0.denom();
                if is_perfect {
                    Some(R(Rational64::new(s1, s2)))
                } else {
                    None
                }
            } else {
                None
            }
        });
        add_primitives!(eg, "cbrt" = |a: R| -> Option<R> {
            if a.0.is_one() {
                Some(R(Rational64::one()))
            } else {
                todo!()
            }
        });

        add_primitives!(eg, "<" = |a: R, b: R| -> Opt { if a.0 < b.0 {Some(())} else {None} });
        add_primitives!(eg, ">" = |a: R, b: R| -> Opt { if a.0 > b.0 {Some(())} else {None} });
        add_primitives!(eg, "<=" = |a: R, b: R| -> Opt { if a.0 <= b.0 {Some(())} else {None} });
        add_primitives!(eg, ">=" = |a: R, b: R| -> Opt { if a.0 >= b.0 {Some(())} else {None} });
   }

    fn extract_term(
        &self,
        _egraph: &EGraph,
        value: Value,
        _extractor: &extract::Extractor,
        termdag: &mut TermDag,
    ) -> Option<(extract::Cost, Term)> {
        #[cfg(debug_assertions)]
        debug_assert_eq!(value.tag, self.name());

        let rat = R::load(self, &value);
        let numer = termdag.lit(Literal::Int(*rat.0.numer()));
        let denom = termdag.lit(Literal::Int(*rat.0.denom()));
        Some((1, termdag.app("rational".into(), vec![numer, denom])))
    }
}

impl FromSort for R {
    type Sort = RationalSort;
    fn load(_sort: &Self::Sort, value: &Value) -> Self {
        let i = value.bits as usize;
        *RATS.lock().unwrap().get_index(i).unwrap()
    }
}

impl IntoSort for R {
    type Sort = RationalSort;
    fn store(self, _sort: &Self::Sort) -> Option<Value> {
        let (i, _) = RATS.lock().unwrap().insert_full(self);
        Some(Value {
            #[cfg(debug_assertions)]
            tag: RationalSort.name(),
            bits: i as u64,
        })
    }
}
