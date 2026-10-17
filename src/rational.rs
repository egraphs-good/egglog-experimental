//! Exact rational numbers for egglog programs.
//!
//! [`RationalSort`] registers the `Rational` sort and these overloaded
//! primitives:
//!
//! - `(rational numerator denominator)` constructs a value; the denominator
//!   must be nonzero.
//! - `+`, `-`, `*`, `/`, `min`, `max`, `neg`, and `abs` perform arithmetic.
//! - `<`, `>`, `<=`, and `>=` compare values.
//! - `floor`, `ceil`, `round`, `numer`, `denom`, and `to-f64` inspect or
//!   convert values.
//! - `pow` and `sqrt` return a result only when it is exactly representable.
//!   `log` and `cbrt` currently support only the value one.
//!
//! [`new_experimental_egraph`] registers this sort automatically.

use egglog::prelude::BaseSort;
use egglog::sort::{BaseValues, Boxed, F, OrderedFloat};
use num::integer::Roots;
use num::rational::Rational64;
use num::traits::{CheckedAdd, CheckedDiv, CheckedMul, CheckedSub, One, Signed, ToPrimitive, Zero};

/// Rust representation of an egglog `Rational` value.
pub type R = Boxed<Rational64>;
use crate::ast::Literal;

use super::*;

/// The egglog `Rational` base sort and its primitive operations.
#[derive(Debug)]
pub struct RationalSort;

impl BaseSort for RationalSort {
    type Base = R;

    fn name(&self) -> &str {
        "Rational"
    }

    #[rustfmt::skip]
    fn register_primitives(&self, eg: &mut EGraph) {
        eg.type_info().register_builtin_family(egglog::proto::HostSortFamily {
            name: "Rational".into(), arity: 0,
            bindings: Some(egglog::proto::SortBindings {
                python: Some(egglog::proto::TypeBinding { path: vec!["egglog".into(), "builtins".into(), "Rational".into()], type_params: vec![] }),
                rust: Some(egglog::proto::TypeBinding { path: vec!["egglog_experimental".into(), "typed".into(), "builtins".into(), "Rational".into()], type_params: vec![] }),
                ..Default::default()
            }),
        }).expect("invalid Rational family presentation");
        add_primitive!(eg, "+" [id = "egglog.experimental.rational.add", bindings = |s| egglog::builtin::scalar_member_bindings(s, "__add__", "add", &["other"], Some("Add"), None)] = |a: R, b: R| -?> R { a.0.checked_add(&b.0).map(R::new) });
        add_primitive!(eg, "-" [id = "egglog.experimental.rational.sub", bindings = |s| egglog::builtin::scalar_member_bindings(s, "__sub__", "sub", &["other"], Some("Sub"), None)] = |a: R, b: R| -?> R { a.0.checked_sub(&b.0).map(R::new) });
        add_primitive!(eg, "*" [id = "egglog.experimental.rational.mul", bindings = |s| egglog::builtin::scalar_member_bindings(s, "__mul__", "mul", &["other"], Some("Mul"), None)] = |a: R, b: R| -?> R { a.0.checked_mul(&b.0).map(R::new) });
        add_primitive!(eg, "/" [id = "egglog.experimental.rational.div", bindings = |s| egglog::builtin::scalar_member_bindings(s, "__truediv__", "div", &["other"], Some("Div"), None)] = |a: R, b: R| -?> R { a.0.checked_div(&b.0).map(R::new) });

        add_primitive!(eg, "min" [id = "egglog.experimental.rational.min", bindings = |s| egglog::builtin::scalar_member_bindings(s, "min", "min", &["other"], None, None)] = |a: R, b: R| -> R { R::new(a.0.min(b.0)) });
        add_primitive!(eg, "max" [id = "egglog.experimental.rational.max", bindings = |s| egglog::builtin::scalar_member_bindings(s, "max", "max", &["other"], None, None)] = |a: R, b: R| -> R { R::new(a.0.max(b.0)) });
        add_primitive!(eg, "neg" [id = "egglog.experimental.rational.neg", bindings = |s| egglog::builtin::scalar_member_bindings(s, "__neg__", "neg", &[], Some("Neg"), None)] = |a: R| -> R { R::new(-a.0) });
        add_primitive!(eg, "abs" [id = "egglog.experimental.rational.abs", bindings = |s| egglog::builtin::scalar_member_bindings(s, "__abs__", "abs", &[], None, None)] = |a: R| -> R { R::new(a.0.abs()) });
        add_primitive!(eg, "floor" [id = "egglog.experimental.rational.floor", bindings = |s| egglog::builtin::scalar_member_bindings(s, "floor", "floor", &[], None, None)] = |a: R| -> R { R::new(a.0.floor()) });
        add_primitive!(eg, "ceil" [id = "egglog.experimental.rational.ceil", bindings = |s| egglog::builtin::scalar_member_bindings(s, "ceil", "ceil", &[], None, None)] = |a: R| -> R { R::new(a.0.ceil()) });
        add_primitive!(eg, "round" [id = "egglog.experimental.rational.round", bindings = |s| egglog::builtin::scalar_member_bindings(s, "round", "round", &[], None, None)] = |a: R| -> R { R::new(a.0.round()) });
        add_primitive!(eg, "rational" [id = "egglog.experimental.rational.make", bindings = |s: &egglog::proto::GenericSignature| {
            use egglog::proto as pb;
            let owner = Some(pb::BindingOwner { kind: Some(pb::binding_owner::Kind::Sort(s.output.unwrap())) });
            pb::CallableBindings {
                python: Some(pb::PythonBindings { views: vec![pb::PythonCallable {
                    kind: pb::PythonCallKind::Initializer.into(), owner,
                    params: ["num", "den"].iter().enumerate().map(|(i, name)| pb::PythonParameter { core_input: Some(i as u32), name: (*name).into(), default_expr: None }).collect(),
                    ..Default::default()
                }] }),
                rust: Some(pb::RustBindings { views: vec![pb::RustCallable {
                    path: vec!["new".into()], owner,
                    params: ["num", "den"].iter().enumerate().map(|(i, name)| pb::RustParameter { core_input: Some(i as u32), name: (*name).into(), borrowed: false }).collect(),
                    ..Default::default()
                }] }),
                ..Default::default()
            }
        }] = |a: i64, b: i64| -> R { R::new(Rational64::new(a, b)) });
        add_primitive!(eg, "numer" [id = "egglog.experimental.rational.numer", bindings = |s| {
            let mut bindings = egglog::builtin::scalar_member_bindings(s, "numer", "numer", &[], None, None);
            bindings.python.as_mut().unwrap().views[0].kind = egglog::proto::PythonCallKind::Property.into();
            bindings
        }] = |a: R| -> i64 { *a.0.numer() });
        add_primitive!(eg, "denom" [id = "egglog.experimental.rational.denom", bindings = |s| {
            let mut bindings = egglog::builtin::scalar_member_bindings(s, "denom", "denom", &[], None, None);
            bindings.python.as_mut().unwrap().views[0].kind = egglog::proto::PythonCallKind::Property.into();
            bindings
        }] = |a: R| -> i64 { *a.0.denom() });

        add_primitive!(eg, "to-f64" [id = "egglog.experimental.rational.to_f64", bindings = |s| egglog::builtin::scalar_member_bindings(s, "to_f64", "to_f64", &[], None, None)] = |a: R| -> F { F::new(OrderedFloat(a.0.to_f64().unwrap())) });

        add_primitive!(eg, "pow" [id = "egglog.experimental.rational.pow", bindings = |s| egglog::builtin::scalar_member_bindings(s, "__pow__", "pow", &["other"], None, None)] = |a: R, b: R| -?> R {
            if a.0.is_zero() {
                if b.0.is_positive() {
                    Some(R::new(Rational64::zero()))
                } else {
                    None
                }
            } else if b.0.is_zero() {
                Some(R::new(Rational64::one()))
            } else if let Some(b) = b.0.to_i64() {
                if let Ok(b) = usize::try_from(b) {
                    num::traits::checked_pow(a.0, b).map(R::new)
                } else {
                    // TODO handle negative powers
                    None
                }
            } else {
                None
            }
        });
        add_primitive!(eg, "log" [id = "egglog.experimental.rational.log", bindings = |s| egglog::builtin::scalar_member_bindings(s, "log", "log", &[], None, None)] = |a: R| -?> R {
            if a.0.is_one() {
                Some(R::new(Rational64::zero()))
            } else {
                todo!()
            }
        });
        add_primitive!(eg, "sqrt" [id = "egglog.experimental.rational.sqrt", bindings = |s| egglog::builtin::scalar_member_bindings(s, "sqrt", "sqrt", &[], None, None)] = |a: R| -?> R {
            if a.0.numer().is_positive() && a.0.denom().is_positive() {
                let s1 = a.0.numer().sqrt();
                let s2 = a.0.denom().sqrt();
                let is_perfect = &(s1 * s1) == a.0.numer() && &(s2 * s2) == a.0.denom();
                if is_perfect {
                    Some(R::new(Rational64::new(s1, s2)))
                } else {
                    None
                }
            } else {
                None
            }
        });
        add_primitive!(eg, "cbrt" [id = "egglog.experimental.rational.cbrt", bindings = |s| egglog::builtin::scalar_member_bindings(s, "cbrt", "cbrt", &[], None, None)] = |a: R| -?> R {
            if a.0.is_one() {
                Some(R::new(Rational64::one()))
            } else {
                todo!()
            }
        });

        add_primitive!(eg, "<" [id = "egglog.experimental.rational.lt", bindings = |s| egglog::builtin::scalar_member_bindings(s, "__lt__", "lt", &["other"], None, None)] = |a: R, b: R| -?> () { if a.0 < b.0 {Some(())} else {None} });
        add_primitive!(eg, ">" [id = "egglog.experimental.rational.gt", bindings = |s| egglog::builtin::scalar_member_bindings(s, "__gt__", "gt", &["other"], None, None)] = |a: R, b: R| -?> () { if a.0 > b.0 {Some(())} else {None} });
        add_primitive!(eg, "<=" [id = "egglog.experimental.rational.le", bindings = |s| egglog::builtin::scalar_member_bindings(s, "__le__", "le", &["other"], None, None)] = |a: R, b: R| -?> () { if a.0 <= b.0 {Some(())} else {None} });
        add_primitive!(eg, ">=" [id = "egglog.experimental.rational.ge", bindings = |s| egglog::builtin::scalar_member_bindings(s, "__ge__", "ge", &["other"], None, None)] = |a: R, b: R| -?> () { if a.0 >= b.0 {Some(())} else {None} });
   }

    fn reconstruct_termdag(
        &self,
        base_values: &BaseValues,
        value: Value,
        termdag: &mut TermDag,
    ) -> TermId {
        let rat = base_values.unwrap::<R>(value);

        let numer = rat.0.numer();
        let denom = rat.0.denom();

        let numer = termdag.lit(Literal::Int(*numer));
        let denom = termdag.lit(Literal::Int(*denom));

        termdag.app("rational".into(), vec![numer, denom])
    }
}
