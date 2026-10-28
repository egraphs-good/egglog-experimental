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
        eg.type_info().register_builtin_family(egglog::builtin::FamilyDescription {
            name: "Rational".into(), arity: 0,
        }).expect("invalid Rational family description");
        add_primitive!(eg, "+" [id = "egglog.experimental.rational.add"] = |a: R, b: R| -?> R { a.0.checked_add(&b.0).map(R::new) });
        add_primitive!(eg, "-" [id = "egglog.experimental.rational.sub"] = |a: R, b: R| -?> R { a.0.checked_sub(&b.0).map(R::new) });
        add_primitive!(eg, "*" [id = "egglog.experimental.rational.mul"] = |a: R, b: R| -?> R { a.0.checked_mul(&b.0).map(R::new) });
        add_primitive!(eg, "/" [id = "egglog.experimental.rational.div"] = |a: R, b: R| -?> R { a.0.checked_div(&b.0).map(R::new) });

        add_primitive!(eg, "min" [id = "egglog.experimental.rational.min"] = |a: R, b: R| -> R { R::new(a.0.min(b.0)) });
        add_primitive!(eg, "max" [id = "egglog.experimental.rational.max"] = |a: R, b: R| -> R { R::new(a.0.max(b.0)) });
        add_primitive!(eg, "neg" [id = "egglog.experimental.rational.neg"] = |a: R| -> R { R::new(-a.0) });
        add_primitive!(eg, "abs" [id = "egglog.experimental.rational.abs"] = |a: R| -> R { R::new(a.0.abs()) });
        add_primitive!(eg, "floor" [id = "egglog.experimental.rational.floor"] = |a: R| -> R { R::new(a.0.floor()) });
        add_primitive!(eg, "ceil" [id = "egglog.experimental.rational.ceil"] = |a: R| -> R { R::new(a.0.ceil()) });
        add_primitive!(eg, "round" [id = "egglog.experimental.rational.round"] = |a: R| -> R { R::new(a.0.round()) });
        add_primitive!(eg, "rational" [id = "egglog.experimental.rational.make"] = |a: i64, b: i64| -> R { R::new(Rational64::new(a, b)) });
        add_primitive!(eg, "numer" [id = "egglog.experimental.rational.numer"] = |a: R| -> i64 { *a.0.numer() });
        add_primitive!(eg, "denom" [id = "egglog.experimental.rational.denom"] = |a: R| -> i64 { *a.0.denom() });

        add_primitive!(eg, "to-f64" [id = "egglog.experimental.rational.to_f64"] = |a: R| -> F { F::new(OrderedFloat(a.0.to_f64().unwrap())) });

        add_primitive!(eg, "pow" [id = "egglog.experimental.rational.pow"] = |a: R, b: R| -?> R {
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
        add_primitive!(eg, "log" [id = "egglog.experimental.rational.log"] = |a: R| -?> R {
            if a.0.is_one() {
                Some(R::new(Rational64::zero()))
            } else {
                todo!()
            }
        });
        add_primitive!(eg, "sqrt" [id = "egglog.experimental.rational.sqrt"] = |a: R| -?> R {
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
        add_primitive!(eg, "cbrt" [id = "egglog.experimental.rational.cbrt"] = |a: R| -?> R {
            if a.0.is_one() {
                Some(R::new(Rational64::one()))
            } else {
                todo!()
            }
        });

        add_primitive!(eg, "<" [id = "egglog.experimental.rational.lt"] = |a: R, b: R| -?> () { if a.0 < b.0 {Some(())} else {None} });
        add_primitive!(eg, ">" [id = "egglog.experimental.rational.gt"] = |a: R, b: R| -?> () { if a.0 > b.0 {Some(())} else {None} });
        add_primitive!(eg, "<=" [id = "egglog.experimental.rational.le"] = |a: R, b: R| -?> () { if a.0 <= b.0 {Some(())} else {None} });
        add_primitive!(eg, ">=" [id = "egglog.experimental.rational.ge"] = |a: R, b: R| -?> () { if a.0 >= b.0 {Some(())} else {None} });
   }

    fn reconstruct_termdag(
        &self,
        base_values: &BaseValues,
        value: Value,
        termdag: &mut TermDag,
    ) -> TermId {
        let rat = base_values.unwrap::<R>(value);
        termdag.lit(
            egglog::sort::base_literal(RationalSort.to_arcsort(), rat)
                .expect("Rational native literal type"),
        )
    }

    fn fmt_value(
        &self,
        values: &BaseValues,
        value: Value,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        let rat = values.unwrap::<R>(value);
        write!(f, "(rational {} {})", rat.numer(), rat.denom())
    }
}
