//! Exact rational numbers for egglog programs.
//!
//! [`RationalSort`] registers the `Rational` sort and these overloaded
//! primitives:
//!
//! - `(rational numerator denominator)` constructs a canonical, i64-backed
//!   value. It is undefined when the denominator is zero or normalization
//!   would overflow.
//! - `+`, `-`, `*`, `/`, `min`, `max`, `neg`, and `abs` perform arithmetic.
//! - `<`, `>`, `<=`, and `>=` compare values.
//! - `floor`, `ceil`, `round`, `numer`, `denom`, and `to-f64` inspect or
//!   convert values.
//! - `pow` accepts nonnegative integer exponents, with zero to the zeroth
//!   power undefined. `sqrt` and `cbrt` return exact rational roots, and `log`
//!   is defined only for one. Operations that overflow or fall outside these
//!   domains are undefined.
//!
//! [`new_experimental_egraph`] registers this sort automatically.

use egglog::prelude::BaseSort;
use egglog::sort::{BaseValues, Boxed, F, OrderedFloat};
use num::integer::{Integer, Roots};
use num::rational::Rational64;
use num::traits::{One, Signed, ToPrimitive, Zero};

/// Rust representation of an egglog `Rational` value.
pub type R = Boxed<Rational64>;
use crate::ast::Literal;

use super::*;

fn canonical_rational(numer: i128, denom: i128) -> Option<Rational64> {
    if denom == 0 {
        return None;
    }

    // Normalize in i128 so that flipping an i64::MIN denominator cannot
    // overflow before we determine whether the canonical result fits in i64.
    let mut numer = numer;
    let mut denom = denom;
    let gcd = numer.abs().gcd(&denom.abs());
    numer /= gcd;
    denom /= gcd;
    if denom < 0 {
        numer = -numer;
        denom = -denom;
    }

    Some(Rational64::new_raw(
        i64::try_from(numer).ok()?,
        i64::try_from(denom).ok()?,
    ))
}

fn rational_binary(
    lhs: &Rational64,
    rhs: &Rational64,
    operation: impl FnOnce(i128, i128, i128, i128) -> (i128, i128),
) -> Option<Rational64> {
    let (numer, denom) = operation(
        i128::from(*lhs.numer()),
        i128::from(*lhs.denom()),
        i128::from(*rhs.numer()),
        i128::from(*rhs.denom()),
    );
    canonical_rational(numer, denom)
}

fn exact_cbrt(value: &Rational64) -> Option<Rational64> {
    let numer = value.numer().cbrt();
    let denom = value.denom().cbrt();
    let is_perfect = numer
        .checked_mul(numer)
        .and_then(|square| square.checked_mul(numer))
        == Some(*value.numer())
        && denom
            .checked_mul(denom)
            .and_then(|square| square.checked_mul(denom))
            == Some(*value.denom());
    is_perfect.then(|| Rational64::new_raw(numer, denom))
}

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
        add_primitive!(eg, "+" = |a: R, b: R| -?> R {
            rational_binary(&a.0, &b.0, |an, ad, bn, bd| (an * bd + bn * ad, ad * bd)).map(R::new)
        });
        add_primitive!(eg, "-" = |a: R, b: R| -?> R {
            rational_binary(&a.0, &b.0, |an, ad, bn, bd| (an * bd - bn * ad, ad * bd)).map(R::new)
        });
        add_primitive!(eg, "*" = |a: R, b: R| -?> R {
            rational_binary(&a.0, &b.0, |an, ad, bn, bd| (an * bn, ad * bd)).map(R::new)
        });
        add_primitive!(eg, "/" = |a: R, b: R| -?> R {
            rational_binary(&a.0, &b.0, |an, ad, bn, bd| (an * bd, ad * bn)).map(R::new)
        });

        add_primitive!(eg, "min" = |a: R, b: R| -> R { R::new(a.0.min(b.0)) });
        add_primitive!(eg, "max" = |a: R, b: R| -> R { R::new(a.0.max(b.0)) });
        add_primitive!(eg, "neg" = |a: R| -?> R {
            a.0.numer().checked_neg().map(|numer| {
                R::new(Rational64::new_raw(numer, *a.0.denom()))
            })
        });
        add_primitive!(eg, "abs" = |a: R| -?> R {
            if a.0.is_negative() {
                a.0.numer().checked_neg().map(|numer| {
                    R::new(Rational64::new_raw(numer, *a.0.denom()))
                })
            } else {
                Some(a)
            }
        });
        add_primitive!(eg, "floor" = |a: R| -> R {
            R::new(Rational64::from_integer(a.0.numer().div_floor(a.0.denom())))
        });
        add_primitive!(eg, "ceil" = |a: R| -> R {
            R::new(Rational64::from_integer(a.0.numer().div_ceil(a.0.denom())))
        });
        add_primitive!(eg, "round" = |a: R| -> R { R::new(a.0.round()) });
        add_primitive!(eg, "rational" = |a: i64, b: i64| -?> R {
            canonical_rational(i128::from(a), i128::from(b)).map(R::new)
        });
        add_primitive!(eg, "numer" = |a: R| -> i64 { *a.0.numer() });
        add_primitive!(eg, "denom" = |a: R| -> i64 { *a.0.denom() });

        add_primitive!(eg, "to-f64" = |a: R| -> F { F::new(OrderedFloat(a.0.to_f64().unwrap())) });

        add_primitive!(eg, "pow" = |a: R, b: R| -?> R {
            if !b.0.is_integer() || b.0.is_negative() {
                None
            } else if a.0.is_zero() {
                if b.0.is_positive() {
                    Some(R::new(Rational64::zero()))
                } else {
                    None
                }
            } else if b.0.is_zero() {
                Some(R::new(Rational64::one()))
            } else {
                usize::try_from(*b.0.numer())
                    .ok()
                    .and_then(|exponent| num::traits::checked_pow(a.0, exponent))
                    .map(R::new)
            }
        });
        add_primitive!(eg, "log" = |a: R| -?> R {
            if a.0.is_one() {
                Some(R::new(Rational64::zero()))
            } else {
                None
            }
        });
        add_primitive!(eg, "sqrt" = |a: R| -?> R {
            if !a.0.is_negative() {
                let s1 = a.0.numer().sqrt();
                let s2 = a.0.denom().sqrt();
                let is_perfect = s1.checked_mul(s1) == Some(*a.0.numer())
                    && s2.checked_mul(s2) == Some(*a.0.denom());
                if is_perfect {
                    Some(R::new(Rational64::new_raw(s1, s2)))
                } else {
                    None
                }
            } else {
                None
            }
        });
        add_primitive!(eg, "cbrt" = |a: R| -?> R {
            exact_cbrt(&a.0).map(R::new)
        });

        add_primitive!(eg, "<" = |a: R, b: R| -?> () { if a.0 < b.0 {Some(())} else {None} });
        add_primitive!(eg, ">" = |a: R, b: R| -?> () { if a.0 > b.0 {Some(())} else {None} });
        add_primitive!(eg, "<=" = |a: R, b: R| -?> () { if a.0 <= b.0 {Some(())} else {None} });
        add_primitive!(eg, ">=" = |a: R, b: R| -?> () { if a.0 >= b.0 {Some(())} else {None} });
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
