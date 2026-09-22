//! Named symbolic counterparts of core builtin sorts and their native operations.
//!
//! Exact integer promotions use ordinary [`From`] conversions: [`I64`] promotes
//! to [`BigInt`] or [`BigRat`], and [`BigInt`] promotes to [`BigRat`]. These author
//! native calls without evaluating their operands, including observed values;
//! converting an observed operand does not make it eligible for live execution.
use super::{
    CallableRef, DecodeError, EgglogValue, Fact, FrozenScalar, SortRef,
    expr::{Expr, NodeKind, ValueInput},
};
use egglog::ast::Literal;
use std::{borrow::Cow, marker::PhantomData, ops};

fn primitive<S: EgglogValue>(name: &'static str, total: bool, args: std::vec::Vec<Expr>) -> S {
    S::from_expression(Expr::call(
        S::sort_ref(),
        CallableRef::primitive(name, total),
        args,
    ))
}
fn predicate(name: &'static str, args: std::vec::Vec<Expr>) -> Fact {
    Fact::Expr(Expr::call(
        Unit::sort_ref(),
        CallableRef::primitive(name, false),
        args,
    ))
}
macro_rules! scalar {
    ($name:ident,$sort:literal) => {
        #[derive(Clone, Debug, PartialEq, Eq, Hash)]
        #[doc = concat!("Symbolic or observed `", stringify!($name), "` values. Equality compares authored syntax or snapshot identity.")]
        pub struct $name(pub(crate) Expr);
        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Display::fmt(&self.0, f)
            }
        }
        impl ValueInput for $name {
            type Owned = Self;
        }
        impl From<&$name> for $name {
            fn from(value: &$name) -> Self { value.clone() }
        }
        impl EgglogValue for $name {
            fn sort_ref() -> SortRef {
                SortRef::builtin($sort)
            }
            fn expression(&self) -> &Expr {
                &self.0
            }
            fn from_expression(expr: Expr) -> Self {
                Self(expr)
            }
        }
    };
}
scalar!(I64, "i64");
scalar!(F64, "f64");
scalar!(Bool, "bool");
scalar!(String, "String");
scalar!(Unit, "Unit");
scalar!(BigInt, "BigInt");
scalar!(BigRat, "BigRat");
scalar!(Rational, "Rational");
impl From<i64> for I64 {
    fn from(v: i64) -> Self {
        Self(Expr::new(
            Self::sort_ref(),
            NodeKind::Literal(Literal::Int(v)),
            super::origin(),
        ))
    }
}
impl From<i32> for I64 {
    fn from(v: i32) -> Self {
        Self::from(i64::from(v))
    }
}
impl From<&i64> for I64 {
    fn from(v: &i64) -> Self {
        Self::from(*v)
    }
}
impl From<&i32> for I64 {
    fn from(v: &i32) -> Self {
        Self::from(*v)
    }
}
impl From<f64> for F64 {
    fn from(v: f64) -> Self {
        Self(Expr::new(
            Self::sort_ref(),
            NodeKind::Literal(Literal::Float(v.into())),
            super::origin(),
        ))
    }
}
impl From<&f64> for F64 {
    fn from(v: &f64) -> Self {
        Self::from(*v)
    }
}
impl From<bool> for Bool {
    fn from(v: bool) -> Self {
        Self(Expr::new(
            Self::sort_ref(),
            NodeKind::Literal(Literal::Bool(v)),
            super::origin(),
        ))
    }
}
impl From<&str> for String {
    fn from(v: &str) -> Self {
        Self(Expr::new(
            Self::sort_ref(),
            NodeKind::Literal(Literal::String(v.into())),
            super::origin(),
        ))
    }
}
impl From<std::string::String> for String {
    fn from(v: std::string::String) -> Self {
        Self::from(v.as_str())
    }
}
impl From<&std::string::String> for String {
    fn from(v: &std::string::String) -> Self {
        Self::from(v.as_str())
    }
}
impl From<()> for Unit {
    fn from(_: ()) -> Self {
        Self(Expr::new(
            Self::sort_ref(),
            NodeKind::Literal(Literal::Unit),
            super::origin(),
        ))
    }
}
macro_rules! decode_literal {
    ($symbolic:ident,$host:ty,$variant:ident,$convert:expr) => {
        impl TryFrom<&$symbolic> for $host {
            type Error = DecodeError;
            fn try_from(x: &$symbolic) -> Result<Self, Self::Error> {
                if x.0.node().sort != $symbolic::sort_ref() {
                    return Err(DecodeError(
                        concat!("expected exact ", stringify!($symbolic), " sort").into(),
                    ));
                }
                match &x.0.node().kind {
                    NodeKind::Literal(Literal::$variant(v)) => Ok(($convert)(v)),
                    NodeKind::Frozen(reference) => match reference.scalar() {
                        Some(FrozenScalar::$symbolic(v)) => Ok(($convert)(v)),
                        _ => Err(DecodeError(
                            concat!("expected frozen ", stringify!($symbolic), " scalar").into(),
                        )),
                    },
                    _ => Err(DecodeError(
                        concat!("expected a portable ", stringify!($symbolic), " literal").into(),
                    )),
                }
            }
        }
        impl TryFrom<$symbolic> for $host {
            type Error = DecodeError;
            fn try_from(x: $symbolic) -> Result<Self, Self::Error> {
                Self::try_from(&x)
            }
        }
    };
}
decode_literal!(I64, i64, Int, |v: &i64| *v);
impl TryFrom<&F64> for f64 {
    type Error = DecodeError;
    fn try_from(x: &F64) -> Result<Self, Self::Error> {
        if x.0.node().sort != F64::sort_ref() {
            return Err(DecodeError("expected exact F64 sort".into()));
        }
        match &x.0.node().kind {
            NodeKind::Literal(Literal::Float(v)) => Ok(v.0),
            NodeKind::Frozen(reference) => match reference.scalar() {
                Some(FrozenScalar::F64(bits)) => Ok(f64::from_bits(*bits)),
                _ => Err(DecodeError("expected frozen F64 scalar".into())),
            },
            _ => Err(DecodeError("expected a portable F64 literal".into())),
        }
    }
}
impl TryFrom<F64> for f64 {
    type Error = DecodeError;
    fn try_from(x: F64) -> Result<Self, Self::Error> {
        Self::try_from(&x)
    }
}
decode_literal!(Bool, bool, Bool, |v: &bool| *v);
decode_literal!(
    String,
    std::string::String,
    String,
    |v: &std::string::String| v.clone()
);
impl TryFrom<&Unit> for () {
    type Error = DecodeError;
    fn try_from(x: &Unit) -> Result<Self, Self::Error> {
        if x.0.node().sort != Unit::sort_ref() {
            return Err(DecodeError("expected exact Unit sort".into()));
        }
        match &x.0.node().kind {
            NodeKind::Literal(Literal::Unit) => Ok(()),
            NodeKind::Frozen(reference)
                if matches!(reference.scalar(), Some(FrozenScalar::Unit)) =>
            {
                Ok(())
            }
            _ => Err(DecodeError("expected Unit literal or frozen scalar".into())),
        }
    }
}
impl TryFrom<Unit> for () {
    type Error = DecodeError;
    fn try_from(x: Unit) -> Result<Self, Self::Error> {
        Self::try_from(&x)
    }
}
macro_rules! binary {
    ($sort:ident,$trait:ident,$method:ident,$native:literal,$total:expr) => {
        impl<T: Into<$sort>> ops::$trait<T> for $sort {
            type Output = Self;
            fn $method(self, rhs: T) -> Self {
                primitive($native, $total, vec![self.0, rhs.into().0])
            }
        }
        impl<T: Into<$sort>> ops::$trait<T> for &$sort {
            type Output = $sort;
            fn $method(self, rhs: T) -> $sort {
                primitive($native, $total, vec![self.0.clone(), rhs.into().0])
            }
        }
    };
}
macro_rules! numbers {
    ($sort:ident,$total:expr) => {
        binary!($sort, Add, add, "+", $total);
        binary!($sort, Sub, sub, "-", $total);
        binary!($sort, Mul, mul, "*", $total);
        binary!($sort, Div, div, "/", false);
        impl $sort {
            /// Builds the native less-than query.
            pub fn lt(&self, rhs: impl Into<Self>) -> Fact {
                predicate("<", vec![self.0.clone(), rhs.into().0])
            }
            /// Builds the native less-than-or-equal query.
            pub fn le(&self, rhs: impl Into<Self>) -> Fact {
                predicate("<=", vec![self.0.clone(), rhs.into().0])
            }
            /// Builds the native greater-than query.
            pub fn gt(&self, rhs: impl Into<Self>) -> Fact {
                predicate(">", vec![self.0.clone(), rhs.into().0])
            }
            /// Builds the native greater-than-or-equal query.
            pub fn ge(&self, rhs: impl Into<Self>) -> Fact {
                predicate(">=", vec![self.0.clone(), rhs.into().0])
            }
            /// Builds the native minimum expression.
            pub fn min(&self, rhs: impl Into<Self>) -> Self {
                primitive("min", true, vec![self.0.clone(), rhs.into().0])
            }
            /// Builds the native maximum expression.
            pub fn max(&self, rhs: impl Into<Self>) -> Self {
                primitive("max", true, vec![self.0.clone(), rhs.into().0])
            }
        }
    };
}
numbers!(I64, false);
numbers!(F64, true);
numbers!(BigInt, true);
numbers!(BigRat, false);
numbers!(Rational, false);
binary!(I64, Rem, rem, "%", false);
binary!(F64, Rem, rem, "%", false);
binary!(BigInt, Rem, rem, "%", false);
macro_rules! boolean_comparisons {
    ($sort:ident) => {
        impl $sort {
            /// Builds a Boolean-valued native equality comparison.
            pub fn bool_eq(&self, rhs: impl Into<Self>) -> Bool {
                primitive("bool-=", true, vec![self.0.clone(), rhs.into().0])
            }
            /// Builds a Boolean-valued native less-than comparison.
            pub fn bool_lt(&self, rhs: impl Into<Self>) -> Bool {
                primitive("bool-<", true, vec![self.0.clone(), rhs.into().0])
            }
            /// Builds a Boolean-valued native less-than-or-equal comparison.
            pub fn bool_le(&self, rhs: impl Into<Self>) -> Bool {
                primitive("bool-<=", true, vec![self.0.clone(), rhs.into().0])
            }
            /// Builds a Boolean-valued native greater-than comparison.
            pub fn bool_gt(&self, rhs: impl Into<Self>) -> Bool {
                primitive("bool->", true, vec![self.0.clone(), rhs.into().0])
            }
            /// Builds a Boolean-valued native greater-than-or-equal comparison.
            pub fn bool_ge(&self, rhs: impl Into<Self>) -> Bool {
                primitive("bool->=", true, vec![self.0.clone(), rhs.into().0])
            }
        }
    };
}
boolean_comparisons!(I64);
boolean_comparisons!(BigInt);
binary!(I64, BitAnd, bitand, "&", true);
binary!(I64, BitOr, bitor, "|", true);
binary!(I64, BitXor, bitxor, "^", true);
binary!(I64, Shl, shl, "<<", false);
binary!(I64, Shr, shr, ">>", false);
binary!(BigInt, BitAnd, bitand, "&", true);
binary!(BigInt, BitOr, bitor, "|", true);
binary!(BigInt, BitXor, bitxor, "^", true);
binary!(Bool, BitAnd, bitand, "and", true);
binary!(Bool, BitOr, bitor, "or", true);
binary!(Bool, BitXor, bitxor, "xor", true);
binary!(String, Add, add, "+", true);
impl ops::Neg for I64 {
    type Output = Self;
    fn neg(self) -> Self {
        I64::from(0) - self
    }
}
impl ops::Neg for &I64 {
    type Output = I64;
    fn neg(self) -> I64 {
        I64::from(0) - self
    }
}
impl ops::Neg for F64 {
    type Output = Self;
    fn neg(self) -> Self {
        primitive("neg", true, vec![self.0])
    }
}
impl ops::Neg for &F64 {
    type Output = F64;
    fn neg(self) -> F64 {
        primitive("neg", true, vec![self.0.clone()])
    }
}
impl ops::Neg for BigInt {
    type Output = Self;
    fn neg(self) -> Self {
        BigInt::from(0) - self
    }
}
impl ops::Neg for &BigInt {
    type Output = BigInt;
    fn neg(self) -> BigInt {
        BigInt::from(0) - self
    }
}
impl ops::Neg for BigRat {
    type Output = Self;
    fn neg(self) -> Self {
        primitive("neg", true, vec![self.0])
    }
}
impl ops::Neg for &BigRat {
    type Output = BigRat;
    fn neg(self) -> BigRat {
        primitive("neg", true, vec![self.0.clone()])
    }
}
impl ops::Not for I64 {
    type Output = Self;
    fn not(self) -> Self {
        primitive("not-i64", true, vec![self.0])
    }
}
impl ops::Not for &I64 {
    type Output = I64;
    fn not(self) -> I64 {
        primitive("not-i64", true, vec![self.0.clone()])
    }
}
impl ops::Not for BigInt {
    type Output = Self;
    fn not(self) -> Self {
        primitive("not-Z", true, vec![self.0])
    }
}
impl ops::Not for &BigInt {
    type Output = BigInt;
    fn not(self) -> BigInt {
        primitive("not-Z", true, vec![self.0.clone()])
    }
}
impl ops::Not for Bool {
    type Output = Self;
    fn not(self) -> Self {
        primitive("not", true, vec![self.0])
    }
}
impl ops::Not for &Bool {
    type Output = Bool;
    fn not(self) -> Bool {
        primitive("not", true, vec![self.0.clone()])
    }
}
impl I64 {
    /// Builds native string conversion; it does not format the authoring DAG.
    pub fn to_string(&self) -> String {
        primitive("to-string", true, vec![self.0.clone()])
    }
    /// Builds native absolute value, preserving native overflow/failure behavior.
    pub fn abs(&self) -> Self {
        primitive("abs", false, vec![self.0.clone()])
    }
    /// Builds native integer logarithm; evaluation is partial outside its native domain.
    pub fn log2(&self) -> Self {
        primitive("log2", false, vec![self.0.clone()])
    }
    /// Builds native floating-point conversion.
    pub fn to_f64(&self) -> F64 {
        primitive("to-f64", true, vec![self.0.clone()])
    }
}
impl F64 {
    /// Builds native string conversion; it does not format the authoring DAG.
    pub fn to_string(&self) -> String {
        primitive("to-string", true, vec![self.0.clone()])
    }
    /// Builds native exponentiation, preserving its domain restrictions.
    pub fn pow(&self, rhs: impl Into<Self>) -> Self {
        primitive("^", true, vec![self.0.clone(), rhs.into().0])
    }
    /// Builds native absolute value, preserving native overflow/failure behavior.
    pub fn abs(&self) -> Self {
        primitive("abs", true, vec![self.0.clone()])
    }
    /// Builds native square root, preserving its domain restrictions.
    pub fn sqrt(&self) -> Self {
        primitive("sqrt", false, vec![self.0.clone()])
    }
    /// Builds native exponential.
    pub fn exp(&self) -> Self {
        primitive("exp", true, vec![self.0.clone()])
    }
    /// Builds native logarithm, preserving its domain restrictions.
    pub fn log(&self) -> Self {
        primitive("log", false, vec![self.0.clone()])
    }
    /// Builds native integer conversion with the source sort's native semantics.
    pub fn to_i64(&self) -> I64 {
        primitive("to-i64", true, vec![self.0.clone()])
    }
}
impl Bool {
    /// Succeeds as a query exactly when the native Boolean value is true.
    pub fn guard(&self) -> Fact {
        predicate("guard", vec![self.0.clone()])
    }
}
impl String {
    /// Builds native substring replacement.
    pub fn replace(&self, from: impl Into<Self>, to: impl Into<Self>) -> Self {
        primitive(
            "replace",
            true,
            vec![self.0.clone(), from.into().0, to.into().0],
        )
    }
    /// Builds native substring-match counting.
    pub fn count_matches(&self, pattern: impl Into<Self>) -> I64 {
        primitive(
            "count-matches",
            true,
            vec![self.0.clone(), pattern.into().0],
        )
    }
}
impl From<i64> for BigInt {
    fn from(v: i64) -> Self {
        primitive("bigint", true, vec![I64::from(v).0])
    }
}
impl From<i32> for BigInt {
    fn from(v: i32) -> Self {
        Self::from(i64::from(v))
    }
}
impl From<I64> for BigInt {
    fn from(value: I64) -> Self {
        primitive("bigint", true, vec![value.0])
    }
}
impl From<&I64> for BigInt {
    fn from(value: &I64) -> Self {
        primitive("bigint", true, vec![value.0.clone()])
    }
}
impl BigInt {
    /// Builds native string conversion; it does not format the authoring DAG.
    pub fn to_string(&self) -> String {
        primitive("to-string", true, vec![self.0.clone()])
    }
    /// Builds decimal BigInt parsing; malformed input fails during native evaluation.
    pub fn from_string(v: impl Into<String>) -> Self {
        primitive("from-string", false, vec![v.into().0])
    }
    /// Builds the native BigInt bit-count expression.
    pub fn bits(&self) -> Self {
        primitive("bits", true, vec![self.0.clone()])
    }
}
impl<T: Into<I64>> ops::Shl<T> for BigInt {
    type Output = Self;
    fn shl(self, rhs: T) -> Self {
        primitive("<<", false, vec![self.0, rhs.into().0])
    }
}
impl<T: Into<I64>> ops::Shl<T> for &BigInt {
    type Output = BigInt;
    fn shl(self, rhs: T) -> BigInt {
        primitive("<<", false, vec![self.0.clone(), rhs.into().0])
    }
}
impl<T: Into<I64>> ops::Shr<T> for BigInt {
    type Output = Self;
    fn shr(self, rhs: T) -> Self {
        primitive(">>", false, vec![self.0, rhs.into().0])
    }
}
impl<T: Into<I64>> ops::Shr<T> for &BigInt {
    type Output = BigInt;
    fn shr(self, rhs: T) -> BigInt {
        primitive(">>", false, vec![self.0.clone(), rhs.into().0])
    }
}
impl From<i64> for BigRat {
    fn from(value: i64) -> Self {
        Self::new(value, 1)
    }
}
impl From<i32> for BigRat {
    fn from(value: i32) -> Self {
        Self::new(value, 1)
    }
}
impl From<I64> for BigRat {
    fn from(value: I64) -> Self {
        Self::new(value, 1)
    }
}
impl From<&I64> for BigRat {
    fn from(value: &I64) -> Self {
        Self::new(value, 1)
    }
}
impl From<BigInt> for BigRat {
    fn from(value: BigInt) -> Self {
        Self::new(value, 1)
    }
}
impl From<&BigInt> for BigRat {
    fn from(value: &BigInt) -> Self {
        Self::new(value, 1)
    }
}
impl BigRat {
    /// Builds native BigRat logarithm. The pinned implementation handles one;
    /// other inputs may panic, exactly as in the native primitive.
    pub fn log(&self) -> Self {
        primitive("log", false, vec![self.0.clone()])
    }
    /// Builds native BigRat cube root. The pinned implementation handles one;
    /// other inputs may panic, exactly as in the native primitive.
    pub fn cbrt(&self) -> Self {
        primitive("cbrt", false, vec![self.0.clone()])
    }
    /// Constructs a symbolic native value from its typed components; evaluation is deferred.
    pub fn new(numerator: impl Into<BigInt>, denominator: impl Into<BigInt>) -> Self {
        primitive(
            "bigrat",
            false,
            vec![numerator.into().0, denominator.into().0],
        )
    }
    /// Builds native numerator projection.
    pub fn numer(&self) -> BigInt {
        primitive("numer", true, vec![self.0.clone()])
    }
    /// Builds native denominator projection.
    pub fn denom(&self) -> BigInt {
        primitive("denom", true, vec![self.0.clone()])
    }
    /// Builds native floating-point conversion.
    pub fn to_f64(&self) -> F64 {
        primitive("to-f64", false, vec![self.0.clone()])
    }
    /// Builds native integer conversion with the source sort's native semantics.
    pub fn to_i64(&self) -> I64 {
        primitive("to-i64", false, vec![self.0.clone()])
    }
    /// Builds native absolute value, preserving native overflow/failure behavior.
    pub fn abs(&self) -> Self {
        primitive("abs", true, vec![self.0.clone()])
    }
    /// Builds native floor, preserving native numeric behavior.
    pub fn floor(&self) -> Self {
        primitive("floor", true, vec![self.0.clone()])
    }
    /// Builds native ceiling, preserving native numeric behavior.
    pub fn ceil(&self) -> Self {
        primitive("ceil", true, vec![self.0.clone()])
    }
    /// Builds native rounding, preserving native numeric behavior.
    pub fn round(&self) -> Self {
        primitive("round", true, vec![self.0.clone()])
    }
    /// Builds native exponentiation, preserving its domain restrictions.
    pub fn pow(&self, rhs: impl Into<Self>) -> Self {
        primitive("pow", false, vec![self.0.clone(), rhs.into().0])
    }
    /// Builds native square root, preserving its domain restrictions.
    pub fn sqrt(&self) -> Self {
        primitive("sqrt", false, vec![self.0.clone()])
    }
}
impl Rational {
    /// Builds native Rational logarithm; inputs other than one may panic.
    pub fn log(&self) -> Self {
        primitive("log", false, vec![self.0.clone()])
    }
    /// Builds native Rational cube root; inputs other than one may panic.
    pub fn cbrt(&self) -> Self {
        primitive("cbrt", false, vec![self.0.clone()])
    }
    /// Constructs a symbolic native value from its typed components; evaluation is deferred.
    pub fn new(numerator: impl Into<I64>, denominator: impl Into<I64>) -> Self {
        primitive(
            "rational",
            false,
            vec![numerator.into().0, denominator.into().0],
        )
    }
    /// Builds native numerator projection.
    pub fn numer(&self) -> I64 {
        primitive("numer", true, vec![self.0.clone()])
    }
    /// Builds native denominator projection.
    pub fn denom(&self) -> I64 {
        primitive("denom", true, vec![self.0.clone()])
    }
    /// Builds native floating-point conversion.
    pub fn to_f64(&self) -> F64 {
        primitive("to-f64", true, vec![self.0.clone()])
    }
    /// Builds native absolute value, preserving native overflow/failure behavior.
    pub fn abs(&self) -> Self {
        primitive("abs", false, vec![self.0.clone()])
    }
    /// Builds native floor, preserving native numeric behavior.
    pub fn floor(&self) -> Self {
        primitive("floor", false, vec![self.0.clone()])
    }
    /// Builds native ceiling, preserving native numeric behavior.
    pub fn ceil(&self) -> Self {
        primitive("ceil", false, vec![self.0.clone()])
    }
    /// Builds native rounding, preserving native numeric behavior.
    pub fn round(&self) -> Self {
        primitive("round", false, vec![self.0.clone()])
    }
    /// Builds native exponentiation, preserving its domain restrictions.
    pub fn pow(&self, rhs: impl Into<Self>) -> Self {
        primitive("pow", false, vec![self.0.clone(), rhs.into().0])
    }
    /// Builds native square root, preserving its domain restrictions.
    pub fn sqrt(&self) -> Self {
        primitive("sqrt", false, vec![self.0.clone()])
    }
}
impl ops::Neg for Rational {
    type Output = Self;
    fn neg(self) -> Self {
        primitive("neg", false, vec![self.0])
    }
}
impl ops::Neg for &Rational {
    type Output = Rational;
    fn neg(self) -> Rational {
        primitive("neg", false, vec![self.0.clone()])
    }
}
macro_rules! container {
    ($name:ident,$family:literal,$($arg:ident),+) => {
        #[doc = concat!("Symbolic or observed `", stringify!($name), "` values. Equality compares authored syntax or snapshot identity.")]
        #[derive(Clone,Debug,PartialEq,Eq,Hash)] pub struct $name<$($arg:EgglogValue),+>(pub(crate) Expr,PhantomData<($($arg,)+)>);
        impl<$($arg:EgglogValue),+> std::fmt::Display for $name<$($arg),+> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Display::fmt(&self.0, f)
            }
        }
        impl<$($arg:EgglogValue),+> ValueInput for $name<$($arg),+> {
            type Owned=Self;
        }
        impl<$($arg:EgglogValue),+> From<&$name<$($arg),+>> for $name<$($arg),+> {
            fn from(value:&$name<$($arg),+>)->Self{value.clone()}
        }
        impl<$($arg:EgglogValue),+> EgglogValue for $name<$($arg),+> {
            fn sort_ref()->SortRef{SortRef::container($family,vec![$($arg::sort_ref()),+])}
            fn expression(&self)->&Expr{&self.0}
            fn from_expression(expr:Expr)->Self{Self(expr,PhantomData)}
        }
    };
}
container!(Vec, "Vec", S);
container!(Set, "Set", S);
container!(MultiSet, "MultiSet", S);
container!(Map, "Map", K, V);
container!(Pair, "Pair", L, R);
impl<L: EgglogValue, R: EgglogValue> Pair<L, R> {
    /// Constructs a symbolic native value from its typed components; evaluation is deferred.
    pub fn new(left: impl Into<L>, right: impl Into<R>) -> Self {
        primitive(
            "pair",
            true,
            vec![
                left.into().expression().clone(),
                right.into().expression().clone(),
            ],
        )
    }
    /// Projects the first component symbolically.
    pub fn first(&self) -> L {
        primitive("pair-first", true, vec![self.0.clone()])
    }
    /// Projects the second component symbolically.
    pub fn second(&self) -> R {
        primitive("pair-second", true, vec![self.0.clone()])
    }
}
macro_rules! collection {
    ($name:ident,$prefix:literal) => {
        impl<S: EgglogValue> $name<S> {
            /// Constructs symbolic container syntax in iterator order; native normalization is deferred.
            pub fn of<I, T>(values: I) -> Self
            where
                I: IntoIterator<Item = T>,
                T: Into<S>,
            {
                primitive(
                    concat!($prefix, "-of"),
                    true,
                    values
                        .into_iter()
                        .map(|x| x.into().expression().clone())
                        .collect(),
                )
            }
            /// Constructs an empty container with this exact applied sort.
            pub fn empty() -> Self {
                Self::of(std::iter::empty::<S>())
            }
            /// Builds native container length.
            pub fn len(&self) -> I64 {
                primitive(concat!($prefix, "-length"), true, vec![self.0.clone()])
            }
            /// Builds the native membership query.
            pub fn contains(&self, item: impl Into<S>) -> Fact {
                predicate(
                    concat!($prefix, "-contains"),
                    vec![self.0.clone(), item.into().expression().clone()],
                )
            }
            /// Builds the native non-membership query.
            pub fn not_contains(&self, item: impl Into<S>) -> Fact {
                predicate(
                    concat!($prefix, "-not-contains"),
                    vec![self.0.clone(), item.into().expression().clone()],
                )
            }
        }
    };
}
collection!(Vec, "vec");
collection!(Set, "set");
collection!(MultiSet, "multiset");
impl<S: EgglogValue> Vec<S> {
    /// Builds native lookup; a missing element fails at its evaluation position.
    pub fn get(&self, index: impl Into<I64>) -> S {
        primitive("vec-get", false, vec![self.0.clone(), index.into().0])
    }
    /// Builds a vector with one appended element.
    pub fn push(&self, value: impl Into<S>) -> Self {
        primitive(
            "vec-push",
            true,
            vec![self.0.clone(), value.into().expression().clone()],
        )
    }
    /// Builds native vector concatenation.
    pub fn append(&self, rhs: impl Into<Self>) -> Self {
        primitive("vec-append", true, vec![self.0.clone(), rhs.into().0])
    }
    /// Builds native vector pop.
    pub fn pop(&self) -> Self {
        primitive("vec-pop", false, vec![self.0.clone()])
    }
    /// Builds native indexed vector replacement; invalid indices fail at evaluation.
    pub fn set(&self, index: impl Into<I64>, value: impl Into<S>) -> Self {
        primitive(
            "vec-set",
            false,
            vec![
                self.0.clone(),
                index.into().0,
                value.into().expression().clone(),
            ],
        )
    }
    /// Builds native removal, preserving the container's missing-element behavior.
    pub fn remove(&self, index: impl Into<I64>) -> Self {
        primitive("vec-remove", false, vec![self.0.clone(), index.into().0])
    }
}
impl<S: EgglogValue> Set<S> {
    /// Builds native lookup; a missing element fails at its evaluation position.
    pub fn get(&self, index: impl Into<I64>) -> S {
        primitive("set-get", false, vec![self.0.clone(), index.into().0])
    }
    /// Builds native immutable insertion.
    pub fn insert(&self, value: impl Into<S>) -> Self {
        primitive(
            "set-insert",
            true,
            vec![self.0.clone(), value.into().expression().clone()],
        )
    }
    /// Builds native removal, preserving the container's missing-element behavior.
    pub fn remove(&self, value: impl Into<S>) -> Self {
        primitive(
            "set-remove",
            true,
            vec![self.0.clone(), value.into().expression().clone()],
        )
    }
    /// Builds native set union.
    pub fn union(&self, rhs: impl Into<Self>) -> Self {
        primitive("set-union", true, vec![self.0.clone(), rhs.into().0])
    }
    /// Builds native set difference.
    pub fn difference(&self, rhs: impl Into<Self>) -> Self {
        primitive("set-diff", true, vec![self.0.clone(), rhs.into().0])
    }
    /// Builds native container intersection.
    pub fn intersection(&self, rhs: impl Into<Self>) -> Self {
        primitive("set-intersect", true, vec![self.0.clone(), rhs.into().0])
    }
}
impl<S: EgglogValue> MultiSet<S> {
    /// Constructs a multiset element with its native multiplicity.
    pub fn single(value: impl Into<S>, count: impl Into<I64>) -> Self {
        primitive(
            "multiset-single",
            false,
            vec![value.into().expression().clone(), count.into().0],
        )
    }
    /// Builds native immutable insertion.
    pub fn insert(&self, value: impl Into<S>) -> Self {
        primitive(
            "multiset-insert",
            true,
            vec![self.0.clone(), value.into().expression().clone()],
        )
    }
    /// Builds native removal, preserving the container's missing-element behavior.
    pub fn remove(&self, value: impl Into<S>) -> Self {
        primitive(
            "multiset-remove",
            false,
            vec![self.0.clone(), value.into().expression().clone()],
        )
    }
    /// Builds native multiset subtraction, which is partial for insufficient multiplicity.
    pub fn subtract(&self, rhs: impl Into<Self>) -> Self {
        primitive(
            "multiset-subtract",
            false,
            vec![self.0.clone(), rhs.into().0],
        )
    }
    /// Builds native swapped-order multiset subtraction.
    pub fn subtract_swapped(&self, rhs: impl Into<Self>) -> Self {
        primitive(
            "multiset-subtract-swapped",
            false,
            vec![self.0.clone(), rhs.into().0],
        )
    }
    /// Builds native container intersection.
    pub fn intersection(&self, rhs: impl Into<Self>) -> Self {
        primitive(
            "multiset-intersection",
            true,
            vec![self.0.clone(), rhs.into().0],
        )
    }
    /// Builds native multiplicity-preserving multiset sum.
    pub fn sum(&self, rhs: impl Into<Self>) -> Self {
        primitive("multiset-sum", true, vec![self.0.clone(), rhs.into().0])
    }
    /// Builds native multiset count normalization.
    pub fn reset_counts(&self) -> Self {
        primitive("multiset-reset-counts", true, vec![self.0.clone()])
    }
    /// Builds native multiset selection; selection order is the backend's.
    pub fn pick(&self) -> S {
        primitive("multiset-pick", false, vec![self.0.clone()])
    }
    /// Builds native maximum-element selection, partial for an empty multiset.
    pub fn pick_max(&self) -> S {
        primitive("multiset-pick-max", false, vec![self.0.clone()])
    }
    /// Builds native multiplicity lookup.
    pub fn count(&self, value: impl Into<S>) -> I64 {
        primitive(
            "multiset-count",
            true,
            vec![self.0.clone(), value.into().expression().clone()],
        )
    }
}
impl<S: super::EqualitySort> MultiSet<S> {
    /// Builds the native action that unions the multiset's equality-sort elements.
    pub fn union_values(&self) -> super::Action {
        super::Action::Effect(Expr::call(
            S::sort_ref(),
            CallableRef::primitive("multiset-union-values", false),
            vec![self.0.clone()],
        ))
    }
}
impl<S: EgglogValue> MultiSet<MultiSet<S>> {
    /// Builds native flattening by multiset sum.
    pub fn sum_multisets(&self) -> MultiSet<S> {
        primitive("multiset-sum-multisets", true, vec![self.0.clone()])
    }
}
impl<K: EgglogValue, V: EgglogValue> Map<K, V> {
    /// Constructs an empty container with this exact applied sort.
    pub fn empty() -> Self {
        primitive("map-empty", true, vec![])
    }
    /// Constructs symbolic container syntax in iterator order; native normalization is deferred.
    pub fn of<I, A, B>(values: I) -> Self
    where
        I: IntoIterator<Item = (A, B)>,
        A: Into<K>,
        B: Into<V>,
    {
        primitive(
            "map-of",
            true,
            values
                .into_iter()
                .flat_map(|(k, v)| [k.into().expression().clone(), v.into().expression().clone()])
                .collect(),
        )
    }
    /// Builds native immutable insertion.
    pub fn insert(&self, key: impl Into<K>, value: impl Into<V>) -> Self {
        primitive(
            "map-insert",
            true,
            vec![
                self.0.clone(),
                key.into().expression().clone(),
                value.into().expression().clone(),
            ],
        )
    }
    /// Builds native lookup; a missing element fails at its evaluation position.
    pub fn get(&self, key: impl Into<K>) -> V {
        primitive(
            "map-get",
            false,
            vec![self.0.clone(), key.into().expression().clone()],
        )
    }
    /// Builds native removal, preserving the container's missing-element behavior.
    pub fn remove(&self, key: impl Into<K>) -> Self {
        primitive(
            "map-remove",
            true,
            vec![self.0.clone(), key.into().expression().clone()],
        )
    }
    /// Builds native container length.
    pub fn len(&self) -> I64 {
        primitive("map-length", true, vec![self.0.clone()])
    }
    /// Builds the native membership query.
    pub fn contains(&self, key: impl Into<K>) -> Fact {
        predicate(
            "map-contains",
            vec![self.0.clone(), key.into().expression().clone()],
        )
    }
    /// Builds the native non-membership query.
    pub fn not_contains(&self, key: impl Into<K>) -> Fact {
        predicate(
            "map-not-contains",
            vec![self.0.clone(), key.into().expression().clone()],
        )
    }
}
macro_rules! portable_sequence {
    ($kind:ident) => {
        impl<S: EgglogValue, T: Into<S>> From<std::vec::Vec<T>> for $kind<S> {
            fn from(values: std::vec::Vec<T>) -> Self {
                Self::of(values)
            }
        }
        impl<S: EgglogValue, T: Into<S>, const N: usize> From<[T; N]> for $kind<S> {
            fn from(values: [T; N]) -> Self {
                Self::of(values)
            }
        }
    };
}
portable_sequence!(Vec);
portable_sequence!(Set);
portable_sequence!(MultiSet);
macro_rules! decode_sequence {
    ($kind:ident,$head:literal) => {
        impl<S: EgglogValue> $kind<S> {
            /// Inspect immediate elements without evaluation. Observed elements retain
            /// their snapshot; authored elements retain their original syntax.
            pub fn items(&self) -> Result<std::vec::Vec<S>, DecodeError> {
                if self.0.node().sort != Self::sort_ref() {
                    return Err(DecodeError(
                        concat!("expected exact ", stringify!($kind), " sort").into(),
                    ));
                }
                let args = match &self.0.node().kind {
                    NodeKind::Call(head, args) if *head == CallableRef::primitive($head, true) => {
                        Cow::Borrowed(args.as_slice())
                    }
                    NodeKind::Frozen(reference) => Cow::Owned(reference.children()?),
                    _ => {
                        return Err(DecodeError(
                            concat!("expected portable ", $head, " form").into(),
                        ));
                    }
                };
                args.iter()
                    .map(|arg| {
                        if arg.node().sort != S::sort_ref() {
                            return Err(DecodeError(
                                "container element has a different exact sort".into(),
                            ));
                        }
                        Ok(S::from_expression(arg.clone()))
                    })
                    .collect()
            }
        }
        impl<S: EgglogValue> TryFrom<&$kind<S>> for std::vec::Vec<S> {
            type Error = DecodeError;
            fn try_from(value: &$kind<S>) -> Result<Self, Self::Error> {
                value.items()
            }
        }
        impl<S: EgglogValue> TryFrom<$kind<S>> for std::vec::Vec<S> {
            type Error = DecodeError;
            fn try_from(value: $kind<S>) -> Result<Self, Self::Error> {
                Self::try_from(&value)
            }
        }
    };
}
decode_sequence!(Vec, "vec-of");
decode_sequence!(Set, "set-of");
decode_sequence!(MultiSet, "multiset-of");
impl<K: EgglogValue, V: EgglogValue, A: Into<K>, B: Into<V>> From<std::vec::Vec<(A, B)>>
    for Map<K, V>
{
    fn from(values: std::vec::Vec<(A, B)>) -> Self {
        Self::of(values)
    }
}
impl<K: EgglogValue, V: EgglogValue> TryFrom<&Map<K, V>> for std::vec::Vec<(K, V)> {
    type Error = DecodeError;
    fn try_from(value: &Map<K, V>) -> Result<Self, Self::Error> {
        value.entries()
    }
}
impl<K: EgglogValue, V: EgglogValue> Map<K, V> {
    /// Inspect paired keys and values without evaluation. Observed fields retain
    /// their snapshot; authored entries retain their original syntax and order.
    pub fn entries(&self) -> Result<std::vec::Vec<(K, V)>, DecodeError> {
        if self.0.node().sort != Self::sort_ref() {
            return Err(DecodeError("expected exact Map sort".into()));
        }
        let args = match &self.0.node().kind {
            NodeKind::Call(head, args)
                if *head == CallableRef::primitive("map-of", true)
                    || (*head == CallableRef::primitive("map-empty", true) && args.is_empty()) =>
            {
                Cow::Borrowed(args.as_slice())
            }
            NodeKind::Frozen(reference) => Cow::Owned(reference.children()?),
            _ => return Err(DecodeError("expected portable map-of form".into())),
        };
        if !args.len().is_multiple_of(2) {
            return Err(DecodeError("expected paired Map fields".into()));
        }
        args.chunks_exact(2)
            .map(|pair| {
                if pair[0].node().sort != K::sort_ref() || pair[1].node().sort != V::sort_ref() {
                    return Err(DecodeError("map entry has a different exact sort".into()));
                }
                Ok((
                    K::from_expression(pair[0].clone()),
                    V::from_expression(pair[1].clone()),
                ))
            })
            .collect()
    }
}
impl<K: EgglogValue, V: EgglogValue> TryFrom<Map<K, V>> for std::vec::Vec<(K, V)> {
    type Error = DecodeError;
    fn try_from(value: Map<K, V>) -> Result<Self, Self::Error> {
        Self::try_from(&value)
    }
}
impl<L: EgglogValue, R: EgglogValue, A: Into<L>, B: Into<R>> From<(A, B)> for Pair<L, R> {
    fn from((a, b): (A, B)) -> Self {
        Self::new(a, b)
    }
}
impl<L: EgglogValue, R: EgglogValue> TryFrom<&Pair<L, R>> for (L, R) {
    type Error = DecodeError;
    fn try_from(value: &Pair<L, R>) -> Result<Self, Self::Error> {
        value.fields()
    }
}
impl<L: EgglogValue, R: EgglogValue> Pair<L, R> {
    /// Inspect both fields without evaluation or detachment. Observed children
    /// retain their snapshot, including equality-class references.
    pub fn fields(&self) -> Result<(L, R), DecodeError> {
        if self.0.node().sort != Self::sort_ref() {
            return Err(DecodeError("expected exact Pair sort".into()));
        }
        let args = match &self.0.node().kind {
            NodeKind::Call(head, args) if *head == CallableRef::primitive("pair", true) => {
                Cow::Borrowed(args.as_slice())
            }
            NodeKind::Frozen(reference) => Cow::Owned(reference.children()?),
            _ => return Err(DecodeError("expected portable pair form".into())),
        };
        if args.len() != 2
            || args[0].node().sort != L::sort_ref()
            || args[1].node().sort != R::sort_ref()
        {
            return Err(DecodeError(
                "expected two Pair fields with their exact sorts".into(),
            ));
        }
        Ok((
            L::from_expression(args[0].clone()),
            R::from_expression(args[1].clone()),
        ))
    }
}
impl<L: EgglogValue, R: EgglogValue> TryFrom<Pair<L, R>> for (L, R) {
    type Error = DecodeError;
    fn try_from(value: Pair<L, R>) -> Result<Self, Self::Error> {
        Self::try_from(&value)
    }
}
impl From<num::BigInt> for BigInt {
    fn from(value: num::BigInt) -> Self {
        Self::from_string(value.to_string())
    }
}
impl From<&num::BigInt> for BigInt {
    fn from(value: &num::BigInt) -> Self {
        Self::from_string(value.to_string())
    }
}
impl TryFrom<&BigInt> for num::BigInt {
    type Error = DecodeError;
    fn try_from(value: &BigInt) -> Result<Self, Self::Error> {
        if value.0.node().sort != BigInt::sort_ref() {
            return Err(DecodeError("expected exact BigInt sort".into()));
        }
        match &value.0.node().kind {
            NodeKind::Frozen(reference) => match reference.scalar() {
                Some(FrozenScalar::BigInt(value)) => Ok(value.clone()),
                _ => Err(DecodeError("expected frozen BigInt scalar".into())),
            },
            NodeKind::Call(head, args)
                if *head == CallableRef::primitive("bigint", true) && args.len() == 1 =>
            {
                Ok(i64::try_from(I64::from_expression(args[0].clone()))?.into())
            }
            NodeKind::Call(head, args)
                if *head == CallableRef::primitive("from-string", false) && args.len() == 1 =>
            {
                let text = std::string::String::try_from(String::from_expression(args[0].clone()))?;
                text.parse()
                    .map_err(|_| DecodeError("invalid portable BigInt decimal".into()))
            }
            _ => Err(DecodeError(
                "expected portable bigint or from-string form".into(),
            )),
        }
    }
}
impl TryFrom<BigInt> for num::BigInt {
    type Error = DecodeError;
    fn try_from(value: BigInt) -> Result<Self, Self::Error> {
        Self::try_from(&value)
    }
}
impl From<num::BigRational> for BigRat {
    fn from(value: num::BigRational) -> Self {
        Self::new(value.numer(), value.denom())
    }
}
impl From<num::BigInt> for BigRat {
    fn from(value: num::BigInt) -> Self {
        Self::new(value, 1)
    }
}
impl From<&num::BigInt> for BigRat {
    fn from(value: &num::BigInt) -> Self {
        Self::new(value, 1)
    }
}
impl TryFrom<&BigRat> for num::BigRational {
    type Error = DecodeError;
    fn try_from(value: &BigRat) -> Result<Self, Self::Error> {
        if value.0.node().sort != BigRat::sort_ref() {
            return Err(DecodeError("expected exact BigRat sort".into()));
        }
        match &value.0.node().kind {
            NodeKind::Frozen(reference) => match reference.scalar() {
                Some(FrozenScalar::BigRat(value)) => Ok(value.clone()),
                _ => Err(DecodeError("expected frozen BigRat scalar".into())),
            },
            NodeKind::Call(head, args)
                if *head == CallableRef::primitive("bigrat", false) && args.len() == 2 =>
            {
                let numerator = num::BigInt::try_from(BigInt::from_expression(args[0].clone()))?;
                let denominator = num::BigInt::try_from(BigInt::from_expression(args[1].clone()))?;
                if denominator == num::BigInt::from(0) {
                    return Err(DecodeError("zero BigRat denominator".into()));
                }
                Ok(num::BigRational::new(numerator, denominator))
            }
            _ => Err(DecodeError("expected portable bigrat form".into())),
        }
    }
}
impl TryFrom<BigRat> for num::BigRational {
    type Error = DecodeError;
    fn try_from(value: BigRat) -> Result<Self, Self::Error> {
        Self::try_from(&value)
    }
}
impl From<num::rational::Rational64> for Rational {
    fn from(value: num::rational::Rational64) -> Self {
        Self::new(*value.numer(), *value.denom())
    }
}
impl TryFrom<&Rational> for num::rational::Rational64 {
    type Error = DecodeError;
    fn try_from(value: &Rational) -> Result<Self, Self::Error> {
        if value.0.node().sort != Rational::sort_ref() {
            return Err(DecodeError("expected exact Rational sort".into()));
        }
        match &value.0.node().kind {
            NodeKind::Frozen(reference) => match reference.scalar() {
                Some(FrozenScalar::Rational(value)) => Ok(*value),
                _ => Err(DecodeError("expected frozen Rational scalar".into())),
            },
            NodeKind::Call(head, args)
                if *head == CallableRef::primitive("rational", false) && args.len() == 2 =>
            {
                let numerator = i64::try_from(I64::from_expression(args[0].clone()))?;
                let denominator = i64::try_from(I64::from_expression(args[1].clone()))?;
                if denominator == 0 {
                    return Err(DecodeError("zero Rational denominator".into()));
                }
                // Normalize in unbounded arithmetic so an invalid portable value
                // returns a decode error instead of overflowing during reduction.
                let normalized = num::BigRational::new(numerator.into(), denominator.into());
                let numerator = num::ToPrimitive::to_i64(normalized.numer())
                    .ok_or_else(|| DecodeError("Rational numerator does not fit i64".into()))?;
                let denominator = num::ToPrimitive::to_i64(normalized.denom())
                    .ok_or_else(|| DecodeError("Rational denominator does not fit i64".into()))?;
                Ok(Self::new_raw(numerator, denominator))
            }
            _ => Err(DecodeError("expected portable rational form".into())),
        }
    }
}
impl TryFrom<Rational> for num::rational::Rational64 {
    type Error = DecodeError;
    fn try_from(value: Rational) -> Result<Self, Self::Error> {
        Self::try_from(&value)
    }
}
