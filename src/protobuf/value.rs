//! The scalar wire codec and its typed native/host representation.
//!
//! This is the authority for payload/sort agreement and exact numeric validity.
//! Host runtimes adapt these typed values mechanically; they do not parse wire
//! integers or interpret constructor-shaped expressions.

use crate::proto as pb;
use egglog::{ArcSort, EGraph, Value};
use num::{Integer, One, ToPrimitive, Zero};
use std::any::TypeId;

pub use num::{BigInt, BigRational, rational::Rational64};

#[derive(Clone, Copy, PartialEq, Eq)]
enum ScalarFamily {
    I64,
    F64,
    String,
    Bool,
    Unit,
    BigInt,
    BigRat,
    Rational,
}

impl TryFrom<&str> for ScalarFamily {
    type Error = String;
    fn try_from(name: &str) -> Result<Self, Self::Error> {
        Ok(match name {
            "i64" => Self::I64,
            "f64" => Self::F64,
            "String" => Self::String,
            "bool" => Self::Bool,
            "Unit" => Self::Unit,
            "BigInt" => Self::BigInt,
            "BigRat" => Self::BigRat,
            "Rational" => Self::Rational,
            _ => return Err("sort has no builtin scalar codec".into()),
        })
    }
}

/// Validate a leaf provider payload, preserving builtin scalar family ownership.
/// Custom codecs may produce only childless data of a non-scalar family.
pub fn validate_leaf(family: &str, value: &pb::PrimitiveValue) -> Result<(), String> {
    if let Some(pb::primitive_value::Value::Custom(custom)) = &value.value {
        if !custom.args.is_empty() || ScalarFamily::try_from(family).is_ok() {
            return Err("custom leaf codec disagrees with its declared result sort".into());
        }
        Ok(())
    } else {
        Scalar::decode(Some(family), value).map(|_| ())
    }
}

/// An owned native scalar, independent of an e-graph and host language.
#[derive(Clone, Debug, PartialEq)]
pub enum Scalar {
    /// A signed 64-bit integer.
    I64(i64),
    /// The exact IEEE-754 bit pattern.
    F64Bits(u64),
    /// A Unicode string.
    String(String),
    /// A boolean.
    Bool(bool),
    /// The single Unit value.
    Unit,
    /// An arbitrary-precision integer.
    BigInt(BigInt),
    /// A reduced arbitrary-precision fraction.
    BigRat(BigRational),
    /// A reduced fraction with signed 64-bit components.
    Rational(Rational64),
}

impl Scalar {
    /// Decode scalar data without normalization; when supplied, `family` must
    /// agree with the payload. Sortless proof literals omit the expected family.
    pub fn decode(family: Option<&str>, value: &pb::PrimitiveValue) -> Result<Self, String> {
        use pb::primitive_value::Value as V;
        let (actual, scalar) = match value.value.as_ref() {
            Some(V::I64(value)) => (ScalarFamily::I64, Self::I64(*value)),
            Some(V::F64Bits(bits)) => (ScalarFamily::F64, Self::F64Bits(*bits)),
            Some(V::String(value)) => (ScalarFamily::String, Self::String(value.clone())),
            Some(V::Bool(value)) => (ScalarFamily::Bool, Self::Bool(*value)),
            Some(V::Unit(_)) => (ScalarFamily::Unit, Self::Unit),
            Some(V::BigInt(text)) => (ScalarFamily::BigInt, Self::BigInt(canonical_decimal(text)?)),
            Some(V::BigRat(ratio)) => {
                let numerator = canonical_decimal(&ratio.numerator)?;
                let denominator = canonical_decimal(&ratio.denominator)?;
                check_fraction(&numerator, &denominator)?;
                (
                    ScalarFamily::BigRat,
                    Self::BigRat(BigRational::new_raw(numerator, denominator)),
                )
            }
            Some(V::Rational(ratio)) => {
                check_fraction(
                    &BigInt::from(ratio.numerator),
                    &BigInt::from(ratio.denominator),
                )?;
                (
                    ScalarFamily::Rational,
                    Self::Rational(Rational64::new_raw(ratio.numerator, ratio.denominator)),
                )
            }
            _ => return Err("expected a scalar value".into()),
        };
        let expected = family.map(ScalarFamily::try_from).transpose()?;
        if expected.is_some_and(|family| family != actual) {
            return Err("scalar payload does not match its sort".into());
        }
        Ok(scalar)
    }

    /// Form host fraction data using unbounded reduction before range checking.
    /// This normalization is a host construction operation, never wire decoding.
    pub fn from_fraction(
        family: &str,
        numerator: BigInt,
        denominator: BigInt,
    ) -> Result<Self, String> {
        if denominator.is_zero() {
            return Err("fraction denominator must be nonzero".into());
        }
        let value = BigRational::new(numerator, denominator);
        match family {
            "BigRat" => Ok(Self::BigRat(value)),
            "Rational" => Ok(Self::Rational(Rational64::new_raw(
                value
                    .numer()
                    .to_i64()
                    .ok_or("Rational numerator is outside i64")?,
                value
                    .denom()
                    .to_i64()
                    .ok_or("Rational denominator is outside positive i64")?,
            ))),
            _ => Err("expected BigRat or Rational sort".into()),
        }
    }

    /// Encode scalar data, checking host ratios made with `new_raw` as well.
    pub fn encode(&self) -> Result<pb::PrimitiveValue, String> {
        use pb::primitive_value::Value as V;
        let value = match self {
            Self::I64(value) => V::I64(*value),
            Self::F64Bits(value) => V::F64Bits(*value),
            Self::String(value) => V::String(value.clone()),
            Self::Bool(value) => V::Bool(*value),
            Self::Unit => V::Unit(pb::Unit {}),
            Self::BigInt(value) => V::BigInt(value.to_string()),
            Self::BigRat(value) => {
                check_fraction(value.numer(), value.denom())?;
                V::BigRat(pb::BigRat {
                    numerator: value.numer().to_string(),
                    denominator: value.denom().to_string(),
                })
            }
            Self::Rational(value) => {
                check_fraction(&BigInt::from(*value.numer()), &BigInt::from(*value.denom()))?;
                V::Rational(pb::Rational {
                    numerator: *value.numer(),
                    denominator: *value.denom(),
                })
            }
        };
        Ok(pb::PrimitiveValue { value: Some(value) })
    }

    /// Lower scalar data to native literal payloads, without constructor calls.
    pub fn into_literal(self) -> Result<egglog::ast::Literal, String> {
        use egglog::ast::Literal;
        use egglog::prelude::BaseSort;
        Ok(match self {
            Self::I64(value) => Literal::Int(value),
            Self::F64Bits(bits) => Literal::Float(f64::from_bits(bits).into()),
            Self::String(value) => Literal::String(value),
            Self::Bool(value) => Literal::Bool(value),
            Self::Unit => Literal::Unit,
            Self::BigInt(value) => egglog::sort::base_literal(
                egglog::sort::BigIntSort.to_arcsort(),
                egglog::sort::Z::new(value),
            )?,
            Self::BigRat(value) => egglog::sort::base_literal(
                egglog::sort::BigRatSort.to_arcsort(),
                egglog::sort::Q::new(value),
            )?,
            Self::Rational(value) => egglog::sort::base_literal(
                crate::rational::RationalSort.to_arcsort(),
                crate::rational::R::new(value),
            )?,
        })
    }

    /// Recover a typed scalar from a native literal without evaluating syntax.
    pub fn from_literal(literal: &egglog::ast::Literal) -> Result<(&'static str, Self), String> {
        use egglog::ast::Literal;
        Ok(match literal {
            Literal::Int(value) => ("i64", Self::I64(*value)),
            Literal::Float(value) => ("f64", Self::F64Bits(value.0.to_bits())),
            Literal::String(value) => ("String", Self::String(value.clone())),
            Literal::Bool(value) => ("bool", Self::Bool(*value)),
            Literal::Unit => ("Unit", Self::Unit),
            Literal::Native(_) => {
                let sort = egglog::sort::literal_sort(literal);
                if sort.value_type() == Some(TypeId::of::<egglog::sort::Z>()) {
                    (
                        "BigInt",
                        Self::BigInt(
                            egglog::sort::downcast_base_literal::<egglog::sort::Z>(literal)?.0,
                        ),
                    )
                } else if sort.value_type() == Some(TypeId::of::<egglog::sort::Q>()) {
                    (
                        "BigRat",
                        Self::BigRat(
                            egglog::sort::downcast_base_literal::<egglog::sort::Q>(literal)?.0,
                        ),
                    )
                } else if sort.value_type() == Some(TypeId::of::<crate::rational::R>()) {
                    (
                        "Rational",
                        Self::Rational(
                            egglog::sort::downcast_base_literal::<crate::rational::R>(literal)?.0,
                        ),
                    )
                } else {
                    return Err("native literal requires an explicit custom codec".into());
                }
            }
        })
    }

    /// Read an actual base value without reconstructing or interpreting syntax.
    /// Unknown native types remain the responsibility of explicit custom codecs.
    pub fn reflect(graph: &EGraph, sort: &ArcSort, value: Value) -> Option<Self> {
        let actual = sort.value_type()?;
        Some(if actual == TypeId::of::<i64>() {
            Self::I64(graph.value_to_base::<i64>(value))
        } else if actual == TypeId::of::<egglog::sort::F>() {
            Self::F64Bits(graph.value_to_base::<egglog::sort::F>(value).0.0.to_bits())
        } else if actual == TypeId::of::<egglog::sort::S>() {
            Self::String(graph.value_to_base::<egglog::sort::S>(value).0)
        } else if actual == TypeId::of::<bool>() {
            Self::Bool(graph.value_to_base::<bool>(value))
        } else if actual == TypeId::of::<()>() {
            Self::Unit
        } else if actual == TypeId::of::<egglog::sort::Z>() {
            Self::BigInt(graph.value_to_base::<egglog::sort::Z>(value).0)
        } else if actual == TypeId::of::<egglog::sort::Q>() {
            Self::BigRat(graph.value_to_base::<egglog::sort::Q>(value).0)
        } else if actual == TypeId::of::<crate::rational::R>() {
            Self::Rational(graph.value_to_base::<crate::rational::R>(value).0)
        } else {
            return None;
        })
    }
}

fn canonical_decimal(text: &str) -> Result<BigInt, String> {
    let value: BigInt = text.parse().map_err(|_| "invalid decimal integer")?;
    if value.to_string() != text {
        return Err("noncanonical decimal integer".into());
    }
    Ok(value)
}

fn check_fraction(numerator: &BigInt, denominator: &BigInt) -> Result<(), String> {
    if denominator <= &BigInt::zero() || numerator.gcd(denominator) != BigInt::one() {
        return Err("fraction must be reduced with a positive denominator".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wire_validation_and_host_normalization_are_separate() {
        for value in ["+1", "01", "-0", "", "1.0"] {
            assert!(
                Scalar::decode(
                    Some("BigInt"),
                    &pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::BigInt(value.into()))
                    }
                )
                .is_err()
            );
        }
        let reduced = Scalar::from_fraction("BigRat", (-2).into(), (-4).into()).unwrap();
        assert_eq!(
            reduced,
            Scalar::BigRat(BigRational::new(1.into(), 2.into()))
        );
        assert!(
            Scalar::BigRat(BigRational::new_raw(2.into(), 4.into()))
                .encode()
                .is_err()
        );
        assert!(Scalar::from_fraction("Rational", 1.into(), BigInt::from(i64::MIN)).is_err());
        let min = Scalar::from_fraction("Rational", BigInt::from(i64::MIN), 1.into()).unwrap();
        assert_eq!(
            Scalar::decode(Some("Rational"), &min.encode().unwrap()).unwrap(),
            min
        );
    }

    #[test]
    fn custom_leaf_codecs_cannot_overload_scalar_families() {
        let mut value = pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Custom(
                pb::CustomValue::default(),
            )),
        };
        assert!(validate_leaf("i64", &value).is_err());
        assert!(validate_leaf("BigRat", &value).is_err());
        assert!(validate_leaf("HostData", &value).is_ok());
        let Some(pb::primitive_value::Value::Custom(custom)) = &mut value.value else {
            unreachable!()
        };
        custom.args.push(0);
        assert!(validate_leaf("HostData", &value).is_err());
    }

    #[test]
    fn scalar_round_trips_preserve_bits_and_large_values() {
        let huge: BigInt = BigInt::from(10).pow(6000) + 123;
        for (family, value) in [
            ("i64", Scalar::I64(i64::MIN)),
            ("f64", Scalar::F64Bits(0xfff8_1234_5678_9abc)),
            ("String", Scalar::String("λ\0\"".into())),
            ("bool", Scalar::Bool(false)),
            ("Unit", Scalar::Unit),
            ("BigInt", Scalar::BigInt(huge.clone())),
            ("BigRat", Scalar::BigRat(BigRational::new(huge, 17.into()))),
            (
                "Rational",
                Scalar::Rational(Rational64::new_raw(i64::MIN, 3)),
            ),
        ] {
            let encoded = value.encode().unwrap();
            assert_eq!(Scalar::decode(Some(family), &encoded).unwrap(), value);
            assert!(Scalar::decode(Some("unknown"), &encoded).is_err());
        }
    }
}

#[derive(Clone, Copy)]
pub(super) enum ContainerKind {
    Vec,
    Set,
    MultiSet,
    Pair,
    Map,
    Maybe,
}

// Admission precedes calling an extensible sort's inner_values method: unknown
// implementations cannot enter a builtin codec merely by printing its name.
pub(super) fn container_kind(
    sort: &ArcSort,
    wire_sort: &pb::Sort,
) -> Result<ContainerKind, String> {
    let Some(pb::sort::Kind::Primitive(family)) = &wire_sort.kind else {
        return Err("container requires a primitive sort".into());
    };
    let (kind, arity) = match (family.name.as_str(), sort.value_type()) {
        ("Vec", Some(t)) if t == TypeId::of::<egglog::sort::VecContainer>() => {
            (ContainerKind::Vec, 1)
        }
        ("Set", Some(t)) if t == TypeId::of::<egglog::sort::SetContainer>() => {
            (ContainerKind::Set, 1)
        }
        ("MultiSet", Some(t)) if t == TypeId::of::<egglog::sort::MultiSetContainer>() => {
            (ContainerKind::MultiSet, 1)
        }
        ("Pair", Some(t)) if t == TypeId::of::<egglog::sort::PairContainer>() => {
            (ContainerKind::Pair, 2)
        }
        ("Map", Some(t)) if t == TypeId::of::<egglog::sort::MapContainer>() => {
            (ContainerKind::Map, 2)
        }
        ("Maybe", Some(t)) if t == TypeId::of::<crate::maybe::MaybeContainer>() => {
            (ContainerKind::Maybe, 1)
        }
        _ => return Err(format!("no inert container codec for {}", sort.name())),
    };
    if family.args.len() != arity || sort.inner_sorts().len() != arity {
        return Err("container runtime type/sort arity mismatch".into());
    }
    Ok(kind)
}

// Children have already been observed in native inner_values order. Their
// structure is data, independent of the sort's source reconstruction spelling.
pub(super) fn container_payload(
    sort: &ArcSort,
    wire_sort: &pb::Sort,
    children: &[u32],
    nodes: &[pb::Node],
) -> Result<pb::primitive_value::Value, String> {
    use pb::primitive_value::Value as V;
    let kind = container_kind(sort, wire_sort)?;
    let Some(pb::sort::Kind::Primitive(family)) = &wire_sort.kind else {
        unreachable!("admitted primitive sort")
    };
    let arity = family.args.len();
    if children.iter().enumerate().any(|(index, child)| {
        nodes
            .get(*child as usize)
            .is_none_or(|node| node.sort_id != family.args[index % arity])
    }) {
        return Err("container child sort mismatch".into());
    }
    Ok(match kind {
        ContainerKind::Vec => V::Vec(pb::ValueList {
            items: children.to_vec(),
        }),
        ContainerKind::Set => V::Set(pb::ValueList {
            items: children.to_vec(),
        }),
        ContainerKind::MultiSet => V::Multiset(pb::ValueList {
            items: children.to_vec(),
        }),
        ContainerKind::Pair if children.len() == 2 => V::Pair(pb::PairValue {
            first: Some(children[0]),
            second: Some(children[1]),
        }),
        ContainerKind::Map if children.len().is_multiple_of(2) => V::Map(pb::MapValue {
            entries: children
                .chunks_exact(2)
                .map(|pair| pb::MapEntry {
                    key: Some(pair[0]),
                    value: Some(pair[1]),
                })
                .collect(),
        }),
        ContainerKind::Maybe if children.len() <= 1 => V::Maybe(pb::MaybeValue {
            value: children.first().copied(),
        }),
        _ => return Err("invalid native container child arity".into()),
    })
}
