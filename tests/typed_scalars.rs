#![cfg(feature = "typed")]

use egglog_experimental::typed::{
    builtins::{F64, I64},
    prelude::*,
};
use std::hash::{DefaultHasher, Hash, Hasher};

#[sort]
pub struct Math;
#[declarations]
impl Math {
    #[constructor(from, try_from, args = NumArgs)]
    pub fn Num(value: I64) -> Self;
    pub fn Add(a: Math, b: Math) -> Self;
}

#[test]
fn generated_addition_in_constructor_callback_executes_as_bytes() -> Result<(), TypedError> {
    let fold = ruleset(|i: &I64, j: &I64| {
        rewrite(Math::Add(Math::Num(i), Math::Num(j)), Math::Num(i + j))
    });
    let term = Math::Add(Math::Num(2_i64), Math::Num(3_i64));
    let mut graph = EGraph::default();
    graph.register(&term)?;
    graph.run(&fold)?;
    assert!(graph.check(eq(&term, Math::Num(5_i64)))?);
    let value: I64 = graph.extract(&term)?.try_into()?;
    assert_eq!(i64::try_from(&value)?, 5);
    assert_eq!(NumArgs::get_args(&Math::Num(&value))?.unwrap().value, value);
    assert!(get_args(&term, |x: &I64| Math::Num(x))?.is_none());
    let fresh = NumArgs::fresh();
    assert_ne!(fresh.value, NumArgs::fresh().value);
    assert_ne!(fresh.value, var::<I64>("__typed_v_0"));
    assert!(graph.check(Math::Num(&fresh.value))?);
    graph.run(&fold)?;
    Ok(())
}

#[test]
fn literals_and_all_operand_ownership_forms_remain_syntax() -> Result<(), TypedError> {
    let a = I64::from(2);
    let b = I64::from(3);
    let sum = &a + &b;
    assert_eq!(a.clone() + b.clone(), sum);
    assert_eq!(a.clone() + &b, sum);
    assert_eq!(&a + b.clone(), sum);
    assert_ne!(sum, I64::from(5));
    assert!(i64::try_from(&sum).is_err());
    assert!(get_args(&sum, |x: &I64, y: &I64| x + y).is_err());
    assert!(i64::try_from(&var::<I64>("x")).is_err());
    for value in [i64::MIN, -1, 0, i64::MAX] {
        assert_eq!(i64::try_from(&I64::from(value))?, value);
        assert_eq!(i64::try_from(&I64::from(&value))?, value);
    }
    let a = F64::from(1.25);
    let b = F64::from(2.5);
    let sum = &a + &b;
    assert_eq!(a.clone() + b.clone(), sum);
    assert_eq!(a.clone() + &b, sum);
    assert_eq!(&a + b.clone(), sum);
    assert!(f64::try_from(&sum).is_err());
    let mut graph = EGraph::default();
    assert_eq!(
        i64::try_from(&graph.extract(I64::from(2) + I64::from(3))?)?,
        5
    );
    assert_eq!(f64::try_from(&graph.extract(sum)?)?, 3.75);
    Ok(())
}

#[test]
fn exact_float_bits_are_distinct_from_native_equality() -> Result<(), TypedError> {
    for bits in [
        0,
        1 << 63,
        1,
        0x7ff0_0000_0000_0000,
        0x7ff8_0000_0000_0001,
        0x7ff8_0000_0000_0002,
    ] {
        let value = f64::from_bits(bits);
        let a = F64::from(value);
        let b = F64::from(&value);
        assert_eq!(f64::try_from(&a)?.to_bits(), bits);
        assert_eq!(a, b);
        let mut ah = DefaultHasher::new();
        let mut bh = DefaultHasher::new();
        a.hash(&mut ah);
        b.hash(&mut bh);
        assert_eq!(ah.finish(), bh.finish());
    }
    let positive = F64::from(0.0);
    let negative = F64::from(-0.0);
    let nan_a = F64::from(f64::from_bits(0x7ff8_0000_0000_0001));
    let nan_b = F64::from(f64::from_bits(0x7ff8_0000_0000_0002));
    assert_ne!(positive, negative);
    assert_ne!(nan_a, nan_b);
    let mut graph = EGraph::default();
    assert!(graph.check(eq(&positive, &negative))?);
    assert!(graph.check(eq(&nan_a, &nan_b))?);
    Ok(())
}

#[test]
fn overflow_is_native_evaluation_failure_not_authoring_arithmetic() {
    let value = I64::from(i64::MAX) + I64::from(1);
    assert!(i64::try_from(&value).is_err());
    let error = EGraph::default().extract(&value).unwrap_err();
    let TypedError::Engine(error) = error else {
        panic!("expected structured engine failure: {error}");
    };
    assert_eq!(
        error.code,
        egglog_experimental::proto::ErrorCode::EvaluationFailed as i32
    );
}

#[test]
// The two symbolic Add orders exercise different ownership/child arrangements,
// even though Clippy treats the overloaded operator as commutative arithmetic.
#[allow(clippy::if_same_then_else)]
fn scalar_chains_compare_hash_and_drop_without_recursive_ownership() {
    for left_growing in [false, true] {
        let chain = || {
            let leaf = I64::from(1);
            let mut value = leaf.clone();
            for _ in 0..100_000 {
                value = if left_growing {
                    value + &leaf
                } else {
                    &leaf + value
                };
            }
            value
        };
        let a = chain();
        let b = chain();
        assert_eq!(a, b);
        let mut ah = DefaultHasher::new();
        let mut bh = DefaultHasher::new();
        a.hash(&mut ah);
        b.hash(&mut bh);
        assert_eq!(ah.finish(), bh.finish());
        std::thread::spawn(move || drop((a, b))).join().unwrap();
    }
}
