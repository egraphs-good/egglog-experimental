#![cfg(feature = "typed")]

use egglog_experimental::proto as pb;
use egglog_experimental::typed::{
    builtins::{I64, Vec as EVec},
    prelude::*,
};
use std::hash::{DefaultHasher, Hash, Hasher};

#[sort]
pub struct Atom;
#[declarations]
impl Atom {
    pub fn A() -> Self;
    pub fn B() -> Self;
    #[constructor(args = PackArgs)]
    pub fn Pack(values: EVec<Atom>) -> Self;
}

#[test]
fn append_receiver_and_equality_union_execute_as_bytes() -> Result<(), TypedError> {
    let xs = EVec::<I64>::of([1_i64, 2]);
    let ys = EVec::<I64>::of([3_i64]);
    let mut graph = EGraph::default();
    for (call, expected) in [
        (xs.append(std::iter::empty::<EVec<I64>>()), vec![1, 2]),
        (xs.append([&ys, &xs]), vec![1, 2, 3, 1, 2]),
    ] {
        assert!(Vec::<I64>::try_from(&call).is_err());
        assert_eq!(
            Vec::<I64>::try_from(&graph.extract(call)?)?
                .iter()
                .map(i64::try_from)
                .collect::<Result<Vec<_>, _>>()?,
            expected
        );
    }
    let a = Atom::A();
    let b = Atom::B();
    let left = EVec::<Atom>::of([&a]);
    let right = EVec::<Atom>::of([&b]);
    graph.register(left.union(&right))?;
    assert!(graph.check(eq(&a, &b))?);
    let bad_length = left.union(EVec::<Atom>::empty());
    assert!(
        matches!(graph.register(bad_length), Err(TypedError::Engine(frame)) if matches!(&frame.result, Some(pb::run_program_response::Result::Error(error))
        if error.code == pb::ErrorCode::RuntimeFailure as i32))
    );
    Ok(())
}

#[test]
fn ordinary_vector_methods_preserve_values_and_failures_through_bytes() -> Result<(), TypedError> {
    let xs = EVec::<I64>::of([7_i64, 11, 7]);
    let mut graph = EGraph::default();
    for (call, expected) in [
        (xs.push(3_i64), vec![7, 11, 7, 3]),
        (xs.pop(), vec![7, 11]),
        (EVec::<I64>::empty().pop(), vec![]),
        (xs.set(1_i64, 9_i64), vec![7, 9, 7]),
        (xs.remove(1_i64), vec![7, 7]),
    ] {
        assert!(Vec::<I64>::try_from(&call).is_err());
        assert_eq!(
            Vec::<I64>::try_from(&graph.extract(call)?)?
                .iter()
                .map(i64::try_from)
                .collect::<Result<Vec<_>, _>>()?,
            expected
        );
    }
    assert_eq!(i64::try_from(&graph.extract(xs.length())?)?, 3);
    assert!(graph.check(xs.contains(11_i64))?);
    assert!(!graph.check(xs.contains(42_i64))?);
    assert!(graph.check(xs.not_contains(42_i64))?);
    assert!(!graph.check(xs.not_contains(11_i64))?);
    for index in [-1_i64, 3] {
        for call in [xs.set(index, 9_i64), xs.remove(index)] {
            assert!(
                matches!(graph.extract(call), Err(TypedError::Engine(frame)) if matches!(&frame.result, Some(pb::run_program_response::Result::Error(error))
        if error.code == pb::ErrorCode::RuntimeFailure as i32))
            );
        }
    }
    let nested = EVec::<EVec<I64>>::of([&xs]);
    assert_eq!(
        Vec::<EVec<I64>>::try_from(&graph.extract(nested.append([&nested]))?)?.len(),
        2
    );
    Ok(())
}

#[test]
fn generated_vec_calls_and_ordered_values_execute_as_bytes() -> Result<(), TypedError> {
    let xs = EVec::<I64>::of([7_i64, 11, 7]);
    assert_eq!(
        Vec::<I64>::try_from(&xs)?,
        [I64::from(7), I64::from(11), I64::from(7)]
    );
    assert_eq!(xs.call_name(), None);
    let symbolic = I64::from(1) / I64::from(0);
    let authored = EVec::<I64>::of([&symbolic]);
    assert_eq!(Vec::<I64>::try_from(&authored)?, [symbolic]);
    let mut graph = EGraph::with_recording(true)?;
    graph.register(&xs)?;
    assert!(graph.history()?.nodes.iter().any(|node| matches!(
        &node.kind,
        Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Vec(_))
        }))
    )));
    assert_eq!(i64::try_from(&graph.extract(xs.get(1_i64))?)?, 11);
    let value = graph.extract(&xs)?;
    let decoded = Vec::<I64>::try_from(&value)?;
    assert_eq!(
        decoded
            .iter()
            .map(i64::try_from)
            .collect::<Result<Vec<_>, _>>()?,
        [7, 11, 7]
    );
    assert_eq!(
        xs, value,
        "already literal children retain their data shape"
    );
    assert!(graph.check(eq(&xs, &value))?);
    for empty in [
        EVec::<I64>::empty(),
        EVec::<I64>::of(std::iter::empty::<I64>()),
    ] {
        assert!(Vec::<I64>::try_from(&graph.extract(empty)?)?.is_empty());
    }
    for (end, expected) in [
        (i64::MIN, vec![]),
        (-1, vec![]),
        (0, vec![]),
        (1, vec![0]),
        (5, vec![0, 1, 2, 3, 4]),
    ] {
        let range: EVec<I64> = I64::from(end).range();
        assert!(Vec::<I64>::try_from(&range).is_err());
        let extracted = graph.extract(&range)?;
        let values = Vec::<I64>::try_from(&extracted)?;
        assert_eq!(
            values
                .iter()
                .map(i64::try_from)
                .collect::<Result<Vec<_>, _>>()?,
            expected
        );
        assert!(graph.check(eq(range, extracted))?);
    }
    let last: I64 = I64::from(5).range().get(4_i64);
    assert_eq!(i64::try_from(&graph.extract(last)?)?, 4);
    let range_error = graph.extract(I64::from(5).range().get(5_i64)).unwrap_err();
    assert!(matches!(range_error, TypedError::Engine(frame)
        if matches!(&frame.result, Some(pb::run_program_response::Result::Error(error))
            if error.code == pb::ErrorCode::RuntimeFailure as i32)));
    let error = graph.extract(xs.get(9_i64)).unwrap_err();
    let TypedError::Engine(frame) = error else {
        panic!("{error}")
    };
    let Some(pb::run_program_response::Result::Error(error)) = &frame.result else {
        panic!("expected terminal error frame")
    };
    assert_eq!(error.code, pb::ErrorCode::RuntimeFailure as i32);
    assert!(graph.check(eq(xs.get(0_i64), I64::from(7)))?);
    Ok(())
}

#[test]
fn equality_elements_nested_vectors_and_existing_selectors() -> Result<(), TypedError> {
    let a = Atom::A();
    let b = Atom::B();
    let xs = EVec::<Atom>::of([&a, &b, &a]);
    let empty = EVec::<Atom>::empty();
    let nested = EVec::<EVec<Atom>>::of([&xs, &empty]);
    let packed = Atom::Pack(&xs);
    assert_eq!(PackArgs::get_args(&packed)?.unwrap().values, xs);
    let mut graph = EGraph::default();
    graph.register((&packed, &nested))?;
    assert!(graph.check(eq(xs.get(1_i64), &b))?);
    let extracted = graph.extract(&nested)?;
    let outer = Vec::<EVec<Atom>>::try_from(&extracted)?;
    assert_eq!(outer.len(), 2);
    let inner = Vec::<Atom>::try_from(&outer[0])?;
    assert_eq!(inner, [a.clone(), b, a]);
    assert!(Vec::<Atom>::try_from(&outer[1])?.is_empty());
    assert_eq!(
        PackArgs::get_args(&graph.extract(&packed)?)?
            .unwrap()
            .values,
        outer[0]
    );
    let fresh = PackArgs::fresh();
    assert_ne!(fresh.values, PackArgs::fresh().values);
    assert!(graph.check(Atom::Pack(&fresh.values))?);
    Ok(())
}

#[test]
fn vector_composition_retains_iterative_comparison_hash_and_drop() {
    for growing_first in [false, true] {
        let chain = || {
            let leaf = Atom::A();
            let mut term = leaf.clone();
            for _ in 0..100_000 {
                let children = if growing_first {
                    [term, leaf.clone()]
                } else {
                    [leaf.clone(), term]
                };
                term = Atom::Pack(EVec::<Atom>::of(children));
            }
            term
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
