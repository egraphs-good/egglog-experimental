#![cfg(feature = "typed")]

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
fn generated_vec_calls_and_ordered_values_execute_as_bytes() -> Result<(), TypedError> {
    let xs = EVec::<I64>::of([7_i64, 11, 7]);
    assert!(Vec::<I64>::try_from(&xs).is_err(), "of is symbolic syntax");
    let mut graph = EGraph::default();
    graph.register(&xs)?;
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
    assert_ne!(xs, value, "symbolic Call is not an inert value record");
    assert!(graph.check(eq(&xs, &value))?);
    for empty in [
        EVec::<I64>::empty(),
        EVec::<I64>::of(std::iter::empty::<I64>()),
    ] {
        assert!(Vec::<I64>::try_from(&graph.extract(empty)?)?.is_empty());
    }
    let error = graph.extract(xs.get(9_i64)).unwrap_err();
    let TypedError::Engine(error) = error else {
        panic!("{error}")
    };
    assert_eq!(
        error.code,
        egglog_experimental::proto::ErrorCode::EvaluationFailed as i32
    );
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
