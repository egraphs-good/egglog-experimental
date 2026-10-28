#![cfg(feature = "typed")]

use egglog_experimental::proto as pb;
use egglog_experimental::typed::{
    builtins::{I64, Maybe, Vec as EVec},
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
    pub fn Pack(value: Maybe<Atom>) -> Self;
}

#[test]
fn maybe_inspection_preserves_none_and_symbolic_children() -> Result<(), TypedError> {
    let none = Maybe::<I64>::none();
    let symbolic = I64::from(7) / I64::from(0);
    let some = Maybe::<I64>::some(&symbolic);
    assert_eq!(some.call_name(), None);
    assert_eq!(Option::<I64>::try_from(&none)?, None);
    assert_eq!(Option::<I64>::try_from(&some)?, Some(symbolic));
    let nested = Maybe::<Maybe<I64>>::some(&none);
    assert_eq!(Option::<Maybe<I64>>::try_from(&nested)?, Some(none));
    assert_ne!(nested, Maybe::<Maybe<I64>>::none());
    assert!(Option::<I64>::try_from(&var::<Maybe<I64>>("symbolic")).is_err());
    let indirect = EVec::of([&some]).get(0_i64);
    assert!(Option::<I64>::try_from(&indirect).is_err());
    let atom = Atom::A();
    let packed = Atom::Pack(Maybe::some(&atom));
    assert_eq!(
        Option::<Atom>::try_from(&PackArgs::get_args(&packed)?.unwrap().value)?,
        Some(atom)
    );
    Ok(())
}

#[test]
fn maybe_calls_values_and_eager_defaults_execute_as_bytes() -> Result<(), TypedError> {
    let mut graph = EGraph::default();
    let none = Maybe::<I64>::none();
    let some = Maybe::<I64>::some(7_i64);
    assert_eq!(i64::try_from(&graph.extract(some.unwrap())?)?, 7);
    assert_eq!(i64::try_from(&graph.extract(some.unwrap_or(2_i64))?)?, 7);
    assert_eq!(i64::try_from(&graph.extract(none.unwrap_or(2_i64))?)?, 2);
    assert!(
        matches!(graph.extract(none.unwrap()), Err(TypedError::Engine(frame)) if matches!(&frame.result, Some(pb::run_program_response::Result::Error(error))
        if error.code == pb::ErrorCode::RuntimeFailure as i32))
    );
    assert!(
        matches!(graph.extract(some.unwrap_or(I64::from(1) / I64::from(0))), Err(TypedError::Engine(frame)) if matches!(&frame.result, Some(pb::run_program_response::Result::Error(error))
        if error.code == pb::ErrorCode::RuntimeFailure as i32))
    );
    let formed = graph.extract(&some)?;
    assert_eq!(some, formed);
    assert_eq!(Option::<I64>::try_from(&formed)?, Some(I64::from(7)));
    let nested = graph.extract(Maybe::<Maybe<I64>>::some(&none))?;
    let child = Option::<Maybe<I64>>::try_from(&nested)?.unwrap();
    assert_eq!(Option::<I64>::try_from(&child)?, None);
    drop(graph);
    let mut fresh = EGraph::default();
    assert_eq!(fresh.extract(&formed)?, formed);
    let replayed = fresh.extract(&nested)?;
    assert_eq!(replayed, nested);
    let mut before = DefaultHasher::new();
    let mut after = DefaultHasher::new();
    nested.hash(&mut before);
    replayed.hash(&mut after);
    assert_eq!(before.finish(), after.finish());
    Ok(())
}

#[test]
fn maybe_nested_equality_values_rebuild_and_keep_owned_sharing() -> Result<(), TypedError> {
    let a = Atom::A();
    let b = Atom::B();
    let left = Maybe::<Maybe<Atom>>::some(Maybe::<Atom>::some(&a));
    let right = Maybe::<Maybe<Atom>>::some(Maybe::<Atom>::some(&b));
    let mut graph = EGraph::default();
    graph.register((&left, &right))?;
    graph.register(union(&a, &b))?;
    assert!(graph.check(eq(&left, &right))?);
    let repeated = graph.extract(EVec::<Maybe<Maybe<Atom>>>::of([&left, &left]))?;
    drop(graph);
    let values = Vec::<Maybe<Maybe<Atom>>>::try_from(&repeated)?;
    assert_eq!(values.len(), 2);
    assert_eq!(values[0], values[1]);
    assert!(Option::<Maybe<Atom>>::try_from(&values[0])?.is_some());
    let mut fresh = EGraph::default();
    assert_eq!(fresh.extract(&repeated)?, repeated);
    Ok(())
}
