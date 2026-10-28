#![cfg(feature = "typed")]

use egglog_experimental::proto as pb;
use egglog_experimental::typed::{
    builtins::{F64, I64, Map, Pair, Vec as EVec},
    prelude::*,
};

#[sort]
pub struct Atom;
#[declarations]
impl Atom {
    pub fn A() -> Self;
    #[constructor(args = PackArgs)]
    pub fn Pack(value: Map<Atom, EVec<Pair<I64, I64>>>) -> Self;
}

#[test]
fn ordinary_map_methods_execute_as_bytes() -> Result<(), TypedError> {
    let map = Map::<I64, I64>::of([(1_i64, 7_i64), (2, 9)]);
    let mut graph = EGraph::default();
    assert_eq!(i64::try_from(&graph.extract(map.length())?)?, 2);
    let removed = map.remove(1_i64);
    assert!(removed.entries().is_err());
    assert_eq!(
        graph.extract(removed)?.entries()?,
        [(I64::from(2), I64::from(9))]
    );
    assert!(graph.check(eq(map.remove(42_i64), &map))?);
    assert!(graph.check(map.contains(1_i64))?);
    assert!(!graph.check(map.contains(42_i64))?);
    assert!(graph.check(map.not_contains(42_i64))?);
    assert!(!graph.check(map.not_contains(1_i64))?);
    Ok(())
}

#[test]
fn map_tuple_packing_and_direct_entries_preserve_symbolic_order() -> Result<(), TypedError> {
    fn generic<K: EgglogValue, V: EgglogValue>(pairs: impl Into<EVec<Pair<K, V>>>) -> Map<K, V> {
        Map::from_pairs(pairs)
    }
    let key = I64::from(2) + I64::from(3);
    let value = F64::from(1.5);
    let pairs = EVec::<Pair<I64, F64>>::of([
        Pair::new(&key, &value),
        Pair::new(1_i64, 2.5_f64),
        Pair::new(&key, 3.5_f64),
    ]);
    let expected = vec![
        (key.clone(), value.clone()),
        (I64::from(1), F64::from(2.5)),
        (key.clone(), F64::from(3.5)),
    ];
    let from_pairs: Map<I64, F64> = generic(&pairs);
    assert_eq!(from_pairs, Map::from_pairs(pairs.clone()));
    assert!(
        from_pairs.entries().is_err(),
        "from_pairs is always an operation"
    );
    let map = Map::<I64, F64>::of(expected.clone());
    assert_eq!(map.call_name(), None);
    assert_eq!(map.entries()?, expected);
    assert_eq!(Vec::<(I64, F64)>::try_from(&map)?, expected);
    assert_eq!(Vec::<(I64, F64)>::try_from(map.clone())?, expected);
    assert_eq!(Map::from(&map), map);
    assert_eq!(Map::<I64, F64>::from(expected.clone()).entries()?, expected);
    assert_eq!(
        Map::<I64, F64>::of([(&key, &value)]).entries()?,
        [(key, value)]
    );
    assert_eq!(Vec::<Pair<I64, F64>>::try_from(&pairs)?.len(), 3);
    for empty in [
        Map::<I64, F64>::empty(),
        Map::<I64, F64>::of(std::iter::empty::<(I64, F64)>()),
    ] {
        assert!(empty.entries()?.is_empty());
    }
    let mut graph = EGraph::with_recording(true)?;
    graph.register(&map)?;
    assert!(graph.history()?.nodes.iter().any(|node| matches!(&node.kind,
        Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue { value: Some(pb::primitive_value::Value::Map(map)) })) if map.entries.len() == 3)));
    assert!(graph.check(eq(&map, &from_pairs))?);
    assert_eq!(graph.extract(&from_pairs)?.entries()?.len(), 2);
    for empty in [
        Map::<I64, F64>::from_pairs(EVec::<Pair<I64, F64>>::empty()),
        Map::<I64, F64>::from_pairs(EVec::<Pair<I64, F64>>::of(
            std::iter::empty::<Pair<I64, F64>>(),
        )),
    ] {
        assert!(empty.entries().is_err());
        assert!(graph.extract(empty)?.entries()?.is_empty());
    }
    assert!(var::<Map<I64, F64>>("map").entries().is_err());
    assert!(map.insert(9_i64, 4.5_f64).entries().is_err());
    Ok(())
}

#[test]
fn map_converts_each_host_component_once() -> Result<(), TypedError> {
    use std::{cell::Cell, rc::Rc};
    struct Counted(i64, Rc<Cell<usize>>);
    impl From<Counted> for I64 {
        fn from(value: Counted) -> Self {
            value.1.set(value.1.get() + 1);
            I64::from(value.0)
        }
    }
    let count = Rc::new(Cell::new(0));
    let map = Map::<I64, I64>::of(
        [(2, 7), (1, 8), (2, 9)]
            .map(|(k, v)| (Counted(k, count.clone()), Counted(v, count.clone()))),
    );
    assert_eq!(count.get(), 6);
    assert_eq!(
        map.entries()?,
        [
            (I64::from(2), I64::from(7)),
            (I64::from(1), I64::from(8)),
            (I64::from(2), I64::from(9))
        ]
    );
    assert_eq!(count.get(), 6);
    Ok(())
}

#[test]
fn maps_execute_computed_vec_inputs_and_reingest_native_values() -> Result<(), TypedError> {
    let pairs = EVec::<Pair<I64, F64>>::of([Pair::new(7_i64, 1.5_f64), Pair::new(7_i64, 2.5_f64)]);
    let computed = EVec::<EVec<Pair<I64, F64>>>::of([&pairs]).get(0_i64);
    let map = Map::<I64, F64>::from_pairs(&computed);
    assert!(map.entries().is_err(), "inspection cannot evaluate Vec.get");
    let mut graph = EGraph::default();
    graph.register(&map)?;
    assert_eq!(f64::try_from(&graph.extract(map.get(7_i64))?)?, 2.5);
    let value = graph.extract(&map)?;
    assert_eq!(value.entries()?, [(I64::from(7), F64::from(2.5))]);
    assert_ne!(value, map);
    assert!(graph.check(eq(&value, &map))?);
    let key = I64::from(7);
    let replacement = F64::from(3.5);
    let updated = value.insert(&key, &replacement);
    assert_eq!(graph.extract(updated.get(key))?, replacement);
    let error = graph.extract(value.get(99_i64)).unwrap_err();
    let TypedError::Engine(frame) = error else {
        panic!("{error}")
    };
    let Some(pb::run_program_response::Result::Error(error)) = &frame.result else {
        panic!("expected terminal error frame")
    };
    assert_eq!(error.code, pb::ErrorCode::RuntimeFailure as i32);
    assert!(graph.check(eq(value.get(7_i64), F64::from(2.5)))?);
    drop(graph);
    let mut fresh = EGraph::default();
    assert_eq!(fresh.extract(&value)?.entries()?, value.entries()?);
    Ok(())
}

#[test]
fn nested_maps_pairs_vectors_and_selectors_keep_graph_independent_ownership()
-> Result<(), TypedError> {
    let atom = Atom::A();
    let pair = Pair::<I64, I64>::new(7_i64, 11_i64);
    let vector = EVec::<Pair<I64, I64>>::of([&pair, &pair]);
    let map = Map::<Atom, EVec<Pair<I64, I64>>>::of([(&atom, &vector)]);
    let packed = Atom::Pack(&map);
    assert_eq!(PackArgs::get_args(&packed)?.unwrap().value, map);
    let nested = Pair::<EVec<Map<Atom, EVec<Pair<I64, I64>>>>, Map<I64, Map<I64, F64>>>::new(
        EVec::of([&map, &map]),
        Map::of([(1_i64, Map::<I64, F64>::of([(2_i64, 3.5_f64)]))]),
    );
    let mut graph = EGraph::default();
    graph.register((&packed, &nested))?;
    let value = graph.extract(nested)?;
    let packed = graph.extract(packed)?;
    drop(graph);
    let (maps, outer) = value.fields()?;
    let maps = Vec::<Map<Atom, EVec<Pair<I64, I64>>>>::try_from(&maps)?;
    assert_eq!(maps.len(), 2);
    assert_eq!(maps[0], maps[1]);
    let entries = maps[0].entries()?;
    assert_eq!(entries[0].0, atom);
    let pairs = Vec::<Pair<I64, I64>>::try_from(&entries[0].1)?;
    assert_eq!(pairs[0], pairs[1]);
    assert_eq!(pairs[0].fields()?, (I64::from(7), I64::from(11)));
    assert_eq!(
        outer.entries()?[0].1.entries()?,
        [(I64::from(2), F64::from(3.5))]
    );
    assert_eq!(PackArgs::get_args(&packed)?.unwrap().value, maps[0]);
    Ok(())
}
