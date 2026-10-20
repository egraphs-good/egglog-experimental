#![cfg(feature = "typed")]

use egglog_experimental::typed::{
    builtins::{I64, Pair, Set, Unit, Vec as EVec},
    prelude::*,
};

#[sort]
pub struct Atom;
#[declarations]
impl Atom {
    pub fn A() -> Self;
    pub fn B() -> Self;
    #[constructor(args = PackArgs)]
    pub fn Pack(values: Set<Pair<I64, Atom>>) -> Self;
}

#[test]
fn generated_set_methods_execute_as_bytes_without_local_deduplication() -> Result<(), TypedError> {
    let x = I64::from(2);
    let inputs = [x.clone(), I64::from(1), x];
    let s: Set<I64> = Set::of(inputs.iter());
    assert!(Vec::<I64>::try_from(&s).is_err(), "of remains symbolic");
    let mut graph = EGraph::default();
    graph.register(&s)?;
    let value = graph.extract(&s)?;
    let members = Vec::<I64>::try_from(&value)?;
    assert_eq!(members.len(), 2);
    assert!(members.contains(&I64::from(1)) && members.contains(&I64::from(2)));
    assert_ne!(s, value);
    assert!(graph.check(eq(&s, &value))?);
    assert_eq!(i64::try_from(&graph.extract(s.length())?)?, 2);
    assert!(graph.check(s.contains(1_i64))?);
    assert!(graph.check(s.not_contains(3_i64))?);
    let _: Unit = graph.extract(s.contains(2_i64))?;
    let other = Set::<I64>::of([2_i64, 3]);
    for (actual, expected) in [
        (s.insert(3_i64), Set::of([1_i64, 2, 3])),
        (s.remove(1_i64), Set::of([2_i64])),
        (s.remove(99_i64), s.clone()),
        (s.union(&other), Set::of([1_i64, 2, 3])),
        (s.diff(&other), Set::of([1_i64])),
        (s.intersect(&other), Set::of([2_i64])),
    ] {
        assert!(graph.check(eq(actual, expected))?);
    }
    for empty in [Set::<I64>::empty(), Set::of(std::iter::empty::<I64>())] {
        assert!(Vec::<I64>::try_from(&graph.extract(empty)?)?.is_empty());
    }
    // This is native Value order, independently of extracted enumeration.
    let indexed = Set::<I64>::of([1_i64, -1, 2, 4, 1]);
    assert_eq!(i64::try_from(&graph.extract(indexed.get(0_i64))?)?, 1);
    assert_eq!(i64::try_from(&graph.extract(indexed.get(3_i64))?)?, -1);
    for index in [-1_i64, 2] {
        let TypedError::Engine(error) = graph.extract(s.get(index)).unwrap_err() else {
            panic!("expected native partial get failure")
        };
        assert_eq!(
            error.code,
            egglog_experimental::proto::ErrorCode::EvaluationFailed as i32
        );
        assert!(graph.check(s.contains(1_i64))?);
    }
    for predicate in [s.contains(9_i64), s.not_contains(1_i64)] {
        assert!(matches!(
            graph.extract(predicate),
            Err(TypedError::Engine(_))
        ));
        assert!(graph.check(s.not_contains(9_i64))?);
    }
    assert!(matches!(
        graph.extract(Set::<I64>::empty().get(0_i64)),
        Err(TypedError::Engine(_))
    ));
    Ok(())
}

#[test]
fn set_iterator_conversions_preserve_input_order_and_duplicates() {
    use std::{cell::RefCell, rc::Rc};
    struct Counted(i64, Rc<RefCell<Vec<i64>>>);
    impl From<Counted> for I64 {
        fn from(value: Counted) -> Self {
            value.1.borrow_mut().push(value.0);
            I64::from(value.0)
        }
    }
    let seen = Rc::new(RefCell::new(vec![]));
    let s = Set::<I64>::of([2, 1, 2].into_iter().map(|x| Counted(x, seen.clone())));
    assert_eq!(*seen.borrow(), [2, 1, 2]);
    assert!(Vec::<I64>::try_from(&s).is_err());
    assert_eq!(*seen.borrow(), [2, 1, 2]);
}

#[test]
fn nested_set_values_own_children_and_reingest_after_session_drop() -> Result<(), TypedError> {
    let a = Atom::A();
    let pair = Pair::<I64, Atom>::new(7_i64, &a);
    let s = Set::<Pair<I64, Atom>>::of([&pair, &pair]);
    let packed = Atom::Pack(&s);
    assert_eq!(PackArgs::get_args(&packed)?.unwrap().values, s);
    let nested = Pair::<EVec<Set<Pair<I64, Atom>>>, Set<Set<I64>>>::new(
        EVec::of([&s, &s]),
        Set::of([Set::<I64>::of([1_i64, 2]), Set::empty()]),
    );
    let mut graph = EGraph::default();
    graph.register((&packed, &nested))?;
    let value = graph.extract(&nested)?;
    let packed = graph.extract(&packed)?;
    let mut cloned = graph.try_clone()?;
    drop(graph);
    let (sets, outer) = value.fields()?;
    let sets = Vec::<Set<Pair<I64, Atom>>>::try_from(&sets)?;
    assert_eq!(sets.len(), 2);
    assert_eq!(sets[0], sets[1]);
    let children = Vec::<Pair<I64, Atom>>::try_from(&sets[0])?;
    assert_eq!(children.len(), 1);
    assert_eq!(children[0].fields()?, (I64::from(7), a));
    assert_eq!(PackArgs::get_args(&packed)?.unwrap().values, sets[0]);
    let outer = Vec::<Set<I64>>::try_from(&outer)?;
    let cardinalities = outer
        .iter()
        .map(|s| Vec::<I64>::try_from(s).map(|v| v.len()))
        .collect::<Result<Vec<_>, _>>()?;
    assert_eq!(cardinalities.len(), 2);
    assert!(cardinalities.contains(&0) && cardinalities.contains(&2));
    let mut fresh = EGraph::default();
    let fresh_value = fresh.extract(&value)?;
    assert!(fresh.check(eq(&fresh_value, &value))?);
    let cloned_value = cloned.extract(&value)?;
    assert!(cloned.check(eq(&cloned_value, &value))?);
    Ok(())
}

#[test]
fn rewrite_merge_rebuilds_equality_members_in_nested_sets() -> Result<(), TypedError> {
    let a = Atom::A();
    let b = Atom::B();
    let s = Set::<Atom>::of([&a, &b]);
    let pairs = Set::<Pair<I64, Atom>>::of([Pair::new(7_i64, &a), Pair::new(7_i64, &b)]);
    let mut graph = EGraph::default();
    graph.register((&s, &pairs))?;
    assert_eq!(i64::try_from(&graph.extract(s.length())?)?, 2);
    assert_eq!(i64::try_from(&graph.extract(pairs.length())?)?, 2);
    // Direct Action Union is outside this slice; use the supported rewrite path.
    graph.run(ruleset(rewrite(&a, &b)))?;
    assert_eq!(i64::try_from(&graph.extract(s.length())?)?, 1);
    assert_eq!(i64::try_from(&graph.extract(pairs.length())?)?, 1);
    assert_eq!(Vec::<Atom>::try_from(&graph.extract(&s)?)?.len(), 1);
    assert_eq!(
        Vec::<Pair<I64, Atom>>::try_from(&graph.extract(&pairs)?)?.len(),
        1
    );
    assert!(graph.check((s.contains(&a), s.contains(&b)))?);
    Ok(())
}
