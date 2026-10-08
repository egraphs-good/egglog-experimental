#![cfg(feature = "typed")]

use egglog_experimental::typed::prelude::*;
use std::hash::{DefaultHasher, Hash, Hasher};

#[sort]
pub struct Atom;
#[declarations]
impl Atom {
    pub fn A() -> Self;
    pub fn B() -> Self;
}

#[sort(name = "Pair")]
pub struct Pair;
#[declarations]
impl Pair {
    pub fn P() -> Self;
}

#[test]
fn nominal_pair_name_executes_without_renaming_the_native_family() -> Result<(), TypedError> {
    assert!(Pair::sort_ref() == egglog_experimental::typed::SortRef::equality("Pair"));
    let value = Pair::P();
    let mut graph = EGraph::default();
    graph.register(&value)?;
    assert!(graph.check(eq(&value, &value))?);
    assert_eq!(graph.extract(&value)?, value);
    Ok(())
}

#[sort]
pub struct Math;
#[declarations]
impl Math {
    #[constructor(from, try_from, args = WrapArgs)]
    pub fn Wrap(value: Atom) -> Self;
    #[constructor(args = PairArgs)]
    pub fn Pair(left: Math, right: Math) -> Self;
}

#[test]
fn constructors_selectors_and_real_byte_execution() -> Result<(), TypedError> {
    let leaf: Math = Atom::A().into();
    let root = Math::Pair(&leaf, &leaf);
    let args = PairArgs::get_args(&root)?.unwrap();
    assert_eq!(args.left, leaf);
    assert_eq!(args.right, leaf);
    assert!(WrapArgs::get_args(&root)?.is_none());
    assert_eq!(Atom::try_from(&leaf)?, Atom::A());
    assert!(Atom::try_from(&root).is_err());
    let collapse = ruleset(|x: &Math| rewrite(Math::Pair(x, x), x));
    let mut graph = EGraph::default();
    graph.register(&root)?;
    graph.run(&collapse)?;
    assert!(graph.check(eq(&root, &leaf))?);
    let extracted: Math = graph.extract(&root)?;
    assert_eq!(Atom::try_from(extracted)?, Atom::A());
    // Reusing the same occurrence must send its installed name, not resupply it.
    graph.run(&collapse)?;
    Ok(())
}

#[test]
fn escaped_fresh_variables_and_names_never_alias() -> Result<(), TypedError> {
    let fields = PairArgs::fresh();
    assert_eq!(fields.left, fields.left.clone());
    assert_ne!(fields.left, fields.right);
    assert_ne!(fields.left, PairArgs::fresh().left);
    for name in ["__typed_v_0", "@typed:f:0:0", "@typed:n:78", "_0"] {
        assert_ne!(fields.left, var::<Math>(name));
    }
    let mut escaped = None;
    let _empty = ruleset(|x: &Math| {
        escaped = Some(x.clone());
    });
    let x = escaped.unwrap();
    let a = Math::Wrap(Atom::A());
    let b = Math::Wrap(Atom::B());
    let mut graph = EGraph::default();
    graph.register(Math::Pair(&a, &b))?;
    assert!(!graph.check(Math::Pair(&x, &x))?);
    assert!(graph.check(Math::Pair(&fields.left, &fields.right))?);
    let named = var::<Math>("__typed_v_0");
    assert!(graph.check((Math::Pair(&x, &named), eq(&x, &a), eq(&named, &b)))?);
    assert!(graph.register(&x).is_err());
    assert!(graph.extract(&x).is_err());
    let unbound = ruleset(rewrite(
        Math::Pair(&fields.left, &fields.left),
        &fields.right,
    ));
    assert!(graph.run(&unbound).is_err());
    assert!(!graph.check(eq(&a, &b))?);
    Ok(())
}

#[test]
fn named_sort_conflict_is_rejected_without_mutation() -> Result<(), TypedError> {
    let mut graph = EGraph::default();
    graph.register(Math::Wrap(Atom::A()))?;
    assert!(
        graph
            .check((
                eq(var::<Atom>("x"), Atom::A()),
                eq(var::<Math>("x"), Math::Wrap(Atom::B())),
            ))
            .is_err()
    );
    assert!(!graph.check(Math::Wrap(Atom::B()))?);
    Ok(())
}

#[test]
fn independent_deep_graphs_compare_hash_and_drop_iteratively() {
    fn chain(left_growing: bool) -> Math {
        let leaf = Math::Wrap(Atom::A());
        let mut value = leaf.clone();
        for _ in 0..100_000 {
            value = if left_growing {
                Math::Pair(value, &leaf)
            } else {
                Math::Pair(&leaf, value)
            };
        }
        value
    }
    for order in [false, true] {
        let a = chain(order);
        let b = chain(order);
        assert_eq!(a, b);
        let mut ah = DefaultHasher::new();
        let mut bh = DefaultHasher::new();
        a.hash(&mut ah);
        b.hash(&mut bh);
        assert_eq!(ah.finish(), bh.finish());
        assert!(format!("{a:?}").len() < 2000);
        std::thread::spawn(move || drop((a, b))).join().unwrap();
    }
}
