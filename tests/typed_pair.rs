#![cfg(feature = "typed")]

use egglog_experimental::proto as pb;
use egglog_experimental::typed::{
    builtins::{F64, I64, Pair, Vec as EVec},
    prelude::*,
};

#[sort]
pub struct Atom;
#[declarations]
impl Atom {
    pub fn A() -> Self;
    #[constructor(args = PackArgs)]
    pub fn Pack(value: Pair<Atom, I64>) -> Self;
}

#[test]
fn pair_fields_preserve_symbolic_children_and_tuple_conversions() -> Result<(), TypedError> {
    fn generic<L: EgglogValue, R: EgglogValue>(
        left: impl Into<L>,
        right: impl Into<R>,
    ) -> Pair<L, R> {
        (left, right).into()
    }
    let symbolic = I64::from(2) + I64::from(3);
    let right = F64::from(1.5);
    let pair = Pair::<I64, F64>::new(&symbolic, &right);
    assert_eq!(pair.call_name(), None);
    assert_eq!(pair, generic(&symbolic, &right));
    assert_eq!(
        Pair::<I64, F64>::from((7_i64, 2.5_f64)).fields()?,
        (I64::from(7), F64::from(2.5))
    );
    assert_eq!(pair.fields()?, (symbolic.clone(), right.clone()));
    assert_eq!(
        <(I64, F64)>::try_from(&pair)?,
        (symbolic.clone(), right.clone())
    );
    assert_eq!(<(I64, F64)>::try_from(pair.clone())?, (symbolic, right));
    assert_eq!(Pair::from(&pair), pair);
    assert!(var::<Pair<I64, F64>>("p").fields().is_err());
    Ok(())
}

#[test]
fn pair_calls_values_and_projections_execute_through_bytes() -> Result<(), TypedError> {
    let pair = Pair::<I64, F64>::new(I64::from(2) + I64::from(3), 1.5_f64);
    let mut graph = EGraph::with_recording(true)?;
    graph.register(&pair)?;
    assert!(graph.history()?.nodes.iter().any(|node| matches!(
        &node.kind,
        Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Pair(_))
        }))
    )));
    assert_eq!(i64::try_from(&graph.extract(pair.first())?)?, 5);
    assert_eq!(f64::try_from(&graph.extract(pair.second())?)?, 1.5);
    let value = graph.extract(&pair)?;
    assert_ne!(pair, value, "extraction evaluates the symbolic child");
    assert!(graph.check(eq(&pair, &value))?);
    assert_eq!(value.fields()?, (I64::from(5), F64::from(1.5)));
    let ordered = Pair::<I64, I64>::new(7_i64, 11_i64);
    assert_eq!(
        graph.extract(ordered)?.fields()?,
        (I64::from(7), I64::from(11))
    );
    drop(graph);
    let mut fresh = EGraph::default();
    assert_eq!(fresh.extract(&value)?.fields()?, value.fields()?);
    Ok(())
}

#[test]
fn nested_pairs_vectors_and_constructor_selectors_keep_ownership() -> Result<(), TypedError> {
    let atom = Atom::A();
    let pair = Pair::<Atom, I64>::new(&atom, 7_i64);
    let packed = Atom::Pack(&pair);
    assert_eq!(PackArgs::get_args(&packed)?.unwrap().value, pair);
    let nested = Pair::<EVec<Pair<Atom, I64>>, Pair<Atom, Atom>>::new(
        EVec::of([&pair, &pair]),
        Pair::new(&atom, &atom),
    );
    let mut graph = EGraph::default();
    graph.register((&packed, &nested))?;
    let value = graph.extract(nested)?;
    let extracted_pack = graph.extract(packed)?;
    let fresh = PackArgs::fresh();
    assert!(graph.check(Atom::Pack(&fresh.value))?);
    drop(graph);
    let (vector, repeated) = value.fields()?;
    let children = Vec::<Pair<Atom, I64>>::try_from(&vector)?;
    assert_eq!(children.len(), 2);
    assert_eq!(children[0], children[1]);
    assert_eq!(children[0].fields()?, (atom.clone(), I64::from(7)));
    assert_eq!(repeated.fields()?, (atom.clone(), atom));
    assert_eq!(
        PackArgs::get_args(&extracted_pack)?.unwrap().value,
        children[0]
    );
    Ok(())
}
