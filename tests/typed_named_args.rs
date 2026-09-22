#![cfg(feature = "typed")]

use egglog_experimental::typed::{builtins as egg, prelude::*};

#[sort]
pub struct Term;

#[constructor(args = LeafArgs)]
pub fn leaf(value: egg::I64) -> Term;

#[constructor(name = "named-args::pair", args = PairArgs)]
pub fn pair(left: Term, right: Term) -> Term;

#[constructor(name = "named-args::pair")]
fn compatible_pair(left: Term, right: Term) -> Term;

#[constructor(name = "named-args::pair", cost = 7)]
fn incompatible_pair(left: Term, right: Term) -> Term;

#[constructor(name = "named-args::pair")]
fn wrong_signature(left: egg::I64, right: Term) -> Term;

#[function(name = "named-args::pair", no_merge)]
fn wrong_kind(left: Term, right: Term) -> Term;

#[constructor(args = EmptyArgs)]
fn empty() -> Term;

#[function(no_merge, args = StoredArgs)]
fn stored(key: egg::I64) -> Term;

#[relation(args = SeenArgs)]
fn seen(value: Term);

#[relation]
fn other_seen(value: Term);

#[declarations]
impl Term {
    #[constructor(args = InherentArgs)]
    pub fn with(&self, other: Self) -> Self;

    #[constructor(args = AssociatedArgs)]
    pub fn associated(value: egg::I64) -> Self;

    #[function(no_merge, args = WeightArgs)]
    pub fn weight(&self, axis: egg::I64) -> egg::I64;

    #[relation(args = MarkedArgs)]
    pub fn marked(self, other: Self);
}

trait Operations {
    fn combine(self, other: &Term) -> Term;
    fn lookup(&self, axis: egg::I64) -> egg::I64;
    fn visited(&self, other: Term) -> Relation;
}

#[declarations]
impl Operations for Term {
    #[constructor(args = CombineArgs)]
    fn combine(self, other: &Term) -> Term;

    #[function(no_merge, args = LookupArgs)]
    fn lookup(&self, axis: egg::I64) -> egg::I64;

    #[relation(args = VisitedArgs)]
    fn visited(&self, other: Term) -> Relation;
}

#[declarations]
impl std::ops::Add for Term {
    type Output = Self;
    #[constructor(args = AddArgs)]
    fn add(self, rhs: Self) -> Self::Output;
}

#[declarations]
impl std::ops::Sub<&Term> for Term {
    type Output = Self;
    #[constructor(args = SubArgs)]
    fn sub(self, rhs: &Term) -> Self::Output;
}

#[declarations]
impl std::ops::Neg for &Term {
    type Output = Term;
    #[constructor(args = NegArgs)]
    fn neg(self) -> Self::Output;
}

#[constructor(args = HygienicArgs)]
fn hygienic(__egglog_node0: egg::I64, __egglog_selected_0_0: egg::I64, r#type: Term) -> Term;

#[relation(args = FreshFieldsArgs)]
fn fresh_fields(__egglog_scope0: egg::I64, fresh: egg::I64);

#[function(no_merge, args = ZeroArgs)]
fn zero() -> egg::I64;

#[relation(args = ReadyArgs)]
fn ready();

#[sort]
struct CloneShadow;

impl CloneShadow {
    fn clone(&self) -> Self {
        panic!("generated extraction must use the Clone trait")
    }
}

trait Wrap {
    fn wrap(value: CloneShadow) -> Term;
}

#[declarations]
impl Wrap for Term {
    #[constructor(args = WrapArgs)]
    fn wrap(value: CloneShadow) -> Term;
}

#[constructor(args = MissingFreeArgs)]
#[cfg(any())]
fn missing_free(value: Missing) -> Term;

#[declarations]
#[cfg(any())]
impl Term {
    #[constructor(args = MissingImplArgs)]
    pub fn missing_impl(value: Missing) -> Self;
}

#[declarations]
impl Term {
    #[cfg_attr(all(), cfg_attr(all(), cfg(any()), allow(dead_code)), inline)]
    #[constructor(args = MissingNestedArgs)]
    pub fn missing_nested(value: Missing) -> Self;
}

mod visibility {
    use super::*;

    #[constructor(args = PublicArgs)]
    pub fn public(value: egg::I64) -> Term;

    #[declarations]
    impl Term {
        #[constructor(args = PublicMethodArgs)]
        pub fn public_method(&self) -> Self;
    }
}

#[test]
fn named_construction_and_exact_inspection_share_the_original_call() -> Result<(), TypedError> {
    let args = PairArgs {
        left: leaf(1),
        right: leaf(2),
    };
    let expected = pair(&args.left, &args.right);
    let built = Term::from(args.clone());
    assert_eq!(built, expected);
    assert_eq!(built.call_name(), expected.call_name());
    let decoded = PairArgs::get_args(&built)?.unwrap();
    assert_eq!(decoded.left, args.left);
    assert_eq!(decoded.right, args.right);
    assert!(PairArgs::get_args(&leaf(1))?.is_none());
    assert!(PairArgs::get_args(&var::<Term>("x"))?.is_none());
    assert!(PairArgs::get_args(&compatible_pair(leaf(1), leaf(2)))?.is_some());
    assert!(PairArgs::get_args(&incompatible_pair(leaf(1), leaf(2))).is_err());
    assert!(PairArgs::get_args(&wrong_signature(1, leaf(2))).is_err());
    assert!(PairArgs::get_args(&wrong_kind(leaf(1), leaf(2))).is_err());
    assert_eq!(Term::from(EmptyArgs {}), empty());
    assert!(EmptyArgs::get_args(&empty())?.is_some());

    let symbolic = leaf(egg::I64::from(1) + 2);
    let literal = LeafArgs::get_args(&symbolic)?.unwrap();
    assert!(
        i64::try_from(&literal.value).is_err(),
        "inspection does not evaluate"
    );
    assert_eq!(literal.value, egg::I64::from(1) + 2);
    Ok(())
}

#[test]
fn fresh_fields_are_independent_and_clones_preserve_identity() -> Result<(), TypedError> {
    let first = PairArgs::fresh();
    let second = PairArgs::fresh();
    assert_ne!(first.left, first.right);
    for field in [&first.left, &first.right] {
        assert_ne!(field, &second.left);
        assert_ne!(field, &second.right);
        assert_ne!(field, &var::<Term>("left"));
    }
    let cloned = first.clone();
    assert_eq!(cloned.left, first.left);
    assert_eq!(cloned.right, first.right);
    let updated = PairArgs {
        left: leaf(1),
        ..first.clone()
    };
    assert_eq!(updated.right, first.right);
    let decoded = PairArgs::get_args(&Term::from(updated))?.unwrap();
    assert_eq!(decoded.left, leaf(1));
    assert_eq!(decoded.right, first.right);
    assert_eq!(Term::from(EmptyArgs::fresh()), empty());
    Ok(())
}

#[test]
fn partial_patterns_are_independent_unless_a_field_is_shared() -> Result<(), TypedError> {
    let first = PairArgs {
        left: leaf(1),
        ..PairArgs::fresh()
    };
    let second = PairArgs {
        left: leaf(2),
        ..PairArgs::fresh()
    };
    let shared = PairArgs {
        right: first.right.clone(),
        ..second.clone()
    };
    let mut graph = EGraph::default();
    graph.register((pair(leaf(1), leaf(3)), pair(leaf(2), leaf(4))))?;
    assert!(graph.check((Term::from(first.clone()), Term::from(second)))?);
    assert!(!graph.check((Term::from(first), Term::from(shared)))?);
    Ok(())
}

#[test]
fn matched_records_preserve_rhs_fields_but_new_rhs_variables_are_rejected() -> Result<(), TypedError>
{
    let args = PairArgs::fresh();
    let condition = eq(&args.left, leaf(1));
    let group = ruleset(
        rewrite(
            Term::from(args.clone()),
            PairArgs {
                left: leaf(5),
                ..args
            },
        )
        .when(condition),
    );
    let original = pair(leaf(1), leaf(2));
    let expected = pair(leaf(5), leaf(2));
    let mut graph = EGraph::default();
    graph.register(&original)?;
    graph.run(&group)?;
    assert!(graph.check(eq(&original, expected))?);
    assert!(!graph.check(eq(&original, pair(leaf(5), leaf(3))))?);

    let invalid = ruleset(rewrite(
        pair(leaf(1), leaf(2)),
        PairArgs {
            left: leaf(5),
            ..PairArgs::fresh()
        },
    ));
    let before = graph.num_tuples()?;
    assert!(matches!(graph.run(&invalid), Err(TypedError::Invalid(_))));
    assert_eq!(graph.num_tuples()?, before);
    Ok(())
}

#[test]
fn fresh_records_support_functions_relations_receivers_and_hygiene() -> Result<(), TypedError> {
    let function = StoredArgs::fresh();
    assert_ne!(function.key, StoredArgs::fresh().key);
    let relation = SeenArgs::fresh();
    assert_ne!(relation.value, SeenArgs::fresh().value);
    let receiver = InherentArgs::fresh();
    assert_ne!(receiver.receiver, receiver.other);
    assert_eq!(
        Term::from(receiver.clone()),
        receiver.receiver.with(&receiver.other),
    );
    let trait_args = CombineArgs::fresh();
    assert_ne!(trait_args.receiver, trait_args.other);
    let operator = AddArgs::fresh();
    assert_ne!(operator.receiver, operator.rhs);
    let hygienic = HygienicArgs::fresh();
    assert_ne!(hygienic.__egglog_node0, hygienic.__egglog_selected_0_0);
    let shadowed = WrapArgs::fresh();
    let _ = Term::from(shadowed);
    let fields = FreshFieldsArgs::fresh();
    assert_ne!(fields.__egglog_scope0, fields.fresh);
    assert_eq!(egg::I64::from(ZeroArgs::fresh()), zero());
    assert!(ReadyArgs::get_args(&Relation::from(ReadyArgs::fresh()))?.is_some());

    let mut graph = EGraph::default();
    graph.register((set(stored(3), leaf(4)), seen(leaf(5))))?;
    assert!(graph.check((Term::from(function), Relation::from(relation)))?);
    Ok(())
}

#[test]
fn functions_and_relations_use_the_same_record_surface() -> Result<(), TypedError> {
    let function: Term = StoredArgs { key: 3.into() }.into();
    assert_eq!(function, stored(3));
    assert_eq!(StoredArgs::get_args(&function)?.unwrap().key, 3.into());
    let relation: Relation = SeenArgs { value: leaf(4) }.into();
    assert_eq!(relation.call_name(), seen(leaf(4)).call_name());
    assert_eq!(SeenArgs::get_args(&relation)?.unwrap().value, leaf(4));
    assert!(SeenArgs::get_args(&other_seen(leaf(4)))?.is_none());

    let mut graph = EGraph::default();
    graph.register((set(&function, leaf(9)), &relation))?;
    assert!(graph.check((eq(&function, leaf(9)), &relation))?);
    Ok(())
}

#[test]
fn records_support_inherent_trait_and_operator_receivers() -> Result<(), TypedError> {
    let a = leaf(1);
    let b = leaf(2);
    let with: Term = InherentArgs {
        receiver: a.clone(),
        other: b.clone(),
    }
    .into();
    assert_eq!(with, a.with(&b));
    assert_eq!(InherentArgs::get_args(&with)?.unwrap().receiver, a);
    assert_eq!(
        Term::from(AssociatedArgs { value: 7.into() }),
        Term::associated(7)
    );

    let weight: egg::I64 = WeightArgs {
        receiver: a.clone(),
        axis: 2.into(),
    }
    .into();
    assert_eq!(weight, a.weight(2));
    assert_eq!(WeightArgs::get_args(&weight)?.unwrap().axis, 2.into());
    let marked: Relation = MarkedArgs {
        receiver: a.clone(),
        other: b.clone(),
    }
    .into();
    assert_eq!(MarkedArgs::get_args(&marked)?.unwrap().other, b);

    let combined: Term = CombineArgs {
        receiver: a.clone(),
        other: b.clone(),
    }
    .into();
    assert_eq!(combined, a.clone().combine(&b));
    assert_eq!(CombineArgs::get_args(&combined)?.unwrap().receiver, a);
    let lookup: egg::I64 = LookupArgs {
        receiver: a.clone(),
        axis: 3.into(),
    }
    .into();
    assert_eq!(lookup, a.lookup(3.into()));
    assert_eq!(LookupArgs::get_args(&lookup)?.unwrap().axis, 3.into());
    let visited: Relation = VisitedArgs {
        receiver: a.clone(),
        other: b.clone(),
    }
    .into();
    assert_eq!(VisitedArgs::get_args(&visited)?.unwrap().other, b);

    let sum: Term = AddArgs {
        receiver: a.clone(),
        rhs: b.clone(),
    }
    .into();
    assert_eq!(sum, &a + &b);
    assert_eq!(AddArgs::get_args(&sum)?.unwrap().rhs, b);
    let difference: Term = SubArgs {
        receiver: a.clone(),
        rhs: b.clone(),
    }
    .into();
    assert_eq!(difference, &a - &b);
    assert_eq!(SubArgs::get_args(&difference)?.unwrap().receiver, a);
    let negative: Term = NegArgs {
        receiver: a.clone(),
    }
    .into();
    assert_eq!(negative, -&a);
    assert_eq!(NegArgs::get_args(&negative)?.unwrap().receiver, a);
    Ok(())
}

#[test]
fn generated_records_preserve_hygiene_and_visibility() -> Result<(), TypedError> {
    let args = HygienicArgs::get_args(&hygienic(1, 2, leaf(3)))?.unwrap();
    assert_eq!(args.__egglog_node0, 1.into());
    assert_eq!(args.__egglog_selected_0_0, 2.into());
    assert_eq!(args.r#type, leaf(3));
    let symbolic = var::<CloneShadow>("shadow");
    let wrapped: Term = WrapArgs {
        value: Clone::clone(&symbolic),
    }
    .into();
    assert_eq!(WrapArgs::get_args(&wrapped)?.unwrap().value, symbolic);
    let value: Term = visibility::PublicArgs { value: 8.into() }.into();
    assert_eq!(value, visibility::public(8));
    let method: Term = visibility::PublicMethodArgs {
        receiver: value.clone(),
    }
    .into();
    assert_eq!(
        visibility::PublicMethodArgs::get_args(&method)?
            .unwrap()
            .receiver,
        value
    );
    Ok(())
}

#[test]
fn frozen_record_fields_retain_snapshot_provenance() -> Result<(), TypedError> {
    let left = let_("named-record-left", leaf(1));
    let output = let_("named-record", pair(&left, leaf(2)));
    let mut graph = EGraph::default();
    graph.register(&output)?;
    let frozen = graph.freeze()?;
    let observed = frozen.lookup(&output)?;
    let node = frozen.nodes(&observed)?.next().unwrap();
    let fields = PairArgs::get_args(&node)?.unwrap();
    assert_eq!(
        frozen.as_view(&fields.left)?,
        frozen.as_view(&frozen.lookup(&left)?)?
    );
    let different_snapshot = graph.freeze()?;
    assert!(different_snapshot.as_view(&fields.left).is_err());
    let left_node = frozen.nodes(&fields.left)?.next().unwrap();
    let leaf_fields = LeafArgs::get_args(&left_node)?.unwrap();
    assert!(graph.register(Term::from(fields.clone())).is_err());
    drop(graph);
    drop(frozen);
    assert_eq!(i64::try_from(leaf_fields.value)?, 1);
    assert!(PairArgs::get_args(&Term::from(fields))?.is_some());
    Ok(())
}

#[constructor(args = ManyArgs)]
#[allow(clippy::too_many_arguments)]
fn many(
    a00: egg::I64,
    a01: egg::I64,
    a02: egg::I64,
    a03: egg::I64,
    a04: egg::I64,
    a05: egg::I64,
    a06: egg::I64,
    a07: egg::I64,
    a08: egg::I64,
    a09: egg::I64,
    a10: egg::I64,
    a11: egg::I64,
    a12: egg::I64,
    a13: egg::I64,
    a14: egg::I64,
    a15: egg::I64,
    a16: egg::I64,
    a17: egg::I64,
    a18: egg::I64,
    a19: egg::I64,
    a20: egg::I64,
    a21: egg::I64,
    a22: egg::I64,
    a23: egg::I64,
    a24: egg::I64,
    a25: egg::I64,
    a26: egg::I64,
) -> Term;

#[test]
fn named_records_handle_the_cublaslt_arity() -> Result<(), TypedError> {
    let fresh = ManyArgs::fresh();
    assert_ne!(fresh.a00, fresh.a13);
    assert_ne!(fresh.a13, fresh.a26);
    let call = many(
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
        25, 26,
    );
    let args = ManyArgs::get_args(&call)?.unwrap();
    assert_eq!(args.a00, 0.into());
    assert_eq!(args.a13, 13.into());
    assert_eq!(args.a26, 26.into());
    assert_eq!(Term::from(args), call);
    Ok(())
}
