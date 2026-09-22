#![cfg(feature = "typed")]

use egglog_experimental::typed::{builtins as egg, prelude::*};

#[sort]
pub struct Term;

#[declarations]
impl Term {
    #[constructor(from(i32, i64, &i32, &i64), try_from(i64), cost = 3)]
    pub fn integer(value: egg::I64) -> Self;
    #[constructor(from(f64, &f64), try_from(f64))]
    pub fn float(value: egg::F64) -> Self;
    #[constructor(from(&str, std::string::String, &std::string::String), try_from(std::string::String))]
    pub fn var(value: egg::String) -> Self;
    pub fn pair(&self, other: Self) -> Self;
    pub fn seen(&self);
    #[function(no_merge)]
    pub fn stored(&self) -> Self;
    #[function(merge = |old: egg::I64, new| old.max(new))]
    pub fn weight(&self) -> egg::I64;

    pub fn ordinary<T>(&self, value: T) -> T {
        #![allow(unused_variables)]
        let unused = 1;
        value
    }
    pub const fn ordinary_const(value: usize) -> usize {
        value + 1
    }
}

#[declarations]
impl std::ops::Add for Term {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output;
}

#[declarations]
impl std::ops::Neg for Term {
    type Output = Self;
    fn neg(self) -> Self::Output {
        #![allow(clippy::let_and_return)]
        let result = self;
        result
    }
}

trait Rows {
    fn row(&self) -> Relation;
    fn duplicate(&self) -> Term;
    fn ordinary(&self) -> usize;
}

#[declarations]
impl Rows for Term {
    fn row(&self);
    fn duplicate(&self) -> Term;
    fn ordinary(&self) -> usize {
        7
    }
}

#[sort]
pub struct Free;
#[constructor(from(bool), try_from(bool))]
pub fn free(value: egg::Bool) -> Free;

#[sort]
pub struct Hygiene;
#[constructor(from(i64), try_from(i64))]
fn value(__egglog_source0: egg::I64) -> Hygiene;

type Integer = egg::I64;
#[sort]
pub struct Aliased;
#[constructor(from(i64), try_from(i64))]
fn aliased(value: Integer) -> Aliased;

#[sort]
pub struct ViaTrait;
trait Construct {
    fn create(value: &egg::I64) -> Self;
}
#[declarations]
impl Construct for ViaTrait {
    #[constructor(from(i64), try_from(i64))]
    fn create(value: &egg::I64) -> Self;
}

struct Counted<'a>(&'a std::cell::Cell<usize>);
impl From<Counted<'_>> for egg::I64 {
    fn from(value: Counted<'_>) -> Self {
        value.0.set(value.0.get() + 1);
        Self::from(7)
    }
}
#[sort]
pub struct CountedTerm;
#[constructor(from(Counted<'_>))]
fn counted(value: egg::I64) -> CountedTerm;

#[declarations]
#[cfg(any())]
impl Term {
    #[constructor(from, try_from(MissingNative))]
    fn absent(value: Missing) -> Self;
}

#[declarations]
impl Term {
    #![cfg(any())]
    #[constructor(from, try_from(MissingNative))]
    fn absent_inner_cfg(value: Missing) -> Self;
}

#[declarations]
impl Term {
    #[cfg(any())]
    #[constructor(from, try_from(MissingNative))]
    fn absent_method(value: Missing) -> Self;
    #[cfg_attr(all(), cfg_attr(all(), cfg(any()), allow(dead_code)), inline)]
    #[constructor(from, try_from(MissingNative))]
    fn absent_nested_cfg(value: Missing) -> Self;
}

#[constructor(from, try_from(MissingNative))]
#[cfg(any())]
fn absent_free(value: Missing) -> Term;

#[sort]
pub struct ViaOwnedTrait;
trait ConstructOwned {
    fn create(value: egg::I64) -> Self;
}
#[declarations]
impl ConstructOwned for ViaOwnedTrait {
    #[constructor(try_from(i64))]
    fn create(value: egg::I64) -> Self;
}

#[sort]
pub struct Aggregate;
#[declarations]
impl Aggregate {
    #[constructor(try_from)]
    fn single(value: Term) -> Self;
    #[constructor(try_from(std::vec::Vec<Term>))]
    fn list(value: egg::Vec<Term>) -> Self;
}

struct KeptInput(egg::I64);
static REVERSE_CALLS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
impl From<egg::I64> for KeptInput {
    fn from(value: egg::I64) -> Self {
        REVERSE_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Self(value)
    }
}
#[sort]
struct CountedReverse;
#[constructor(try_from(KeptInput))]
fn counted_reverse(value: egg::I64) -> CountedReverse;

#[sort]
struct CloneShadow;
impl CloneShadow {
    fn clone(&self) -> Self {
        panic!("inspection must use the Clone trait, not an inherent method")
    }
}
#[sort]
struct ShadowWrapper;
trait ConstructShadow {
    fn create(value: CloneShadow) -> Self;
}
#[declarations]
impl ConstructShadow for ShadowWrapper {
    #[constructor(try_from)]
    fn create(value: CloneShadow) -> Self;
}

#[test]
fn generated_reverse_conversions_inspect_without_evaluating() -> Result<(), TypedError> {
    for n in [i64::MIN, -1, 0, i64::MAX] {
        let term = Term::from(n);
        assert_eq!(i64::try_from(&term)?, n);
        let native: i64 = term.clone().try_into()?;
        assert_eq!(native, n);
        assert_eq!(egg::I64::try_from(&term)?, egg::I64::from(n));
        assert_eq!(egg::I64::try_from(term)?, egg::I64::from(n));
    }
    for bits in [0, 1_u64 << 63, 0x7ff8_0000_0000_0042, 0x7ff0_0000_0000_0000] {
        let term = Term::float(f64::from_bits(bits));
        assert_eq!(f64::try_from(&term)?.to_bits(), bits);
        assert_eq!(f64::try_from(term)?.to_bits(), bits);
    }
    let text = "λ\n\"🦀";
    assert_eq!(std::string::String::try_from(Term::var(text))?, text);
    assert!(bool::try_from(free(true))?);
    assert_eq!(i64::try_from(value(7))?, 7);
    assert_eq!(i64::try_from(aliased(7))?, 7);
    assert_eq!(i64::try_from(ViaTrait::create(&7.into()))?, 7);
    assert_eq!(i64::try_from(ViaOwnedTrait::create(7.into()))?, 7);
    let shadow = var::<CloneShadow>("shadow");
    let wrapped = ShadowWrapper::create(Clone::clone(&shadow));
    assert_eq!(CloneShadow::try_from(wrapped)?, shadow);

    let expression = Term::integer(egg::I64::from(2) + 3);
    assert_eq!(egg::I64::try_from(&expression)?, egg::I64::from(2) + 3);
    assert!(matches!(
        i64::try_from(&expression),
        Err(TypedError::Decode(_))
    ));
    assert!(matches!(
        i64::try_from(Term::var("x")),
        Err(TypedError::Decode(_))
    ));
    assert!(i64::try_from(var::<Term>("x")).is_err());
    assert!(i64::try_from(let_("not evaluated", Term::integer(5))).is_err());
    let mut graph = EGraph::new(EGraphOptions::default());
    assert_eq!(i64::try_from(graph.extract(&expression)?)?, 5);

    let before = REVERSE_CALLS.load(std::sync::atomic::Ordering::Relaxed);
    let converted = KeptInput::try_from(counted_reverse(7))?;
    assert_eq!(
        REVERSE_CALLS.load(std::sync::atomic::Ordering::Relaxed),
        before + 1
    );
    assert_eq!(converted.0, egg::I64::from(7));
    Ok(())
}

#[test]
fn generated_reverse_conversions_preserve_frozen_children() -> Result<(), TypedError> {
    let child = Term::integer(7);
    let capture = let_("reverse-child", child.clone());
    let list = let_(
        "reverse-list",
        Aggregate::list([child.clone(), child.clone()]),
    );
    let single = let_("reverse-single", Aggregate::single(&child));
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register((&capture, &list, &single))?;
    let frozen = graph.freeze()?;
    let observed = frozen.lookup(&capture)?;
    assert!(i64::try_from(&observed).is_err()); // No implicit producer choice.
    let node = frozen.nodes(&observed)?.next().unwrap();
    assert_eq!(i64::try_from(&node)?, 7);
    let scalar = egg::I64::try_from(&node)?;
    assert_eq!(i64::try_from(&scalar)?, 7);
    assert!(graph.register(&scalar).is_err());

    let observed_list = frozen.lookup(&list)?;
    assert!(Vec::<Term>::try_from(&observed_list).is_err());
    let selected_list = frozen.nodes(&observed_list)?.next().unwrap();
    let decoded = Vec::<Term>::try_from(&selected_list)?;
    assert_eq!(decoded, vec![observed.clone(), observed.clone()]);
    assert!(graph.register(&decoded).is_err());
    assert!(i64::try_from(&decoded[0]).is_err()); // Children remain classes.
    let observed_single = frozen.lookup(&single)?;
    let selected_single = frozen.nodes(&observed_single)?.next().unwrap();
    assert_eq!(Term::try_from(&selected_single)?, observed);
    drop(graph);
    drop(frozen);
    assert_eq!(i64::try_from(node)?, 7);
    Ok(())
}

#[test]
fn generated_reverse_conversions_retain_exact_declaration_checks() {
    #[constructor(name = concat!(module_path!(), "::Term::integer"), cost = 3)]
    fn compatible(value: egg::I64) -> Term;
    #[constructor(name = concat!(module_path!(), "::Term::integer"), cost = 4)]
    fn incompatible(value: egg::I64) -> Term;
    assert_eq!(i64::try_from(compatible(7)).unwrap(), 7);
    assert!(matches!(
        i64::try_from(incompatible(7)),
        Err(TypedError::Invalid(_))
    ));
}

#[test]
fn inferred_declarations_and_ordinary_bodies_keep_their_roles() -> Result<(), TypedError> {
    let term = Term::integer(7);
    assert_eq!(term.ordinary(11), 11);
    assert_eq!(Term::ordinary_const(3), 4);
    assert_eq!(Rows::ordinary(&term), 7);
    assert_eq!(-term.clone(), term);
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register((
        &term,
        term.pair(8),
        &term + 9,
        term.seen(),
        term.row(),
        term.duplicate(),
        set(term.stored(), &term),
        set(term.weight(), 3),
        set(term.weight(), 5),
    ))?;
    assert!(graph.check((term.seen(), term.row(), eq(term.weight(), 5)))?);
    assert_eq!(graph.extract_with_cost(&term)?.1, 4);
    let frozen = graph.freeze()?;
    assert_eq!(frozen.table(|term: &Term| term.stored())?.rows.len(), 1);
    assert_eq!(frozen.table(|term: &Term| term.seen())?.rows.len(), 1);
    Ok(())
}

#[test]
fn generated_conversions_use_exact_constructors_and_explicit_host_routes() -> Result<(), TypedError>
{
    let symbolic = var::<egg::I64>("symbolic");
    assert_eq!(Term::from(&symbolic), Term::integer(&symbolic));
    assert_eq!(
        Term::from(symbolic),
        Term::integer(var::<egg::I64>("symbolic"))
    );
    for value in [
        Term::from(7i32),
        Term::from(&7i32),
        Term::from(7i64),
        Term::from(&7i64),
    ] {
        assert_eq!(value, Term::integer(7));
    }
    let name = std::string::String::from("name");
    assert_eq!(Term::from(&name), Term::var(&name));
    assert_eq!(Term::from(name), Term::var("name"));
    assert_eq!(Term::from("name"), Term::var("name"));
    let name = egg::String::from("symbolic-name");
    assert_eq!(Term::from(&name), Term::var(&name));
    assert_eq!(Term::from(name), Term::var("symbolic-name"));
    for bits in [0, 1 << 63, f64::INFINITY.to_bits(), 0x7ff8_0000_0000_0042] {
        let host = f64::from_bits(bits);
        let value = Term::from(&host);
        assert_eq!(value, Term::from(host));
        let (value,) = get_args(&value, |value: &egg::F64| Term::float(value))?.unwrap();
        assert_eq!(f64::try_from(value).unwrap().to_bits(), bits);
    }
    assert_eq!(Free::from(true), free(true));
    assert_eq!(Free::from(egg::Bool::from(true)), free(true));
    assert_eq!(Free::from(&egg::Bool::from(true)), free(true));
    assert_eq!(Hygiene::from(7i64), value(7));
    assert_eq!(Aliased::from(&Integer::from(7)), aliased(7));
    assert_eq!(ViaTrait::from(7i64), ViaTrait::create(&7.into()));
    assert_eq!(
        ViaTrait::from(&egg::I64::from(7)),
        ViaTrait::create(&7.into())
    );
    let calls = std::cell::Cell::new(0);
    assert_eq!(CountedTerm::from(Counted(&calls)), counted(7));
    assert_eq!(calls.get(), 1);
    Ok(())
}

#[test]
fn generated_conversion_preserves_frozen_input_provenance() -> Result<(), TypedError> {
    let capture = let_("number", egg::I64::from(7));
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register(&capture)?;
    let frozen = graph.freeze()?;
    let observed = frozen.lookup(&capture)?;
    let converted = Term::from(&observed);
    drop(graph);
    drop(frozen);
    let (child,) = get_args(&converted, |value: &egg::I64| Term::integer(value))?.unwrap();
    assert_eq!(child, observed);
    assert_eq!(i64::try_from(child).unwrap(), 7);
    let mut live = EGraph::new(EGraphOptions::default());
    assert!(matches!(
        live.register(converted),
        Err(TypedError::Invalid(_))
    ));
    assert_eq!(live.num_tuples()?, 0);
    Ok(())
}
