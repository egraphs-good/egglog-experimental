#![cfg(feature = "typed")]
use egglog_experimental::typed::{builtins::I64, prelude::*};

mod default_names {
    use super::*;

    #[sort]
    pub struct Term;
    #[declarations]
    impl Term {
        pub fn Empty() -> Self;
        pub fn Leaf(value: I64) -> Self;
        pub fn Named(value: I64) -> Self;
    }

    #[constructor]
    fn leaf(value: I64) -> Term;
    #[function(no_merge)]
    fn weight(term: Term) -> I64;
    #[relation]
    fn seen(term: Term);

    #[declarations]
    impl Term {
        #[constructor]
        pub fn constant(value: I64) -> Term;
        #[constructor]
        pub fn pair(&self, other: Term) -> Term;
        #[function(no_merge)]
        pub fn weight(&self) -> I64;
        #[relation]
        pub fn seen(&self);
    }

    #[declarations]
    impl std::ops::Add<&Term> for &Term {
        type Output = Term;
        #[constructor]
        fn add(self, rhs: &Term) -> Term;
    }

    mod nested {
        use super::*;

        #[constructor]
        pub fn leaf(value: I64) -> Term;
    }
    pub use nested::leaf as reexported_leaf;

    #[test]
    fn names_follow_declaration_scope_and_authored_callable_role() -> Result<(), TypedError> {
        let x = Term::Leaf(1);
        let y = Term::Named(2);
        let mut graph = EGraph::new(EGraphOptions::default());
        graph.register((
            Term::Empty(),
            &x,
            &y,
            leaf(3),
            set(weight(&x), 4),
            seen(&x),
            Term::constant(6),
            x.pair(&y),
            set(x.weight(), 5),
            x.seen(),
            &x + &y,
        ))?;
        // Free and inherent functions with the same Rust name remain distinct.
        assert!(graph.check((eq(weight(&x), 4), eq(x.weight(), 5)))?);
        let frozen = graph.freeze()?;
        let raw = graph.into_raw();
        assert!(raw.get_sort_by_name(Term::sort_ref().name()).is_some());
        for (name, expected) in [
            (
                frozen.table(|n: &I64| leaf(n))?.name,
                concat!(module_path!(), "::leaf"),
            ),
            (
                frozen.table(|term: &Term| weight(term))?.name,
                concat!(module_path!(), "::weight"),
            ),
            (
                frozen.table(|term: &Term| seen(term))?.name,
                concat!(module_path!(), "::seen"),
            ),
            (
                frozen.table(|n: &I64| Term::constant(n))?.name,
                concat!(module_path!(), "::Term::constant"),
            ),
            (
                frozen.table(|a: &Term, b: &Term| a.pair(b))?.name,
                concat!(module_path!(), "::Term::pair"),
            ),
            (
                frozen.table(|term: &Term| term.weight())?.name,
                concat!(module_path!(), "::Term::weight"),
            ),
            (
                frozen.table(|term: &Term| term.seen())?.name,
                concat!(module_path!(), "::Term::seen"),
            ),
            (
                frozen.table(Term::Empty)?.name,
                concat!(module_path!(), "::Term::Empty"),
            ),
            (
                frozen.table(|n: &I64| Term::Leaf(n))?.name,
                concat!(module_path!(), "::Term::Leaf"),
            ),
            (
                frozen.table(|n: &I64| Term::Named(n))?.name,
                concat!(module_path!(), "::Term::Named"),
            ),
            (
                frozen.table(|a: &Term, b: &Term| a + b)?.name,
                concat!(
                    module_path!(),
                    "::<Term as std :: ops :: Add < & Term >>::add"
                ),
            ),
        ] {
            assert_eq!(name.as_ref(), expected);
            assert!(raw.get_function(expected).is_some());
        }
        Ok(())
    }

    #[test]
    fn modules_isolate_defaults_and_reexports_keep_original_identity() -> Result<(), TypedError> {
        let local = leaf(1);
        let nested = nested::leaf(1);
        assert_ne!(local, nested);
        assert_eq!(nested, reexported_leaf(1));
        assert_eq!(
            get_args(&nested, |n: &I64| reexported_leaf(n))?,
            Some((I64::from(1),))
        );
        assert!(get_args(&local, |n: &I64| reexported_leaf(n))?.is_none());
        let mut graph = EGraph::new(EGraphOptions::default());
        graph.register((&local, &nested, reexported_leaf(1)))?;
        let frozen = graph.freeze()?;
        let local = frozen.table(|n: &I64| leaf(n))?;
        let original = frozen.table(|n: &I64| nested::leaf(n))?;
        let reexported = frozen.table(|n: &I64| reexported_leaf(n))?;
        assert_eq!(local.name.as_ref(), concat!(module_path!(), "::leaf"));
        assert_eq!(
            original.name.as_ref(),
            concat!(module_path!(), "::nested::leaf")
        );
        assert_eq!(original.name, reexported.name);
        assert_eq!(local.rows.len(), 1);
        assert_eq!(original.rows.len(), 1);
        assert_eq!(reexported.rows.len(), 1);
        assert_eq!(original.rows[0].output, reexported.rows[0].output);
        assert_ne!(local.rows[0].output, original.rows[0].output);
        Ok(())
    }
}

#[sort]
pub struct Num;
#[sort]
pub struct BorrowedNum;
#[declarations]
impl std::ops::Add for &BorrowedNum {
    type Output = BorrowedNum;
    #[constructor]
    fn add(self, rhs: Self) -> Self::Output;
}
#[declarations]
impl Num {
    #[constructor(from(i64))]
    pub fn lit(value: I64) -> Self;
    #[constructor(from(&str))]
    pub fn named(value: egglog_experimental::typed::builtins::String) -> Self;
    #[constructor]
    pub fn pair(&self, other: Self) -> Self;
    #[function(no_merge)]
    pub fn weight(&self, axis: I64) -> I64;
    #[relation]
    pub fn seen(&self);
    #[constructor]
    pub fn group(values: egglog_experimental::typed::builtins::Vec<Self>) -> Self;
}
#[declarations]
impl std::ops::Add for Num {
    type Output = Self;
    #[constructor]
    fn add(self, rhs: Self) -> Self::Output;
}
#[declarations]
impl std::ops::Neg for &Num {
    type Output = Num;
    #[constructor]
    fn neg(self) -> Self::Output;
}
#[declarations]
impl std::ops::Sub for Num {
    type Output = Self;
    #[constructor]
    fn sub(self, rhs: Self) -> Self;
}
#[declarations]
impl std::ops::Div for Num {
    type Output = Self;
    #[constructor]
    fn div(self, rhs: Self) -> Self;
}
trait Measure {
    fn measure(&self, axis: &I64) -> I64;
}
#[declarations]
impl Measure for Num {
    #[function(no_merge)]
    fn measure(&self, axis: &I64) -> I64;
}
#[constructor]
fn foreign_result(value: I64) -> Num;
#[function(no_merge)]
fn absent(value: Num) -> I64;
#[constructor]
fn wrapped(value: Num) -> Num;

#[constructor]
#[allow(clippy::too_many_arguments)]
fn many(
    a0: I64,
    a1: I64,
    a2: I64,
    a3: I64,
    a4: I64,
    a5: I64,
    a6: I64,
    a7: I64,
    a8: I64,
    a9: I64,
    a10: I64,
    a11: I64,
    a12: I64,
    a13: I64,
    a14: I64,
    a15: I64,
    a16: I64,
    a17: I64,
    a18: I64,
    a19: I64,
    a20: I64,
    a21: I64,
    a22: I64,
    a23: I64,
    a24: I64,
    a25: I64,
    a26: I64,
    a27: I64,
    a28: I64,
    a29: I64,
    a30: I64,
    a31: I64,
) -> Num;
#[constructor]
fn empty() -> Num;

#[test]
fn selector_zero_and_32_argument_boundaries() -> Result<(), TypedError> {
    let node = many(
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
        25, 26, 27, 28, 29, 30, 31,
    );
    let selected = get_args(
        &node,
        |a0: &I64,
         a1: &I64,
         a2: &I64,
         a3: &I64,
         a4: &I64,
         a5: &I64,
         a6: &I64,
         a7: &I64,
         a8: &I64,
         a9: &I64,
         a10: &I64,
         a11: &I64,
         a12: &I64,
         a13: &I64,
         a14: &I64,
         a15: &I64,
         a16: &I64,
         a17: &I64,
         a18: &I64,
         a19: &I64,
         a20: &I64,
         a21: &I64,
         a22: &I64,
         a23: &I64,
         a24: &I64,
         a25: &I64,
         a26: &I64,
         a27: &I64,
         a28: &I64,
         a29: &I64,
         a30: &I64,
         a31: &I64| {
            many(
                a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
                a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31,
            )
        },
    )?
    .unwrap();
    assert_eq!(selected.0, I64::from(0));
    assert_eq!(selected.31, I64::from(31));
    assert_eq!(get_args(&empty(), empty)?, Some(()));
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register(empty())?;
    assert!(!graph.check(absent(Num::lit(3)))?);
    let frozen = graph.freeze()?;
    assert_eq!(frozen.table(empty)?.rows[0].args, ());
    assert!(frozen.table(|n: &Num| absent(n))?.rows.is_empty());
    assert!(frozen.table(|a: &I64, b: &I64| a + b).is_err());
    graph.register(subsume(empty()))?;
    let frozen = graph.freeze()?;
    let table = frozen.table(empty)?;
    assert!(table.rows[0].subsumed);
    let node = frozen.nodes(&table.rows[0].output)?.next().unwrap();
    assert!(frozen.is_subsumed(&node)?);
    assert!(frozen.is_subsumed(&table.rows[0].output).is_err());
    Ok(())
}

#[constructor]
fn hygiene(
    reference: I64,
    resolve: I64,
    __egglog_arg_0: I64,
    __egglog_reference: I64,
    __egglog_resolve: I64,
) -> Num;

static MERGE_INITIALIZATIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
fn shared_merge(old: I64, new: I64) -> I64 {
    MERGE_INITIALIZATIONS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    old.max(new)
}
fn old(left: I64, right: I64) -> I64 {
    left.max(right)
}
#[function(merge=old)]
fn old_named_merge(value: I64) -> I64;
#[sort]
struct RecursiveSelf;
#[declarations]
impl RecursiveSelf {
    fn Leaf(value: I64) -> Self;
    fn More(values: egglog_experimental::typed::builtins::Vec<Self>) -> Self;
}
#[declarations]
impl std::ops::Mul for Num {
    type Output = I64;
    #[function(merge=shared_merge)]
    fn mul(self, rhs: Self) -> I64;
}

#[test]
fn generated_names_are_hygienic_and_operator_definition_is_shared() -> Result<(), TypedError> {
    assert!(get_args(&old_named_merge(1), |x: &I64| old_named_merge(x))?.is_some());
    let recursive = RecursiveSelf::More(egglog_experimental::typed::builtins::Vec::of([
        RecursiveSelf::Leaf(1),
    ]));
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register(recursive)?;
    let values = get_args(
        &hygiene(1, 2, 3, 4, 5),
        |a: &I64, b: &I64, c: &I64, d: &I64, e: &I64| hygiene(a, b, c, d, e),
    )?
    .unwrap();
    assert_eq!(values, (1.into(), 2.into(), 3.into(), 4.into(), 5.into()));
    let x = Num::lit(1);
    let y = Num::lit(2);
    for value in [
        &x * &y,
        x.clone() * &y,
        &x * y.clone(),
        x.clone() * y.clone(),
        &x * 2,
        x.clone() * 2,
        &x * I64::from(2),
    ] {
        assert!(get_args(&value, |a: &Num, b: &Num| a * b)?.is_some());
    }
    assert_eq!(
        MERGE_INITIALIZATIONS.load(std::sync::atomic::Ordering::SeqCst),
        1
    );
    Ok(())
}

#[test]
fn conversions_preserve_constructors_calls_and_selector_sorts() -> Result<(), TypedError> {
    let x = Num::named("x");
    let integer = I64::from(2);
    let expected = &x + Num::lit(2);
    assert_eq!(&x + 2, expected);
    assert_eq!(x.clone() + 2, expected);
    assert_eq!(&x + &integer, expected);
    assert_eq!(&x + integer, expected);
    assert_eq!(&x + "y", &x + Num::named("y"));
    assert_eq!(x.pair(2), x.pair(Num::lit(2)));
    assert_eq!(wrapped("x"), wrapped(&x));
    assert_eq!(
        get_args(&expected, |a: &Num, b: &Num| a + b)?.unwrap(),
        (x.clone(), Num::lit(2))
    );
    assert!(get_args(&expected, |a: &Num, b: &I64| a + b).is_err());
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register((&expected, &x + 2, x.clone() + 2))?;
    let table = graph.freeze()?.table(|a: &Num, b: &Num| a + b)?;
    assert_eq!(table.rows.len(), 1);
    assert_eq!(
        table.name.as_ref(),
        concat!(module_path!(), "::<Num as std :: ops :: Add>::add")
    );
    graph.register(Num::from("unbound"))?;
    Ok(())
}

#[test]
fn conversions_run_once_per_operand_in_operators_methods_and_free_calls() {
    struct Counted<'a>(&'a std::cell::Cell<usize>);
    impl From<Counted<'_>> for Num {
        fn from(value: Counted<'_>) -> Self {
            value.0.set(value.0.get() + 1);
            Self::lit(2)
        }
    }
    impl From<&Counted<'_>> for Num {
        fn from(value: &Counted<'_>) -> Self {
            value.0.set(value.0.get() + 1);
            Self::lit(2)
        }
    }
    let count = std::cell::Cell::new(0);
    let value = Counted(&count);
    let x = Num::lit(1);
    let expected = &x + Num::lit(2);
    assert_eq!(&x + Counted(&count), expected);
    assert_eq!(count.get(), 1);
    assert_eq!(x.clone() + Counted(&count), expected);
    assert_eq!(count.get(), 2);
    assert_eq!(&x + &value, expected);
    assert_eq!(count.get(), 3);
    assert_eq!(x.clone() + &value, expected);
    assert_eq!(count.get(), 4);
    assert_eq!(x.pair(Counted(&count)), x.pair(Num::lit(2)));
    assert_eq!(count.get(), 5);
    assert_eq!(x.pair(&value), x.pair(Num::lit(2)));
    assert_eq!(count.get(), 6);
    assert_eq!(wrapped(&value), wrapped(Num::lit(2)));
    assert_eq!(count.get(), 7);
    assert_eq!(wrapped(value), wrapped(Num::lit(2)));
    assert_eq!(count.get(), 8);
}

mod heterogeneous {
    use super::*;
    #[sort]
    pub struct Left;
    #[sort]
    pub struct Right;
    #[sort]
    pub struct Output;
    type __EgglogRhs0 = Right;
    type __EgglogSignature0 = Output;
    #[constructor]
    pub fn left() -> Left;
    #[constructor(from(i64))]
    pub fn right(value: I64) -> Right;
    #[declarations]
    impl std::ops::Add<&__EgglogRhs0> for &Left {
        type Output = __EgglogSignature0;
        #[constructor(name = "ordinary::heterogeneous-add", cost = 7)]
        fn add(self, reference: &__EgglogRhs0) -> Self::Output;
    }
}

#[test]
fn heterogeneous_operator_conversions_keep_exact_signature_and_hygiene() -> Result<(), TypedError> {
    use heterogeneous::*;
    let x = left();
    let y = right(2);
    let sum: Output = &x + &y;
    for value in [
        x.clone() + y.clone(),
        &x + y.clone(),
        x.clone() + &y,
        &x + 2,
        x.clone() + 2,
    ] {
        assert_eq!(value, sum);
        assert_eq!(
            get_args(&value, |a: &Left, b: &Right| a + b)?.unwrap(),
            (x.clone(), y.clone())
        );
    }
    let capture = let_("heterogeneous", sum);
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register(&capture)?;
    let (extracted, cost) = graph.extract_with_cost(&capture)?;
    assert_eq!(extracted, &x + &y);
    assert_eq!(cost, 10); // Operator cost 7, two constructors, and one literal.
    let frozen = graph.freeze()?;
    let table = frozen.table(|a: &Left, b: &Right| a + b)?;
    assert_eq!(table.name.as_ref(), "ordinary::heterogeneous-add");
    assert_eq!(table.rows.len(), 1);
    assert_eq!(table.rows[0].output, frozen.lookup(&capture)?);
    let node = frozen.nodes(&table.rows[0].output)?.next().unwrap();
    assert_eq!(
        get_args(&node, |a: &Left, b: &Right| a + b)?.unwrap(),
        table.rows[0].args
    );
    Ok(())
}

#[constructor(name = "ordinary::collision")]
fn collision_ctor() -> Num;
#[function(name = "ordinary::collision", no_merge)]
fn collision_function() -> Num;
#[sort(name = "NativeNum")]
struct NativeNum;
#[constructor(name = "NativeLeaf", cost = 2)]
fn native_leaf() -> NativeNum;

#[test]
fn incompatible_nominal_heads_and_unverified_native_options_fail_closed() -> Result<(), TypedError>
{
    assert!(get_args(&collision_ctor(), collision_function).is_err());
    let mut native = egglog::EGraph::default();
    native
        .parse_and_run_program(
            None,
            "(sort NativeNum) (constructor NativeLeaf () NativeNum :cost 1) (NativeLeaf)",
        )
        .map_err(|e| TypedError::Decode(e.to_string()))?;
    egglog_experimental::typed::native::with_frozen(
        &native,
        &[],
        FreezeLimits::default(),
        |snapshot, _| {
            assert!(snapshot.table(native_leaf).is_err());
            assert_eq!(snapshot.tables().count(), 1);
            Ok(())
        },
    )?;
    Ok(())
}

#[test]
fn ordinary_methods_operators_and_projection() -> Result<(), TypedError> {
    let borrowed = var::<BorrowedNum>("borrowed");
    assert_eq!(&borrowed + &borrowed, borrowed.clone() + borrowed.clone());
    let x = Num::lit(1);
    let y = foreign_result(2);
    assert_eq!(x.call_name(), Some(concat!(module_path!(), "::Num::lit")));
    assert_eq!(
        y.call_name(),
        Some(concat!(module_path!(), "::foreign_result"))
    );
    assert_eq!(
        x.weight(2).call_name(),
        Some(concat!(module_path!(), "::Num::weight"))
    );
    assert!(borrowed.call_name().is_none());
    assert!(I64::from(1).call_name().is_none());
    assert_eq!((I64::from(1) + 2).call_name(), Some("+"));
    let sum = &x + &y;
    assert_eq!(sum, x.clone() + y.clone());
    assert_eq!(sum, &x + y.clone());
    assert_eq!(sum, x.clone() + &y);
    assert_eq!(-&x, -x.clone());
    let (left, right) = get_args(&sum, |a: &Num, b: &Num| a + b)?.unwrap();
    assert_eq!((left, right), (x.clone(), y.clone()));
    assert_eq!(
        get_args(&x, |n: &I64| Num::lit(n))?.unwrap().0,
        I64::from(1)
    );
    assert!(get_args(&y, |n: &I64| Num::lit(n))?.is_none());
    assert!(get_args(&sum, |a: &Num, b: &Num| b + a).is_err());
    assert!(get_args(&sum, |a: &Num, _b: &Num| a + a).is_err());
    assert!(get_args(&sum, |a: &Num, b: &Num| a + (a + b)).is_err());
    assert!(get_args(&sum, |a: &Num, _b: &Num| a + &y).is_err());
    assert!(get_args(&x, |_a: &I64| Num::lit(1)).is_err());
    assert_eq!(format!("{}", x.weight(2)), "Num::lit(1).weight(2)");
    assert_eq!(sum.to_string(), "Num::lit(1) + foreign_result(2)");
    assert_eq!(get_args(&x.measure(&2.into()), Num::measure)?.unwrap().0, x);
    Ok(())
}

#[test]
fn frozen_values_keep_sorts_snapshot_identity_and_producers() -> Result<(), TypedError> {
    let x = Num::lit(1);
    let y = foreign_result(2);
    let capture = let_("root", &x + &y);
    assert!(capture.call_name().is_none());
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register((&capture, x.seen(), set(x.weight(2), 9)))?;
    let frozen = graph.freeze()?;
    let observed: Num = frozen.lookup(&capture)?;
    assert!(observed.call_name().is_none());
    let observed_again = frozen.lookup(&capture)?;
    assert_eq!(observed, observed_again);
    assert!(frozen.lookup(&observed).is_err());
    assert!(get_args(&observed, |a: &Num, b: &Num| a + b)?.is_none());
    let node = frozen.nodes(&observed)?.next().unwrap();
    assert!(node.call_name().is_none());
    assert_ne!(observed, node);
    assert!(frozen.nodes(&node).is_err());
    assert!(!frozen.is_subsumed(&node)?);
    let (left, right) = get_args(&node, |a: &Num, b: &Num| a + b)?.unwrap();
    assert!(frozen.as_view(&left).is_ok());
    assert!(frozen.as_view(&right).is_ok());
    let table = frozen.table(|n: &Num, axis: &I64| n.weight(axis))?;
    assert_eq!(table.rows.len(), 1);
    assert_eq!(table.rows[0].args.0, left);
    assert!(get_args(&table.rows[0].output, |n: &Num, axis: &I64| n.weight(axis))?.is_none());
    assert!(frozen.table(|n: &Num| absent(n)).is_err());
    let relations = frozen.table(|n: &Num| n.seen())?;
    assert_eq!(relations.rows.len(), 1);
    let other = graph.freeze()?;
    assert_ne!(observed, other.lookup(&capture)?);
    assert!(other.as_view(&observed).is_err());
    assert!(other.as_view(&left).is_err());
    assert!(other.as_view(&right).is_err());
    let before = graph.num_tuples()?;
    for action in [
        Action::from(&observed),
        Action::from(&left + &right),
        delete(I64::from(3)),
    ] {
        assert!(matches!(
            graph.register(action),
            Err(TypedError::Invalid(_))
        ));
        assert_eq!(graph.num_tuples()?, before);
    }
    assert!(
        graph
            .register(Num::lit(table.rows[0].output.clone()))
            .is_err()
    );
    assert!(graph.register(set(&x, &y)).is_err());
    Ok(())
}

#[test]
fn display_preserves_operator_precedence_and_method_receivers() {
    let a = var::<Num>("a");
    let b = var::<Num>("b");
    let c = var::<Num>("c");
    assert_eq!((&a + &b - &c).to_string(), "a + b - c");
    assert_eq!((&a - (&b - &c)).to_string(), "a - (b - c)");
    assert_eq!((&a / (&b / &c)).to_string(), "a / (b / c)");
    assert_eq!(((&a + &b) / &c).to_string(), "(a + b) / c");
    assert_eq!((&a + &b / &c).to_string(), "a + b / c");
    assert_eq!(format!("{}", &a * (&b + &c)), "a * (b + c)");
    assert_eq!((-(&a + &b)).to_string(), "-(a + b)");
    assert_eq!((-(-&a)).to_string(), "-(-a)");
    assert_eq!(format!("{}", (&a + &b).weight(2)), "(a + b).weight(2)");
    assert_eq!(format!("{}", (-&a).weight(2)), "(-a).weight(2)");
    let group = Num::group(egglog_experimental::typed::builtins::Vec::of([
        a.clone(),
        b,
    ]));
    assert!(
        get_args(
            &group,
            |xs: &egglog_experimental::typed::builtins::Vec<Num>| Num::group(xs)
        )
        .unwrap()
        .is_some()
    );
    let mut deep = a;
    for _ in 0..100_000 {
        deep = -deep;
    }
    let displayed = deep.to_string();
    assert_eq!(displayed.len(), 299_999);
}
