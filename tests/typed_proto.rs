#![cfg(feature = "typed")]

use egglog_experimental::typed::prelude::*;
use std::hash::{DefaultHasher, Hash, Hasher};

mod relation_predicates {
    use super::*;
    use egglog_experimental::proto as pb;
    use egglog_experimental::typed::builtins::{I64, String as EggString, Unit};
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[sort(name = "DType")]
    struct DType;
    #[declarations]
    impl DType {
        #[constructor(name = "F32")]
        fn F32() -> Self;
    }
    #[sort(name = "IR")]
    struct Ir;
    #[declarations]
    impl Ir {
        #[constructor(name = "Input")]
        fn Input(node: I64, label: EggString, dtype: DType) -> Self;
    }
    #[sort(name = "IList")]
    struct IList;
    #[declarations]
    impl IList {
        #[constructor(name = "ICons")]
        fn ICons(head: Ir, tail: IList) -> Self;
        #[constructor(name = "INil")]
        fn INil() -> Self;
    }

    // The genuine Luminal declaration is a separate, single-method impl.
    #[declarations]
    impl IList {
        #[relation(name = "identical_inputs")]
        pub fn identical_inputs(&self);
    }
    #[declarations]
    impl IList {
        #[relation(name = "ordered_inputs")]
        fn ordered_inputs(&self, index: I64);
    }
    #[relation(name = "identical_inputs")]
    fn free_identical_inputs(value: IList);
    #[relation(name = "ordered_inputs")]
    fn free_ordered_inputs(value: IList, index: I64);

    static INITIALIZATIONS: AtomicUsize = AtomicUsize::new(0);
    fn counted_relation_name() -> &'static str {
        INITIALIZATIONS.fetch_add(1, Ordering::SeqCst);
        "counted_inputs"
    }
    #[declarations]
    impl IList {
        #[relation(name = counted_relation_name())]
        fn counted_inputs(&self, index: I64);
    }

    #[function(name = "relation_marker", merge = |_old: I64, new: I64| new)]
    fn marker() -> I64;
    #[function(name = "relation_unit_value", no_merge)]
    fn unit_value(key: I64) -> Unit;
    #[constructor(name = "RelationUnitChild")]
    fn unit_child(value: Unit) -> Ir;

    #[test]
    fn luminal_identical_inputs_base_and_induction_use_query_and_head_rows()
    -> Result<(), TypedError> {
        let x = Ir::Input(1_i64, "x", DType::F32());
        let y = Ir::Input(2_i64, "y", DType::F32());
        let single = IList::ICons(&x, IList::INil());
        let repeated = IList::ICons(&x, &single);
        let mixed = IList::ICons(&y, &single);
        let mut graph = EGraph::new()?;
        graph.register((&single, &repeated, &mixed))?;
        let predicate: Unit = single.identical_inputs();
        assert!(!graph.check(&predicate)?);
        assert!(!graph.check(&predicate)?, "query must not insert a row");

        // These are the actual predicate base/head and inductive/query shapes
        // from L's loops rules. This component fixture does not replace or edit
        // L's still-independent .label API or claim its whole ruleset ran.
        let predicates = ruleset(|vl: &IList, vx: &Ir, vtail: &IList| {
            (
                rule(
                    (eq(vl, IList::ICons(vx, IList::INil())),),
                    (vl.identical_inputs(),),
                ),
                rule(
                    (
                        eq(vl, IList::ICons(vx, IList::ICons(vx, vtail))),
                        IList::ICons(vx, vtail).identical_inputs(),
                    ),
                    (vl.identical_inputs(),),
                ),
            )
        });
        for _ in 0..3 {
            graph.run(&predicates)?;
        }
        assert!(graph.check(single.identical_inputs())?);
        assert!(graph.check(repeated.identical_inputs())?);
        assert!(!graph.check(mixed.identical_inputs())?);
        assert!(!graph.check(IList::INil().identical_inputs())?);
        assert!(graph.check(free_identical_inputs(&single))?);
        Ok(())
    }

    #[test]
    fn owned_borrowed_unit_predicates_delete_and_reinsert_without_a_value_wrapper()
    -> Result<(), TypedError> {
        let list = IList::ICons(Ir::Input(3_i64, "owned", DType::F32()), IList::INil());
        let predicate: Unit = list.identical_inputs();
        let mut graph = EGraph::new()?;
        assert!(!graph.check(&predicate)?);
        graph.register(&predicate)?;
        assert!(graph.check(predicate.clone())?);
        graph.register(predicate.clone())?;
        graph.register(delete(&predicate))?;
        assert!(!graph.check(&predicate)?);
        graph.register(predicate.clone())?;
        assert!(graph.check(&predicate)?);
        assert!(graph.check(free_identical_inputs(&list))?);
        drop(list);
        assert!(graph.check(predicate)?);
        Ok(())
    }

    #[test]
    fn free_and_borrowed_receiver_inputs_keep_order_and_initialize_once() -> Result<(), TypedError>
    {
        let list = IList::ICons(Ir::Input(4_i64, "order", DType::F32()), IList::INil());
        let other = IList::INil();
        let borrowed = &list;
        let first: Unit = list.counted_inputs(11_i64);
        let index = I64::from(11_i64);
        let second: Unit = borrowed.counted_inputs(&index);
        assert_eq!(INITIALIZATIONS.load(Ordering::SeqCst), 1);
        // Structural call equality is not native retained-row identity.
        assert_eq!(first, second);
        let Some((selected_list, selected_index)) =
            get_args(&first, |value: &IList, index: &I64| {
                value.counted_inputs(index)
            })?
        else {
            panic!("an input-only relation call must retain its ordered argument records");
        };
        assert_eq!(selected_list, list);
        assert_eq!(selected_index, index);
        assert_eq!(i64::try_from(&selected_index)?, 11);
        let mut graph = EGraph::new()?;
        graph.register((&first, list.ordered_inputs(11_i64)))?;
        assert!(graph.check(second)?);
        assert!(graph.check(free_ordered_inputs(&list, 11_i64))?);
        assert!(!graph.check(free_ordered_inputs(&list, 12_i64))?);
        assert!(!graph.check(free_ordered_inputs(&other, 11_i64))?);
        assert_eq!(INITIALIZATIONS.load(Ordering::SeqCst), 1);
        Ok(())
    }

    #[test]
    fn relation_values_and_captures_reject_before_marker_writes() -> Result<(), TypedError> {
        for installed in [false, true] {
            for case in [
                "nested",
                "set-value",
                "set-target",
                "subsume",
                "capture",
                "extract",
                "equality",
            ] {
                let list = IList::ICons(Ir::Input(5_i64, "guard", DType::F32()), IList::INil());
                let predicate: Unit = list.identical_inputs();
                let mut graph = EGraph::new()?;
                graph.register(set(marker(), 0_i64))?;
                if installed {
                    graph.register(&predicate)?;
                }
                let result = match case {
                    "nested" => graph.register((set(marker(), 99_i64), unit_child(&predicate))),
                    "set-value" => {
                        graph.register((set(marker(), 99_i64), set(unit_value(1_i64), &predicate)))
                    }
                    "set-target" => {
                        graph.register((set(marker(), 99_i64), set(&predicate, Unit::from(()))))
                    }
                    "subsume" => graph.register((set(marker(), 99_i64), subsume(&predicate))),
                    "capture" => {
                        let captured = let_("not-a-relation-value", &predicate);
                        graph.register((set(marker(), 99_i64), &captured))
                    }
                    "extract" => graph.extract(&predicate).map(|_| ()),
                    "equality" => graph.check(eq(&predicate, Unit::from(()))).map(|_| ()),
                    _ => unreachable!(),
                };
                let error = result.expect_err("relation row used as a value must be rejected");
                match &error {
                    TypedError::Invalid(_) => {}
                    TypedError::Engine(error) => {
                        assert_eq!(error.code, pb::ErrorCode::InvalidProgram as i32)
                    }
                    other => panic!("{installed}/{case}: wrong error {other:?}"),
                }
                if matches!(case, "set-target" | "subsume") {
                    // Existing row-action kind checks reject these operations
                    // before packing. Relation support only extends Delete.
                    let TypedError::Invalid(message) = &error else {
                        panic!("{installed}/{case}: expected existing action-kind rejection");
                    };
                    assert!(message.contains("Set requires a function"));
                    assert!(message.contains("Subsume requires a constructor"));
                } else {
                    assert!(
                        error.to_string().contains("relation"),
                        "{installed}/{case}: {error:?}"
                    );
                }
                assert_eq!(
                    i64::try_from(&graph.extract(marker())?)?,
                    0,
                    "{installed}/{case}"
                );
                graph.register((set(marker(), 2_i64), &predicate))?;
                assert!(graph.check(&predicate)?);
                assert_eq!(i64::try_from(&graph.extract(marker())?)?, 2);
            }
        }
        Ok(())
    }

    #[relation(name = "__typed_capture_0")]
    fn authored_capture_spelling(key: I64);

    #[test]
    fn first_relation_delete_reserves_its_name_before_fresh_capture_allocation()
    -> Result<(), TypedError> {
        let mut graph = EGraph::new()?;
        let captured = let_("ordinary-relation-neighbor", I64::from(17_i64));
        graph.register((delete(authored_capture_spelling(42_i64)), &captured))?;
        assert_eq!(i64::try_from(&graph.extract(&captured)?)?, 17);
        assert!(!graph.check(authored_capture_spelling(42_i64))?);
        Ok(())
    }
}

mod trait_operators {
    use super::*;
    use egglog_experimental::typed::builtins::I64;
    use std::sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    };

    #[sort(name = "Expression")]
    struct DimExpr;

    #[declarations]
    impl DimExpr {
        #[constructor(name = "MNum", from(i32, i64, &i32, &i64))]
        fn MNum(value: I64) -> Self;
    }

    // These are the five genuine Luminal declaration shapes, not separate
    // hand-written operator bodies or replacement runtime fixtures.
    #[declarations]
    impl std::ops::Add<&DimExpr> for &DimExpr {
        type Output = DimExpr;
        #[constructor(name = "MAdd")]
        fn add(self, rhs: &DimExpr) -> DimExpr;
    }
    #[declarations]
    impl std::ops::Sub<&DimExpr> for &DimExpr {
        type Output = DimExpr;
        #[constructor(name = "MSub")]
        fn sub(self, rhs: &DimExpr) -> DimExpr;
    }
    #[declarations]
    impl std::ops::Mul<&DimExpr> for &DimExpr {
        type Output = DimExpr;
        #[constructor(name = "MMul")]
        fn mul(self, rhs: &DimExpr) -> DimExpr;
    }
    #[declarations]
    impl std::ops::Div<&DimExpr> for &DimExpr {
        type Output = DimExpr;
        #[constructor(name = "MDiv")]
        fn div(self, rhs: &DimExpr) -> DimExpr;
    }
    #[declarations]
    impl std::ops::Rem<&DimExpr> for &DimExpr {
        type Output = DimExpr;
        #[constructor(name = "MMod")]
        fn rem(self, rhs: &DimExpr) -> DimExpr;
    }

    #[constructor(name = "MAdd")]
    fn exact_add(left: DimExpr, right: DimExpr) -> DimExpr;
    #[constructor(name = "MSub")]
    fn exact_sub(left: DimExpr, right: DimExpr) -> DimExpr;
    #[constructor(name = "MMul")]
    fn exact_mul(left: DimExpr, right: DimExpr) -> DimExpr;
    #[constructor(name = "MDiv")]
    fn exact_div(left: DimExpr, right: DimExpr) -> DimExpr;
    #[constructor(name = "MMod")]
    fn exact_rem(left: DimExpr, right: DimExpr) -> DimExpr;

    #[test]
    fn ownership_forms_keep_exact_names_and_selector_operand_order() -> Result<(), TypedError> {
        let left = DimExpr::MNum(11_i64);
        let right = DimExpr::MNum(7_i64);
        macro_rules! check_forms {
            ($operator:tt, $exact:ident) => {
                for value in [
                    &left $operator &right,
                    left.clone() $operator &right,
                    &left $operator right.clone(),
                    left.clone() $operator right.clone(),
                    &left $operator 7_i32,
                    left.clone() $operator I64::from(7_i64),
                ] {
                    assert_eq!(value, $exact(&left, &right));
                    let (a, b) = get_args(&value, |a: &DimExpr, b: &DimExpr| a $operator b)?.unwrap();
                    assert_eq!(a, left);
                    assert_eq!(b, right);
                    assert!(get_args(&value, |a: &DimExpr, b: &DimExpr| b $operator a).is_err());
                }
            };
        }
        check_forms!(+, exact_add);
        check_forms!(-, exact_sub);
        check_forms!(*, exact_mul);
        check_forms!(/, exact_div);
        check_forms!(%, exact_rem);
        assert!(get_args(&(&left + &right), |a: &DimExpr, b: &DimExpr| a - b)?.is_none());

        // Nominal arithmetic remains syntax, including a zero divisor. The
        // existing byte engine installs and extracts these constructors.
        let values = vec![
            &left + &right,
            &left - &right,
            &left * &right,
            &left / 0_i64,
            &left % 0_i64,
        ];
        let mut graph = EGraph::new()?;
        graph.register(values.clone())?;
        let extracted = graph.extract(&values[3])?;
        drop(graph);
        let (a, b) = get_args(&extracted, |a: &DimExpr, b: &DimExpr| a / b)?.unwrap();
        assert_eq!(a, left);
        assert_eq!(b, DimExpr::MNum(0_i64));
        Ok(())
    }

    #[sort]
    struct Initialized;
    #[declarations]
    impl Initialized {
        #[constructor(from(i32, i64))]
        fn Num(value: I64) -> Self;
    }
    static INITIALIZATIONS: AtomicUsize = AtomicUsize::new(0);
    fn counted_name() -> &'static str {
        INITIALIZATIONS.fetch_add(1, Ordering::SeqCst);
        "trait-operator-initialized"
    }
    #[declarations]
    impl std::ops::Add<&Initialized> for &Initialized {
        type Output = Initialized;
        #[constructor(name = counted_name())]
        fn add(self, rhs: &Initialized) -> Initialized;
    }
    struct CountedRhs {
        value: Initialized,
        conversions: Arc<AtomicUsize>,
    }
    impl From<CountedRhs> for Initialized {
        fn from(rhs: CountedRhs) -> Self {
            assert_eq!(INITIALIZATIONS.load(Ordering::SeqCst), 1);
            rhs.conversions.fetch_add(1, Ordering::SeqCst);
            rhs.value
        }
    }

    #[test]
    fn metadata_initializes_once_and_rhs_converts_once_after_it() -> Result<(), TypedError> {
        let left = Initialized::Num(11_i64);
        let right = Initialized::Num(7_i64);
        let conversions = Arc::new(AtomicUsize::new(0));
        for borrowed in [false, true] {
            let rhs = CountedRhs {
                value: right.clone(),
                conversions: conversions.clone(),
            };
            let value = if borrowed {
                &left + rhs
            } else {
                left.clone() + rhs
            };
            let (a, b) = get_args(&value, |a: &Initialized, b: &Initialized| a + b)?.unwrap();
            assert_eq!(a, left);
            assert_eq!(b, right);
        }
        assert_eq!(conversions.load(Ordering::SeqCst), 2);
        assert_eq!(&left + 7_i32, left.clone() + 7_i64);
        assert_eq!(&left + &right, left.clone() + right.clone());
        assert_eq!(INITIALIZATIONS.load(Ordering::SeqCst), 1);
        Ok(())
    }

    #[sort]
    struct Left;
    #[sort]
    struct Right;
    #[sort]
    struct Output;
    type RightAlias = Right;
    #[declarations]
    impl Left {
        fn Leaf(value: I64) -> Self;
    }
    #[declarations]
    impl Right {
        #[constructor(from(i64))]
        fn Leaf(value: I64) -> Self;
    }
    #[declarations]
    impl core::ops::Add<&RightAlias> for &Left {
        type Output = Output;
        #[constructor(name = "heterogeneous-operator")]
        fn add(self, rhs: &Right) -> Output;
    }
    #[constructor(name = "heterogeneous-operator")]
    fn exact_heterogeneous(left: Left, right: Right) -> Output;

    #[test]
    fn heterogeneous_declared_sorts_and_type_aliases_stay_fixed() -> Result<(), TypedError> {
        let left = Left::Leaf(11_i64);
        let right = Right::Leaf(7_i64);
        for value in [&left + &right, left.clone() + 7_i64] {
            assert_eq!(value, exact_heterogeneous(&left, &right));
            let (a, b) = get_args(&value, |a: &Left, b: &Right| a + b)?.unwrap();
            assert_eq!(a, left);
            assert_eq!(b, right);
        }
        Ok(())
    }

    #[sort]
    struct __EgglogSignature;
    #[sort]
    struct __EgglogRhs;
    #[declarations]
    impl __EgglogSignature {
        fn Leaf(value: I64) -> Self;
    }
    #[declarations]
    impl __EgglogRhs {
        fn Leaf(value: I64) -> Self;
    }
    #[declarations]
    impl std::ops::Add<&__EgglogRhs> for &__EgglogSignature {
        type Output = __EgglogSignature;
        #[constructor]
        fn add(self, __egglog_argument_0: &__EgglogRhs) -> __EgglogSignature;
    }
    #[declarations]
    impl std::ops::Add<&UndefinedRhs> for &__EgglogRhs {
        type Output = __EgglogRhs;
        #[cfg(any())]
        #[constructor]
        fn add(self, rhs: &UndefinedRhs) -> __EgglogRhs;
    }

    #[test]
    fn generated_items_do_not_shadow_authored_sorts_and_parameters() -> Result<(), TypedError> {
        let left = __EgglogSignature::Leaf(11_i64);
        let right = __EgglogRhs::Leaf(7_i64);
        let value = &left + &right;
        let (a, b) = get_args(&value, |a: &__EgglogSignature, b: &__EgglogRhs| a + b)?.unwrap();
        assert_eq!(a, left);
        assert_eq!(b, right);
        assert_eq!(value, left + right);
        Ok(())
    }

    struct Ordinary;
    #[declarations]
    impl std::ops::Add<&Ordinary> for &Ordinary {
        type Output = Ordinary;
        fn add(self, rhs: &Ordinary) -> Ordinary {
            let _ = (self, rhs);
            Ordinary
        }
    }
    #[test]
    fn ordinary_body_bearing_trait_impl_remains_plain_rust() {
        let _: Ordinary = &Ordinary + &Ordinary;
    }
}

mod constructor_from_sources {
    use super::*;
    use egglog_experimental::typed::builtins::{F64, I64, String as EString};

    #[sort(name = "Expression")]
    struct DimExpr;

    #[declarations]
    impl DimExpr {
        #[constructor(name = "MNum", from(i32, i64, &i32, &i64))]
        fn MNum(number: I64) -> Self;

        #[constructor(name = "MFloat", from(f64, &f64))]
        fn MFloat(value: F64) -> Self;

        #[constructor(name = "MVar", from(&str, std::string::String, &std::string::String))]
        fn MVar(name: EString) -> Self;

        #[cfg(any())]
        #[constructor(from(UndefinedSource))]
        fn Disabled(value: UndefinedInput) -> Self;
    }

    #[test]
    fn integer_sources_preserve_fields_and_symbolic_ownership() -> Result<(), TypedError> {
        for value in [i32::MIN, -1, 0, i32::MAX] {
            let expression = DimExpr::from(value);
            assert_eq!(expression, DimExpr::MNum(value));
            assert_eq!(DimExpr::from(&value), expression);
            let (field,) = get_args(&expression, |number: &I64| DimExpr::MNum(number))?.unwrap();
            assert_eq!(i64::try_from(&field)?, i64::from(value));
        }
        for value in [i64::MIN, -1, 0, i64::MAX] {
            let expression = DimExpr::from(value);
            assert_eq!(expression, DimExpr::MNum(value));
            assert_eq!(DimExpr::from(&value), expression);
        }
        let number = var::<I64>("number");
        assert_eq!(DimExpr::from(&number), DimExpr::MNum(&number));
        assert_eq!(DimExpr::from(number.clone()), DimExpr::MNum(&number));
        let quotient = I64::from(1_i64) / I64::from(0_i64);
        assert_eq!(DimExpr::from(&quotient), DimExpr::MNum(&quotient));
        Ok(())
    }

    #[test]
    fn float_bits_and_names_remain_literal_data() -> Result<(), TypedError> {
        for bits in [
            0x0000_0000_0000_0000,
            0x8000_0000_0000_0000,
            0x7ff8_0000_0000_1234,
            f64::INFINITY.to_bits(),
        ] {
            let value = f64::from_bits(bits);
            let expression = DimExpr::from(value);
            assert_eq!(expression, DimExpr::MFloat(value));
            assert_eq!(DimExpr::from(&value), expression);
            let (field,) = get_args(&expression, |value: &F64| DimExpr::MFloat(value))?.unwrap();
            assert_eq!(f64::try_from(&field)?.to_bits(), bits);
        }
        let float = var::<F64>("float");
        assert_eq!(DimExpr::from(&float), DimExpr::MFloat(&float));
        assert_eq!(DimExpr::from(float.clone()), DimExpr::MFloat(&float));
        let name = "quote\" slash\\ nul\0 λ😀".to_owned();
        let symbolic = EString::from(name.as_str());
        let expected = DimExpr::MVar(&symbolic);
        assert_eq!(DimExpr::from(name.as_str()), expected);
        assert_eq!(DimExpr::from(name.clone()), expected);
        assert_eq!(DimExpr::from(&name), expected);
        assert_eq!(DimExpr::from(&symbolic), expected);
        assert_eq!(DimExpr::from(symbolic.clone()), expected);
        let (field,) = get_args(&expected, |name: &EString| DimExpr::MVar(name))?.unwrap();
        assert_eq!(std::string::String::try_from(&field)?, name);
        assert_ne!(DimExpr::from("x"), var::<DimExpr>("x"));
        assert_ne!(DimExpr::from(1_i64), DimExpr::from(1.0_f64));
        Ok(())
    }

    #[test]
    fn converted_constructors_execute_through_registered_bytes() -> Result<(), TypedError> {
        let number = DimExpr::from(i32::MIN);
        let name = DimExpr::from("value\0λ");
        let float = DimExpr::from(2.5_f64);
        let mut graph = EGraph::new()?;
        graph.register(vec![number.clone(), name.clone(), float.clone()])?;
        assert_eq!(graph.extract(&number)?, number);
        assert_eq!(graph.extract(&name)?, name);
        assert_eq!(graph.extract(&float)?, float);
        let (field,) = get_args(&number, |number: &I64| DimExpr::MNum(number))?.unwrap();
        assert_eq!(i64::try_from(&field)?, i64::from(i32::MIN));
        Ok(())
    }
}

#[sort]
struct RuleTerms;
#[declarations]
impl RuleTerms {
    fn Input(value: egglog_experimental::typed::builtins::I64) -> Self;
    fn Copied(value: egglog_experimental::typed::builtins::I64) -> Self;
    fn Second(value: egglog_experimental::typed::builtins::I64) -> Self;
    fn CapturePair(
        first: egglog_experimental::typed::builtins::I64,
        second: egglog_experimental::typed::builtins::I64,
    ) -> Self;
}

#[function(no_merge, args = ReadArgs)]
fn Read(
    key: egglog_experimental::typed::builtins::I64,
) -> egglog_experimental::typed::builtins::I64;

#[function(no_merge, args = EmptyArgs)]
fn EmptyRead() -> egglog_experimental::typed::builtins::I64;

mod merged_functions {
    use super::*;
    use egglog_experimental::typed::builtins::I64;
    use std::sync::{
        OnceLock,
        atomic::{AtomicUsize, Ordering},
    };

    #[declarations]
    impl RuleTerms {
        #[function(name = "lower", merge = |old: I64, new: I64| old.max(new))]
        fn lower(&self) -> I64;

        #[function(name = "upper", merge = |old: I64, new: I64| old.min(new))]
        fn upper(&self) -> I64;

        #[function(name = "len", merge = |old: I64, new: I64| { let _ = old; new })]
        fn len(&self) -> I64;

        #[function(name = "nominal", merge = |old: RuleTerms, new: RuleTerms| { let _ = old; new })]
        fn nominal(&self) -> RuleTerms;

        #[function(name = "nth_from_end", merge = |old: RuleTerms, new: RuleTerms| { let _ = old; new })]
        fn nth_from_end(&self, index: I64) -> RuleTerms;
    }

    static DEFINITIONS: AtomicUsize = AtomicUsize::new(0);

    #[function(name = "counted_merge", merge = |old: I64, new: I64| {
        DEFINITIONS.fetch_add(1, Ordering::SeqCst);
        old.max(new)
    })]
    fn counted(key: I64) -> I64;

    #[function(name = "shared_merge", merge = |old: I64, new: I64| old.max(new))]
    fn shared_first(key: I64) -> I64;

    #[function(name = "shared_merge", merge = |old: I64, new: I64| old.max(new))]
    fn shared_second(key: I64) -> I64;

    #[function(name = "shared_merge", merge = |old: I64, new: I64| old.min(new))]
    fn shared_conflict(key: I64) -> I64;

    #[function(merge = |_: I64, _: I64| var::<I64>("outside"))]
    fn foreign_variable(key: I64) -> I64;

    #[function(merge = |_: I64, new: I64| let_("merge-capture", new))]
    fn captured_variable(key: I64) -> I64;

    static ESCAPED_PARAMETERS: OnceLock<(I64, I64)> = OnceLock::new();

    #[function(merge = |old: I64, new: I64| {
        ESCAPED_PARAMETERS
            .set((old, new.clone()))
            .expect("the donor definition is authored once");
        new
    })]
    fn parameter_donor(key: I64) -> I64;

    #[function(merge = |_: I64, _: I64| {
        ESCAPED_PARAMETERS.get().expect("donor was authored").0.clone()
    })]
    fn escaped_old(key: I64) -> I64;

    #[function(merge = |_: I64, _: I64| {
        ESCAPED_PARAMETERS.get().expect("donor was authored").1.clone()
    })]
    fn escaped_new(key: I64) -> I64;

    #[test]
    fn escaped_merge_parameters_are_foreign_before_marker_writes() -> Result<(), TypedError> {
        let _ = parameter_donor(0);
        let mut graph = EGraph::new()?;
        for escaped in [escaped_old(1), escaped_new(1)] {
            assert!(matches!(
                graph.register((set(Read(93), 93), set(escaped, 1))),
                Err(TypedError::Invalid(_))
            ));
            assert!(!graph.check(Read(93))?);
        }
        Ok(())
    }

    #[function(merge = |old: I64, _: I64| recursive_merge(old))]
    fn recursive_merge(key: I64) -> I64;

    #[function(merge = |old: I64, _: I64| mutual_second(old))]
    fn mutual_first(key: I64) -> I64;

    #[function(merge = |old: I64, _: I64| mutual_first(old))]
    fn mutual_second(key: I64) -> I64;

    fn bounded_merge_initialization(
        case: &str,
        initialize: impl FnOnce() + std::panic::UnwindSafe,
    ) {
        const CHILD_CASE: &str = "EGGLOG_TYPED_MERGE_INITIALIZATION_CASE";
        if std::env::var(CHILD_CASE).as_deref() == Ok(case) {
            eprintln!("{case}: merge initialization child entered");
            let panic = std::panic::catch_unwind(initialize)
                .expect_err("recursive merge authoring must reject before waiting");
            let message = panic
                .downcast_ref::<&str>()
                .copied()
                .or_else(|| {
                    panic
                        .downcast_ref::<std::string::String>()
                        .map(String::as_str)
                })
                .unwrap_or("");
            assert!(
                message.contains("recursive function merge initialization"),
                "{case}: unexpected authoring panic: {message}"
            );
            return;
        }
        let mut child = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                &format!("merged_functions::merge_initialization_{case}_is_bounded"),
                "--nocapture",
                "--test-threads=1",
            ])
            .env(CHILD_CASE, case)
            .spawn()
            .expect("start merge-initialization child");
        let started = std::time::Instant::now();
        let status = loop {
            match child.try_wait() {
                Ok(Some(status)) => break status,
                Ok(None) if started.elapsed() < std::time::Duration::from_secs(5) => {
                    std::thread::sleep(std::time::Duration::from_millis(10));
                }
                Ok(None) => {
                    let killed = child.kill();
                    let reaped = child.wait();
                    panic!(
                        "{case}: merge initialization exceeded5s; child kill={killed:?}, wait={reaped:?}"
                    );
                }
                Err(error) => {
                    let killed = child.kill();
                    let reaped = child.wait();
                    panic!("{case}: child wait failed: {error}; kill={killed:?}, wait={reaped:?}");
                }
            }
        };
        assert!(status.success(), "{case}: child failed: {status}");
    }

    #[test]
    fn merge_initialization_self_is_bounded() {
        bounded_merge_initialization("self", || {
            let _ = recursive_merge(0);
        });
    }

    #[test]
    fn merge_initialization_mutual_is_bounded() {
        bounded_merge_initialization("mutual", || {
            let _ = mutual_first(0);
        });
    }

    mod caller_panic_macro {
        use super::*;

        macro_rules! panic {
            ($($message:tt)*) => {
                ()
            };
        }

        #[function(merge = |old: I64, _: I64| recursive(old))]
        fn recursive(key: I64) -> I64;

        pub(super) fn initialize() {
            panic!("the caller's panic macro is deliberately inert");
            let _ = recursive(0);
        }
    }

    #[test]
    fn merge_initialization_caller_panic_macro_is_bounded() {
        bounded_merge_initialization("caller_panic_macro", caller_panic_macro::initialize);
    }

    #[sort]
    struct __EgglogMergeInitialization;

    #[declarations]
    impl __EgglogMergeInitialization {
        fn Before() -> Self;
        fn After() -> Self;
    }

    #[function(merge = |_: __EgglogMergeInitialization, new: __EgglogMergeInitialization| new)]
    fn reset_item_scope(key: I64) -> __EgglogMergeInitialization;

    #[test]
    fn merge_initialization_reset_item_does_not_shadow_authored_sort() -> Result<(), TypedError> {
        let first = __EgglogMergeInitialization::Before();
        let second = __EgglogMergeInitialization::After();
        let mut graph = EGraph::new()?;
        graph.register((
            set(reset_item_scope(0), &first),
            set(reset_item_scope(0), &second),
        ))?;
        assert_eq!(graph.extract(reset_item_scope(0))?, second);
        assert!(!graph.check(eq(&first, &second))?);
        Ok(())
    }

    static CONCURRENT_DEFINITIONS: AtomicUsize = AtomicUsize::new(0);

    #[function(merge = |old: I64, new: I64| {
        CONCURRENT_DEFINITIONS.fetch_add(1, Ordering::SeqCst);
        std::thread::sleep(std::time::Duration::from_millis(50));
        old.max(new)
    })]
    fn concurrent_definition(key: I64) -> I64;

    #[test]
    fn merge_initialization_concurrent_callers_share_one_definition() {
        let gate = std::sync::Arc::new(std::sync::Barrier::new(3));
        let first_gate = std::sync::Arc::clone(&gate);
        let first = std::thread::spawn(move || {
            first_gate.wait();
            concurrent_definition(1)
        });
        let second_gate = std::sync::Arc::clone(&gate);
        let second = std::thread::spawn(move || {
            second_gate.wait();
            concurrent_definition(2)
        });
        gate.wait();
        let first = first.join();
        let second = second.join();
        assert_ne!(first.unwrap(), second.unwrap());
        assert_eq!(CONCURRENT_DEFINITIONS.load(Ordering::SeqCst), 1);
    }

    static RETRY_ATTEMPTS: AtomicUsize = AtomicUsize::new(0);

    #[function(merge = |old: I64, new: I64| {
        assert_ne!(
            RETRY_ATTEMPTS.fetch_add(1, Ordering::SeqCst),
            0,
            "intentional merge authoring panic"
        );
        old.max(new)
    })]
    fn retried_definition(key: I64) -> I64;

    #[test]
    fn merge_initialization_retries_after_authoring_panic() {
        let panic = std::panic::catch_unwind(|| {
            let _ = retried_definition(1);
        })
        .expect_err("first authoring attempt must panic");
        let message = panic
            .downcast_ref::<&str>()
            .copied()
            .or_else(|| {
                panic
                    .downcast_ref::<std::string::String>()
                    .map(String::as_str)
            })
            .unwrap_or("");
        assert!(message.contains("intentional merge authoring panic"));
        assert_ne!(retried_definition(1), retried_definition(2));
        assert_eq!(RETRY_ATTEMPTS.load(Ordering::SeqCst), 2);
    }

    #[test]
    fn luminal_shaped_bounds_and_scalar_keep_new() -> Result<(), TypedError> {
        let key = RuleTerms::Input(7);
        let mut graph = EGraph::new()?;
        for value in [10_i64, 30, 20] {
            graph.register((
                set(key.lower(), value),
                set(key.upper(), value),
                set(key.len(), value),
            ))?;
        }
        assert_eq!(i64::try_from(&graph.extract(key.lower())?)?, 30);
        assert_eq!(i64::try_from(&graph.extract(key.upper())?)?, 10);
        assert_eq!(i64::try_from(&graph.extract(key.len())?)?, 20);
        assert_eq!(
            get_args(&key.lower(), |owner: &RuleTerms| owner.lower())?
                .unwrap()
                .0,
            key
        );
        Ok(())
    }

    #[test]
    fn nominal_keep_new_does_not_union_the_outputs() -> Result<(), TypedError> {
        let key = RuleTerms::Input(0);
        let first = RuleTerms::Input(1);
        let second = RuleTerms::Copied(2);
        let mut graph = EGraph::new()?;
        graph.register((set(key.nominal(), &first), set(key.nominal(), &second)))?;
        graph.register((
            set(key.nth_from_end(2), &first),
            set(key.nth_from_end(2), &second),
        ))?;
        assert_eq!(graph.extract(key.nominal())?, second);
        assert_eq!(graph.extract(key.nth_from_end(2))?, second);
        assert_eq!(
            get_args(&key.nth_from_end(2), |owner: &RuleTerms, index: &I64| {
                owner.nth_from_end(index)
            })?
            .unwrap(),
            (key, I64::from(2))
        );
        assert!(!graph.check(eq(&first, &second))?);
        Ok(())
    }

    #[test]
    fn merge_definition_is_authored_once_across_graphs() -> Result<(), TypedError> {
        for key in [1_i64, 2] {
            let mut graph = EGraph::new()?;
            graph.register((set(counted(key), 10), set(counted(key), 30)))?;
            assert_eq!(i64::try_from(&graph.extract(counted(key))?)?, 30);
        }
        assert_eq!(DEFINITIONS.load(Ordering::SeqCst), 1);
        Ok(())
    }

    #[test]
    fn compatible_owners_share_the_actual_merge_body() -> Result<(), TypedError> {
        let mut graph = EGraph::new()?;
        graph.register((
            set(shared_first(1), 10),
            set(shared_second(1), 30),
            set(shared_first(1), 20),
        ))?;
        assert_eq!(i64::try_from(&graph.extract(shared_second(1))?)?, 30);
        // A separately authored compatible owner must also resupply cleanly.
        graph.register(set(shared_second(1), 25))?;
        assert_eq!(i64::try_from(&graph.extract(shared_first(1))?)?, 30);
        Ok(())
    }

    #[test]
    fn conflicting_bodies_and_unbound_inputs_reject_before_marker() -> Result<(), TypedError> {
        let mut graph = EGraph::new()?;
        graph.register(set(shared_first(1), 10))?;
        assert!(
            graph
                .register((set(Read(91), 91), set(shared_conflict(1), 30)))
                .is_err()
        );
        assert!(!graph.check(Read(91))?);
        assert_eq!(i64::try_from(&graph.extract(shared_first(1))?)?, 10);
        for value in [foreign_variable(1), captured_variable(1)] {
            assert!(matches!(
                graph.register((set(Read(92), 92), set(value, 1))),
                Err(TypedError::Invalid(_))
            ));
            assert!(!graph.check(Read(92))?);
        }
        Ok(())
    }
}

mod lazy_rulesets {
    use super::*;
    use egglog_experimental::typed::builtins::I64;
    use std::sync::{
        LazyLock,
        atomic::{AtomicUsize, Ordering},
    };

    static BODIES: AtomicUsize = AtomicUsize::new(0);
    static NAMES: AtomicUsize = AtomicUsize::new(0);
    static EXACT_BODIES: AtomicUsize = AtomicUsize::new(0);

    #[ruleset]
    fn copy(value: &I64) -> Rule {
        BODIES.fetch_add(1, Ordering::SeqCst);
        rule(RuleTerms::Input(value), RuleTerms::Copied(value))
    }

    #[ruleset(name = {
        assert_eq!(EXACT_BODIES.load(Ordering::SeqCst), 1, "body precedes the name");
        NAMES.fetch_add(1, Ordering::SeqCst);
        format!("exact::{}", "lazy-name")
    })]
    fn exact() -> _ {
        assert_eq!(
            NAMES.load(Ordering::SeqCst),
            0,
            "name has not run before the body"
        );
        EXACT_BODIES.fetch_add(1, Ordering::SeqCst);
        rule((), RuleTerms::Second(84))
    }

    #[ruleset(name = "")]
    fn empty_name() {}

    #[ruleset(name = "__typed_ruleset_0")]
    fn private_looking_name() {}

    #[ruleset(name = "nested::lazy")]
    fn nested() -> Ruleset {
        ruleset((&copy, &copy))
    }

    #[ruleset]
    #[cfg(any())]
    pub fn disabled() -> UndeclaredType {
        unresolved_body()
    }

    #[ruleset]
    fn borrowed_35(
        named_ruleset: &I64,
        a01: &I64,
        a02: &I64,
        a03: &I64,
        a04: &I64,
        a05: &I64,
        a06: &I64,
        a07: &I64,
        a08: &I64,
        a09: &I64,
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
        a31: &I64,
        a32: &I64,
        a33: &I64,
        a34: &I64,
    ) -> Rule {
        let _ = (
            named_ruleset,
            a01,
            a02,
            a03,
            a04,
            a05,
            a06,
            a07,
            a08,
            a09,
            a10,
            a11,
            a12,
            a13,
            a14,
            a15,
            a16,
            a17,
            a18,
            a19,
            a20,
            a21,
            a22,
            a23,
            a24,
            a25,
            a26,
            a27,
            a28,
            a29,
            a30,
            a31,
            a32,
            a33,
            a34,
        );
        rule((), RuleTerms::Copied(35))
    }

    macro_rules! borrowed_limit {
        ($name:ident, $count:literal; $($arg:ident),+ $(,)?) => {
            #[ruleset]
            fn $name($($arg: &I64),+) -> Rule {
                let _ = ($($arg),+);
                rule((), RuleTerms::Copied($count))
            }
        };
    }

    borrowed_limit!(borrowed_63, 63; named_ruleset, a01, a02, a03, a04, a05, a06, a07, a08, a09, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48, a49, a50, a51, a52, a53, a54, a55, a56, a57, a58, a59, a60, a61, a62);
    borrowed_limit!(borrowed_64, 64; named_ruleset, a01, a02, a03, a04, a05, a06, a07, a08, a09, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48, a49, a50, a51, a52, a53, a54, a55, a56, a57, a58, a59, a60, a61, a62, a63);

    static SHARED: LazyLock<Rule> = LazyLock::new(|| rule((), RuleTerms::Copied(126)));

    #[ruleset(name = "lazy::rejected")]
    fn rejected(value: &I64) -> (&'static Rule, Rule) {
        (&*SHARED, rule((), RuleTerms::Second(value)))
    }

    #[ruleset(name = "lazy::valid")]
    fn valid() -> &'static Rule {
        &SHARED
    }

    #[ruleset(name = "lazy::collision")]
    fn collision_first() -> Rule {
        rule((), RuleTerms::Copied(127))
    }

    #[ruleset(name = "lazy::collision")]
    fn collision_other() -> Rule {
        rule((), RuleTerms::Second(127))
    }

    #[test]
    fn lazy_ruleset_initializer_names_and_shared_cursors() -> Result<(), TypedError> {
        for mut graph in [EGraph::default(), EGraph::default()] {
            graph.register(RuleTerms::Input(83))?;
            let response = graph.run(&copy)?;
            assert!(
                response
                    .ruleset_publication
                    .unwrap()
                    .names
                    .contains(&concat!(module_path!(), "::copy").to_owned())
            );
            assert_eq!(
                response
                    .profile
                    .unwrap()
                    .runs
                    .iter()
                    .flat_map(|run| &run.rules)
                    .map(|rule| rule.matches.unwrap())
                    .sum::<u64>(),
                1
            );

            let response = graph.run(&nested)?;
            assert!(
                response
                    .ruleset_publication
                    .unwrap()
                    .names
                    .contains(&"nested::lazy".into())
            );
            assert_eq!(
                response
                    .profile
                    .unwrap()
                    .runs
                    .iter()
                    .flat_map(|run| &run.rules)
                    .map(|rule| rule.matches.unwrap())
                    .sum::<u64>(),
                0
            );

            let forced = std::cell::Cell::new(0);
            let lazy_alias = LazyLock::new(|| {
                forced.set(forced.get() + 1);
                (*copy).clone()
            });
            let alias = ruleset((&copy, &nested, &lazy_alias, &lazy_alias));
            assert_eq!(
                forced.get(),
                1,
                "a capturing initializer is also forced once"
            );
            let mut cloned = graph.try_clone()?;
            let copied = (*copy).clone();
            for group in [&*copy, &alias, &copied] {
                let response = cloned.run(group)?;
                assert_eq!(
                    response
                        .profile
                        .unwrap()
                        .runs
                        .iter()
                        .flat_map(|run| &run.rules)
                        .map(|rule| rule.matches.unwrap())
                        .sum::<u64>(),
                    0
                );
            }
            assert!(graph.check(RuleTerms::Copied(83))?);
        }
        assert_eq!(BODIES.load(Ordering::SeqCst), 1);
        Ok(())
    }

    #[test]
    fn lazy_ruleset_exact_name_expression_empty_name_and_borrowed_input_limits()
    -> Result<(), TypedError> {
        for mut graph in [EGraph::default(), EGraph::default()] {
            for (group, expected) in [
                (&*exact, "exact::lazy-name"),
                (&*empty_name, ""),
                (&*private_looking_name, "__typed_ruleset_0"),
                (&*borrowed_35, concat!(module_path!(), "::borrowed_35")),
                (&*borrowed_63, concat!(module_path!(), "::borrowed_63")),
                (&*borrowed_64, concat!(module_path!(), "::borrowed_64")),
            ] {
                assert!(
                    graph
                        .run(group)?
                        .ruleset_publication
                        .unwrap()
                        .names
                        .contains(&expected.to_owned())
                );
            }
            assert!(graph.check((
                RuleTerms::Second(84),
                RuleTerms::Copied(35),
                RuleTerms::Copied(63),
                RuleTerms::Copied(64),
            ))?);
        }
        assert_eq!(EXACT_BODIES.load(Ordering::SeqCst), 1);
        assert_eq!(NAMES.load(Ordering::SeqCst), 1);
        Ok(())
    }

    #[test]
    fn lazy_ruleset_failed_preparation_keeps_shared_rule_retryable() -> Result<(), TypedError> {
        let mut graph = EGraph::default();
        assert!(
            matches!(graph.run(&rejected), Err(TypedError::Engine(error))
            if error.code == egglog_experimental::proto::ErrorCode::InvalidProgram as i32)
        );
        assert!(!graph.check(RuleTerms::Copied(126))?);
        let response = graph.run(&valid)?;
        assert!(
            response
                .ruleset_publication
                .unwrap()
                .names
                .contains(&"lazy::valid".into())
        );
        assert!(graph.check(RuleTerms::Copied(126))?);
        Ok(())
    }

    #[test]
    fn lazy_ruleset_equal_names_do_not_coalesce_different_occurrences() -> Result<(), TypedError> {
        let mut graph = EGraph::default();
        graph.run(&collision_first)?;
        assert!(matches!(
            graph.run(&collision_other),
            Err(TypedError::Engine(_))
        ));
        assert!(!graph.check(RuleTerms::Second(127))?);
        let response = graph.run(&collision_first)?;
        assert_eq!(
            response
                .profile
                .unwrap()
                .runs
                .iter()
                .flat_map(|run| &run.rules)
                .map(|rule| rule.matches.unwrap())
                .sum::<u64>(),
            0
        );
        let mut independent = EGraph::default();
        independent.run(&collision_other)?;
        assert!(independent.check(RuleTerms::Second(127))?);
        Ok(())
    }
}

#[test]
fn typed_union_subsume_native_actions() -> Result<(), TypedError> {
    use egglog_experimental::typed::builtins::I64;
    for in_rule in [false, true] {
        for reversed in [false, true] {
            let input = RuleTerms::Input(17);
            let copied = RuleTerms::Copied(17);
            let saved_input = let_("input", &input);
            let saved_copied = let_("copied", &copied);
            let mut graph = EGraph::new()?;
            if reversed {
                graph.register((&saved_copied, &saved_input))?;
            } else {
                graph.register((&saved_input, &saved_copied))?;
            }
            assert!(graph.check(ne(&saved_input, &saved_copied))?);
            if in_rule {
                let group = ruleset(|value: &I64| {
                    let input = RuleTerms::Input(value);
                    let copied = RuleTerms::Copied(value);
                    let merge = if reversed {
                        union(&copied, &input)
                    } else {
                        union(&input, &copied)
                    };
                    rule((&input, &copied), (merge, subsume(&input)))
                });
                graph.run(&group)?;
            } else {
                let merge = if reversed {
                    union(&copied, &input)
                } else {
                    union(&input, &copied)
                };
                graph.register((merge, subsume(&input)))?;
            }
            assert!(graph.check(eq(&saved_input, &saved_copied))?);
            assert!(!graph.check(ne(&saved_input, &saved_copied))?);
            assert_eq!(graph.extract(&saved_input)?, copied);
            assert_ne!(input, copied, "authoring equality stays structural");
        }
    }
    Ok(())
}

#[test]
fn typed_union_subsume_invalid_targets_captures_and_occurrences() -> Result<(), TypedError> {
    use egglog_experimental::typed::builtins::I64;
    let input = RuleTerms::Input(71);
    let copied = RuleTerms::Copied(71);
    let saved = let_("saved", &input);
    let mut graph = EGraph::new()?;
    graph.register(subsume(&input))?;
    assert!(
        graph.check(&input)?,
        "native subsumption creates an absent row"
    );
    assert!(matches!(
        graph.register((set(Read(72), 1), union(&saved, &copied))),
        Err(TypedError::Invalid(_))
    ));
    assert!(!graph.check(Read(72))?);
    graph.register(&saved)?;
    graph.register(union(&saved, &copied))?;
    assert!(graph.check(eq(&saved, &copied))?);
    for action in [
        subsume(Read(1)),
        subsume(I64::from(1)),
        subsume(I64::from(1) + I64::from(2)),
        subsume(&saved),
    ] {
        assert!(matches!(
            graph.register((set(Read(72), 1), &action)),
            Err(TypedError::Invalid(_))
        ));
        assert!(!graph.check(Read(72))?);
        let nested = ruleset((rule((), set(Read(72), 2)), ruleset(rule((), action))));
        assert!(matches!(graph.run(&nested), Err(TypedError::Invalid(_))));
        assert!(!graph.check(Read(72))?);
    }
    // Established captures are still forbidden in rules, including union heads.
    assert!(matches!(
        graph.run(&ruleset(rule((), union(&saved, &copied)))),
        Err(TypedError::Invalid(_))
    ));
    let unbound = ruleset(|x: &I64| rule((), subsume(RuleTerms::Input(x))));
    assert!(graph.run(&unbound).is_err());
    let direct_input = RuleTerms::Input(171);
    let direct_copied = RuleTerms::Copied(171);
    graph.register((&direct_input, &direct_copied))?;
    assert!(graph.check(ne(&direct_input, &direct_copied))?);
    let shared = union(&direct_input, &direct_copied);
    graph.register((set(Read(72), 1), &shared, shared.clone()))?;
    assert!(graph.check(eq(Read(72), I64::from(1)))?);
    assert!(graph.check(eq(&direct_input, &direct_copied))?);
    graph.register(delete(Read(72)))?;
    assert!(!graph.check(Read(72))?);
    assert!(matches!(graph.run(&ruleset(rule((), (&shared, &shared)))),
        Err(TypedError::Engine(error)) if error.message.contains("repeated action Union occurrence")));
    assert!(!graph.check(Read(72))?);
    graph.register((
        union(input.clone(), copied.clone()),
        union(input.clone(), &copied),
        union(&input, copied.clone()),
        union(&input, &copied),
    ))?;
    graph.run(&ruleset((rule((), &shared), rule((), &shared))))?;
    // Existing constructor conversion, not a new untyped RHS conversion path.
    let atom = Atom::A();
    let wrapped = Math::Wrap(&atom);
    graph.register(union(&wrapped, &atom))?;
    Ok(())
}

#[test]
fn generated_ne_infers_borrowed_inputs_and_observes_native_merges() -> Result<(), TypedError> {
    use egglog_experimental::typed::builtins::{I64, Unit, Vec};
    let left = I64::from(17);
    let right = I64::from(23);
    let mut graph = EGraph::new()?;
    for fact in [
        ne(left.clone(), right.clone()),
        ne(left.clone(), &right),
        ne(&left, right.clone()),
        egglog_experimental::typed::ne(&left, &right),
        ne(&left, 0),
    ] {
        let _: &Unit = &fact;
        assert!(graph.check(&fact)?);
    }
    assert!(!graph.check(ne(&left, 17))?);
    assert!(graph.check((ne(&left, &right), eq(&left, 17)))?);
    assert_eq!(left, I64::from(17));
    assert_eq!(right, I64::from(23));

    let left = RuleTerms::Input(17);
    let right = RuleTerms::Copied(17);
    let left_vec = Vec::<RuleTerms>::of([&left]);
    let right_vec = Vec::<RuleTerms>::of([&right]);
    graph.register((&left, &right, &left_vec, &right_vec))?;
    assert!(graph.check(ne(&left, &right))?);
    assert!(graph.check(ne(&left_vec, &right_vec))?);
    graph.run(&ruleset(rewrite(&left, &right)))?;
    assert!(graph.check(eq(&left, &right))?);
    assert!(!graph.check(ne(&left, &right))?);
    assert!(!graph.check(ne(&left_vec, &right_vec))?);
    assert_ne!(left, right, "Rust syntax did not become equal");
    assert_ne!(left_vec, right_vec, "native class equality controls ne");
    assert!(graph.check(ne(I64::from(17), 23))?);
    Ok(())
}

#[test]
fn typed_capture_ordered_reads() -> Result<(), TypedError> {
    let before = let_("before", Read(1));
    let after = let_("after", Read(1));
    let mut graph = EGraph::new()?;
    graph.register(vec![
        set(Read(1), 10),
        (&before).into(),
        RuleTerms::Input(7).into(),
        delete(Read(1)),
        set(Read(1), 20),
        after.clone().into(),
    ])?;
    assert_eq!(i64::try_from(&graph.extract(&before)?)?, 10);
    assert_eq!(i64::try_from(&graph.extract(&after)?)?, 20);
    assert!(graph.check(RuleTerms::Input(7))?);
    Ok(())
}

#[test]
fn typed_capture_identity_queries_selectors_and_atomic_conflicts() -> Result<(), TypedError> {
    use egglog_experimental::typed::builtins::{F64, I64};
    let capture = let_("", Read(1));
    let equal = let_("", Read(1));
    assert_eq!(capture, equal);
    let digest = |value: &I64| {
        let mut h = DefaultHasher::new();
        value.hash(&mut h);
        h.finish()
    };
    assert_eq!(digest(&capture), digest(&equal));
    assert_ne!(capture, let_("λ🦀", Read(1)));
    assert_ne!(capture, let_("", Read(2)));
    assert!(ReadArgs::get_args(&capture)?.is_none());
    assert!(get_args(&capture, || let_("pattern", EmptyRead())).is_err());
    let mut graph = EGraph::new()?;
    graph.register(set(Read(1), 10))?;
    assert!(graph.check(&capture).is_err());
    assert_eq!(i64::try_from(&graph.extract(&capture)?)?, 10);
    graph.register((delete(Read(1)), set(Read(1), 20), &equal))?;
    assert_eq!(i64::try_from(&graph.extract(&equal)?)?, 10);
    assert!(graph.check(eq(&capture, 10))?);
    for conflict in [let_("", Read(2)), let_("", I64::from(10))] {
        assert!(graph.register((set(Read(9), 9), conflict)).is_err());
        assert!(!graph.check(Read(9))?);
    }
    assert!(
        graph
            .register((set(Read(9), 9), let_("", F64::from(1.0))))
            .is_err()
    );
    assert!(!graph.check(Read(9))?);
    assert!(
        graph
            .register((set(Read(9), 9), set(&capture, 30)))
            .is_err()
    );
    assert!(graph.register((set(Read(9), 9), delete(&capture))).is_err());
    assert!(!graph.check(Read(9))?);
    assert_eq!(i64::try_from(&graph.extract(let_("λ🦀", Read(1)))?)?, 20);
    Ok(())
}

#[test]
fn typed_capture_nesting_rules_and_explicit_host_boundary() -> Result<(), TypedError> {
    use egglog_experimental::typed::builtins::I64;
    let mut graph = EGraph::new()?;
    graph.register(set(Read(1), 3))?;
    let first = let_("first", Read(1));
    graph.register(RuleTerms::Input(&first))?;
    assert!(graph.check(RuleTerms::Input(3))?);
    let second = let_("second", I64::from(7));
    assert!(
        graph
            .register((set(Read(9), 9), set(Read(Read(1)), &second)))
            .is_err()
    );
    assert!(!graph.check(Read(9))?);
    graph.register(&second)?;
    graph.register(set(Read(Read(1)), &second))?;
    assert_eq!(i64::try_from(&graph.extract(Read(3))?)?, 7);
    let host_nested = let_("host", I64::from(5));
    assert!(graph.register(I64::from(1) + &host_nested).is_err());
    graph.register(&host_nested)?;
    graph.register(I64::from(1) + &host_nested)?;
    for group in [
        ruleset(rule(eq(&first, 3), RuleTerms::Copied(3))),
        ruleset(rule((), RuleTerms::Copied(&first))),
        ruleset(rule((), RuleTerms::Copied(3)).when(eq(&first, 3))),
        ruleset(rewrite(RuleTerms::Input(&first), RuleTerms::Copied(&first))),
    ] {
        assert!(graph.run(&group).is_err());
    }
    assert!(!graph.check(RuleTerms::Copied(3))?);
    assert!(graph.register(let_("open", var::<I64>("x"))).is_err());
    let left = let_("left-nested", Read(1));
    let right = let_("right-nested", Read(2));
    assert!(matches!(
        graph.register(RuleTerms::CapturePair(&left, &right)),
        Err(TypedError::Engine(_))
    ));
    graph.register((delete(Read(1)), set(Read(1), 30), set(Read(2), 20)))?;
    graph.register(RuleTerms::CapturePair(&left, &right))?;
    assert!(graph.check(RuleTerms::CapturePair(3, 20))?);
    let outer = let_("outer", RuleTerms::Input(let_("inner", Read(1))));
    graph.register(&outer)?;
    assert!(graph.check(eq(&outer, RuleTerms::Input(30)))?);
    Ok(())
}

#[test]
fn typed_capture_clone_and_nested_scope_read_times() -> Result<(), TypedError> {
    let mut graph = EGraph::new()?;
    graph.register(set(Read(1), 10))?;
    let capture = let_("saved", Read(1));
    let mut before = graph.try_clone()?;
    graph.register(&capture)?;
    let mut after = graph.try_clone()?;
    before.register((delete(Read(1)), set(Read(1), 20), &capture))?;
    graph.register((delete(Read(1)), set(Read(1), 30)))?;
    assert_eq!(i64::try_from(&before.extract(&capture)?)?, 20);
    assert_eq!(i64::try_from(&after.extract(&capture)?)?, 10);
    assert_eq!(i64::try_from(&graph.extract(&capture)?)?, 10);
    graph.push()?;
    let child = let_("child", Read(1));
    graph.register(&child)?;
    graph.push()?;
    let inner = let_("inner", Read(1));
    graph.register(&inner)?;
    graph.pop()?;
    assert!(graph.check(&inner).is_err());
    assert_eq!(i64::try_from(&graph.extract(&child)?)?, 30);
    graph.pop()?;
    assert!(graph.check(&child).is_err());
    assert_eq!(i64::try_from(&graph.extract(&capture)?)?, 10);
    graph.register((delete(Read(1)), set(Read(1), 40), &child))?;
    assert_eq!(i64::try_from(&graph.extract(child)?)?, 40);
    Ok(())
}

#[declarations]
impl RuleTerms {
    #[function(no_merge, args = PairReadArgs)]
    fn PairRead(
        first: egglog_experimental::typed::builtins::I64,
        second: egglog_experimental::typed::builtins::I64,
    ) -> egglog_experimental::typed::builtins::I64;
}

#[test]
fn typed_table_function_selectors_are_exact_owned_syntax() -> Result<(), TypedError> {
    use egglog_experimental::typed::builtins::I64;
    // No engine exists while fields are constructed, inspected and retained.
    let first = PairReadArgs::fresh();
    let second = PairReadArgs::fresh();
    assert_ne!(first.first, first.second);
    assert_ne!(first.first, second.first);
    assert_eq!(first.clone().first, first.first);
    let record = PairReadArgs {
        first: I64::from(7),
        second: I64::from(8),
    };
    let call: I64 = record.clone().into();
    assert_eq!(call, RuleTerms::PairRead(&record.first, &record.second));
    let updated: I64 = PairReadArgs {
        second: I64::from(9),
        ..record
    }
    .into();
    assert_eq!(updated, RuleTerms::PairRead(7, 9));
    let fields = PairReadArgs::get_args(&call)?.unwrap();
    drop(call);
    assert_eq!(fields.first, I64::from(7));
    assert_eq!(fields.second, I64::from(8));
    assert!(EmptyArgs::get_args(&EmptyRead())?.is_some());
    let empty: I64 = EmptyArgs::fresh().into();
    assert_eq!(empty, EmptyRead());
    assert!(ReadArgs::get_args(&empty)?.is_none());
    assert!(ReadArgs::get_args(&I64::from(7))?.is_none());
    assert!(get_args(&updated, |a: &I64, b: &I64| RuleTerms::PairRead(b, a)).is_err());
    assert!(get_args(&updated, |a: &I64, _: &I64| RuleTerms::PairRead(a, a)).is_err());
    assert!(get_args(&updated, |a: &I64| Read(Read(a))).is_err());
    assert!(get_args(&updated, |a: &I64, b: &I64| a + b).is_err());
    let read = Read(7);
    let mut graph = EGraph::new()?;
    assert!(!graph.check(&read)?);
    assert_eq!(ReadArgs::get_args(&read)?.unwrap().key, I64::from(7));
    assert!(
        !graph.check(&read)?,
        "syntax inspection must not insert a row"
    );
    graph.register(set(&read, 42))?;
    let extracted = graph.extract(&read)?;
    assert!(ReadArgs::get_args(&extracted)?.is_none());
    Ok(())
}

#[test]
fn typed_table_nullary_head_only_and_query_binders() -> Result<(), TypedError> {
    use egglog_experimental::typed::builtins::I64;
    let actions = [set(EmptyRead(), 11)];
    let conditional = ruleset(|x: &I64| {
        rule(RuleTerms::Input(x), (actions.as_slice(), set(Read(x), x))).when(eq(x, 7))
    });
    let mut graph = EGraph::new()?;
    graph.run(&conditional)?;
    assert!(
        !graph.check(EmptyRead())?,
        "installing a rule cannot run its head"
    );
    assert!(!graph.check(Read(7))?);
    graph.register(RuleTerms::Input(7))?;
    let response = graph.run(&conditional)?;
    assert!(response.detail.updated);
    assert_eq!(i64::try_from(&graph.extract(EmptyRead())?)?, 11);
    assert_eq!(i64::try_from(&graph.extract(Read(7))?)?, 7);
    graph.register(delete(EmptyRead()))?;
    assert!(!graph.check(EmptyRead())?);
    let nullary = ruleset(rule((), set(EmptyRead(), 12)));
    let mut fresh = EGraph::new()?;
    fresh.register(delete(EmptyRead()))?;
    assert!(!fresh.check(EmptyRead())?);
    fresh.run(&nullary)?;
    assert_eq!(i64::try_from(&fresh.extract(EmptyRead())?)?, 12);
    let unbound = ruleset(|x: &I64| rule((), set(Read(x), 0)));
    assert!(matches!(fresh.run(&unbound), Err(TypedError::Engine(_))));
    Ok(())
}

#[test]
fn typed_table_delete_is_row_addressing_and_invalid_targets_are_deferred() -> Result<(), TypedError>
{
    use egglog_experimental::typed::builtins::I64;
    let absent = RuleTerms::Input(71);
    let invalid = [
        set(&absent, &absent),
        set(I64::from(1), 2),
        delete(I64::from(1) + I64::from(2)),
    ];
    let mut graph = EGraph::new()?;
    graph.register((delete(&absent), delete(Read(71))))?;
    assert!(!graph.check(&absent)?);
    assert!(!graph.check(Read(71))?);
    graph.register(&absent)?;
    graph.register(delete(&absent))?;
    assert!(!graph.check(&absent)?);
    for action in &invalid {
        assert!(matches!(
            graph.register((set(Read(72), 1), action)),
            Err(TypedError::Invalid(_))
        ));
        assert!(
            !graph.check(Read(72))?,
            "authoring failure rejects the whole submission"
        );
        let bad = rule((), action).when(eq(I64::from(1), 1));
        let nested = ruleset((rule((), set(Read(72), 2)), ruleset(bad)));
        assert!(matches!(graph.run(&nested), Err(TypedError::Invalid(_))));
        assert!(!graph.check(Read(72))?);
    }
    Ok(())
}

#[test]
fn typed_table_prefix_clone_scope_and_nested_borrowed_inputs() -> Result<(), TypedError> {
    let mut graph = EGraph::new()?;
    assert!(matches!(
        graph.register((
            set(Read(1), 10),
            set(Read(2), 20),
            set(Read(1), 30),
            set(Read(3), 30)
        )),
        Err(TypedError::Engine(_))
    ));
    assert_eq!(i64::try_from(&graph.extract(Read(1))?)?, 10);
    assert_eq!(i64::try_from(&graph.extract(Read(2))?)?, 20);
    assert!(!graph.check(Read(3))?);
    let inner = Read(1);
    let nested = Read(&inner);
    let actions = vec![set(&nested, 100), delete(Read(2))];
    graph.register((actions.as_slice(), ()))?;
    assert_eq!(i64::try_from(&graph.extract(Read(10))?)?, 100);
    assert!(!graph.check(Read(2))?);
    let mut cloned = graph.try_clone()?;
    graph.push()?;
    graph.register((delete(Read(1)), set(Read(1), 40)))?;
    graph.push()?;
    graph.register((delete(Read(1)), set(Read(1), 50)))?;
    graph.pop()?;
    assert_eq!(i64::try_from(&graph.extract(Read(1))?)?, 40);
    graph.pop()?;
    assert_eq!(i64::try_from(&graph.extract(Read(1))?)?, 10);
    cloned.register((delete(Read(1)), set(Read(1), 60)))?;
    assert_eq!(i64::try_from(&cloned.extract(Read(1))?)?, 60);
    assert_eq!(i64::try_from(&graph.extract(Read(1))?)?, 10);
    graph.stats()?;
    Ok(())
}

#[test]
fn typed_table_ordered_writes_and_named_arguments() -> Result<(), TypedError> {
    use egglog_experimental::typed::builtins::I64;
    let read = Read(1);
    assert_eq!(ReadArgs::get_args(&read)?.unwrap().key, I64::from(1));
    let mut graph = EGraph::new()?;
    assert!(!graph.check(&read)?);
    graph.register(set(&read, 10))?;
    assert_eq!(i64::try_from(&graph.extract(&read)?)?, 10);
    graph.register((delete(&read), set(&read, 20)))?;
    assert_eq!(i64::try_from(&graph.extract(&read)?)?, 20);
    assert!(matches!(
        graph.register(set(&read, 30)),
        Err(TypedError::Engine(_))
    ));
    Ok(())
}

#[test]
fn typed_scope_restores_rules_and_incremental_cursors() -> Result<(), TypedError> {
    use egglog_experimental::typed::builtins::I64;
    let group = ruleset(|x: &I64| rule(RuleTerms::Input(x), RuleTerms::Copied(x)));
    let shared = ruleset((&group, &group));
    let mut graph = EGraph::new()?;
    graph.register(RuleTerms::Input(1))?;
    graph.push()?;
    graph.run(&shared)?;
    assert!(graph.check(RuleTerms::Copied(1))?);
    graph.pop()?;
    assert!(!graph.check(RuleTerms::Copied(1))?);
    graph.run(&group)?;
    assert!(graph.check(RuleTerms::Copied(1))?);

    graph.push()?;
    graph.register(RuleTerms::Input(2))?;
    graph.run(&shared)?;
    assert!(graph.check(RuleTerms::Copied(2))?);
    graph.push()?;
    graph.register(RuleTerms::Input(3))?;
    graph.run(&group)?;
    assert!(graph.check(RuleTerms::Copied(3))?);
    graph.pop()?;
    assert!(graph.check(RuleTerms::Copied(2))?);
    assert!(!graph.check(RuleTerms::Input(3))?);
    assert!(!graph.check(RuleTerms::Copied(3))?);
    graph.pop()?;
    assert!(!graph.check(RuleTerms::Input(2))?);
    assert!(!graph.check(RuleTerms::Copied(2))?);
    graph.register(RuleTerms::Input(2))?;
    graph.run(&shared)?;
    assert!(graph.check(RuleTerms::Copied(2))?);
    assert!(matches!(graph.pop(), Err(TypedError::Invalid(_))));
    assert!(graph.check((RuleTerms::Copied(1), RuleTerms::Copied(2)))?);
    Ok(())
}

#[test]
fn typed_scope_clone_is_an_independent_current_state_without_saved_scopes() -> Result<(), TypedError>
{
    use egglog_experimental::typed::builtins::I64;
    let group = ruleset(|x: &I64| rule(RuleTerms::Input(x), RuleTerms::Copied(x)));
    let mut source = EGraph::new()?;
    source.push()?;
    source.push()?;
    source.register(RuleTerms::Input(1))?;
    source.run(&group)?;
    let mut cloned = source.try_clone()?;
    assert!(matches!(cloned.pop(), Err(TypedError::Invalid(_))));
    let response = cloned.run(&group)?;
    assert_eq!(
        response
            .profile
            .unwrap()
            .runs
            .iter()
            .flat_map(|r| &r.rules)
            .map(|r| r.matches.unwrap())
            .sum::<u64>(),
        0,
        "cloning keeps already consumed cursors"
    );
    cloned.push()?;
    cloned.register(RuleTerms::Input(2))?;
    cloned.run(&group)?;
    assert!(!source.check(RuleTerms::Copied(2))?);
    source.pop()?;
    source.pop()?;
    assert!(!source.check(RuleTerms::Copied(1))?);
    drop(source);
    assert!(cloned.check((RuleTerms::Copied(1), RuleTerms::Copied(2)))?);
    cloned.pop()?;
    assert!(cloned.check(RuleTerms::Copied(1))?);
    assert!(!cloned.check(RuleTerms::Copied(2))?);
    cloned.register(RuleTerms::Input(3))?;
    cloned.run(&group)?;
    assert!(cloned.check(RuleTerms::Copied(3))?);
    Ok(())
}

#[test]
fn typed_report_run_and_stats_keep_cumulative_native_work() -> Result<(), TypedError> {
    use egglog_experimental::{proto as pb, typed::builtins::I64};
    let group = ruleset(|x: &I64| rule(RuleTerms::Input(x), RuleTerms::Copied(x)));
    let mut graph = EGraph::new()?;
    let mut previous_history = 0;
    let mut matches = 0;
    for input in [1, 2] {
        graph.register(RuleTerms::Input(input))?;
        let run = graph.run(&group)?;
        let detail = &run.detail;
        matches += detail
            .num_matches_per_rule
            .iter()
            .map(|row| row.value)
            .sum::<u64>();
        let stats = graph.stats()?;
        let report = &stats.detail;
        assert!(report.iterations.len() > previous_history);
        previous_history = report.iterations.len();
        assert_eq!(
            report
                .num_matches_per_rule
                .iter()
                .map(|row| row.value)
                .sum::<u64>(),
            matches
        );
        assert!(matches > 0);
        assert!(report.num_matches_per_rule.iter().all(|row| {
            row.rule
                .is_some_and(|index| (index as usize) < stats.rules.len())
                && row.direction == Some(pb::NativeRuleDirection::Single as i32)
        }));
        // The high-level observation returns native detail directly. The wire
        // envelope/control-companion distinction remains covered internally.
        assert!(stats.profile.as_ref().unwrap().complete);
        assert!(graph.check(RuleTerms::Copied(input))?);
    }
    Ok(())
}

#[test]
fn term_rule_heads_and_registration_share_ordered_collection_inputs() -> Result<(), TypedError> {
    use egglog_experimental::typed::builtins::I64;
    let inputs = [RuleTerms::Input(7), RuleTerms::Input(8)];
    let mut graph = EGraph::default();
    graph.register((
        inputs.as_slice(),
        (RuleTerms::Input(9),),
        Vec::<RuleTerms>::new(),
        (),
    ))?;
    let copy = ruleset(|x: &I64| {
        rule(
            RuleTerms::Input(x),
            (
                [RuleTerms::Copied(x)],
                (RuleTerms::Second(x),),
                Vec::<RuleTerms>::new(),
                (),
            ),
        )
        .when(eq(x, 7))
    });
    graph.run(&copy)?;
    assert!(graph.check((RuleTerms::Copied(7), RuleTerms::Second(7)))?);
    assert!(!graph.check(RuleTerms::Copied(8))?);
    assert!(!graph.check(RuleTerms::Second(9))?);

    let guarded =
        ruleset(|x: &I64| rewrite(RuleTerms::Input(x), RuleTerms::Copied(x)).when(eq(x, 7)));
    graph.run(&guarded)?;
    assert!(graph.check(eq(RuleTerms::Input(7), RuleTerms::Copied(7)))?);
    assert!(!graph.check(eq(RuleTerms::Input(8), RuleTerms::Copied(8)))?);
    Ok(())
}

#[test]
fn independent_equal_term_rules_have_independent_matches_and_clones_reuse() -> Result<(), TypedError>
{
    let shared = rule((), RuleTerms::Copied(42));
    let independent = rule((), RuleTerms::Copied(42));
    let group = ruleset((shared.clone(), &shared, independent));
    let mut graph = EGraph::default();
    let first = graph.run(&group)?;
    let matches: u64 = first
        .profile
        .unwrap()
        .runs
        .iter()
        .flat_map(|run| &run.rules)
        .map(|rule| rule.matches.expect("normal rule matches measured"))
        .sum();
    assert_eq!(
        matches, 2,
        "shared alias once, independent equal occurrence once"
    );
    let second = graph.run(&group.clone())?;
    let matches: u64 = second
        .profile
        .unwrap()
        .runs
        .iter()
        .flat_map(|run| &run.rules)
        .map(|rule| rule.matches.expect("normal rule matches measured"))
        .sum();
    assert_eq!(
        matches, 0,
        "cloning the group cannot reset consumed cursors"
    );
    Ok(())
}

#[test]
fn overlapping_groups_and_diamonds_preserve_shared_and_independent_cursors()
-> Result<(), TypedError> {
    let shared = rule((), RuleTerms::Copied(57));
    let independent = rule((), RuleTerms::Copied(57));
    let leaf = ruleset(&shared);
    let left = ruleset((&leaf, &shared));
    let right = ruleset((&leaf, independent));
    let diamond = ruleset((&left, &right, &leaf));
    let flat_overlap = ruleset(&shared);
    let mut graph = EGraph::default();
    for (group, expected) in [(&left, 1), (&diamond, 1), (&right, 0), (&flat_overlap, 0)] {
        let response = graph.run(group)?;
        let matches: u64 = response
            .profile
            .unwrap()
            .runs
            .iter()
            .flat_map(|run| &run.rules)
            .map(|rule| rule.matches.expect("normal rule matches measured"))
            .sum();
        assert_eq!(
            matches, expected,
            "one cursor per shared occurrence, separate cursor for equal independent rule"
        );
    }
    assert!(graph.check(RuleTerms::Copied(57))?);
    Ok(())
}

#[test]
fn native_clone_retains_cursors_but_not_subsequent_mutations() -> Result<(), TypedError> {
    use egglog_experimental::typed::builtins::I64;
    let group = ruleset(|x: &I64| rule(RuleTerms::Input(x), RuleTerms::Copied(x)));
    let mut original = EGraph::default();
    original.register(RuleTerms::Input(1))?;
    original.run(&group)?;
    let mut cloned = original.try_clone()?;
    let response = cloned.run(&group)?;
    let matches: u64 = response
        .profile
        .unwrap()
        .runs
        .iter()
        .flat_map(|run| &run.rules)
        .map(|rule| rule.matches.unwrap())
        .sum();
    assert_eq!(matches, 0, "native clone preserves consumed cursors");
    original.register(RuleTerms::Input(2))?;
    original.run(&group)?;
    assert!(!cloned.check(RuleTerms::Copied(2))?);
    cloned.register(RuleTerms::Input(3))?;
    cloned.run(&group)?;
    assert!(!original.check(RuleTerms::Copied(3))?);
    drop(original);
    assert!(cloned.check((RuleTerms::Copied(1), RuleTerms::Copied(3)))?);
    Ok(())
}

#[test]
fn rejected_rule_preparation_does_not_poison_a_later_valid_group() -> Result<(), TypedError> {
    use egglog_experimental::typed::builtins::I64;
    let shared = rule((), RuleTerms::Copied(123));
    let invalid = rule((), RuleTerms::Second(var::<I64>("rhs_only")));
    let rejected = ruleset((shared.clone(), invalid));
    let valid = ruleset(shared);
    let mut graph = EGraph::default();
    let error = graph.run(&rejected).unwrap_err();
    assert!(matches!(error, TypedError::Engine(error)
        if error.code == egglog_experimental::proto::ErrorCode::InvalidProgram as i32));
    assert!(!graph.check(RuleTerms::Copied(123))?);
    graph.run(&valid)?;
    assert!(graph.check(RuleTerms::Copied(123))?);
    Ok(())
}

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

#[sort]
pub struct Scalars;
#[declarations]
impl Scalars {
    #[constructor(args = ScalarArgs)]
    pub fn Values(
        text: egglog_experimental::typed::builtins::String,
        flag: egglog_experimental::typed::builtins::Bool,
        unit: egglog_experimental::typed::builtins::Unit,
    ) -> Self;
}

#[test]
fn scalar_constructor_fields_and_selectors_execute_through_bytes() -> Result<(), TypedError> {
    use egglog_experimental::typed::builtins::{Bool, String as EString, Unit};
    let term = Scalars::Values("a\0b\n☃", false, ());
    let fields = ScalarArgs::get_args(&term)?.unwrap();
    assert_eq!(fields.text, EString::from("a\0b\n☃"));
    assert_eq!(fields.flag, Bool::from(false));
    assert_eq!(fields.unit, Unit::from(()));
    let mut graph = EGraph::default();
    graph.register(&term)?;
    assert_eq!(graph.extract(&term)?, term);
    assert!(graph.check(Scalars::Values(&ScalarArgs::fresh().text, false, (),))?);
    Ok(())
}

mod wide_callable_authoring {
    use super::*;
    use egglog_experimental::typed::builtins::{I64, String as EString};

    #[sort]
    struct Ir;
    #[sort]
    struct DimExpr;
    #[sort]
    struct DType;

    #[declarations]
    impl DimExpr {
        fn MNum(value: I64) -> Self;
    }
    #[declarations]
    impl DType {
        fn F32() -> Self;
    }
    #[declarations]
    impl Ir {
        fn Input(node: I64, label: EString, dtype: DType) -> Self;
        // The existing Luminal LoopStart declaration, including field order.
        #[constructor(name = "LoopStart", args = LoopStartArgs)]
        fn LoopStart(inp: Ir, loop_id: I64, slot_idx: I64, iters: DimExpr, dtype: DType) -> Self;
    }

    #[test]
    fn loop_start_five_fields_execute_and_select_in_order() -> Result<(), TypedError> {
        let dtype = DType::F32();
        let inp = Ir::Input(2, "input", &dtype);
        let iters = DimExpr::MNum(3);
        let term = Ir::LoopStart(&inp, 17, 23, &iters, &dtype);
        let mut graph = EGraph::new()?;
        graph.register(&term)?;
        let extracted = graph.extract(&term)?;
        assert_eq!(extracted, term);
        let first = LoopStartArgs::fresh();
        let second = LoopStartArgs::fresh();
        assert_ne!(first.loop_id, first.slot_idx);
        assert_ne!(first.loop_id, second.loop_id);
        assert_ne!(first.dtype, second.dtype);
        assert_eq!(first.clone().dtype, first.dtype);
        let pattern = LoopStartArgs {
            dtype: dtype.clone(),
            ..first
        };
        assert!(graph.check(Ir::from(pattern))?);
        drop(graph);

        let fields = LoopStartArgs::get_args(&extracted)?.unwrap();
        assert_eq!(fields.inp, inp);
        assert_eq!(i64::try_from(&fields.loop_id)?, 17);
        assert_eq!(i64::try_from(&fields.slot_idx)?, 23);
        assert_eq!(fields.iters, iters);
        assert_eq!(fields.dtype, dtype);
        let (_, loop_id, slot_idx, _, _) = get_args(
            &extracted,
            |inp: &Ir, loop_id: &I64, slot_idx: &I64, iters: &DimExpr, dtype: &DType| {
                Ir::LoopStart(inp, loop_id, slot_idx, iters, dtype)
            },
        )?
        .unwrap();
        assert_eq!(i64::try_from(&loop_id)?, 17);
        assert_eq!(i64::try_from(&slot_idx)?, 23);
        for duplicate in [false, true] {
            assert!(
                get_args(
                    &extracted,
                    |inp: &Ir, loop_id: &I64, slot_idx: &I64, iters: &DimExpr, dtype: &DType| {
                        Ir::LoopStart(
                            inp,
                            if duplicate { loop_id } else { slot_idx },
                            loop_id,
                            iters,
                            dtype,
                        )
                    },
                )
                .is_err()
            );
        }
        Ok(())
    }

    // Exercise broad signatures without building giant native graphs. Each
    // field receives a distinct value so every selector position is checked.
    macro_rules! wide_constructor {
        ($test:ident, $constructor:ident, $record:ident; $($arg:ident:$index:literal),+) => {
            #[constructor(args = $record)]
            #[allow(clippy::too_many_arguments)]
            fn $constructor($($arg: I64),+) -> Ir;

            #[test]
            fn $test() -> Result<(), TypedError> {
                let value = $constructor($($index),+);
                let fields = $record::get_args(&value)?.unwrap();
                $(assert_eq!(i64::try_from(&fields.$arg)?, $index);)+
                let first = $record::fresh();
                let second = $record::fresh();
                $(assert_ne!(first.$arg, second.$arg);)+
                let rebuilt: Ir = fields.into();
                assert_eq!(rebuilt, value);
                Ok(())
            }
        };
    }

    wide_constructor!(twenty_seven_fields_select, Wide27, Wide27Args;
        a0:0,a1:1,a2:2,a3:3,a4:4,a5:5,a6:6,a7:7,a8:8,a9:9,
        a10:10,a11:11,a12:12,a13:13,a14:14,a15:15,a16:16,a17:17,a18:18,a19:19,
        a20:20,a21:21,a22:22,a23:23,a24:24,a25:25,a26:26);
    wide_constructor!(sixty_four_fields_select, Wide64, Wide64Args;
        a0:0,a1:1,a2:2,a3:3,a4:4,a5:5,a6:6,a7:7,a8:8,a9:9,
        a10:10,a11:11,a12:12,a13:13,a14:14,a15:15,a16:16,a17:17,a18:18,a19:19,
        a20:20,a21:21,a22:22,a23:23,a24:24,a25:25,a26:26,a27:27,a28:28,a29:29,
        a30:30,a31:31,a32:32,a33:33,a34:34,a35:35,a36:36,a37:37,a38:38,a39:39,
        a40:40,a41:41,a42:42,a43:43,a44:44,a45:45,a46:46,a47:47,a48:48,a49:49,
        a50:50,a51:51,a52:52,a53:53,a54:54,a55:55,a56:56,a57:57,a58:58,a59:59,
        a60:60,a61:61,a62:62,a63:63);

    #[test]
    fn plain_declaration_is_not_limited_by_selector_arity() {
        macro_rules! beyond_selectors {
            ($($arg:ident),+) => {
                #[constructor]
                #[allow(clippy::too_many_arguments)]
                fn Wide($($arg: I64),+) -> Ir;
                let _: Ir = Wide($(stringify!($arg).len() as i64),+);
            };
        }
        beyond_selectors!(
            a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
            a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35,
            a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48, a49, a50, a51, a52,
            a53, a54, a55, a56, a57, a58, a59, a60, a61, a62, a63, a64
        );
    }
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
    // Reusing the same occurrence must preserve its installed native cursor.
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

mod function_values {
    use egglog_experimental::typed::{
        builtins::{Function, I64, MultiSet},
        prelude::*,
    };

    #[function(merge = |_old: I64, new: I64| new)]
    fn index(values: MultiSet<I64>, value: I64) -> I64;

    #[function(merge = |_old: I64, new: I64| new)]
    fn prefixed_index(key: I64, values: MultiSet<I64>, value: I64) -> I64;

    #[test]
    fn captured_prefixes_address_only_the_selected_index_rows() -> Result<(), TypedError> {
        let values = MultiSet::<I64>::new([1, 1, 2]);
        let selected = Function::<(MultiSet<I64>, I64), I64>::with_captures(
            (I64::from(41),),
            |(key,), xs, x| prefixed_index(key, xs, x),
        )?;
        let mut graph = EGraph::new()?;
        graph.register(set(prefixed_index(42, &values, 1), 99))?;
        graph.register(values.fill_index(&selected))?;
        assert_eq!(
            i64::try_from(&graph.extract(selected.call(&values, 1))?)?,
            2
        );
        assert_eq!(
            i64::try_from(&graph.extract(selected.call(&values, 2))?)?,
            1
        );
        assert!(graph.check(eq(prefixed_index(42, &values, 1), 99))?);
        graph.register(values.clear_index(selected))?;
        assert!(!graph.check(eq(prefixed_index(41, &values, 1), 2))?);
        assert!(!graph.check(eq(prefixed_index(41, &values, 2), 1))?);
        assert!(graph.check(eq(prefixed_index(42, values, 1), 99))?);
        Ok(())
    }

    #[test]
    fn extracted_function_values_keep_typed_captures_and_declarations() -> Result<(), TypedError> {
        use egglog_experimental::typed::builtins::{Unit, Vec as EggVec};
        let callback =
            Function::<(I64,), I64>::with_captures((I64::from(10),), |(captured,), x| {
                x + captured
            })?;
        let predicate =
            Function::<(I64,), Unit>::with_captures((I64::from(5),), |(captured,), x| {
                ne(&captured, x)
            })?;
        let mut first = EGraph::new()?;
        let callback = first.extract(callback)?;
        let predicate = first.extract(predicate)?;
        let applied =
            Function::<(I64,), I64>::with_captures((callback.clone(),), |(callback,), x| {
                callback.call(x)
            })?;
        let applied = first.extract(applied)?;
        let callbacks = first.extract(EggVec::<Function<(I64,), I64>>::of([&callback]))?;
        let callbacks = std::vec::Vec::<Function<(I64,), I64>>::try_from(&callbacks)?;
        drop(first);
        let mut second = EGraph::new()?;
        assert_eq!(i64::try_from(&second.extract(callback.call(4))?)?, 14);
        assert_eq!(i64::try_from(&second.extract(applied.call(3))?)?, 13);
        assert_eq!(i64::try_from(&second.extract(callbacks[0].call(7))?)?, 17);
        assert!(second.check(predicate.call(6))?);
        assert!(!second.check(predicate.call(5))?);
        Ok(())
    }

    #[test]
    fn ordinary_typed_functions_preserve_writable_targets() -> Result<(), TypedError> {
        let values = MultiSet::<I64>::new([1, 1, 2]);
        let direct = Function::<(MultiSet<I64>, I64), I64>::new(|xs, x| index(xs, x))?;
        let computed =
            Function::<(MultiSet<I64>, I64), I64>::new(|xs, x| index(xs, x) + I64::from(0))?;
        let mut graph = EGraph::new()?;
        graph.register(values.fill_index(&direct))?;
        assert_eq!(i64::try_from(&graph.extract(direct.call(&values, 1))?)?, 2);
        graph.register(set(index(&values, 1), 7))?;
        assert_eq!(i64::try_from(&graph.extract(direct.call(&values, 1))?)?, 7);
        graph.register(values.clear_index(direct))?;
        assert!(!graph.check(eq(index(&values, 1), 7))?);
        assert!(graph.register(values.fill_index(computed)).is_err());
        for value in [1, 2] {
            assert!(!graph.check(eq(index(&values, value), value))?);
        }
        Ok(())
    }
}
