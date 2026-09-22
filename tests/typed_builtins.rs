#![cfg(feature = "typed")]

use egglog_experimental::typed::{builtins as eg, prelude::*};

#[function(name = "bigint", no_merge)]
fn declared_bigint(value: eg::I64) -> eg::BigInt;
#[function(name = "from-string", no_merge)]
fn declared_from_string(value: eg::String) -> eg::BigInt;
#[function(name = "bigrat", no_merge)]
fn declared_bigrat(numerator: eg::BigInt, denominator: eg::BigInt) -> eg::BigRat;

#[test]
fn declared_calls_do_not_decode_as_same_named_primitive_literals() {
    assert!(num::BigInt::try_from(declared_bigint(7)).is_err());
    assert!(num::BigInt::try_from(declared_from_string("7")).is_err());
    assert!(num::BigRational::try_from(declared_bigrat(1, 2)).is_err());
}

#[test]
fn implicit_query_inputs_preserve_exact_scalar_conversions() {
    macro_rules! same_input {
        ($sort:ty, $input:expr) => {{
            let variable = var::<$sort>("value");
            let Fact::Eq(_, actual) = eq(&variable, $input) else {
                unreachable!()
            };
            let expected = <$sort>::from($input);
            assert_eq!(&actual, expected.expression());
            let Fact::Expr(actual) = ne(&variable, $input) else {
                unreachable!()
            };
            let Fact::Expr(expected) = ne(&variable, expected) else {
                unreachable!()
            };
            assert_eq!(actual, expected);
        }};
    }

    same_input!(eg::String, "RELU");
    let text = String::from("quote\" slash\\ newline\n nul\0 λ😀");
    same_input!(eg::String, text.clone());
    same_input!(eg::String, &text);
    for integer in [i64::MIN, -1, 0, i64::MAX] {
        same_input!(eg::I64, integer);
        same_input!(eg::BigInt, integer);
        same_input!(eg::BigRat, integer);
    }
    for integer in [i32::MIN, i32::MAX] {
        same_input!(eg::I64, integer);
        same_input!(eg::BigInt, integer);
        same_input!(eg::BigRat, integer);
    }
    for bits in [
        0,
        1 << 63,
        1,
        f64::MAX.to_bits(),
        f64::INFINITY.to_bits(),
        0x7ff8_0000_0000_0042,
    ] {
        let value = f64::from_bits(bits);
        same_input!(eg::F64, value);
        let Fact::Eq(_, actual) = eq(var::<eg::F64>("float"), value) else {
            unreachable!()
        };
        assert_eq!(
            f64::try_from(eg::F64::from_expression(actual))
                .unwrap()
                .to_bits(),
            bits,
        );
    }
    same_input!(eg::Bool, true);
    same_input!(eg::Bool, false);
    same_input!(eg::Unit, ());
    let huge: num::BigInt = -(num::BigInt::from(1) << 200usize);
    same_input!(eg::BigInt, huge.clone());
    same_input!(eg::BigInt, &huge);
    same_input!(eg::BigRat, huge.clone());
    same_input!(eg::BigRat, &huge);
    let ratio = num::BigRational::new(huge, 17.into());
    same_input!(eg::BigRat, ratio.clone());
    let integer = var::<eg::I64>("integer");
    same_input!(eg::BigInt, &integer);
    same_input!(eg::BigRat, &integer);
}

#[test]
fn implicit_query_promotions_keep_frozen_provenance() -> Result<(), TypedError> {
    let integer = let_("integer", eg::I64::from(7));
    let mut graph = EGraph::default();
    graph.register(&integer)?;
    let frozen = graph.freeze()?;
    let observed = frozen.lookup(&integer)?;
    let Fact::Eq(_, promoted) = eq(var::<eg::BigRat>("rational"), &observed) else {
        unreachable!()
    };
    assert_eq!(&promoted, eg::BigRat::from(&observed).expression());
    let before = graph.num_tuples()?;
    assert!(matches!(
        graph.register(eg::BigRat::from_expression(promoted)),
        Err(TypedError::Invalid(_))
    ));
    assert_eq!(graph.num_tuples()?, before);
    Ok(())
}

#[test]
fn integer_promotions_author_exact_native_calls() -> Result<(), TypedError> {
    let symbolic = var::<eg::I64>("integer");
    assert_eq!(
        eg::BigInt::from(&symbolic),
        eg::BigInt::from(symbolic.clone())
    );
    assert_eq!(
        eg::BigRat::from(&symbolic),
        eg::BigRat::new(eg::BigInt::from(&symbolic), 1)
    );
    assert_eq!(
        eg::BigRat::from(symbolic.clone()),
        eg::BigRat::from(&symbolic)
    );
    assert!(num::BigInt::try_from(eg::BigInt::from(&symbolic)).is_err());
    assert!(num::BigRational::try_from(eg::BigRat::from(&symbolic)).is_err());
    for value in [i64::MIN, -1, 0, i64::MAX] {
        let integer = eg::I64::from(value);
        let big = eg::BigInt::from(value);
        let rational = eg::BigRat::new(&big, 1);
        assert_eq!(eg::BigInt::from(&integer), big);
        assert_eq!(eg::BigInt::from(integer.clone()), big);
        assert_eq!(eg::BigRat::from(value), rational);
        assert_eq!(eg::BigRat::from(&integer), rational);
        assert_eq!(eg::BigRat::from(integer), rational);
        assert_eq!(eg::BigRat::from(&big), rational);
        assert_eq!(eg::BigRat::from(big), rational);
        assert_eq!(
            num::BigRational::try_from(rational).unwrap(),
            num::BigRational::from_integer(value.into())
        );
    }
    assert_eq!(eg::BigRat::from(7_i32), eg::BigRat::new(7, 1));
    let huge: num::BigInt = -(num::BigInt::from(1) << 200usize);
    assert_eq!(eg::BigInt::from(&huge), eg::BigInt::from(huge.clone()));
    assert_eq!(
        eg::BigRat::from(&huge),
        eg::BigRat::new(eg::BigInt::from(&huge), 1)
    );
    assert_eq!(eg::BigRat::from(huge.clone()), eg::BigRat::from(&huge));
    let integer = let_("integer", eg::I64::from(3) + 4);
    let bigint = let_("bigint", eg::BigInt::from(&integer));
    let ratio = let_("ratio", eg::BigRat::from(&bigint) + &integer);
    let huge = let_("huge", eg::BigRat::from(huge.clone()));
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register((&integer, &bigint, &ratio, &huge))?;
    let frozen = graph.freeze()?;
    assert_eq!(
        num::BigInt::try_from(frozen.lookup(&bigint)?).unwrap(),
        7.into()
    );
    assert_eq!(
        num::BigRational::try_from(frozen.lookup(&ratio)?).unwrap(),
        num::BigRational::from_integer(14.into())
    );
    assert_eq!(
        num::BigRational::try_from(frozen.lookup(&huge)?).unwrap(),
        num::BigRational::from_integer(-(num::BigInt::from(1) << 200usize))
    );
    Ok(())
}

#[test]
fn integer_promotions_preserve_frozen_provenance() -> Result<(), TypedError> {
    let integer = let_("integer", eg::I64::from(7));
    let bigint = let_("bigint", eg::BigInt::from(11));
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register((&integer, &bigint))?;
    let frozen = graph.freeze()?;
    let integer = frozen.lookup(&integer)?;
    let bigint = frozen.lookup(&bigint)?;
    let before = graph.num_tuples()?;
    for action in [
        Action::from(eg::BigInt::from(&integer)),
        Action::from(eg::BigInt::from(integer.clone())),
        Action::from(eg::BigRat::from(&integer)),
        Action::from(eg::BigRat::from(integer)),
        Action::from(eg::BigRat::from(&bigint)),
        Action::from(eg::BigRat::from(bigint)),
    ] {
        assert!(matches!(
            graph.register(action),
            Err(TypedError::Invalid(_))
        ));
        assert_eq!(graph.num_tuples()?, before);
    }
    graph.register(eg::BigRat::from(13))?;
    Ok(())
}

#[test]
fn vector_decoding_uses_the_shared_portable_sequence_contract() {
    let portable = eg::Vec::<eg::I64>::of([1, 2, 1]);
    let expected = vec![eg::I64::from(1), eg::I64::from(2), eg::I64::from(1)];
    assert_eq!(portable.items().unwrap(), expected);
    assert_eq!(Vec::<eg::I64>::try_from(&portable).unwrap(), expected);
    assert_eq!(Vec::<eg::I64>::try_from(portable).unwrap(), expected);
    let symbolic = var::<eg::Vec<eg::I64>>("values");
    for error in [
        Vec::<eg::I64>::try_from(&symbolic).unwrap_err(),
        Vec::<eg::I64>::try_from(symbolic).unwrap_err(),
    ] {
        assert_eq!(error.to_string(), "expected portable vec-of form");
    }
}

#[test]
fn frozen_scalars_decode_exact_payloads_after_the_snapshot_is_dropped() -> Result<(), TypedError> {
    let big = (num::BigInt::from(1) << 200usize) + num::BigInt::from(123);
    let ratio = num::BigRational::new(big.clone(), num::BigInt::from(17));
    let rational = num::rational::Rational64::new(-5, 9);
    let text = "quote\" slash\\ newline\n nul\0 λ😀";
    let integer = let_("integer", eg::I64::from(i64::MIN));
    let boolean = let_("boolean", eg::Bool::from(false));
    let unit = let_("unit", eg::Unit::from(()));
    let float = let_("float", eg::F64::from(f64::from_bits(1 << 63)));
    let string = let_("string", eg::String::from(text));
    let bigint = let_("bigint", eg::BigInt::from(big.clone()));
    let bigrat = let_("bigrat", eg::BigRat::from(ratio.clone()));
    let smallrat = let_("smallrat", eg::Rational::from(rational));
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register((
        &integer, &boolean, &unit, &float, &string, &bigint, &bigrat, &smallrat,
    ))?;
    let frozen = graph.freeze()?;
    let integer = frozen.lookup(&integer)?;
    let boolean = frozen.lookup(&boolean)?;
    let unit = frozen.lookup(&unit)?;
    let float = frozen.lookup(&float)?;
    let string = frozen.lookup(&string)?;
    let bigint = frozen.lookup(&bigint)?;
    let bigrat = frozen.lookup(&bigrat)?;
    let smallrat = frozen.lookup(&smallrat)?;
    assert!(i64::try_from(eg::I64::from_expression(boolean.expression().clone())).is_err());
    let before = graph.num_tuples()?;
    assert!(graph.register(&integer + 1).is_err());
    assert_eq!(graph.num_tuples()?, before);
    drop(graph);
    drop(frozen);
    assert_eq!(i64::try_from(&integer).unwrap(), i64::MIN);
    assert_eq!(i64::try_from(integer).unwrap(), i64::MIN);
    assert!(!bool::try_from(boolean).unwrap());
    <()>::try_from(unit).unwrap();
    assert_eq!(f64::try_from(float).unwrap().to_bits(), 1 << 63);
    assert_eq!(String::try_from(string).unwrap(), text);
    assert_eq!(num::BigInt::try_from(bigint).unwrap(), big);
    assert_eq!(num::BigRational::try_from(bigrat).unwrap(), ratio);
    assert_eq!(
        num::rational::Rational64::try_from(smallrat).unwrap(),
        rational
    );
    Ok(())
}

#[sort]
struct FrozenBuiltinTerm;
#[declarations]
impl FrozenBuiltinTerm {
    fn Leaf(value: eg::I64) -> Self;
    fn Children(values: eg::Vec<FrozenBuiltinTerm>) -> Self;
}

#[test]
fn frozen_container_inspection_is_shallow_and_retains_cycles_and_provenance()
-> Result<(), TypedError> {
    let leaf = let_("leaf", FrozenBuiltinTerm::Leaf(7));
    let vector = let_("vector", eg::Vec::of([&leaf, &leaf]));
    let set = let_("set", eg::Set::<eg::I64>::of([3, 1, 3]));
    let bag = let_("bag", eg::MultiSet::<eg::I64>::of([3, 1, 3]));
    let map = let_(
        "map",
        eg::Map::<eg::String, eg::I64>::of([("b", 2), ("a", 1)]),
    );
    let pair = let_(
        "pair",
        eg::Pair::<eg::I64, FrozenBuiltinTerm>::new(9, &leaf),
    );
    let empty = let_("empty", eg::Vec::<eg::String>::empty());
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register((&leaf, &vector, &set, &bag, &map, &pair, &empty))?;
    graph.register(union(&leaf, FrozenBuiltinTerm::Children(&vector)))?;
    let frozen = graph.freeze()?;
    let observed_leaf = frozen.lookup(&leaf)?;
    let observed_vector = frozen.lookup(&vector)?;
    let items = observed_vector.items().unwrap();
    assert_eq!(items, [observed_leaf.clone(), observed_leaf.clone()]);
    assert_eq!(frozen.nodes(&items[0])?.len(), 2);
    let children = frozen
        .nodes(&items[0])?
        .find_map(|node| {
            get_args(&node, |values: &eg::Vec<FrozenBuiltinTerm>| {
                FrozenBuiltinTerm::Children(values)
            })
            .unwrap()
        })
        .unwrap()
        .0;
    assert_eq!(children, observed_vector);
    assert_eq!(children.items().unwrap(), items);
    let observed_empty = frozen.lookup(&empty)?;
    assert!(observed_empty.items().unwrap().is_empty());
    assert!(
        eg::Vec::<eg::I64>::from_expression(observed_empty.expression().clone())
            .items()
            .is_err()
    );
    assert!(frozen.as_view(&items[0]).is_ok());
    assert!(graph.freeze()?.as_view(&items[0]).is_err());
    let before = graph.num_tuples()?;
    assert!(
        graph
            .register(eg::Vec::<FrozenBuiltinTerm>::of(&items))
            .is_err()
    );
    assert_eq!(graph.num_tuples()?, before);
    let set_items = frozen.lookup(&set)?.items().unwrap();
    let bag_items = frozen.lookup(&bag)?.items().unwrap();
    let entries = frozen.lookup(&map)?.entries().unwrap();
    let (number, term) = frozen.lookup(&pair)?.fields().unwrap();
    assert_eq!(term, observed_leaf);
    drop(frozen);
    drop(graph);
    let mut set_values: Vec<_> = set_items
        .into_iter()
        .map(|v| i64::try_from(v).unwrap())
        .collect();
    let mut bag_values: Vec<_> = bag_items
        .into_iter()
        .map(|v| i64::try_from(v).unwrap())
        .collect();
    set_values.sort_unstable();
    bag_values.sort_unstable();
    assert_eq!(set_values, [1, 3]);
    assert_eq!(bag_values, [1, 3, 3]);
    let entries: std::collections::BTreeMap<_, _> = entries
        .into_iter()
        .map(|(key, value)| {
            (
                String::try_from(key).unwrap(),
                i64::try_from(value).unwrap(),
            )
        })
        .collect();
    assert_eq!(
        entries,
        std::collections::BTreeMap::from([("a".to_owned(), 1), ("b".to_owned(), 2)])
    );
    assert_eq!(i64::try_from(number).unwrap(), 9);
    assert_eq!(children.items().unwrap(), items);
    Ok(())
}

#[test]
fn authored_container_inspection_does_not_evaluate_or_normalize() {
    let symbolic = eg::I64::from(1) + 2;
    let pair = eg::Pair::<eg::I64, eg::String>::new(&symbolic, "value");
    let (number, text) = pair.fields().unwrap();
    assert_eq!(number, symbolic);
    assert!(i64::try_from(number).is_err());
    assert_eq!(String::try_from(text).unwrap(), "value");
    assert_eq!(eg::Set::<eg::I64>::of([3, 1, 3]).items().unwrap().len(), 3);
    assert!(
        eg::Map::<eg::I64, eg::String>::empty()
            .entries()
            .unwrap()
            .is_empty()
    );
    assert!(eg::Vec::<eg::I64>::of([1]).push(2).items().is_err());
    assert!(
        var::<eg::Map<eg::I64, eg::String>>("map")
            .entries()
            .is_err()
    );
    assert!(
        var::<eg::Pair<eg::I64, eg::String>>("pair")
            .fields()
            .is_err()
    );
}

#[test]
fn rational_decoding_rejects_invalid_or_unrepresentable_portable_values() {
    let rational = num::rational::Rational64::new(-5, 9);
    assert_eq!(
        num::rational::Rational64::try_from(eg::Rational::from(rational)).unwrap(),
        rational
    );
    assert!(num::rational::Rational64::try_from(eg::Rational::new(1, 0)).is_err());
    assert!(num::rational::Rational64::try_from(eg::Rational::new(i64::MIN, -1)).is_err());
    assert_eq!(
        num::rational::Rational64::try_from(eg::Rational::new(i64::MIN, i64::MIN)).unwrap(),
        num::rational::Rational64::new(1, 1)
    );
}

#[test]
fn builtin_display_prints_the_expression_without_evaluating_it() {
    assert_eq!(format!("{}", eg::I64::from(7)), "7");
    let vector = eg::Vec::<eg::I64>::of([1, 2]);
    let printed = format!("{vector}");
    assert!(printed.contains("vec-of"));
    assert!(printed.contains('1') && printed.contains('2'));
}

#[test]
fn numeric_wrappers_use_registered_native_signatures() -> Result<(), TypedError> {
    let mut graph = EGraph::new(EGraphOptions::default());
    macro_rules! numbers {
        ($one:expr, $two:expr) => {{
            let one = $one;
            let two = $two;
            graph.register([
                &one + &two,
                one.clone() + &two,
                &one + two.clone(),
                &one - &two,
                &one * &two,
                &one / &two,
                one.min(&two),
                one.max(&two),
                -&one,
            ])?;
            assert!(graph.check((
                one.lt(&two),
                one.le(&two),
                two.gt(&one),
                two.ge(&one),
                ne(one, two)
            ))?);
        }};
    }
    numbers!(eg::I64::from(1), eg::I64::from(2));
    numbers!(eg::F64::from(1.0), eg::F64::from(2.0));
    numbers!(eg::BigInt::from(1), eg::BigInt::from(2));
    numbers!(eg::BigRat::new(1, 1), eg::BigRat::new(2, 1));
    numbers!(eg::Rational::new(1, 1), eg::Rational::new(2, 1));
    graph.register([
        eg::I64::from(7) % 3,
        eg::I64::from(-2).abs(),
        eg::I64::from(8).log2(),
        eg::I64::from(3) & 1,
        eg::I64::from(3) | 1,
        eg::I64::from(3) ^ 1,
        eg::I64::from(3) << 1,
        eg::I64::from(3) >> 1,
        !eg::I64::from(3),
    ])?;
    graph.register([
        eg::F64::from(7.0) % 3.0,
        eg::F64::from(-2.0).abs(),
        eg::F64::from(4.0).sqrt(),
        eg::F64::from(0.0).exp(),
        eg::F64::from(1.0).log(),
        eg::F64::from(2.0).pow(3.0),
    ])?;
    graph.register([
        eg::BigInt::from(7) % 3,
        eg::BigInt::from(8).bits(),
        eg::BigInt::from(3) & 1,
        eg::BigInt::from(3) | 1,
        eg::BigInt::from(3) ^ 1,
        eg::BigInt::from(3) << 1,
        eg::BigInt::from(3) >> 1,
        !eg::BigInt::from(3),
        eg::BigInt::from_string("123456789123456789123456789"),
    ])?;
    macro_rules! fractions {
        ($sort:ident) => {
            graph.register([
                eg::$sort::new(-3, 2).abs(),
                eg::$sort::new(3, 2).floor(),
                eg::$sort::new(3, 2).ceil(),
                eg::$sort::new(3, 2).round(),
                eg::$sort::new(2, 1).pow(eg::$sort::new(2, 1)),
                eg::$sort::new(4, 1).sqrt(),
                eg::$sort::new(1, 1).log(),
                eg::$sort::new(1, 1).cbrt(),
            ])?;
        };
    }
    fractions!(BigRat);
    fractions!(Rational);
    let integer = eg::I64::from(7);
    let float = eg::F64::from(7.0);
    let big = eg::BigInt::from(7);
    graph.register((
        &integer + 1,
        &integer % 3,
        &integer << 1,
        &integer >> 1,
        !&integer,
        &float + 1.0,
        &big + 1,
        &big << &integer,
        &big >> &integer,
        !&big,
    ))?;
    graph.register((
        eg::I64::from(3).to_f64(),
        eg::I64::from(3).to_string(),
        eg::F64::from(3.0).to_i64(),
        eg::F64::from(3.0).to_string(),
        eg::BigInt::from(3).to_string(),
        eg::BigRat::new(3, 1).to_i64(),
        eg::BigRat::new(3, 1).to_f64(),
        eg::BigRat::new(3, 2).numer(),
        eg::BigRat::new(3, 2).denom(),
        eg::Rational::new(3, 2).numer(),
        eg::Rational::new(3, 2).denom(),
        eg::Rational::new(3, 2).to_f64(),
    ))?;
    Ok(())
}

#[test]
fn boolean_and_string_wrappers_are_native_expressions() -> Result<(), TypedError> {
    let mut graph = EGraph::new(EGraphOptions::default());
    macro_rules! comparisons {
        ($sort:ident) => {
            graph.register([
                eg::$sort::from(1).bool_eq(1),
                eg::$sort::from(1).bool_lt(2),
                eg::$sort::from(1).bool_le(2),
                eg::$sort::from(2).bool_gt(1),
                eg::$sort::from(2).bool_ge(1),
            ])?;
        };
    }
    comparisons!(I64);
    comparisons!(BigInt);
    graph.register([
        eg::Bool::from(true) & false,
        eg::Bool::from(true) | false,
        eg::Bool::from(true) ^ false,
        !eg::Bool::from(false),
    ])?;
    assert!(graph.check(eg::Bool::from(true).guard())?);
    let truth = eg::Bool::from(true);
    graph.register((
        &truth & false,
        &truth | &truth,
        &truth ^ truth.clone(),
        !&truth,
    ))?;
    let text = eg::String::from("text");
    graph.register((&text + "!", &text + &text, text.replace(&text, &text)))?;
    let unit = eg::Unit::from(());
    graph.register(eg::Unit::from(&unit))?;
    let value = eg::String::from("ababa").replace("a", "x") + "!";
    assert_eq!(String::try_from(graph.extract(&value)?).unwrap(), "xbxbx!");
    let count = eg::String::from("ababa").count_matches("a");
    assert_eq!(i64::try_from(graph.extract(&count)?).unwrap(), 3);
    Ok(())
}

#[test]
fn container_wrappers_and_owned_portable_decoders_round_trip() -> Result<(), TypedError> {
    let mut graph = EGraph::new(EGraphOptions::default());
    let vector = eg::Vec::<eg::I64>::of([1, 2, 3]);
    graph.register([
        vector.push(4),
        vector.append(&vector),
        vector.pop(),
        vector.set(1, 4),
        vector.remove(1),
        eg::Vec::empty(),
    ])?;
    graph.register((vector.len(), vector.get(0)))?;
    assert!(graph.check((vector.contains(1), vector.not_contains(9)))?);
    let set = eg::Set::<eg::I64>::of([1, 2, 3]);
    graph.register([
        set.insert(4),
        set.remove(1),
        set.union(&set),
        set.difference(eg::Set::of([1])),
        set.intersection(&set),
        eg::Set::empty(),
    ])?;
    graph.register((set.len(), set.get(0)))?;
    assert!(graph.check((set.contains(1), set.not_contains(9)))?);
    let multiset = eg::MultiSet::<eg::I64>::of([1, 2, 2]);
    graph.register([
        multiset.insert(4),
        multiset.remove(1),
        multiset.subtract(eg::MultiSet::of([1])),
        eg::MultiSet::<eg::I64>::of([1]).subtract_swapped(&multiset),
        multiset.intersection(&multiset),
        multiset.sum(&multiset),
        multiset.reset_counts(),
        eg::MultiSet::single(4, 2),
        eg::MultiSet::empty(),
        eg::MultiSet::<eg::MultiSet<eg::I64>>::of([&multiset]).sum_multisets(),
    ])?;
    graph.register((
        multiset.len(),
        multiset.pick(),
        multiset.pick_max(),
        multiset.count(2),
    ))?;
    assert!(graph.check((multiset.contains(1), multiset.not_contains(9)))?);
    let map = eg::Map::<eg::I64, eg::String>::of([(1, "one"), (2, "two")]);
    graph.register([map.insert(3, "three"), map.remove(1), eg::Map::empty()])?;
    graph.register((map.len(), map.get(1)))?;
    assert!(graph.check((map.contains(1), map.not_contains(9)))?);
    let pair = eg::Pair::<eg::I64, eg::String>::new(1, "one");
    let key = eg::I64::from(1);
    let value = eg::String::from("one");
    graph.register((
        eg::Vec::<eg::I64>::of([&key]).push(&key).append(&vector),
        eg::Set::<eg::I64>::of([&key]).insert(&key),
        eg::MultiSet::<eg::I64>::of([&key]).insert(&key),
        eg::Map::<eg::I64, eg::String>::of([(&key, &value)]).insert(&key, &value),
        eg::Pair::<eg::I64, eg::String>::new(&key, &value),
    ))?;
    graph.register((pair.first(), pair.second()))?;
    let (left, right) = <(eg::I64, eg::String)>::try_from(graph.extract(&pair)?).unwrap();
    assert_eq!(i64::try_from(left).unwrap(), 1);
    assert_eq!(String::try_from(right).unwrap(), "one");
    assert_eq!(
        Vec::<eg::I64>::try_from(graph.extract(&vector)?)
            .unwrap()
            .len(),
        3
    );
    assert_eq!(
        Vec::<eg::I64>::try_from(graph.extract(&set)?)
            .unwrap()
            .len(),
        3
    );
    assert_eq!(
        Vec::<eg::I64>::try_from(graph.extract(&multiset)?)
            .unwrap()
            .len(),
        3
    );
    assert_eq!(
        Vec::<(eg::I64, eg::String)>::try_from(graph.extract(&map)?)
            .unwrap()
            .len(),
        2
    );
    Ok(())
}

#[test]
fn large_numeric_host_values_round_trip() -> Result<(), TypedError> {
    let mut graph = EGraph::new(EGraphOptions::default());
    let integer = (num::BigInt::from(1) << 200usize) + num::BigInt::from(123);
    let symbolic = eg::BigInt::from(integer.clone());
    assert_eq!(
        num::BigInt::try_from(graph.extract(&symbolic)?).unwrap(),
        integer
    );
    let fraction = num::BigRational::new(integer, num::BigInt::from(17));
    let symbolic = eg::BigRat::from(fraction.clone());
    assert_eq!(
        num::BigRational::try_from(graph.extract(&symbolic)?).unwrap(),
        fraction
    );
    Ok(())
}
