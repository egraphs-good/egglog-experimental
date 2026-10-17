#![cfg(feature = "typed")]

use egglog_experimental::typed::{
    builtins::{Bool, F64, I64, Map, Pair, String as EString, Unit, join},
    prelude::*,
};
use std::hash::{DefaultHasher, Hash, Hasher};

#[test]
fn exact_number_host_codecs_are_checked_and_never_symbolic_constructors() -> Result<(), TypedError>
{
    use egglog_experimental::typed::builtins::{BigInt, BigRat, Rational};
    use num::{BigInt as Z, BigRational as Q, rational::Rational64};

    let huge: Z = "12345678901234567890123456789012345678901".parse().unwrap();
    let integer = BigInt::from(&huge);
    assert_eq!(integer, BigInt::from(huge.clone()));
    assert_eq!(Z::try_from(&integer)?, huge);
    let host = Q::new(huge.clone(), Z::from(2));
    let ratio = BigRat::try_from(&host)?;
    assert_eq!(ratio, BigRat::try_from(host.clone())?);
    assert_eq!(Q::try_from(&ratio)?, host);
    for n in [i64::MIN, -1, 0, i64::MAX] {
        let host = Rational64::new_raw(n, 1);
        let value = Rational::try_from(&host)?;
        let same = Rational::try_from(host)?;
        assert_eq!(value, same);
        assert_eq!(Rational64::try_from(&value)?, host);
        let mut a = DefaultHasher::new();
        let mut b = DefaultHasher::new();
        value.hash(&mut a);
        same.hash(&mut b);
        assert_eq!(a.finish(), b.finish());
    }
    for (n, d) in [(1, 0), (1, -2), (2, 4), (0, 2), (i64::MIN, -1)] {
        assert!(Rational::try_from(Rational64::new_raw(n, d)).is_err());
        assert!(BigRat::try_from(Q::new_raw(Z::from(n), Z::from(d))).is_err());
    }
    assert_ne!(integer, BigInt::from_string(huge.to_string()));
    assert!(Z::try_from(&BigInt::new(7)).is_err());
    assert!(Q::try_from(&BigRat::new(BigInt::new(1), BigInt::new(2))).is_err());
    assert!(Rational64::try_from(&Rational::new(1, 2)).is_err());
    assert!(Rational64::try_from(&var::<Rational>("q")).is_err());
    Ok(())
}

#[test]
fn bignum_generated_family_preserves_symbolic_sorts_and_borrowed_operators()
-> Result<(), TypedError> {
    use egglog_experimental::typed::builtins::{BigInt, BigRat};
    use num::{BigInt as Z, BigRational as Q};

    let a = BigInt::from_string("123456789012345678901");
    let b = BigInt::from_string("-17");
    let amount = I64::from(3);
    let x = BigRat::new(&a, BigInt::new(2));
    let y = BigRat::new(BigInt::new(1), BigInt::new(3));
    for expression in [
        &a + &b,
        &a - &b,
        &a * &b,
        &a / &b,
        &a % &b,
        &a & &b,
        &a | &b,
        &a ^ &b,
        &a << &amount,
        &a >> &amount,
        !&a,
        a.clone().bits(),
        a.clone().min(&b),
        a.clone().max(&b),
        x.clone().numer(),
        x.clone().denom(),
    ] {
        assert!(Z::try_from(&expression).is_err());
    }
    for expression in [
        &x + &y,
        &x - &y,
        &x * &y,
        &x / &y,
        x.clone().min(&y),
        x.clone().max(&y),
        -&x,
        x.clone().abs(),
        x.clone().floor(),
        x.clone().ceil(),
        x.clone().round(),
        x.clone().pow(&y),
        x.clone().log(),
        x.clone().sqrt(),
        x.clone().cbrt(),
    ] {
        assert!(Q::try_from(&expression).is_err());
    }
    for predicate in [
        a.clone().lt(&b),
        a.clone().gt(&b),
        a.clone().le(&b),
        a.clone().ge(&b),
        x.clone().lt(&y),
        x.clone().gt(&y),
        x.clone().le(&y),
        x.clone().ge(&y),
    ] {
        assert!(<()>::try_from(&predicate).is_err());
    }
    for predicate in [
        a.clone().bool_eq(&b),
        a.clone().bool_lt(&b),
        a.clone().bool_gt(&b),
        a.clone().bool_le(&b),
        a.clone().bool_ge(&b),
    ] {
        assert!(bool::try_from(&predicate).is_err());
    }
    assert!(String::try_from(&a.clone().to_string()).is_err());
    assert!(i64::try_from(&x.clone().to_i64()).is_err());
    assert!(f64::try_from(&x.clone().to_f64()).is_err());
    assert_eq!(-&x, -x.clone());
    for shifted in [
        a.clone() << amount.clone(),
        a.clone() << &amount,
        &a << amount.clone(),
    ] {
        assert_eq!(shifted, &a << &amount);
    }
    for shifted in [
        a.clone() >> amount.clone(),
        a.clone() >> &amount,
        &a >> amount.clone(),
    ] {
        assert_eq!(shifted, &a >> &amount);
    }
    assert_ne!(&x - &y, &y - &x);
    assert_eq!(i64::try_from(&amount)?, 3);
    Ok(())
}

#[test]
fn closed_scalar_family_preserves_symbolic_sorts_and_executes_as_bytes() -> Result<(), TypedError> {
    use egglog_experimental::typed::builtins::{Rational, count_matches};
    use num::rational::Rational64;

    let a = I64::from(13);
    let b = I64::from(2);
    let x = F64::from(4.0);
    let y = F64::from(2.0);
    let r = Rational::new(3, 2);
    let s = Rational::new(1, 2);
    let borrowed_a = &a;
    let borrowed_x = &x;
    let borrowed_r = &r;
    for expression in [
        &a | &b,
        &a ^ &b,
        &a << &b,
        &a >> &b,
        !&a,
        a.clone().log2(),
        a.clone().abs(),
        x.clone().to_i64(),
        r.clone().numer(),
        r.clone().denom(),
        count_matches("aba", "a"),
    ] {
        assert!(i64::try_from(&expression).is_err());
    }
    for expression in [
        &x - &y,
        &x * &y,
        &x / &y,
        &x % &y,
        x.clone().pow(&y),
        -&x,
        x.clone().abs(),
        x.clone().exp(),
        x.clone().log(),
        x.clone().sqrt(),
        x.clone().min(&y),
        x.clone().max(&y),
        F64::from_i64(&a),
        r.clone().to_f64(),
    ] {
        assert!(f64::try_from(&expression).is_err());
    }
    for expression in [
        &r - &s,
        &r * &s,
        &r / &s,
        r.clone().min(&s),
        r.clone().max(&s),
        -&r,
        r.clone().abs(),
        r.clone().floor(),
        r.clone().ceil(),
        r.clone().round(),
        r.clone().pow(&s),
        r.clone().log(),
        r.clone().sqrt(),
        r.clone().cbrt(),
    ] {
        assert!(Rational64::try_from(&expression).is_err());
    }
    for predicate in [
        borrowed_a.gt(&b),
        a.le(&b),
        borrowed_x.lt(&y),
        x.gt(&y),
        x.le(&y),
        x.ge(&y),
        x.is_finite(),
        borrowed_r.lt(&s),
        r.gt(&s),
        r.le(&s),
        r.ge(&s),
    ] {
        assert!(<()>::try_from(&predicate).is_err());
    }
    for predicate in [
        a.clone().bool_lt(&b),
        a.clone().bool_gt(&b),
        a.clone().bool_le(&b),
        a.clone().bool_ge(&b),
    ] {
        assert!(bool::try_from(&predicate).is_err());
    }
    assert!(String::try_from(&x.clone().to_string()).is_err());
    assert_eq!(F64::from_i64(13), F64::from_i64(&a));
    assert_eq!(&a << &b, a.clone() << b.clone());
    assert_ne!(&r - &s, &s - &r);

    let mut graph = EGraph::default();
    assert!(graph.check((borrowed_a.gt(&b), a.gt(&b), borrowed_x.gt(&y), x.gt(&y)))?);
    for (left, right) in [(0, 1), (1, 1), (2, 1), (i64::MIN, i64::MAX)] {
        let left_expr = I64::from(left);
        for (predicate, expected) in [
            (left_expr.clone().bool_lt(right), left < right),
            (left_expr.clone().bool_gt(right), left > right),
            (left_expr.clone().bool_le(right), left <= right),
            (left_expr.bool_ge(right), left >= right),
        ] {
            assert_eq!(bool::try_from(&graph.extract(predicate)?)?, expected);
        }
    }
    assert_eq!(f64::try_from(&graph.extract(F64::from_i64(-3))?)?, -3.0);
    assert_eq!(
        i64::try_from(&graph.extract(count_matches("λa\0aλa", "a"))?)?,
        3
    );
    assert!(graph.check(x.clone().is_finite())?);
    assert!(!graph.check(F64::from(f64::INFINITY).is_finite())?);
    assert!(!graph.check(F64::from(f64::NAN).is_finite())?);
    assert_eq!(i64::try_from(&graph.extract(r.clone().numer())?)?, 3);
    assert_eq!(i64::try_from(&graph.extract(r.clone().denom())?)?, 2);
    // Preserve the provider's existing to_i64 exponent conversion.
    let extracted = graph.extract(r.pow(Rational::new(3, 2)))?;
    drop(graph);
    assert_eq!(Rational64::try_from(&extracted)?, Rational64::new(3, 2));
    assert_eq!(EGraph::default().extract(&extracted)?, extracted);
    Ok(())
}

#[test]
fn bignum_projections_and_heterogeneous_shifts_execute_as_bytes() -> Result<(), TypedError> {
    use egglog_experimental::typed::builtins::{BigInt, BigRat};
    use num::{BigInt as Z, BigRational as Q};

    let huge: Z = "-123456789012345678901234567890123456789".parse().unwrap();
    let integer = BigInt::from_string(huge.to_string());
    let ratio = BigRat::new(&integer, BigInt::new(2));
    let mut graph = EGraph::default();
    for (expression, expected) in [
        (ratio.clone().numer(), huge.clone()),
        (ratio.clone().denom(), Z::from(2)),
        (&integer << I64::from(7), &huge << 7),
        (&integer >> &I64::from(7), &huge >> 7),
    ] {
        let extracted = graph.extract(expression)?;
        assert_eq!(Z::try_from(&extracted)?, expected);
        assert_eq!(graph.extract(&extracted)?, extracted);
    }
    assert_eq!(
        String::try_from(&graph.extract(ratio.clone().numer().to_string())?)?,
        huge.to_string()
    );
    assert_eq!(
        Q::try_from(&graph.extract(-&ratio)?)?,
        Q::new(-huge, Z::from(2))
    );
    assert!(graph.check(integer.clone().lt(BigInt::new(0)))?);
    assert!(!graph.check(integer.clone().ge(BigInt::new(0)))?);
    assert!(graph.extract(&integer << I64::from(-1)).is_err());
    assert!(graph.extract(&integer >> I64::from(-1)).is_err());
    Ok(())
}

#[test]
fn exact_number_public_calls_extract_and_replay_without_width_or_float_bridges()
-> Result<(), TypedError> {
    use egglog_experimental::typed::builtins::{BigInt, BigRat, Rational};
    use num::{BigInt as Z, BigRational as Q, rational::Rational64};

    let mut graph = EGraph::default();
    let integer = BigInt::new(I64::from(40) + I64::from(2));
    assert_eq!(Z::try_from(&graph.extract(integer)?)?, Z::from(42));
    let huge: Z = "12345678901234567890123456789012345678901".parse().unwrap();
    let rational = BigRat::new(BigInt::from_string(huge.to_string()), BigInt::new(-2));
    let extracted = graph.extract(rational)?;
    assert_eq!(Q::try_from(&extracted)?, Q::new(huge, Z::from(-2)));
    assert_eq!(graph.extract(&extracted)?, extracted);
    let a = Rational::new(I64::from(2) + I64::from(-1), 2);
    let b = Rational::new(1, 3);
    let sum = &a + &b;
    assert_eq!(sum, a.clone() + b.clone());
    assert_eq!(sum, &a + b.clone());
    assert_eq!(sum, a + &b);
    let extracted = graph.extract(sum)?;
    assert_eq!(Rational64::try_from(&extracted)?, Rational64::new(5, 6));
    assert_eq!(graph.extract(&extracted)?, extracted);
    assert_eq!(
        Rational64::try_from(&graph.extract(Rational::new(1, -2))?)?,
        Rational64::new(-1, 2)
    );
    assert_eq!(
        Rational64::try_from(&graph.extract(Rational::new(0, 7))?)?,
        Rational64::new(0, 1)
    );
    assert!(
        graph
            .extract(BigRat::new(BigInt::new(1), BigInt::new(0)))
            .is_err()
    );
    assert!(
        graph
            .extract(Rational::new(i64::MAX, 1) + Rational::new(1, 1))
            .is_err()
    );
    // Rational::new(_, 0) retains the native panic policy; it is not used as a
    // malformed-data test or silently changed to a checked host conversion.
    Ok(())
}

#[sort]
pub struct Math;
#[declarations]
impl Math {
    #[constructor(from, try_from, args = NumArgs)]
    pub fn Num(value: I64) -> Self;
    pub fn Add(a: Math, b: Math) -> Self;
}

#[test]
fn generated_addition_in_constructor_callback_executes_as_bytes() -> Result<(), TypedError> {
    let fold = ruleset(|i: &I64, j: &I64| {
        rewrite(Math::Add(Math::Num(i), Math::Num(j)), Math::Num(i + j))
    });
    let term = Math::Add(Math::Num(2_i64), Math::Num(3_i64));
    let mut graph = EGraph::default();
    graph.register(&term)?;
    graph.run(&fold)?;
    assert!(graph.check(eq(&term, Math::Num(5_i64)))?);
    let value: I64 = graph.extract(&term)?.try_into()?;
    assert_eq!(i64::try_from(&value)?, 5);
    assert_eq!(NumArgs::get_args(&Math::Num(&value))?.unwrap().value, value);
    assert!(get_args(&term, |x: &I64| Math::Num(x))?.is_none());
    let fresh = NumArgs::fresh();
    assert_ne!(fresh.value, NumArgs::fresh().value);
    assert_ne!(fresh.value, var::<I64>("__typed_v_0"));
    assert!(graph.check(Math::Num(&fresh.value))?);
    graph.run(&fold)?;
    Ok(())
}

#[test]
fn literals_and_all_operand_ownership_forms_remain_syntax() -> Result<(), TypedError> {
    let a = I64::from(2);
    let b = I64::from(3);
    let sum = &a + &b;
    assert_eq!(a.clone() + b.clone(), sum);
    assert_eq!(a.clone() + &b, sum);
    assert_eq!(&a + b.clone(), sum);
    assert_ne!(sum, I64::from(5));
    assert!(i64::try_from(&sum).is_err());
    assert!(get_args(&sum, |x: &I64, y: &I64| x + y).is_err());
    assert!(i64::try_from(&var::<I64>("x")).is_err());
    for value in [i64::MIN, -1, 0, i64::MAX] {
        assert_eq!(i64::try_from(&I64::from(value))?, value);
        assert_eq!(i64::try_from(&I64::from(&value))?, value);
    }
    let a = F64::from(1.25);
    let b = F64::from(2.5);
    let sum = &a + &b;
    assert_eq!(a.clone() + b.clone(), sum);
    assert_eq!(a.clone() + &b, sum);
    assert_eq!(&a + b.clone(), sum);
    assert!(f64::try_from(&sum).is_err());
    let mut graph = EGraph::default();
    assert_eq!(
        i64::try_from(&graph.extract(I64::from(2) + I64::from(3))?)?,
        5
    );
    assert_eq!(f64::try_from(&graph.extract(sum)?)?, 3.75);
    Ok(())
}

#[test]
fn closed_i64_operators_preserve_symbolic_order_and_borrow_reuse() -> Result<(), TypedError> {
    let a = I64::from(-13);
    let b = I64::from(5);
    for forms in [
        [
            &a - &b,
            a.clone() - b.clone(),
            &a - b.clone(),
            a.clone() - &b,
        ],
        [
            &a * &b,
            a.clone() * b.clone(),
            &a * b.clone(),
            a.clone() * &b,
        ],
        [
            &a / &b,
            a.clone() / b.clone(),
            &a / b.clone(),
            a.clone() / &b,
        ],
        [
            &a % &b,
            a.clone() % b.clone(),
            &a % b.clone(),
            a.clone() % &b,
        ],
        [
            &a & &b,
            a.clone() & b.clone(),
            &a & b.clone(),
            a.clone() & &b,
        ],
    ] {
        for form in &forms[1..] {
            assert_eq!(form, &forms[0]);
        }
        assert!(i64::try_from(&forms[0]).is_err());
    }
    assert_ne!(&a - &b, &b - &a);
    assert_ne!(&a / &b, &b / &a);
    assert_ne!(&a % &b, &b % &a);
    assert_eq!(a.min(&b), a.min(b.clone()));
    assert_eq!(a.max(&b), a.max(b.clone()));
    assert_eq!(a.lt(&b), a.lt(b.clone()));
    assert_eq!(a.ge(&b), a.ge(b.clone()));
    for value in [a.min(&b), a.max(&b)] {
        assert!(i64::try_from(&value).is_err());
    }
    for value in [a.lt(&b), a.ge(&b)] {
        assert!(<()>::try_from(&value).is_err());
    }
    assert_ne!(a.lt(&b), b.lt(&a));
    assert_ne!(a.ge(&b), b.ge(&a));
    assert_eq!(i64::try_from(&a)?, -13);
    assert_eq!(i64::try_from(&b)?, 5);
    let rules = ruleset(|x: &I64, y: &I64| {
        rule(
            (Math::Num(x), Math::Num(y), x.lt(y)),
            Math::Add(Math::Num(x.min(y)), Math::Num(x.max(y))),
        )
    });
    let mut graph = EGraph::default();
    graph.register([Math::Num(&a), Math::Num(&b)])?;
    graph.run(&rules)?;
    assert!(graph.check(Math::Add(Math::Num(-13), Math::Num(5)))?);
    Ok(())
}

#[test]
fn closed_i64_generated_bytes_match_native_values_and_partial_queries() -> Result<(), TypedError> {
    let a = I64::from(-13);
    let b = I64::from(5);
    let mut graph = EGraph::default();
    let mut native = egglog_experimental::new_experimental_egraph();
    for (value, source, expected) in [
        (&a - &b, "(- -13 5)", -18),
        (&a * &b, "(* -13 5)", -65),
        (&a / &b, "(/ -13 5)", -2),
        (&a % &b, "(% -13 5)", -3),
        (&a & &b, "(& -13 5)", 1),
        (a.min(&b), "(min -13 5)", -13),
        (a.max(&b), "(max -13 5)", 5),
        (
            I64::from(i64::MIN).min(i64::MAX),
            "(min -9223372036854775808 9223372036854775807)",
            i64::MIN,
        ),
        (
            I64::from(i64::MAX).max(i64::MIN),
            "(max 9223372036854775807 -9223372036854775808)",
            i64::MAX,
        ),
    ] {
        native
            .parse_and_run_program(None, &format!("(check (= {source} {expected}))"))
            .unwrap();
        assert_eq!(i64::try_from(&graph.extract(value)?)?, expected, "{source}");
    }
    for (value, source, expected) in [
        (a.lt(&b), "(< -13 5)", true),
        (b.lt(&a), "(< 5 -13)", false),
        (a.ge(&b), "(>= -13 5)", false),
        (b.ge(&a), "(>= 5 -13)", true),
        (b.lt(&b), "(< 5 5)", false),
        (b.ge(&b), "(>= 5 5)", true),
    ] {
        assert_eq!(
            native
                .parse_and_run_program(None, &format!("(check {source})"))
                .is_ok(),
            expected,
            "{source}"
        );
        assert_eq!(graph.check(value)?, expected, "{source}");
    }
    Ok(())
}

#[test]
fn closed_i64_arithmetic_failures_match_native_evaluation() {
    for (value, source) in [
        (I64::from(1) / I64::from(0), "(/ 1 0)"),
        (I64::from(1) % I64::from(0), "(% 1 0)"),
        (
            I64::from(i64::MIN) / I64::from(-1),
            "(/ -9223372036854775808 -1)",
        ),
        (
            I64::from(i64::MIN) % I64::from(-1),
            "(% -9223372036854775808 -1)",
        ),
        (
            I64::from(i64::MIN) - I64::from(1),
            "(- -9223372036854775808 1)",
        ),
        (
            I64::from(i64::MAX) * I64::from(2),
            "(* 9223372036854775807 2)",
        ),
    ] {
        assert!(
            i64::try_from(&value).is_err(),
            "authoring evaluated {source}"
        );
        assert!(
            egglog_experimental::new_experimental_egraph()
                .parse_and_run_program(None, &format!("(let invalid {source})"))
                .is_err(),
            "{source}"
        );
        let TypedError::Engine(error) = EGraph::default().extract(value).unwrap_err() else {
            panic!("expected a decoded native evaluation error for {source}");
        };
        assert_eq!(
            error.code,
            egglog_experimental::proto::ErrorCode::EvaluationFailed as i32,
            "{source}"
        );
    }
}

#[test]
fn string_bool_and_unit_literals_publish_decode_and_hash_exactly() -> Result<(), TypedError> {
    for text in ["", "a\0b\n☃", "false"] {
        let host = text.to_owned();
        let a = EString::from(text);
        let b = EString::from(&host);
        assert_eq!(a, b);
        assert_eq!(a, EString::from(host));
        assert_eq!(String::try_from(&a)?, text);
        let mut ah = DefaultHasher::new();
        let mut bh = DefaultHasher::new();
        a.hash(&mut ah);
        b.hash(&mut bh);
        assert_eq!(ah.finish(), bh.finish());
    }
    for value in [false, true] {
        let a = Bool::from(value);
        let b = Bool::from(&value);
        assert_eq!(a, b);
        assert_eq!(bool::try_from(&a)?, value);
        let mut ah = DefaultHasher::new();
        let mut bh = DefaultHasher::new();
        a.hash(&mut ah);
        b.hash(&mut bh);
        assert_eq!(ah.finish(), bh.finish());
    }
    assert_ne!(Bool::from(false), Bool::from(true));
    let a = Unit::from(());
    let b = Unit::from(&());
    assert_eq!(a, b);
    <()>::try_from(&a)?;
    let mut ah = DefaultHasher::new();
    let mut bh = DefaultHasher::new();
    a.hash(&mut ah);
    b.hash(&mut bh);
    assert_eq!(ah.finish(), bh.finish());
    assert!(String::try_from(&var::<EString>("s")).is_err());
    assert!(bool::try_from(&var::<Bool>("b")).is_err());
    assert!(<()>::try_from(&var::<Unit>("u")).is_err());
    Ok(())
}

#[test]
fn strings_author_ordered_calls_and_execute_empty_single_and_many_tails() -> Result<(), TypedError>
{
    let a = EString::from("a\0b\n☃");
    let b = EString::from("tail");
    let sum = &a + &b;
    assert_eq!(a.clone() + b.clone(), sum);
    assert_eq!(a.clone() + &b, sum);
    assert_eq!(&a + b.clone(), sum);
    assert_eq!(join([&a, &b]), sum);
    assert_ne!(&b + &a, sum);
    assert!(String::try_from(&sum).is_err());
    let mut graph = EGraph::default();
    assert_eq!(String::try_from(&graph.extract(&sum)?)?, "a\0b\n☃tail");
    for (parts, expected) in [
        (vec![], ""),
        (vec!["a"], "a"),
        (vec!["a", "b", "c", "d"], "abcd"),
    ] {
        assert_eq!(String::try_from(&graph.extract(join(parts))?)?, expected);
    }
    assert_eq!(
        String::try_from(&graph.extract(a.replace("b\n", "replaced"))?)?,
        "a\0replaced☃"
    );
    for value in [i64::MIN, -1, 0, i64::MAX] {
        let text: EString = I64::from(value).to_string();
        assert!(String::try_from(&text).is_err());
        assert_eq!(String::try_from(&graph.extract(text)?)?, value.to_string());
    }
    Ok(())
}

#[test]
fn bool_operators_preserve_syntax_ownership_and_native_truth_tables() -> Result<(), TypedError> {
    let mut graph = EGraph::default();
    for left in [false, true] {
        let a = Bool::from(left);
        assert_eq!(!a.clone(), !&a);
        assert!(bool::try_from(&!&a).is_err());
        assert_eq!(bool::try_from(&graph.extract(!&a)?)?, !left);
        for right in [false, true] {
            let b = Bool::from(right);
            for (borrowed, owned, left_owned, right_owned, expected) in [
                (
                    &a & &b,
                    a.clone() & b.clone(),
                    a.clone() & &b,
                    &a & b.clone(),
                    left & right,
                ),
                (
                    &a | &b,
                    a.clone() | b.clone(),
                    a.clone() | &b,
                    &a | b.clone(),
                    left | right,
                ),
                (
                    &a ^ &b,
                    a.clone() ^ b.clone(),
                    a.clone() ^ &b,
                    &a ^ b.clone(),
                    left ^ right,
                ),
            ] {
                assert_eq!(borrowed, owned);
                assert_eq!(borrowed, left_owned);
                assert_eq!(borrowed, right_owned);
                assert!(bool::try_from(&borrowed).is_err());
                assert_eq!(bool::try_from(&graph.extract(borrowed)?)?, expected);
            }
            assert_eq!(
                bool::try_from(&graph.extract(a.clone().implies(&b))?)?,
                !left || right
            );
        }
    }
    Ok(())
}

#[test]
fn scalar_container_results_keep_exact_sorts_and_graph_independent_ownership()
-> Result<(), TypedError> {
    let pair = Pair::<EString, Bool>::new(join(["a", "b"]), !Bool::from(true));
    let map = Map::<EString, Bool>::of([("a\0b\n☃", false), ("second", true)]);
    let mut graph = EGraph::default();
    let pair = graph.extract(pair)?;
    let map = graph.extract(map)?;
    let unit = graph.extract(Unit::from(()))?;
    drop(graph);
    let (text, flag) = pair.fields()?;
    assert_eq!(String::try_from(&text)?, "ab");
    assert!(!bool::try_from(&flag)?);
    <()>::try_from(&unit)?;
    assert_eq!(map.entries()?.len(), 2);
    let mut fresh = EGraph::default();
    assert_eq!(fresh.extract(&pair)?.fields()?, pair.fields()?);
    assert_eq!(fresh.extract(&map)?.entries()?, map.entries()?);
    assert!(!bool::try_from(&fresh.extract(map.get("a\0b\n☃"))?)?);
    assert_eq!(fresh.extract(&unit)?, unit);
    Ok(())
}

#[test]
fn exact_float_bits_are_distinct_from_native_equality() -> Result<(), TypedError> {
    for bits in [
        0,
        1 << 63,
        1,
        0x7ff0_0000_0000_0000,
        0x7ff8_0000_0000_0001,
        0x7ff8_0000_0000_0002,
    ] {
        let value = f64::from_bits(bits);
        let a = F64::from(value);
        let b = F64::from(&value);
        assert_eq!(f64::try_from(&a)?.to_bits(), bits);
        assert_eq!(a, b);
        let mut ah = DefaultHasher::new();
        let mut bh = DefaultHasher::new();
        a.hash(&mut ah);
        b.hash(&mut bh);
        assert_eq!(ah.finish(), bh.finish());
    }
    let positive = F64::from(0.0);
    let negative = F64::from(-0.0);
    let nan_a = F64::from(f64::from_bits(0x7ff8_0000_0000_0001));
    let nan_b = F64::from(f64::from_bits(0x7ff8_0000_0000_0002));
    assert_ne!(positive, negative);
    assert_ne!(nan_a, nan_b);
    let mut graph = EGraph::default();
    assert!(graph.check(eq(&positive, &negative))?);
    assert!(graph.check(eq(&nan_a, &nan_b))?);
    Ok(())
}

#[test]
fn overflow_is_native_evaluation_failure_not_authoring_arithmetic() {
    let value = I64::from(i64::MAX) + I64::from(1);
    assert!(i64::try_from(&value).is_err());
    let error = EGraph::default().extract(&value).unwrap_err();
    let TypedError::Engine(error) = error else {
        panic!("expected structured engine failure: {error}");
    };
    assert_eq!(
        error.code,
        egglog_experimental::proto::ErrorCode::EvaluationFailed as i32
    );
}

#[test]
// The two symbolic Add orders exercise different ownership/child arrangements,
// even though Clippy treats the overloaded operator as commutative arithmetic.
#[allow(clippy::if_same_then_else)]
fn scalar_chains_compare_hash_and_drop_without_recursive_ownership() {
    for left_growing in [false, true] {
        let chain = || {
            let leaf = I64::from(1);
            let mut value = leaf.clone();
            for _ in 0..100_000 {
                value = if left_growing {
                    value + &leaf
                } else {
                    &leaf + value
                };
            }
            value
        };
        let a = chain();
        let b = chain();
        assert_eq!(a, b);
        let mut ah = DefaultHasher::new();
        let mut bh = DefaultHasher::new();
        a.hash(&mut ah);
        b.hash(&mut bh);
        assert_eq!(ah.finish(), bh.finish());
        std::thread::spawn(move || drop((a, b))).join().unwrap();
    }
}
