#![cfg(feature = "typed")]
#![allow(
    dead_code,
    reason = "the imported example mains are executed by typed_examples"
)]

// Source-specific API regressions live here so the runnable examples can follow
// their original programs without extra constructor-equivalence assertions.
mod subsume {
    include!("../examples/typed_subsume.rs");

    #[test]
    fn saved_root_commutes_after_its_original_constructor_is_subsumed() -> Result<(), TypedError> {
        let mut egraph = EGraph::default();
        let output = let_("output", Math::num(2) * (Math::num(3) * Math::var("x")));
        egraph.register((&output, saved_root(&output)))?;
        egraph.run(replace_three.repeat(10))?;
        egraph.run(rules.repeat(10))?;
        egraph.push()?;
        let probe = let_("probe", &output * 5);
        egraph.register(&probe)?;
        egraph.run(rules.repeat(10))?;
        assert!(egraph.check(eq(probe, Math::num(5) * output))?);
        egraph.pop()?;
        Ok(())
    }
}

#[path = "../examples/typed_array.rs"]
mod array_example;

#[test]
fn array_operators_keep_order_grouping_and_capture_identity()
-> Result<(), egglog_experimental::typed::TypedError> {
    use array_example::{Array, Math};
    use egglog_experimental::typed::prelude::*;
    let [a, b, c] = ["a", "b", "c"].map(Math::var);
    let expression = &a + (&b + &c);
    let (left, right) = get_args(&expression, |left: &Math, right: &Math| left + right)?.unwrap();
    assert_eq!(left, a);
    assert_eq!(right, &b + &c);
    assert_ne!(expression, (&a + &b) + &c);
    assert_ne!(expression, &a + (&c + &b));
    let output = let_("output", Array::a_var("memory").store(&a, 42).select(&a));
    let same_output = output.clone();
    let mut graph = EGraph::default();
    graph.register(&output)?;
    assert!(graph.check(eq(&output, same_output))?);
    assert!(graph.register(let_("output", Math::num(0))).is_err());
    Ok(())
}

#[path = "../examples/typed_bdd.rs"]
mod bdd_example;

#[test]
fn bdd_literals_build_the_same_boolean_nodes() {
    use bdd_example::Bdd;
    let value = Bdd::ite(0, true, false);
    assert_eq!(value, Bdd::ite(0, Bdd::truth(), Bdd::falsity()));
    assert_eq!(&value & true, &value & Bdd::truth());
    assert_eq!(&value | false, &value | Bdd::falsity());
}

#[path = "../examples/typed_antiunify.rs"]
mod antiunify_example;

mod antiunify {
    use super::antiunify_example::*;

    #[test]
    fn nested_constructor_conversions() {
        assert_eq!(
            Expr::var("x") + (Expr::num(1) + 2),
            Expr::var("x") + (Expr::num(1) + Expr::num(2))
        );
    }
}

#[path = "../examples/typed_datatypes.rs"]
mod datatypes_example;

mod datatypes {
    use super::datatypes_example::*;
    use egglog_experimental::typed::{builtins as egg, prelude::*};

    #[test]
    fn boolean_embedding_and_recursive_vector_extraction() -> Result<(), TypedError> {
        let truth = Math::from(true);
        assert_eq!(truth, Math::boolean(Boolean::truth()));
        let expr = let_(
            "datatypes::expr",
            Math::sum(egg::Vec::of([&truth, &Math::from(false)])) + truth,
        );
        let mut egraph = EGraph::default();
        egraph.register(&expr)?;
        let extracted = egraph.extract(&expr)?;
        assert!(get_args(&extracted, |left: &Math, right: &Math| left + right)?.is_some());
        assert!(egraph.check(eq(expr, extracted))?);
        Ok(())
    }
}

#[path = "../examples/typed_eqsat_basic.rs"]
mod eqsat_basic_example;

mod eqsat_basic {
    use super::eqsat_basic_example::*;
    use egglog_experimental::typed::prelude::*;

    #[test]
    fn conversions_do_not_distribute_before_running() -> Result<(), TypedError> {
        let x = Math::from("x");
        assert_eq!(Math::from(2) * (&x + 3), Math::num(2) * (&x + Math::num(3)));
        let expr1 = let_("eqsat::expr1", Math::from(2) * (&x + 3));
        let expr2 = let_("eqsat::expr2", Math::from(6) + Math::from(2) * x);
        let mut egraph = EGraph::default();
        egraph.register((&expr1, &expr2))?;
        assert!(!egraph.check(eq(&expr1, &expr2))?);
        Ok(())
    }
}

#[path = "../examples/typed_herbie.rs"]
mod herbie_example;

mod herbie {
    use super::herbie_example::*;
    use egglog_experimental::typed::{builtins as egg, prelude::*};

    #[test]
    fn rational_only_addition_stays_in_the_domain_theory() -> Result<(), TypedError> {
        let expression: Math = Math::num(egg::BigRat::new(1, 5)) + egg::BigRat::new(3, 10);
        let (left, right) =
            get_args(&expression, |left: &Math, right: &Math| left + right)?.unwrap();
        assert_eq!(left, Math::num(egg::BigRat::new(1, 5)));
        assert_eq!(right, Math::num(egg::BigRat::new(3, 10)));
        let mut graph = EGraph::default();
        graph.register(&expression)?;
        assert!(!graph.check(eq(expression, egg::BigRat::new(1, 2)))?);
        Ok(())
    }

    #[test]
    fn rational_conversions_preserve_symbolic_promotions() {
        let rational = var::<egg::BigRat>("rational");
        for (actual, expected) in [
            (Math::from(2_i64), Math::num(egg::BigRat::from(2_i64))),
            (Math::from(2_i32), Math::num(egg::BigRat::from(2_i32))),
            (Math::from(&rational), Math::num(&rational)),
            (Math::from(rational.clone()), Math::num(rational)),
        ] {
            assert_eq!(actual, expected);
        }
    }
}

#[path = "../examples/typed_herbie_tutorial.rs"]
mod herbie_tutorial_example;

mod herbie_tutorial {
    use super::herbie_tutorial_example::*;
    use egglog_experimental::typed::{builtins as egg, prelude::*};

    #[test]
    fn rational_conversions_preserve_symbolic_promotions() {
        assert_eq!(Math::from(2), Math::num(egg::BigRat::new(2, 1)));
        let rational = var::<egg::BigRat>("rational");
        for (actual, expected) in [
            (Math::from(2_i64), Math::num(egg::BigRat::from(2_i64))),
            (Math::from(2_i32), Math::num(egg::BigRat::from(2_i32))),
            (Math::from(&rational), Math::num(&rational)),
            (Math::from(rational.clone()), Math::num(rational)),
        ] {
            assert_eq!(actual, expected);
        }
    }
}

mod lambda_example {
    include!("../examples/typed_lambda.rs");

    #[test]
    fn source_order_keeps_shared_fixed_rule_occurrences() {
        let core = theory(false);
        let python = theory(true);
        assert_eq!(core.len(), 33);
        assert_eq!(python.len(), 33);
        assert_eq!(ruleset((&core, &python)).len(), 53);
        assert_eq!(ruleset((&core, &core)).len(), 33);
    }
}

mod lambda {
    use super::lambda_example::*;

    #[test]
    fn nested_value_and_variable_conversions() {
        assert_eq!(
            Term::from(1) + true,
            Term::val(Value::num(1)) + Term::val(Value::truth())
        );
        let named = Variable::from("x");
        assert_eq!(
            Term::app(&named, false),
            Term::app(Term::var(&named), Term::val(Value::falsity()))
        );
    }
}

#[path = "../examples/typed_levenshtein_distance.rs"]
mod levenshtein_distance_example;

mod levenshtein_distance {
    use super::levenshtein_distance_example::*;

    #[test]
    fn unicode_conversion_preserves_character_order() {
        // Unicode conversion uses characters, not bytes, and preserves their order.
        assert_eq!(
            Text::from("é猫"),
            Text::cons("é", Text::cons("猫", Text::empty()))
        );
        assert_eq!(
            Text::from(std::string::String::from("é猫")),
            Text::from("é猫")
        );
    }
}

#[path = "../examples/typed_math.rs"]
mod math_example;

mod math {
    use super::math_example::*;
    use egglog_experimental::typed::{builtins as egg, prelude::*};

    #[test]
    fn symbolic_float_conversions_and_fixed_theory_sizes() {
        let symbolic = var::<egg::F64>("conversion_float");
        assert_eq!(Math::from(&symbolic), Math::constant(&symbolic));
        assert_eq!(
            Math::from("x") * 2.0 + 1.0,
            Math::var("x") * Math::constant(2.0) + Math::constant(1.0)
        );
        assert_eq!(prune.len(), 11);
        assert_eq!(math.len(), 58);
    }
}

#[path = "../examples/typed_ndarrays.rs"]
mod ndarrays_example;

mod ndarrays {
    use super::ndarrays_example::*;
    use egglog_experimental::typed::{builtins as egg, prelude::*};

    #[test]
    fn nested_container_conversions_and_extraction() -> Result<(), TypedError> {
        assert_eq!(
            Values::vector([10, 11]),
            Values::vector(egg::Vec::of([Value::number(10), Value::number(11)]))
        );
        let values = egg::Vec::<Value>::of([1, 2]);
        assert_eq!(
            value_at(&values, 0),
            value_at(Values::vector(&values), Value::number(0))
        );
        let left = concat(Values::vector(&values), Values::vector([3]));
        let mut egraph = EGraph::default();
        egraph.register(&left)?;
        assert!(!egraph.check(eq(&left, Values::vector([1, 2, 3])))?);
        let concatenation = ruleset(|left: &egg::Vec<Value>, right: &egg::Vec<Value>| {
            rewrite(
                concat(Values::vector(left), Values::vector(right)),
                Values::vector(left.append(right)),
            )
        });
        egraph.run(concatenation.repeat(30))?;
        let extracted = egraph.extract(&left)?;
        assert_eq!(extracted, Values::vector([1, 2, 3]));
        assert!(egraph.check(eq(left, extracted))?);
        Ok(())
    }
}

#[path = "../examples/typed_rw_analysis.rs"]
mod rw_analysis_example;

mod rw_analysis {
    use super::rw_analysis_example::*;
    use egglog_experimental::typed::builtins as egg;

    #[test]
    fn domain_conversions_preserve_statement_fields() {
        let value = egg::I64::from(10);
        let expected = Expr::constant(Val::int(&value));
        assert_eq!(Expr::from(10_i64), expected);
        assert_eq!(Expr::from(10_i32), expected);
        assert_eq!(Expr::from(&value), expected);
        assert_eq!(Expr::from(value), expected);
        assert_eq!(
            Stmt::assign("x", 10),
            Stmt::assign(Var::named("x"), Expr::constant(Val::int(10)))
        );
        assert_eq!(
            Stmt::if_("condition", 1, 2),
            Stmt::if_(Var::named("condition"), Loc::at(1), Loc::at(2))
        );
    }
}

#[path = "../examples/typed_tutorial_analysis.rs"]
mod tutorial_analysis_example;

mod tutorial_analysis {
    use super::tutorial_analysis_example::theory::*;
    use egglog_experimental::typed::{builtins as egg, prelude::*};

    #[test]
    fn rational_conversions_preserve_expression_order_and_promotions() {
        let one = egg::BigRat::new(1, 1);
        let two = egg::BigRat::new(2, 1);
        let x = Num::from("x");
        assert_eq!(
            Num::from(&two) * (&x / (Num::from(&one) + Num::from(&two) / &two)),
            Num::constant(&two)
                * (&x / (Num::constant(&one) + Num::constant(&two) / Num::constant(&two)))
        );
        let rational = var::<egg::BigRat>("rational");
        for (actual, expected) in [
            (Num::from(2_i64), Num::constant(egg::BigRat::from(2_i64))),
            (Num::from(2_i32), Num::constant(egg::BigRat::from(2_i32))),
            (Num::from(&rational), Num::constant(&rational)),
            (Num::from(rational.clone()), Num::constant(rational)),
        ] {
            assert_eq!(actual, expected);
        }
    }
}

#[path = "../examples/typed_tutorial_basics.rs"]
mod tutorial_basics_example;

mod tutorial_basics {
    use super::tutorial_basics_example::*;
    use egglog_experimental::typed::{builtins as egg, prelude::*};

    #[test]
    fn conversions_preserve_syntax_and_extracted_callables() -> Result<(), TypedError> {
        let x = &Num::from("x");
        // From/Into only choose constructors; they do not evaluate or reassociate.
        assert_eq!(
            Num::from(2) * (x * 3),
            Num::constant(2) * (x * Num::constant(3))
        );
        assert_eq!(Num::from("x"), Num::var("x"));
        assert_ne!(Num::from("x"), var::<Num>("x"));
        let symbolic = &var::<egg::I64>("n");
        assert_eq!(Num::from(symbolic), Num::constant(symbolic));
        assert_eq!(arithmetic.len(), 6);
        let expr1 = let_("basics::expr1", Num::from(2) * (x * 3));
        let expr2 = let_("basics::expr2", Num::from(6) * x);
        let mut egraph = EGraph::default();
        egraph.register((&expr1, &expr2))?;
        assert!(get_args(&egraph.extract(&expr1)?, |x: &Num, y: &Num| x * y)?.is_some());
        assert!(get_args(&egraph.extract(&expr2)?, |x: &Num, y: &Num| x * y)?.is_some());
        Ok(())
    }
}

#[path = "../examples/typed_tutorial_extraction.rs"]
mod tutorial_extraction_example;

mod tutorial_extraction {
    use super::tutorial_extraction_example::*;

    #[test]
    fn conversions_preserve_cost_annotated_operator_syntax() {
        let x = Num::from("x");
        assert_eq!(&x * 2 + 1, &x * Num::constant(2) + Num::constant(1));
        assert_eq!(strength_reduction.len(), 1);
    }
}

#[path = "../examples/typed_typeinfer.rs"]
mod typeinfer_example;

mod typeinfer {
    use super::typeinfer_example::*;

    #[test]
    fn nested_unit_boolean_and_variable_conversions() {
        let name = Ident::from("identity");
        assert_eq!(
            Expr::let_(&name, (), true),
            Expr::let_(Ident::named("identity"), Expr::unit(), Expr::truth())
        );
        assert_eq!(Expr::abs(&name, &name), Expr::abs(&name, Expr::var(&name)));
    }
}
