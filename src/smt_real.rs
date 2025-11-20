use egglog::sort::S;
use egglog::{BaseValue, EGraph, Term, TermDag, Value, prelude::BaseSort, sort::BaseValues};
use egglog::{
    add_primitive,
    ast::Literal,
    sort::{F, OrderedFloat},
};
use smtlib::terms::{IntoWithStorage, StaticSorted};
use smtlib::{Real, Storage};
use std::{fmt::Debug, hash::Hash};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SMTRealValue {
    Const(String),
    Float64(OrderedFloat<f64>),
    Neg(Box<SMTRealValue>),
    Add(Box<SMTRealValue>, Box<SMTRealValue>),
    Sub(Box<SMTRealValue>, Box<SMTRealValue>),
    Mul(Box<SMTRealValue>, Box<SMTRealValue>),
    Div(Box<SMTRealValue>, Box<SMTRealValue>),
}

impl SMTRealValue {
    pub fn to_real<'s>(&self, st: &'s Storage) -> Real<'s> {
        match self {
            SMTRealValue::Const(name) => Real::new_const(st, name).into(),
            SMTRealValue::Float64(num) => num.0.into_with_storage(st),
            SMTRealValue::Neg(x) => -x.to_real(st),
            SMTRealValue::Add(a, b) => a.to_real(st) + b.to_real(st),
            SMTRealValue::Sub(a, b) => a.to_real(st) - b.to_real(st),
            SMTRealValue::Mul(a, b) => a.to_real(st) * b.to_real(st),
            SMTRealValue::Div(a, b) => a.to_real(st) / b.to_real(st),
        }
    }

    pub fn to_term(&self, termdag: &mut TermDag) -> Term {
        match self {
            SMTRealValue::Const(name) => {
                let arg = termdag.lit(Literal::String(name.clone()));
                termdag.app("smt-real-const".into(), vec![arg])
            }
            SMTRealValue::Float64(value) => {
                let arg = termdag.lit(Literal::Float(OrderedFloat(value.0)));
                termdag.app("smt-real".into(), vec![arg])
            }
            SMTRealValue::Neg(x) => {
                let x_term = x.to_term(termdag);
                termdag.app("inv".into(), vec![x_term])
            }
            SMTRealValue::Add(a, b) => {
                let a_term = a.to_term(termdag);
                let b_term = b.to_term(termdag);
                termdag.app("+".into(), vec![a_term, b_term])
            }
            SMTRealValue::Sub(a, b) => {
                let a_term = a.to_term(termdag);
                let b_term = b.to_term(termdag);
                termdag.app("-".into(), vec![a_term, b_term])
            }
            SMTRealValue::Mul(a, b) => {
                let a_term = a.to_term(termdag);
                let b_term = b.to_term(termdag);
                termdag.app("*".into(), vec![a_term, b_term])
            }
            SMTRealValue::Div(a, b) => {
                let a_term = a.to_term(termdag);
                let b_term = b.to_term(termdag);
                termdag.app("/".into(), vec![a_term, b_term])
            }
        }
    }
}

impl BaseValue for SMTRealValue {}

#[derive(Debug)]
pub struct SMTReal;

impl BaseSort for SMTReal {
    type Base = SMTRealValue;

    fn name(&self) -> &str {
        "SMTReal"
    }

    fn reconstruct_termdag(
        &self,
        base_values: &BaseValues,
        value: Value,
        termdag: &mut TermDag,
    ) -> Term {
        let real = base_values.unwrap::<SMTRealValue>(value);
        real.to_term(termdag)
    }

    fn register_primitives(&self, eg: &mut EGraph) {
        // (smt-real-const "x")
        add_primitive!(
            eg,
            "smt-real-const" = |value: S| -> SMTRealValue { { SMTRealValue::Const(value.0) } }
        );
        // (smt-real 1.5)
        add_primitive!(
            eg,
            "smt-real" = |value: F| -> SMTRealValue { { SMTRealValue::Float64(value.0) } }
        );
        // (inv x) - negation
        add_primitive!(
            eg,
            "inv" = |x: SMTRealValue| -> SMTRealValue { SMTRealValue::Neg(Box::new(x)) }
        );
        // (+ a b)
        add_primitive!(
            eg,
            "+" = |a: SMTRealValue, b: SMTRealValue| -> SMTRealValue {
                SMTRealValue::Add(Box::new(a), Box::new(b))
            }
        );
        // (- a b)
        add_primitive!(
            eg,
            "-" = |a: SMTRealValue, b: SMTRealValue| -> SMTRealValue {
                SMTRealValue::Sub(Box::new(a), Box::new(b))
            }
        );
        // (* a b)
        add_primitive!(
            eg,
            "*" = |a: SMTRealValue, b: SMTRealValue| -> SMTRealValue {
                SMTRealValue::Mul(Box::new(a), Box::new(b))
            }
        );
        // (/ a b)
        add_primitive!(
            eg,
            "/" = |a: SMTRealValue, b: SMTRealValue| -> SMTRealValue {
                SMTRealValue::Div(Box::new(a), Box::new(b))
            }
        );
    }
}
