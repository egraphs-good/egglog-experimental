use crate::smt_real::{SMTReal, SMTRealValue};
use egglog::sort::S;
use egglog::{
    BaseValue, EGraph, Term, TermDag, Value,
    prelude::{BaseSort, RustSpan, Span, add_base_sort},
    sort::BaseValues,
    span,
};
use egglog::{add_primitive, ast::Literal};
use smtlib::backend::z3_binary::Z3Binary;
use smtlib::terms::StaticSorted;
use smtlib::{Bool, Int, SatResult, Solver, Sorted, Storage};
use std::{fmt::Debug, hash::Hash};

pub fn add_smt(egraph: &mut EGraph) {
    // important to add ints as base sort before bools bc bools reference ints
    add_base_sort(egraph, SMTInt, span!()).unwrap();
    add_base_sort(egraph, SMTReal, span!()).unwrap();
    add_base_sort(egraph, SMTBool, span!()).unwrap();
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SMTBoolValue {
    Const(String),
    Or(Box<SMTBoolValue>, Box<SMTBoolValue>),
    And(Box<SMTBoolValue>, Box<SMTBoolValue>),
    Not(Box<SMTBoolValue>),
    IntEq(Box<SMTIntValue>, Box<SMTIntValue>),
    RealEq(Box<SMTRealValue>, Box<SMTRealValue>),
}

impl SMTBoolValue {
    pub fn to_bool<'s>(&self, st: &'s Storage) -> Bool<'s> {
        match self {
            SMTBoolValue::Const(name) => Bool::new_const(st, name).into(),
            SMTBoolValue::Or(a, b) => a.to_bool(st) | (b.to_bool(st)),
            SMTBoolValue::And(a, b) => a.to_bool(st) & (b.to_bool(st)),
            SMTBoolValue::Not(a) => !a.to_bool(st),
            SMTBoolValue::IntEq(a, b) => a.to_int(st)._eq(b.to_int(st)),
            SMTBoolValue::RealEq(a, b) => a.to_real(st)._eq(b.to_real(st)),
        }
    }

    pub fn to_term(&self, termdag: &mut TermDag) -> Term {
        match self {
            SMTBoolValue::Const(name) => {
                let arg = termdag.lit(Literal::String(name.clone()));
                termdag.app("smt-bool-const".into(), vec![arg])
            }
            SMTBoolValue::Or(a, b) => {
                let a_term = a.to_term(termdag);
                let b_term = b.to_term(termdag);
                termdag.app("or".into(), vec![a_term, b_term])
            }
            SMTBoolValue::And(a, b) => {
                let a_term = a.to_term(termdag);
                let b_term = b.to_term(termdag);
                termdag.app("and".into(), vec![a_term, b_term])
            }
            SMTBoolValue::Not(a) => {
                let a_term = a.to_term(termdag);
                termdag.app("not".into(), vec![a_term])
            }
            SMTBoolValue::IntEq(a, b) => {
                let a_term = a.to_term(termdag);
                let b_term = b.to_term(termdag);
                termdag.app("smt-=".into(), vec![a_term, b_term])
            }
            SMTBoolValue::RealEq(a, b) => {
                let a_term = a.to_term(termdag);
                let b_term = b.to_term(termdag);
                termdag.app("smt-real-=".into(), vec![a_term, b_term])
            }
        }
    }
}

impl BaseValue for SMTBoolValue {}

#[derive(Debug)]
pub struct SMTBool;

impl BaseSort for SMTBool {
    type Base = SMTBoolValue;

    fn name(&self) -> &str {
        "SMTBool"
    }

    fn reconstruct_termdag(
        &self,
        base_values: &BaseValues,
        value: Value,
        termdag: &mut TermDag,
    ) -> Term {
        let bool = base_values.unwrap::<SMTBoolValue>(value);
        bool.to_term(termdag)
    }

    fn register_primitives(&self, eg: &mut EGraph) {
        // (smt-bool-const "p")
        add_primitive!(
            eg,
            "smt-bool-const" = |value: S| -> SMTBoolValue { { SMTBoolValue::Const(value.0) } }
        );
        // (or b1 b2)
        add_primitive!(
            eg,
            "or" = |a: SMTBoolValue, b: SMTBoolValue| -> SMTBoolValue {
                SMTBoolValue::Or(Box::new(a), Box::new(b))
            }
        );
        // (and b1 b2)
        add_primitive!(
            eg,
            "and" = |a: SMTBoolValue, b: SMTBoolValue| -> SMTBoolValue {
                SMTBoolValue::And(Box::new(a), Box::new(b))
            }
        );
        // (not b)
        add_primitive!(
            eg,
            "not" = |a: SMTBoolValue| -> SMTBoolValue { SMTBoolValue::Not(Box::new(a)) }
        );
        // (= a b)
        add_primitive!(
            eg,
            "smt-=" = |a: SMTIntValue, b: SMTIntValue| -> SMTBoolValue {
                SMTBoolValue::IntEq(Box::new(a), Box::new(b))
            }
        );
        // (smt-real-= a b)
        add_primitive!(
            eg,
            "smt-real-=" = |a: SMTRealValue, b: SMTRealValue| -> SMTBoolValue {
                SMTBoolValue::RealEq(Box::new(a), Box::new(b))
            }
        );

        // (unsat (smt-bool-const "p") (smt-bool-const "q"))
        add_primitive!(
            eg,
            "unsat" = [asserts: SMTBoolValue] -?> () { {
                let st = Storage::new();
                let mut solver = Solver::new(&st, Z3Binary::new("z3").unwrap()).unwrap();
                for b in asserts {
                    solver.assert(b.to_bool(&st)).unwrap();
                }
                if solver.check_sat().unwrap() == SatResult::Unsat {
                    Some(())
                } else {
                    None
                }
            }}
        );
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SMTIntValue {
    Const(String),
    Int64(i64),
    Plus(Box<SMTIntValue>, Box<SMTIntValue>),
    Minus(Box<SMTIntValue>, Box<SMTIntValue>),
    Mult(Box<SMTIntValue>, Box<SMTIntValue>),
}

impl SMTIntValue {
    pub fn to_int<'s>(&self, st: &'s Storage) -> Int<'s> {
        match self {
            SMTIntValue::Const(name) => Int::new_const(st, name).into(),
            SMTIntValue::Int64(num) => Int::new(st, *num),
            SMTIntValue::Plus(a, b) => a.to_int(st) + (b.to_int(st)),
            SMTIntValue::Minus(a, b) => a.to_int(st) - (b.to_int(st)),
            SMTIntValue::Mult(a, b) => a.to_int(st) * b.to_int(st),
        }
    }

    pub fn to_term(&self, termdag: &mut TermDag) -> Term {
        match self {
            SMTIntValue::Const(name) => {
                let arg = termdag.lit(Literal::String(name.clone()));
                termdag.app("smt-int-const".into(), vec![arg])
            }
            SMTIntValue::Int64(value) => {
                let arg = termdag.lit(Literal::Int(*value));
                termdag.app("smt-int".into(), vec![arg])
            }
            SMTIntValue::Plus(a, b) => {
                let a_term = a.to_term(termdag);
                let b_term = b.to_term(termdag);
                termdag.app("+".into(), vec![a_term, b_term])
            }
            SMTIntValue::Minus(a, b) => {
                let a_term = a.to_term(termdag);
                let b_term = b.to_term(termdag);
                termdag.app("-".into(), vec![a_term, b_term])
            }
            SMTIntValue::Mult(a, b) => {
                let a_term = a.to_term(termdag);
                let b_term = b.to_term(termdag);
                termdag.app("*".into(), vec![a_term, b_term])
            }
        }
    }
}

impl BaseValue for SMTIntValue {}

#[derive(Debug)]
pub struct SMTInt;

impl BaseSort for SMTInt {
    type Base = SMTIntValue;

    fn name(&self) -> &str {
        "SMTInt"
    }

    fn reconstruct_termdag(
        &self,
        base_values: &BaseValues,
        value: Value,
        termdag: &mut TermDag,
    ) -> Term {
        let int = base_values.unwrap::<SMTIntValue>(value);
        int.to_term(termdag)
    }

    fn register_primitives(&self, eg: &mut EGraph) {
        // (smt-int-const "p")
        add_primitive!(
            eg,
            "smt-int-const" = |value: S| -> SMTIntValue { { SMTIntValue::Const(value.0) } }
        );
        // (smt-int 1)
        add_primitive!(
            eg,
            "smt-int" = |value: i64| -> SMTIntValue { { SMTIntValue::Int64(value) } }
        );
        // (+ b1 b2)
        add_primitive!(
            eg,
            "+" = |a: SMTIntValue, b: SMTIntValue| -> SMTIntValue {
                SMTIntValue::Plus(Box::new(a), Box::new(b))
            }
        );
        // (- b1 b2)
        add_primitive!(
            eg,
            "-" = |a: SMTIntValue, b: SMTIntValue| -> SMTIntValue {
                SMTIntValue::Minus(Box::new(a), Box::new(b))
            }
        );
        // (* a b)
        add_primitive!(
            eg,
            "*" = |a: SMTIntValue, b: SMTIntValue| -> SMTIntValue {
                SMTIntValue::Mult(Box::new(a), Box::new(b))
            }
        );
    }
}
