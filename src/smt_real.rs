use egglog::sort::{Boxed, S};
use egglog::{BaseValue, EGraph, Term, TermDag, Value, prelude::BaseSort, sort::BaseValues};
use egglog::{
    add_primitive,
    ast::Literal,
    sort::{F, OrderedFloat},
};
use smtlib::backend::z3_binary::Z3Binary;
use smtlib::funs::Fun;
use smtlib::sorts::Sort;
use smtlib::terms::{IntoWithStorage, StaticSorted};
use smtlib::{Bool, Int, Real, Solver, Sorted, Storage};
use std::{fmt::Debug, hash::Hash};

use crate::SMTBaseValue;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SMTRealValue {
    Const(String),
    Float64(OrderedFloat<f64>),
    Neg(Box<SMTRealValue>),
    Add(Box<SMTRealValue>, Box<SMTRealValue>),
    Sub(Box<SMTRealValue>, Box<SMTRealValue>),
    Mul(Box<SMTRealValue>, Box<SMTRealValue>),
    Div(Box<SMTRealValue>, Box<SMTRealValue>),
    FuncApplication(SMTUFRealValue, Vec<SMTBaseValue>),
}

impl SMTRealValue {
    pub fn to_real<'s>(&self, st: &'s Storage, solver: &mut Solver<'s, Z3Binary>) -> Real<'s> {
        match self {
            SMTRealValue::Const(name) => Real::new_const(st, name).into(),
            SMTRealValue::Float64(num) => num.0.into_with_storage(st),
            SMTRealValue::Neg(x) => -x.to_real(st, solver),
            SMTRealValue::Add(a, b) => a.to_real(st, solver) + b.to_real(st, solver),
            SMTRealValue::Sub(a, b) => a.to_real(st, solver) - b.to_real(st, solver),
            SMTRealValue::Mul(a, b) => a.to_real(st, solver) * b.to_real(st, solver),
            SMTRealValue::Div(a, b) => a.to_real(st, solver) / b.to_real(st, solver),
            SMTRealValue::FuncApplication(func, args) => {
                let smt_fun = func.to_uf(st);
                let _ = solver.declare_fun(&smt_fun);
                todo!()
                // smt_fun
                //     .call(
                //         &args
                //             .iter()
                //             .map(|val| match val {
                //                 SMTBaseValue::BoolValue(val) => {
                //                     val.to_bool(st, solver).into_dynamic()
                //                 }
                //                 SMTBaseValue::IntValue(val) => {
                //                     val.to_int(st, solver).into_dynamic()
                //                 }
                //                 SMTBaseValue::RealValue(val) => {
                //                     val.to_real(st, solver).into_dynamic()
                //                 }
                //             })
                //             .collect::<Vec<_>>()[..],
                //     )
                //     .unwrap()
                //     .as_real()
                //     .unwrap()
            }
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
            SMTRealValue::FuncApplication(func, args) => {
                let func_term = func.to_term(termdag);
                let mut children: Vec<Term> = args.iter().map(|arg| arg.to_term(termdag)).collect();
                children.insert(0, func_term);
                termdag.app("smt-call".into(), children)
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SMTUFRealValue {
    Declaration(String, Vec<String>),
}

impl SMTUFRealValue {
    pub fn to_uf<'s>(&self, st: &'s Storage) -> Fun<'s> {
        match self {
            SMTUFRealValue::Declaration(name, types) => {
                let sorts: Result<Vec<Sort>, String> = types
                    .iter()
                    .map(|type_name| match type_name.as_str() {
                        "Int" => Ok(Int::sort()),
                        "Bool" => Ok(Bool::sort()),
                        "Real" => Ok(Real::sort()),
                        other => Err(format!("unknown type {other}")),
                    })
                    .collect();
                Fun::new(st, name.to_string(), sorts.unwrap(), Real::sort())
            }
        }
    }

    pub fn to_term(&self, termdag: &mut TermDag) -> Term {
        match self {
            SMTUFRealValue::Declaration(name, types) => {
                let name = termdag.lit(Literal::String(name.clone()));
                let mut children: Vec<Term> = types
                    .iter()
                    .map(|type_name| termdag.lit(Literal::String(type_name.clone())))
                    .collect();
                children.insert(0, name);
                termdag.app("smt-fn-real".into(), children)
            }
        }
    }
}

impl BaseValue for SMTUFRealValue {}

#[derive(Debug)]
pub struct SMTUFReal;
impl BaseSort for SMTUFReal {
    type Base = SMTUFRealValue;

    fn name(&self) -> &str {
        "SMTUFReal"
    }

    fn reconstruct_termdag(
        &self,
        base_values: &BaseValues,
        value: Value,
        termdag: &mut TermDag,
    ) -> Term {
        let uf = base_values.unwrap::<SMTUFRealValue>(value);
        uf.to_term(termdag)
    }

    fn register_primitives(&self, eg: &mut EGraph) {
        // (smt-uf-real "f" "Int" "Int")
        add_primitive!(
            eg,
            "smt-fn-real" = [args: S] -> SMTUFRealValue { {
                let mut args_iter = args.into_iter();
                let name = args_iter.next().unwrap();
                let types: Vec<String> = args_iter.map(Boxed::into_inner).collect();
                SMTUFRealValue::Declaration(name.0, types)
            } }
        );
    }
}
