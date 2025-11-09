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
use smtlib::{Bool, SatResult, Solver, Storage};
use std::{fmt::Debug, hash::Hash};

pub fn add_smt(egraph: &mut EGraph) {
    add_base_sort(egraph, SMTBool, span!()).unwrap();
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SMTBoolValue {
    Const(String),
    Or(Box<SMTBoolValue>, Box<SMTBoolValue>),
    And(Box<SMTBoolValue>, Box<SMTBoolValue>),
    Not(Box<SMTBoolValue>),
}

impl SMTBoolValue {
    pub fn to_bool<'s>(&self, st: &'s Storage) -> Bool<'s> {
        match self {
            SMTBoolValue::Const(name) => Bool::new_const(st, name).into(),
            SMTBoolValue::Or(a, b) => a.to_bool(st) | (b.to_bool(st)),
            SMTBoolValue::And(a, b) => a.to_bool(st) & (b.to_bool(st)),
            SMTBoolValue::Not(a) => !a.to_bool(st),
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
