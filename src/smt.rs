use crate::smt_real::{SMTReal, SMTRealValue};
use egglog::sort::{F, OrderedFloat, S};
use egglog::{
    BaseValue, EGraph, Term, TermDag, Value,
    prelude::{BaseSort, RustSpan, Span, add_base_sort},
    sort::BaseValues,
    span,
};
use egglog::{add_primitive, ast::Literal};
use smtlib::backend::z3_binary::Z3Binary;
use smtlib::terms::{StaticSorted, exists};
use smtlib::{Bool, Int, Real, SatResultWithModel, Solver, Sorted, Storage};
use smtlib_lowlevel::lexicon::Symbol;
use std::collections::BTreeSet;
use std::{fmt::Debug, hash::Hash};

pub fn add_smt(egraph: &mut EGraph) {
    // important to add ints as base sort before bools bc bools reference ints
    add_base_sort(egraph, SMTInt, span!()).unwrap();
    add_base_sort(egraph, SMTReal, span!()).unwrap();
    add_base_sort(egraph, SMTBool, span!()).unwrap();
    add_base_sort(egraph, SMTValue, span!()).unwrap();
    add_base_sort(egraph, SMTSolved, span!()).unwrap();
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SMTBoolValue {
    Const(String),
    Or(Box<SMTBoolValue>, Box<SMTBoolValue>),
    And(Box<SMTBoolValue>, Box<SMTBoolValue>),
    Not(Box<SMTBoolValue>),
    IntEq(Box<SMTIntValue>, Box<SMTIntValue>),
    RealEq(Box<SMTRealValue>, Box<SMTRealValue>),
    RealExists(String, Box<SMTBoolValue>),
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
            SMTBoolValue::RealExists(var_name, body) => {
                exists(st,Real::new_const(st, var_name), body.to_bool(st))
            }
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
            SMTBoolValue::RealExists(var_name, body) => {
                let var = SMTRealValue::Const(var_name.clone());
                let body_term = body.to_term(termdag);
                let var_term = var.to_term(termdag);
                termdag.app("smt-exists".into(), vec![var_term, body_term])
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
        // (smt-exists <smt-real-const> <smt-real-bool>)
        // e.g. (smt-exists (smt-real-const "x") (smt-real-= (smt-real-const "x") (smt-real 0.0))
        add_primitive!(
            eg,
            "smt-exists" = |var: SMTRealValue, body: SMTBoolValue| -> SMTBoolValue { {
                let SMTRealValue::Const(name) = var else {
                    panic!("smt-exists first argument must be smt-real-const");
                };
                SMTBoolValue::RealExists(name, Box::new(body))
            } }
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

/**
 * SMT Value
 *
 * (smt-value "x" true)
 */

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SMTTerm {
    Bool(bool),
    Int(i64),
    Real(OrderedFloat<f64>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SMTValueValue(String, SMTTerm);

impl SMTValueValue {
    pub fn to_term(&self, termdag: &mut TermDag) -> Term {
        let name_term = termdag.lit(Literal::String(self.0.clone()));
        let term_term = match &self.1 {
            SMTTerm::Bool(b) => termdag.lit(Literal::Bool(*b)),
            SMTTerm::Int(i) => termdag.lit(Literal::Int(*i)),
            SMTTerm::Real(f) => termdag.lit(Literal::Float(*f)),
        };
        termdag.app("smt-value".into(), vec![name_term, term_term])
    }
}
impl BaseValue for SMTValueValue {}

#[derive(Debug)]
pub struct SMTValue;

impl BaseSort for SMTValue {
    type Base = SMTValueValue;

    fn name(&self) -> &str {
        "SMTValue"
    }
    fn reconstruct_termdag(
        &self,
        base_values: &BaseValues,
        value: Value,
        termdag: &mut TermDag,
    ) -> Term {
        let smt_value = base_values.unwrap::<SMTValueValue>(value);
        smt_value.to_term(termdag)
    }
}

/**
 * SMT Solved
 *
 * (unsat)
 * (smt-model (smt-bool-pair "p" true) ...)
 * (smt-value (smt-model ...) "p")
 * (sat? model)
 */

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SMTSolvedValue(Option<Vec<SMTValueValue>>);

impl SMTSolvedValue {
    pub fn get_bool_value(&self, expr: SMTBoolValue) -> Option<bool> {
        if let SMTBoolValue::Const(name) = expr {
            if let Some(vals) = &self.0 {
                for v in vals {
                    if let SMTTerm::Bool(b) = &v.1 {
                        if v.0 == name {
                            return Some(*b);
                        }
                    }
                }
            }
        }
        None
    }

    pub fn get_int_value(&self, expr: SMTIntValue) -> Option<i64> {
        if let SMTIntValue::Const(name) = expr {
            if let Some(vals) = &self.0 {
                for v in vals {
                    if let SMTTerm::Int(i) = &v.1 {
                        if v.0 == name {
                            return Some(*i);
                        }
                    }
                }
            }
        }
        None
    }

    pub fn get_real_value(&self, expr: SMTRealValue) -> Option<OrderedFloat<f64>> {
        if let SMTRealValue::Const(name) = expr {
            if let Some(vals) = &self.0 {
                for v in vals {
                    if let SMTTerm::Real(f) = &v.1 {
                        if v.0 == name {
                            return Some(*f);
                        }
                    }
                }
            }
        }
        None
    }
}

impl BaseValue for SMTSolvedValue {}

#[derive(Debug)]
pub struct SMTSolved;

impl BaseSort for SMTSolved {
    type Base = SMTSolvedValue;

    fn name(&self) -> &str {
        "SMTSolved"
    }

    fn reconstruct_termdag(
        &self,
        base_values: &BaseValues,
        value: Value,
        termdag: &mut TermDag,
    ) -> Term {
        let solved = base_values.unwrap::<SMTSolvedValue>(value);
        match &solved.0 {
            Some(model) => {
                let args = model.iter().map(|v| v.to_term(termdag)).collect::<Vec<_>>();
                termdag.app("smt-model".into(), args)
            }
            None => termdag.app("smt-unsat".into(), vec![]),
        }
    }

    fn register_primitives(&self, eg: &mut EGraph) {
        // (smt-unsat)
        add_primitive!(
            eg,
            "smt-unsat" = || -> SMTSolvedValue { { SMTSolvedValue(None) } }
        );
        // (smt-model v1 v2 ...)
        add_primitive!(
            eg,
            "smt-model" = [values: SMTValueValue] -> SMTSolvedValue { {
                SMTSolvedValue(Some(values.into_iter().collect()))
            } }
        );
        // (smt-sat? model)
        add_primitive!(
            eg,
            "smt-sat?" = |model: SMTSolvedValue| -> bool { { model.0.is_some() } }
        );
        // (smt-value model (smt-bool-const "p"))
        add_primitive!(
            eg,
            "smt-value" = |model: SMTSolvedValue, c: SMTBoolValue| -?> bool { {
                model.get_bool_value(c)
            } }
        );
        add_primitive!(
            eg,
            "smt-value" = |model: SMTSolvedValue, c: SMTIntValue| -?> i64 { {
               model.get_int_value(c)
            } }
        );
        add_primitive!(
            eg,
            "smt-value" = |model: SMTSolvedValue, c: SMTRealValue| -?> F { {
               Some(F::from(model.get_real_value(c)?))
            } }
        );
        // (smt-solve (smt-bool-const "p") (smt-bool-const "q"))
        add_primitive!(
            eg,
            "smt-solve" = [asserts: SMTBoolValue] -> SMTSolvedValue { {
                let st = Storage::new();
                let mut solver = Solver::new(&st, Z3Binary::new("z3").unwrap()).unwrap();
                for b in asserts.clone() {
                    solver.assert(b.to_bool(&st)).unwrap();

                }
                match solver.check_sat_with_model().unwrap() {
                    SatResultWithModel::Sat(model) => {
                        let mut constants = Constants::default();
                        for b in asserts {
                            constants.bool(b);
                        }
                        let mut values = vec![];
                        for name in constants.bools {
                            let Some(term) = model.eval(Bool::new_const(&st, &name)) else {
                                continue;
                            };
                            let smtlib_lowlevel::ast::Term::Identifier(smtlib_lowlevel::ast::QualIdentifier::Identifier(smtlib_lowlevel::ast::Identifier::Simple(Symbol(s)))) = term.term() else {
                                panic!("Expected bool literal");
                            };
                            values.push(SMTValueValue(name, SMTTerm::Bool(s.parse().unwrap())));
                        }
                        for name in constants.ints {
                            let Some(term) = model.eval(Int::new_const(&st, &name)) else {
                                continue;
                            };
                            let smtlib_lowlevel::ast::Term::SpecConstant(smtlib_lowlevel::ast::SpecConstant::Numeral(n)) = term.term() else {
                                panic!("Expected int literal");
                            };
                            values.push(SMTValueValue(name, SMTTerm::Int(n.into_u128().unwrap().try_into().unwrap())));
                        }
                        for name in constants.reals {
                            let Some(term) = model.eval(Real::new_const(&st, &name)) else {
                                continue;
                            };
                            let smtlib_lowlevel::ast::Term::SpecConstant(smtlib_lowlevel::ast::SpecConstant::Decimal(d)) = term.term() else {
                                panic!("Expected real literal");
                            };
                            values.push(SMTValueValue(name, SMTTerm::Real(OrderedFloat(d.0.parse::<f64>().unwrap()))));
                        }
                        SMTSolvedValue(Some(values))
                    }
                    SatResultWithModel::Unsat => SMTSolvedValue(None),
                    SatResultWithModel::Unknown => panic!("SMT solver returned unknown"),
                }
            }}
        );
    }
}

/**
 * all the constants defined
 */
#[derive(Debug, Default)]
struct Constants {
    bools: BTreeSet<String>,
    ints: BTreeSet<String>,
    reals: BTreeSet<String>,
}

impl Constants {
    /**
     * Traverse a bool value and collect all constants
     */
    fn bool(&mut self, v: SMTBoolValue) {
        match v {
            SMTBoolValue::Const(name) => {
                self.bools.insert(name);
            }
            SMTBoolValue::Or(a, b) | SMTBoolValue::And(a, b) => {
                self.bool(*a);
                self.bool(*b);
            }
            SMTBoolValue::Not(a) => {
                self.bool(*a);
            }
            SMTBoolValue::IntEq(a, b) => {
                self.int(*a);
                self.int(*b);
            }
            SMTBoolValue::RealEq(a, b) => {
                self.real(*a);
                self.real(*b);
            }
            SMTBoolValue::RealExists(_, body) => {
                self.bool(*body);
            }
        }
    }

    /**
     * Traverse an int value and collect all constants
     */
    fn int(&mut self, v: SMTIntValue) {
        match v {
            SMTIntValue::Const(name) => {
                self.ints.insert(name);
            }
            SMTIntValue::Int64(_) => {}
            SMTIntValue::Plus(a, b) | SMTIntValue::Minus(a, b) | SMTIntValue::Mult(a, b) => {
                self.int(*a);
                self.int(*b);
            }
        }
    }

    fn real(&mut self, v: SMTRealValue) {
        match v {
            SMTRealValue::Const(name) => {
                self.reals.insert(name);
            }
            SMTRealValue::Float64(_) => {}
            SMTRealValue::Add(a, b)
            | SMTRealValue::Sub(a, b)
            | SMTRealValue::Mul(a, b)
            | SMTRealValue::Div(a, b) => {
                self.real(*a);
                self.real(*b);
            }
            SMTRealValue::Neg(a) => {
                self.real(*a);
            }
        }
    }
}
