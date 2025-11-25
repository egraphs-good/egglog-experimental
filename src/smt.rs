use crate::smt_real::{SMTReal, SMTRealValue};
use egglog::constraint::{self, Constraint, TypeConstraint};
use egglog::sort::{BaseValues, Boxed, F, OrderedFloat, S};
use egglog::{ArcSort, AtomTerm, ExecutionState, Primitive, TypeInfo};
use egglog::{
    BaseValue, EGraph, Term, TermDag, Value,
    prelude::{BaseSort, RustSpan, Span, add_base_sort},
    span,
};
use egglog::{add_primitive, ast::Literal};
use smtlib::backend::z3_binary::Z3Binary;
use smtlib::funs::Fun;
use smtlib::sorts::Sort;
use smtlib::terms::StaticSorted;
use smtlib::{Bool, Int, Real, SatResultWithModel, Solver, Sorted, Storage};
use smtlib_lowlevel::lexicon::Symbol;
use std::any::TypeId;
use std::collections::BTreeSet;
use std::{fmt::Debug, hash::Hash};

pub fn add_smt(egraph: &mut EGraph) {
    // important to add ints as base sort before bools bc bools reference ints
    add_base_sort(egraph, SMTUFInt, span!()).unwrap();
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
    RealLt(Box<SMTRealValue>, Box<SMTRealValue>),
    RealGt(Box<SMTRealValue>, Box<SMTRealValue>),
    RealLte(Box<SMTRealValue>, Box<SMTRealValue>),
    RealGte(Box<SMTRealValue>, Box<SMTRealValue>),
}

impl SMTBoolValue {
    pub fn to_bool<'s>(&self, st: &'s Storage, solver: &mut Solver<'s, Z3Binary>) -> Bool<'s> {
        match self {
            SMTBoolValue::Const(name) => Bool::new_const(st, name).into(),
            SMTBoolValue::Or(a, b) => a.to_bool(st, solver) | (b.to_bool(st, solver)),
            SMTBoolValue::And(a, b) => a.to_bool(st, solver) & (b.to_bool(st, solver)),
            SMTBoolValue::Not(a) => !a.to_bool(st, solver),
            SMTBoolValue::IntEq(a, b) => a.to_int(st, solver)._eq(b.to_int(st, solver)),
            SMTBoolValue::RealEq(a, b) => a.to_real(st)._eq(b.to_real(st)),
            SMTBoolValue::RealLt(a, b) => a.to_real(st).lt(b.to_real(st)),
            SMTBoolValue::RealGt(a, b) => a.to_real(st).gt(b.to_real(st)),
            SMTBoolValue::RealLte(a, b) => a.to_real(st).le(b.to_real(st)),
            SMTBoolValue::RealGte(a, b) => a.to_real(st).ge(b.to_real(st)),
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
            SMTBoolValue::RealLt(a, b) => {
                let a_term = a.to_term(termdag);
                let b_term = b.to_term(termdag);
                termdag.app("smt-real-<".into(), vec![a_term, b_term])
            }
            SMTBoolValue::RealGt(a, b) => {
                let a_term = a.to_term(termdag);
                let b_term = b.to_term(termdag);
                termdag.app("smt-real->".into(), vec![a_term, b_term])
            }
            SMTBoolValue::RealLte(a, b) => {
                let a_term = a.to_term(termdag);
                let b_term = b.to_term(termdag);
                termdag.app("smt-real-<=".into(), vec![a_term, b_term])
            }
            SMTBoolValue::RealGte(a, b) => {
                let a_term = a.to_term(termdag);
                let b_term = b.to_term(termdag);
                termdag.app("smt-real->=".into(), vec![a_term, b_term])
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
        // (smt-real-< a b)
        add_primitive!(
            eg,
            "smt-real-<" = |a: SMTRealValue, b: SMTRealValue| -> SMTBoolValue {
                SMTBoolValue::RealLt(Box::new(a), Box::new(b))
            }
        );
        // (smt-real-> a b)
        add_primitive!(
            eg,
            "smt-real->" = |a: SMTRealValue, b: SMTRealValue| -> SMTBoolValue {
                SMTBoolValue::RealGt(Box::new(a), Box::new(b))
            }
        );
        // (smt-real-<= a b)
        add_primitive!(
            eg,
            "smt-real-<=" = |a: SMTRealValue, b: SMTRealValue| -> SMTBoolValue {
                SMTBoolValue::RealLte(Box::new(a), Box::new(b))
            }
        );
        // (smt-real->= a b)
        add_primitive!(
            eg,
            "smt-real->=" = |a: SMTRealValue, b: SMTRealValue| -> SMTBoolValue {
                SMTBoolValue::RealGte(Box::new(a), Box::new(b))
            }
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
    FuncApplication(SMTUFIntValue, Vec<SMTBaseValue>),
}

impl SMTIntValue {
    pub fn to_int<'s>(&self, st: &'s Storage, solver: &mut Solver<'s, Z3Binary>) -> Int<'s> {
        match self {
            SMTIntValue::Const(name) => Int::new_const(st, name).into(),
            SMTIntValue::Int64(num) => Int::new(st, *num),
            SMTIntValue::Plus(a, b) => a.to_int(st, solver) + b.to_int(st, solver),
            SMTIntValue::Minus(a, b) => a.to_int(st, solver) - b.to_int(st, solver),
            SMTIntValue::Mult(a, b) => a.to_int(st, solver) * b.to_int(st, solver),
            SMTIntValue::FuncApplication(func, args) => {
                let smt_fun = func.to_uf(st);
                let _ = solver.declare_fun(&smt_fun);
                smt_fun
                    .call(
                        &args
                            .iter()
                            .map(|val| match val {
                                SMTBaseValue::BoolValue(val) => {
                                    val.to_bool(st, solver).into_dynamic()
                                }
                                SMTBaseValue::IntValue(val) => {
                                    val.to_int(st, solver).into_dynamic()
                                }
                                SMTBaseValue::RealValue(val) => val.to_real(st).into_dynamic(),
                            })
                            .collect::<Vec<_>>()[..],
                    )
                    .unwrap()
                    .as_int()
                    .unwrap()
            }
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
            SMTIntValue::FuncApplication(func, args) => {
                let func_term = func.to_term(termdag);
                let mut children: Vec<Term> = args.iter().map(|arg| arg.to_term(termdag)).collect();
                children.insert(0, func_term);
                termdag.app("smt-call".into(), children)
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
                    let smt_bool = b.to_bool(&st, &mut solver);
                    solver.assert(smt_bool).unwrap();

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
                            let real_value = extract_real_value(term.term());
                            values.push(SMTValueValue(name, SMTTerm::Real(OrderedFloat(real_value))));
                        }
                        SMTSolvedValue(Some(values))
                    }
                    SatResultWithModel::Unsat => SMTSolvedValue(None),
                    SatResultWithModel::Unknown => panic!("SMT solver returned unknown"),
                }
            }}
        );
        // (smt-call f arg1 arg2 ...)
        eg.add_primitive(UFApply {
            args: eg
                .get_arcsorts_by(|s| {
                    s.value_type() == Some(TypeId::of::<SMTIntValue>())
                        || s.value_type() == Some(TypeId::of::<SMTBoolValue>())
                        || s.value_type() == Some(TypeId::of::<SMTRealValue>())
                })
                .clone(),
            out_sort: eg
                .get_arcsort_by(|s| s.value_type() == Some(TypeId::of::<SMTIntValue>()))
                .clone(),
            fun_sort: eg
                .get_arcsort_by(|s| s.value_type() == Some(TypeId::of::<SMTUFIntValue>()))
                .clone(),
        });
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SMTUFIntValue {
    Declaration(String, Vec<String>),
}

impl SMTUFIntValue {
    pub fn to_uf<'s>(&self, st: &'s Storage) -> Fun<'s> {
        match self {
            SMTUFIntValue::Declaration(name, types) => {
                let sorts: Result<Vec<Sort>, String> = types
                    .iter()
                    .map(|type_name| match type_name.as_str() {
                        "Int" => Ok(Int::sort()),
                        "Bool" => Ok(Bool::sort()),
                        other => Err(format!("unknown type {other}")),
                    })
                    .collect();
                Fun::new(st, name.to_string(), sorts.unwrap(), Int::sort())
            }
        }
    }

    pub fn to_term(&self, termdag: &mut TermDag) -> Term {
        match self {
            SMTUFIntValue::Declaration(name, types) => {
                let name = termdag.lit(Literal::String(name.clone()));
                let mut children: Vec<Term> = types
                    .iter()
                    .map(|type_name| termdag.lit(Literal::String(type_name.clone())))
                    .collect();
                children.insert(0, name);
                termdag.app("smt-fn-int".into(), children)
            }
        }
    }
}

impl BaseValue for SMTUFIntValue {}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SMTBaseValue {
    BoolValue(SMTBoolValue),
    IntValue(SMTIntValue),
    RealValue(SMTRealValue),
}

impl BaseValue for SMTBaseValue {}

impl SMTBaseValue {
    pub fn to_term(&self, termdag: &mut TermDag) -> Term {
        match self {
            SMTBaseValue::BoolValue(arg) => arg.to_term(termdag),
            SMTBaseValue::IntValue(arg) => arg.to_term(termdag),
            SMTBaseValue::RealValue(arg) => arg.to_term(termdag),
        }
    }
}

#[derive(Debug)]
pub struct SMTUFInt;
impl BaseSort for SMTUFInt {
    type Base = SMTUFIntValue;

    fn name(&self) -> &str {
        "SMTUFInt"
    }

    fn reconstruct_termdag(
        &self,
        base_values: &BaseValues,
        value: Value,
        termdag: &mut TermDag,
    ) -> Term {
        let uf = base_values.unwrap::<SMTUFIntValue>(value);
        uf.to_term(termdag)
    }

    fn register_primitives(&self, eg: &mut EGraph) {
        // (smt-uf-int "f" "Int" "Int")
        add_primitive!(
            eg,
            "smt-fn-int" = [args: S] -> SMTUFIntValue { {
                let mut args_iter = args.into_iter();
                let name = args_iter.next().unwrap();
                let types: Vec<String> = args_iter.map(Boxed::into_inner).collect();
                SMTUFIntValue::Declaration(name.0, types)
            } }
        );
    }
}

#[derive(Clone)]
struct UFApply {
    args: Vec<ArcSort>,
    out_sort: ArcSort,
    fun_sort: ArcSort,
}
impl Primitive for UFApply {
    fn name(&self) -> &str {
        "smt-call"
    }
    fn get_type_constraints(&self, _span: &Span) -> Box<dyn TypeConstraint> {
        SMTUFTypeConstraint::default()
            .with_all_arguments_possible_sorts(self.args.clone())
            .with_output_sort(self.out_sort.clone())
            .with_func_sort(self.fun_sort.clone())
            .into_box()
    }
    fn apply(&self, exec_state: &mut ExecutionState, args: &[Value]) -> Option<Value> {
        let (fun_val, args) = args.split_first().unwrap();
        let fun = exec_state.base_values().unwrap::<SMTUFIntValue>(*fun_val);
        let arg_vals: Vec<SMTBaseValue> = match fun.clone() {
            SMTUFIntValue::Declaration(name, arg_types) => {
                assert!(
                    arg_types.len() == args.len(),
                    "Expected function {} to be called with {} args, but got {}",
                    name,
                    arg_types.len(),
                    args.len()
                );
                arg_types
                    .iter()
                    .zip(args)
                    .map(|(arg_type, arg)| match arg_type.as_str() {
                        "Int" => {
                            let int_val = exec_state.base_values().unwrap::<SMTIntValue>(*arg);
                            SMTBaseValue::IntValue(int_val)
                        }
                        "Bool" => SMTBaseValue::BoolValue(
                            exec_state.base_values().unwrap::<SMTBoolValue>(*arg),
                        ),
                        "Real" => SMTBaseValue::RealValue(
                            exec_state.base_values().unwrap::<SMTRealValue>(*arg),
                        ),
                        other => panic!("unknown type {other}"),
                    })
                    .collect::<Vec<SMTBaseValue>>()
            }
        };

        let fun_app: SMTIntValue = { SMTIntValue::FuncApplication(fun, arg_vals) };
        Some(exec_state.base_values().get::<SMTIntValue>(fun_app))
    }
}

/// A type constraint that requires all arguments to have one of the SMT base types.
pub struct SMTUFTypeConstraint {
    func_sort: Option<ArcSort>,
    possible_sorts: Vec<ArcSort>,
    output: Option<ArcSort>,
}

impl Default for SMTUFTypeConstraint {
    /// Creates the `SMTUFTypeConstraint`.
    fn default() -> Self {
        SMTUFTypeConstraint {
            func_sort: None,
            possible_sorts: Vec::new(),
            output: None,
        }
    }
}

impl SMTUFTypeConstraint {
    /// Converts self into a boxed type constraint.
    pub fn into_box(self) -> Box<dyn TypeConstraint> {
        Box::new(self)
    }

    /// Requires function being called to be the given sort.
    pub fn with_func_sort(mut self, sort: ArcSort) -> Self {
        self.func_sort = Some(sort);
        self
    }

    /// Requires all arguments to be one of the given sorts.
    pub fn with_all_arguments_possible_sorts(mut self, sort: Vec<ArcSort>) -> Self {
        self.possible_sorts = sort;
        self
    }

    /// Requires the output argument to have the given sort.
    pub fn with_output_sort(mut self, output_sort: ArcSort) -> Self {
        self.output = Some(output_sort);
        self
    }
}

impl TypeConstraint for SMTUFTypeConstraint {
    fn get(
        &self,
        mut arguments: &[AtomTerm],
        _typeinfo: &TypeInfo,
    ) -> Vec<Box<dyn Constraint<AtomTerm, ArcSort>>> {
        if arguments.is_empty() {
            panic!("all arguments should have length > 0")
        }

        let mut constraints = vec![];
        if let Some(output) = self.output.clone() {
            let (out, inputs) = arguments.split_last().unwrap();
            constraints.push(constraint::assign(out.clone(), output));
            arguments = inputs;
        }

        if let Some(func_sort) = self.func_sort.clone() {
            let (func, inputs) = arguments.split_first().unwrap();
            constraints.push(constraint::assign(func.clone(), func_sort));
            arguments = inputs;
        }

        constraints.extend(arguments.iter().cloned().map(|arg| {
            constraint::xor(
                self.possible_sorts
                    .clone()
                    .into_iter()
                    .map(|sort| constraint::assign(arg.clone(), sort.clone()))
                    .collect(),
            )
        }));
        constraints
    }
}

fn extract_real_value(term: &smtlib_lowlevel::ast::Term) -> f64 {
    match term {
        // Positive decimal: 1.5
        smtlib_lowlevel::ast::Term::SpecConstant(smtlib_lowlevel::ast::SpecConstant::Decimal(
            d,
        )) => d.0.parse::<f64>().unwrap(),
        // Positive numeral: 42
        smtlib_lowlevel::ast::Term::SpecConstant(smtlib_lowlevel::ast::SpecConstant::Numeral(
            n,
        )) => n.into_u128().unwrap() as f64,
        // Negative numbers: (- 1.5) or (- 42)
        smtlib_lowlevel::ast::Term::Application(identifier, arguments) => {
            if let smtlib_lowlevel::ast::QualIdentifier::Identifier(
                smtlib_lowlevel::ast::Identifier::Simple(smtlib_lowlevel::lexicon::Symbol(op)),
            ) = identifier
            {
                if *op == "-" && arguments.len() == 1 {
                    return -extract_real_value(arguments[0]);
                }
            }
            // Rational numbers: (/ 1 3) represents 1/3
            if let smtlib_lowlevel::ast::QualIdentifier::Identifier(
                smtlib_lowlevel::ast::Identifier::Simple(smtlib_lowlevel::lexicon::Symbol(op)),
            ) = identifier
            {
                if *op == "/" && arguments.len() == 2 {
                    let numerator = extract_real_value(arguments[0]);
                    let denominator = extract_real_value(arguments[1]);
                    return numerator / denominator;
                }
            }
            panic!(
                "Unsupported real application format: identifier={identifier:?}, arguments={arguments:?}",
            );
        }
        _ => panic!("Unsupported real term format: {term:?}",),
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
            SMTBoolValue::RealEq(a, b)
            | SMTBoolValue::RealLt(a, b)
            | SMTBoolValue::RealGt(a, b)
            | SMTBoolValue::RealLte(a, b)
            | SMTBoolValue::RealGte(a, b) => {
                self.real(*a);
                self.real(*b);
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
            SMTIntValue::FuncApplication(_, args) => {
                for arg in args {
                    match arg {
                        SMTBaseValue::BoolValue(bool_value) => self.bool(bool_value),
                        SMTBaseValue::IntValue(int_value) => self.int(int_value),
                        SMTBaseValue::RealValue(int_value) => self.real(int_value),
                    }
                }
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
