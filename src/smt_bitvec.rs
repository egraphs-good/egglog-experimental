use egglog::sort::S;
use egglog::{BaseValue, EGraph, Term, TermDag, Value, prelude::BaseSort, sort::BaseValues};
use egglog::{add_primitive, ast::Literal};
use smtlib::terms::STerm;
use smtlib::{Bool, Storage};
use smtlib_lowlevel::ast;
use std::{fmt::Debug, hash::Hash};

/// SMT BitVector value representation
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SMTBitVecValue {
    /// A symbolic bitvector constant with name and bit width
    Const(String, u32),
    /// A concrete bitvector literal with value and bit width
    Literal(i64, u32),
    /// Addition modulo 2^m
    BvAdd(Box<SMTBitVecValue>, Box<SMTBitVecValue>),
    /// Bitwise XOR
    BvXor(Box<SMTBitVecValue>, Box<SMTBitVecValue>),
    /// Bitwise AND
    BvAnd(Box<SMTBitVecValue>, Box<SMTBitVecValue>),
    /// Bitwise NOT (one's complement)
    BvNot(Box<SMTBitVecValue>),
}

impl SMTBitVecValue {

    /// Get the size of the AST rooted at this bitvector value
    pub fn ast_size(&self) -> usize {
        match self {
            SMTBitVecValue::Const(_, _) | SMTBitVecValue::Literal(_, _) => 1,
            SMTBitVecValue::BvAdd(a, b)
            | SMTBitVecValue::BvXor(a, b)
            | SMTBitVecValue::BvAnd(a, b) => 1 + a.ast_size() + b.ast_size(),
            SMTBitVecValue::BvNot(a) => 1 + a.ast_size(),
        }
    }

    /// Get the bit width of this bitvector
    pub fn width(&self) -> u32 {
        match self {
            SMTBitVecValue::Const(_, w) => *w,
            SMTBitVecValue::Literal(_, w) => *w,
            SMTBitVecValue::BvAdd(a, _) => a.width(),
            SMTBitVecValue::BvXor(a, _) => a.width(),
            SMTBitVecValue::BvAnd(a, _) => a.width(),
            SMTBitVecValue::BvNot(a) => a.width(),
        }
    }

    /// Convert to a smtlib STerm
    pub fn to_sterm<'s>(&self, st: &'s Storage) -> STerm<'s> {
        use smtlib_lowlevel::ast::{Identifier, Index, QualIdentifier, Term as AstTerm};
        use smtlib_lowlevel::lexicon::{Numeral, Symbol};

        match self {
            SMTBitVecValue::Const(name, w) => {
                // Create (_ BitVec w) sort
                let bv_sort = ast::Sort::Sort(Identifier::Indexed(
                    Symbol("BitVec"),
                    st.alloc_slice(&[Index::Numeral(Numeral::from_usize(*w as usize))]),
                ));
                let name = st.alloc_str(name);
                let qual_id = QualIdentifier::Sorted(Identifier::Simple(Symbol(name)), bv_sort);
                STerm::new(st, AstTerm::Identifier(qual_id))
            }
            SMTBitVecValue::Literal(value, w) => {
                // Use indexed identifier format: (_ bvN width)
                // e.g., (_ bv0 64) for a 64-bit zero
                // Note: bvN is a single symbol where N is the decimal value
                let bv_symbol = format!("bv{}", *value as u64);
                let ident = Identifier::Indexed(
                    Symbol(st.alloc_str(&bv_symbol)),
                    st.alloc_slice(&[Index::Numeral(Numeral::from_usize(*w as usize))]),
                );
                let qual_id = QualIdentifier::Identifier(ident);
                STerm::new(st, AstTerm::Identifier(qual_id))
            }
            SMTBitVecValue::BvAdd(a, b) => self.binary_op(st, "bvadd", a, b),
            SMTBitVecValue::BvXor(a, b) => self.binary_op(st, "bvxor", a, b),
            SMTBitVecValue::BvAnd(a, b) => self.binary_op(st, "bvand", a, b),
            SMTBitVecValue::BvNot(a) => self.unary_op(st, "bvnot", a),
        }
    }

    fn unary_op<'s>(&self, st: &'s Storage, op: &'static str, a: &SMTBitVecValue) -> STerm<'s> {
        use smtlib_lowlevel::ast::{Identifier, QualIdentifier, Term as AstTerm};
        use smtlib_lowlevel::lexicon::Symbol;

        let qual_id = QualIdentifier::Identifier(Identifier::Simple(Symbol(op)));
        let a_term = a.to_sterm(st);
        STerm::new(
            st,
            AstTerm::Application(qual_id, st.alloc_slice(&[a_term.term()])),
        )
    }

    fn binary_op<'s>(
        &self,
        st: &'s Storage,
        op: &'static str,
        a: &SMTBitVecValue,
        b: &SMTBitVecValue,
    ) -> STerm<'s> {
        use smtlib_lowlevel::ast::{Identifier, QualIdentifier, Term as AstTerm};
        use smtlib_lowlevel::lexicon::Symbol;

        let qual_id = QualIdentifier::Identifier(Identifier::Simple(Symbol(op)));
        let a_term = a.to_sterm(st);
        let b_term = b.to_sterm(st);
        STerm::new(
            st,
            AstTerm::Application(qual_id, st.alloc_slice(&[a_term.term(), b_term.term()])),
        )
    }

    /// Create a Bool term from a comparison operation
    pub fn to_bool_cmp<'s>(
        &self,
        st: &'s Storage,
        op: &'static str,
        other: &SMTBitVecValue,
    ) -> Bool<'s> {
        use smtlib_lowlevel::ast::{Identifier, QualIdentifier, Term as AstTerm};
        use smtlib_lowlevel::lexicon::Symbol;

        let qual_id = QualIdentifier::Identifier(Identifier::Simple(Symbol(op)));
        let a_term = self.to_sterm(st);
        let b_term = other.to_sterm(st);
        let cmp_term =
            AstTerm::Application(qual_id, st.alloc_slice(&[a_term.term(), b_term.term()]));
        STerm::new(st, cmp_term).into()
    }

    pub fn to_term(&self, termdag: &mut TermDag) -> Term {
        match self {
            SMTBitVecValue::Const(name, width) => {
                let name_arg = termdag.lit(Literal::String(name.clone()));
                let width_arg = termdag.lit(Literal::Int(*width as i64));
                termdag.app("smt-bv-const".into(), vec![name_arg, width_arg])
            }
            SMTBitVecValue::Literal(value, width) => {
                let value_arg = termdag.lit(Literal::Int(*value));
                let width_arg = termdag.lit(Literal::Int(*width as i64));
                termdag.app("smt-bv".into(), vec![value_arg, width_arg])
            }
            SMTBitVecValue::BvAdd(a, b) => {
                let a_term = a.to_term(termdag);
                let b_term = b.to_term(termdag);
                termdag.app("bvadd".into(), vec![a_term, b_term])
            }
            SMTBitVecValue::BvXor(a, b) => {
                let a_term = a.to_term(termdag);
                let b_term = b.to_term(termdag);
                termdag.app("bvxor".into(), vec![a_term, b_term])
            }
            SMTBitVecValue::BvAnd(a, b) => {
                let a_term = a.to_term(termdag);
                let b_term = b.to_term(termdag);
                termdag.app("bvand".into(), vec![a_term, b_term])
            }
            SMTBitVecValue::BvNot(a) => {
                let a_term = a.to_term(termdag);
                termdag.app("bvnot".into(), vec![a_term])
            }
        }
    }
}

impl BaseValue for SMTBitVecValue {}

#[derive(Debug)]
pub struct SMTBitVec;

impl BaseSort for SMTBitVec {
    type Base = SMTBitVecValue;

    fn name(&self) -> &str {
        "SMTBitVec"
    }

    fn reconstruct_termdag(
        &self,
        base_values: &BaseValues,
        value: Value,
        termdag: &mut TermDag,
    ) -> Term {
        let bv = base_values.unwrap::<SMTBitVecValue>(value);
        bv.to_term(termdag)
    }

    fn register_primitives(&self, eg: &mut EGraph) {
        // (smt-bv-const "x" 64) - creates a symbolic bitvector constant of width 64
        add_primitive!(
            eg,
            "smt-bv-const" = |name: S, width: i64| -> SMTBitVecValue {
                SMTBitVecValue::Const(name.0, width as u32)
            }
        );

        // (smt-bv 42 64) - creates a bitvector literal with value 42 and width 64
        add_primitive!(
            eg,
            "smt-bv" = |value: i64, width: i64| -> SMTBitVecValue {
                SMTBitVecValue::Literal(value, width as u32)
            }
        );

        // (bvadd a b) - addition modulo 2^m
        add_primitive!(
            eg,
            "bvadd" = |a: SMTBitVecValue, b: SMTBitVecValue| -> SMTBitVecValue {
                SMTBitVecValue::BvAdd(Box::new(a), Box::new(b))
            }
        );

        // (bvxor a b) - bitwise XOR
        add_primitive!(
            eg,
            "bvxor" = |a: SMTBitVecValue, b: SMTBitVecValue| -> SMTBitVecValue {
                SMTBitVecValue::BvXor(Box::new(a), Box::new(b))
            }
        );

        // (bvand a b) - bitwise AND
        add_primitive!(
            eg,
            "bvand" = |a: SMTBitVecValue, b: SMTBitVecValue| -> SMTBitVecValue {
                SMTBitVecValue::BvAnd(Box::new(a), Box::new(b))
            }
        );

        // (bvnot a) - bitwise NOT (one's complement)
        add_primitive!(
            eg,
            "bvnot" = |a: SMTBitVecValue| -> SMTBitVecValue { SMTBitVecValue::BvNot(Box::new(a)) }
        );
    }
}
