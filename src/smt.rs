use egglog::sort::S;
use egglog::{add_primitive, ast::Literal};
use std::{fmt::Debug, hash::Hash};

use egglog::{
    BaseValue, EGraph, Term, TermDag, Value,
    prelude::{BaseSort, RustSpan, Span, add_base_sort},
    sort::BaseValues,
    span,
};

pub fn add_smt(egraph: &mut EGraph) {
    add_base_sort(egraph, SMTBool, span!()).unwrap();
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SMTBoolValue {
    Const(String),
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

        match bool {
            SMTBoolValue::Const(name) => {
                let arg = termdag.lit(Literal::String(name));
                termdag.app("smt-bool-const".into(), vec![arg])
            }
        }
    }

    fn register_primitives(&self, eg: &mut EGraph) {
        // (smt-bool-const "p")
        add_primitive!(
            eg,
            "smt-bool-const" = |value: S| -> SMTBoolValue { { SMTBoolValue::Const(value.0) } }
        );
    }
}
