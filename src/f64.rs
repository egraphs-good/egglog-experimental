//! Additional predicates for the built-in `f64` sort.

use egglog::{EGraph, Term, TermDag, TermId, add_primitive_with_validator, ast::Literal, sort::F};

pub(crate) fn add_f64_primitives(egraph: &mut EGraph) {
    let validator = |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
        let [value] = args else { return None };
        let value = match termdag.get(*value) {
            Term::Lit(Literal::Float(value)) => *value,
            _ => return None,
        };
        value.is_finite().then(|| termdag.lit(Literal::Unit))
    };
    add_primitive_with_validator!(
        egraph,
        "f64-is-finite" = |value: F| -?> () {
            value.0.is_finite().then_some(())
        },
        validator
    );
}
