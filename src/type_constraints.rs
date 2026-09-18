//! Shared type constraints for experimental primitives with a finite set of
//! exact, nominal signatures.
//!
//! Egglog passes a primitive constraint one [`AtomTerm`] for every input and
//! one final term for the result. The helpers here match that complete call
//! shape against signatures assembled from the sorts currently registered in
//! the [`egglog::TypeInfo`]. Matching uses sort names because these primitives
//! distinguish nominal aliases even when their Rust value representations are
//! identical.

use egglog::constraint::{self, Constraint, ImpossibleConstraint};
use egglog::prelude::Span;
use egglog::{ArcSort, Atom, AtomTerm};

/// Builds a constraint for an overloaded primitive whose valid types can be
/// enumerated exactly.
///
/// `arguments` contains each input term followed by the result term, and
/// `expected` is that total length. Every item yielded by `signatures` must use
/// the same ordering and length. A single compatible signature assigns every
/// position. Multiple compatible signatures wait for surrounding context to
/// select one, and no compatible signatures report a type error.
///
/// An arity mismatch returns an impossible constraint, allowing Egglog to
/// report a normal type error instead of running this matcher with malformed
/// input.
pub(crate) fn exact_signatures(
    name: &str,
    span: &Span,
    arguments: &[AtomTerm],
    expected: usize,
    signatures: impl IntoIterator<Item = Vec<ArcSort>>,
) -> Vec<Box<dyn Constraint<AtomTerm, ArcSort>>> {
    if arguments.len() != expected {
        return vec![constraint::impossible(
            ImpossibleConstraint::ArityMismatch {
                atom: Atom {
                    span: span.clone(),
                    head: name.to_owned(),
                    args: arguments.to_vec(),
                },
                expected,
            },
        )];
    }
    vec![constraint::xor(
        signatures
            .into_iter()
            .map(|signature| {
                debug_assert_eq!(signature.len(), expected);
                constraint::and(
                    arguments
                        .iter()
                        .cloned()
                        .zip(signature)
                        .map(|(argument, sort)| constraint::assign(argument, sort))
                        .collect(),
                )
            })
            .collect(),
    )]
}
