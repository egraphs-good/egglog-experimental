//! Shared type constraints for experimental primitives with a finite set of
//! exact, nominal signatures.
//!
//! Egglog passes a primitive constraint one [`AtomTerm`] for every input and
//! one final term for the result. The helpers here match that complete call
//! shape against signatures assembled from the sorts currently registered in
//! the [`egglog::TypeInfo`]. Matching uses sort names because these primitives
//! distinguish nominal aliases even when their Rust value representations are
//! identical.

use egglog::constraint::{self, Assignment, Constraint, ConstraintError, ImpossibleConstraint};
use egglog::prelude::Span;
use egglog::{ArcSort, Atom, AtomTerm};

/// Resolves a primitive call against a deterministic list of complete
/// input-plus-result signatures.
#[derive(Clone)]
struct ExactSignatures {
    /// Input terms followed by the primitive's result term.
    arguments: Vec<AtomTerm>,
    /// Candidate sorts in the same order as `arguments`.
    signatures: Vec<Vec<ArcSort>>,
}

impl Constraint<AtomTerm, ArcSort> for ExactSignatures {
    fn update(
        &mut self,
        assignment: &mut Assignment<AtomTerm, ArcSort>,
        _key: fn(&ArcSort) -> &str,
    ) -> Result<bool, ConstraintError<AtomTerm, ArcSort>> {
        let mut errors = Vec::new();
        // First discard every signature that conflicts with a sort already
        // assigned by another constraint. Preserve the individual conflicts
        // so an impossible call reports why no candidate survived.
        let compatible: Vec<_> = self
            .signatures
            .iter()
            .filter(|signature| {
                for (argument, expected) in self.arguments.iter().zip(signature.iter()) {
                    if let Some(actual) = assignment.get(argument)
                        && actual.name() != expected.name()
                    {
                        errors.push(ConstraintError::InconsistentConstraint(
                            argument.clone(),
                            expected.clone(),
                            actual.clone(),
                        ));
                        return false;
                    }
                }
                true
            })
            .collect();

        if compatible.is_empty() {
            // An empty signature list means the registered nominal sorts do
            // not contain any valid overload for this primitive. Report the
            // call's result as unconstrained instead of constructing an empty
            // `NoConstraintSatisfied`, whose rendered diagnostic has no
            // explanation beneath "all alternatives failed".
            if errors.is_empty() {
                return Err(ConstraintError::UnconstrainedVar(
                    self.arguments.last().unwrap().clone(),
                ));
            }
            return Err(ConstraintError::NoConstraintSatisfied(errors));
        }

        let mut changed = false;
        // A position shared by every surviving signature is no longer
        // ambiguous, so publish it immediately and let the solver propagate
        // that information to neighboring constraints.
        for index in 0..self.signatures[0].len() {
            let argument = self.arguments[index].clone();
            if assignment.get(&argument).is_some() {
                continue;
            }
            let first = &compatible[0][index];
            if compatible
                .iter()
                .all(|signature| signature[index].name() == first.name())
            {
                assignment.insert(argument, first.clone());
                changed = true;
            }
        }
        Ok(changed)
    }

    fn pretty(&self) -> String {
        self.signatures
            .iter()
            .map(|signature| {
                signature
                    .iter()
                    .map(|sort| sort.name())
                    .collect::<Vec<_>>()
                    .join(" -> ")
            })
            .collect::<Vec<_>>()
            .join(" \\/ ")
    }
}

/// Builds a constraint for an overloaded primitive whose valid types can be
/// enumerated exactly.
///
/// `arguments` contains each input term followed by the result term, and
/// `expected` is that total length. Every item yielded by `signatures` must use
/// the same ordering and length. The constraint publishes a sort only when all
/// surviving signatures agree at that position. It never chooses among
/// distinct nominal aliases, so unresolved ambiguity remains an ordinary type
/// inference error for surrounding context to resolve.
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
    let mut signatures: Vec<_> = signatures.into_iter().collect();
    for signature in &signatures {
        debug_assert_eq!(signature.len(), expected);
    }
    // TypeInfo iteration order is not an API guarantee. Sort and deduplicate
    // candidates so propagation and diagnostics are reproducible.
    signatures.sort_by(|left, right| {
        left.iter()
            .map(|sort| sort.name())
            .cmp(right.iter().map(|sort| sort.name()))
    });
    signatures.dedup_by(|left, right| {
        left.iter()
            .map(|sort| sort.name())
            .eq(right.iter().map(|sort| sort.name()))
    });
    vec![Box::new(ExactSignatures {
        arguments: arguments.to_vec(),
        signatures,
    })]
}
