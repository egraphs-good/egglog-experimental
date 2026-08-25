//! Compact DAG printing for [`TermDag`] terms: subterms shared across the
//! printed roots are let-bound once instead of expanded at every use.
//!
//! Extraction results are highly shared — the variants of one e-class mostly
//! differ near the root, and different roots share leaves and common
//! subexpressions — so expanding every term to a tree can blow the printed
//! size up by orders of magnitude relative to the underlying [`TermDag`].
//! [`render_terms_with_shared_lets`] renders a set of terms against a single
//! sequence of let bindings instead (the `(let ...)` s-expression around them
//! is assembled by the caller, e.g. `multi-extract :dag`):
//!
//! - a binding is introduced only for an `App` term that is referenced two or
//!   more times across all printed terms; everything else is inlined, so
//!   unshared output looks exactly like the ordinary printed form;
//! - binding names are `?t0`, `?t1`, ... in dependency order: a definition
//!   may reference earlier names, like `let*`;
//! - the printed size is `O(|TermDag|)` instead of the sum of the expanded
//!   tree sizes.

use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use egglog::{Term, TermDag, TermId};

/// Render `roots` against a single shared sequence of let bindings.
///
/// Returns the ordered `(name, definition)` bindings and the rendered string
/// for each root, in order. A root that is itself bound renders as its
/// binding name.
pub fn render_terms_with_shared_lets(
    termdag: &TermDag,
    roots: &[TermId],
) -> (Vec<(String, String)>, Vec<String>) {
    // Reference counts over the DAG: one per child slot of each distinct
    // reachable `App`, plus one per root occurrence — i.e., how many times
    // each term would be printed if nothing were bound.
    let mut counts: HashMap<TermId, usize> = HashMap::new();
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut reachable: Vec<TermId> = Vec::new();
    let mut stack: Vec<TermId> = Vec::new();
    for &root in roots {
        *counts.entry(root).or_insert(0) += 1;
        stack.push(root);
    }
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        reachable.push(id);
        if let Term::App(_, children) = termdag.get(id) {
            for &child in children {
                *counts.entry(child).or_insert(0) += 1;
                stack.push(child);
            }
        }
    }
    // A term's children always have smaller ids, so ascending id order is
    // dependency order.
    reachable.sort_unstable();

    let mut bindings: Vec<(String, String)> = Vec::new();
    // How a use site refers to each term: its binding name, or its full
    // rendition inlined.
    let mut repr: HashMap<TermId, String> = HashMap::new();
    for &id in &reachable {
        let term = termdag.get(id);
        let rendered = match term {
            Term::Lit(lit) => format!("{lit}"),
            Term::Var(v) => v.clone(),
            Term::App(name, children) => {
                let mut s = String::new();
                write!(s, "({name}").unwrap();
                for child in children {
                    s.push(' ');
                    s.push_str(&repr[child]);
                }
                s.push(')');
                s
            }
        };
        if matches!(term, Term::App(..)) && counts[&id] >= 2 {
            let name = format!("?t{}", bindings.len());
            bindings.push((name.clone(), rendered));
            repr.insert(id, name);
        } else {
            repr.insert(id, rendered);
        }
    }

    let rendered_roots = roots.iter().map(|r| repr[r].clone()).collect();
    (bindings, rendered_roots)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dag() -> (TermDag, TermId, TermId) {
        let mut td = TermDag::default();
        let one = td.lit(egglog::ast::Literal::Int(1));
        let two = td.lit(egglog::ast::Literal::Int(2));
        let n1 = td.app("Num".into(), vec![one]);
        let n2 = td.app("Num".into(), vec![two]);
        let add = td.app("Add".into(), vec![n1, n2]);
        let neg = td.app("Neg".into(), vec![add]);
        (td, add, neg)
    }

    #[test]
    fn shared_subterm_is_bound_once() {
        let (td, add, neg) = dag();
        let (bindings, rendered) = render_terms_with_shared_lets(&td, &[add, neg]);
        // `add` is used twice (as a root and under Neg), so it is bound;
        // Num/literals are used once each and stay inline.
        assert_eq!(
            bindings,
            vec![("?t0".into(), "(Add (Num 1) (Num 2))".into())]
        );
        assert_eq!(rendered, vec!["?t0".to_string(), "(Neg ?t0)".to_string()]);
    }

    #[test]
    fn unshared_terms_are_inlined() {
        let (td, _, neg) = dag();
        let (bindings, rendered) = render_terms_with_shared_lets(&td, &[neg]);
        assert!(bindings.is_empty());
        assert_eq!(rendered, vec!["(Neg (Add (Num 1) (Num 2)))".to_string()]);
    }

    #[test]
    fn duplicate_children_count_as_two_references() {
        let mut td = TermDag::default();
        let one = td.lit(egglog::ast::Literal::Int(1));
        let n1 = td.app("Num".into(), vec![one]);
        let double = td.app("Add".into(), vec![n1, n1]);
        let (bindings, rendered) = render_terms_with_shared_lets(&td, &[double]);
        assert_eq!(bindings, vec![("?t0".into(), "(Num 1)".into())]);
        assert_eq!(rendered, vec!["(Add ?t0 ?t0)".to_string()]);
    }
}
