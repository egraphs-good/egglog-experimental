//! Compact DAG printing for [`TermDag`] terms: subterms shared across the
//! printed roots are let-bound once instead of expanded at every use.
//!
//! Extraction results are highly shared — the variants of one e-class mostly
//! differ near the root, and different roots share leaves and common
//! subexpressions — so expanding every term to a tree can blow the printed
//! size up by orders of magnitude relative to the underlying [`TermDag`].
//! [`render_terms_with_shared_lets`] renders a set of terms against a single
//! sequence of let bindings instead (the `(let ...)` s-expression around them
//! is assembled by the caller, e.g. `(multi-extract n :dag ...)`):
//!
//! - a binding is introduced only for an `App` term that is referenced two or
//!   more times across all printed terms; everything else is inlined, so
//!   unshared output looks exactly like the ordinary printed form;
//! - binding names are fresh `?t0`, `?t1`, ... names in dependency order (with
//!   names already used by term variables skipped), so a definition may
//!   reference earlier names, like `let*`;
//! - the printed size is `O(|TermDag|)` instead of the sum of the expanded
//!   tree sizes.

use std::collections::HashSet;

use egglog::{Term, TermDag, TermId};

/// Render `roots` against a single shared sequence of let bindings.
///
/// Returns the ordered `(name, definition)` bindings and the rendered string
/// for each root, in order. A root that is itself bound renders as its
/// binding name.
pub(crate) fn render_terms_with_shared_lets(
    termdag: &TermDag,
    roots: &[TermId],
) -> (Vec<(String, String)>, Vec<String>) {
    // Count each child edge of a distinct reachable `App`, plus each root
    // occurrence. A repeated parent will be bound, so its children occur only
    // in that one definition and its outgoing edges are deliberately counted
    // once rather than once per expanded-tree occurrence.
    // TermIds are dense arena indices, so per-term state needs no hash lookup.
    let mut counts = vec![0; termdag.size()];
    let mut seen = vec![false; termdag.size()];
    let mut used_names = HashSet::new();
    let mut reachable = Vec::new();
    let mut stack = Vec::new();
    for &root in roots {
        counts[root] += 1;
        stack.push(root);
    }
    while let Some(id) = stack.pop() {
        if seen[id] {
            continue;
        }
        seen[id] = true;
        reachable.push(id);
        match termdag.get(id) {
            Term::Var(name) => {
                used_names.insert(name.clone());
            }
            Term::App(_, children) => {
                for &child in children {
                    counts[child] += 1;
                    stack.push(child);
                }
            }
            Term::Lit(_) => {}
        }
    }
    // A term's children always have smaller ids, so ascending id order is
    // dependency order.
    reachable.sort_unstable();

    let mut projected = TermDag::default();
    let mut projected_ids = vec![0; termdag.size()];
    let mut bindings = Vec::new();
    let mut next_name = 0;
    for &id in &reachable {
        let term = termdag.get(id);
        let projected_id = match term {
            Term::Lit(lit) => projected.lit(lit.clone()),
            Term::Var(name) => projected.var(name.clone()),
            Term::App(name, children) => projected.app(
                name.clone(),
                children.iter().map(|&child| projected_ids[child]).collect(),
            ),
        };
        if matches!(term, Term::App(..)) && counts[id] >= 2 {
            let name = loop {
                let candidate = format!("?t{next_name}");
                next_name += 1;
                if used_names.insert(candidate.clone()) {
                    break candidate;
                }
            };
            bindings.push((name.clone(), projected.to_string(projected_id)));
            projected_ids[id] = projected.var(name);
        } else {
            projected_ids[id] = projected_id;
        }
    }

    let rendered_roots = roots
        .iter()
        .map(|&root| projected.to_string(projected_ids[root]))
        .collect();
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

    #[test]
    fn duplicate_roots_bind_the_root_without_recounting_children() {
        let (td, _, neg) = dag();
        let (bindings, rendered) = render_terms_with_shared_lets(&td, &[neg, neg]);
        assert_eq!(
            bindings,
            vec![("?t0".into(), "(Neg (Add (Num 1) (Num 2)))".into())]
        );
        assert_eq!(rendered, vec!["?t0".to_string(), "?t0".to_string()]);
    }

    #[test]
    fn nested_bindings_are_in_dependency_order() {
        let (td, add, neg) = dag();
        let (bindings, rendered) = render_terms_with_shared_lets(&td, &[add, neg, neg]);
        assert_eq!(
            bindings,
            vec![
                ("?t0".into(), "(Add (Num 1) (Num 2))".into()),
                ("?t1".into(), "(Neg ?t0)".into()),
            ]
        );
        assert_eq!(rendered, vec!["?t0", "?t1", "?t1"]);
    }

    #[test]
    fn generated_names_do_not_capture_term_variables() {
        let mut td = TermDag::default();
        let user_var = td.var("?t0".into());
        let shared = td.app("A".into(), vec![]);
        let root = td.app("Pair".into(), vec![shared, user_var]);
        let (bindings, rendered) = render_terms_with_shared_lets(&td, &[root, shared]);
        assert_eq!(bindings, vec![("?t1".into(), "(A)".into())]);
        assert_eq!(rendered, vec!["(Pair ?t1 ?t0)", "?t1"]);
    }

    #[test]
    fn deep_unshared_term_renders_linearly() {
        let depth = 20_000;
        let mut td = TermDag::default();
        let mut root = td.app("Z".into(), vec![]);
        for _ in 0..depth {
            root = td.app("F".into(), vec![root]);
        }

        let (bindings, rendered) = render_terms_with_shared_lets(&td, &[root]);
        assert!(bindings.is_empty());
        assert_eq!(rendered[0].len(), 4 * depth + 3);
    }
}
