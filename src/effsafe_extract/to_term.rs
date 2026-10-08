//! Turn an extraction into egglog terms.

use egglog::{EGraph, TermDag, TermId};
use rustc_hash::FxHashMap;

use super::term_graph::{Extraction, NodeKind, SortId, TermGraph};

/// Build the term for `extraction`, whose nodes are in topological order with
/// the root last. `placeholders` gives the term for each placeholder sort.
pub fn extraction_to_term(
    g: &TermGraph,
    egraph: &EGraph,
    placeholders: &FxHashMap<SortId, TermId>,
    extraction: &Extraction,
    termdag: &mut TermDag,
) -> TermId {
    let mut terms: Vec<TermId> = Vec::with_capacity(extraction.len());
    for en in extraction {
        let enode = g.enode(en.class, en.node);
        let sort = &g.sorts[g.classes[en.class].sort];
        let children: Vec<TermId> = en.children.iter().map(|&c| terms[c]).collect();
        let term = match enode.kind {
            NodeKind::Op(op) => termdag.app(g.ops[op].name.clone(), children),
            NodeKind::Base(value) => egraph.reconstruct_base_value(sort, value, termdag),
            NodeKind::Container(value) => {
                egraph.reconstruct_container_value(sort, value, termdag, children)
            }
            NodeKind::Placeholder => placeholders[&g.classes[en.class].sort],
        };
        terms.push(term);
    }
    *terms.last().expect("extraction is empty")
}
