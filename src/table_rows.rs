//! Subtype-agnostic row iteration over e-graph tables.
//!
//! egglog splits table scans by subtype: [`EGraph::function_entries`] for
//! `function` tables and [`EGraph::constructor_enodes`] for constructors and
//! relations. Several commands in this crate treat both uniformly, so this
//! helper dispatches on the subtype and hands the callback the whole row —
//! inputs followed by the output (or eclass) column.

use egglog::ast::FunctionSubtype;
use egglog::{EGraph, Error, Read, Value};

/// Call `f` once per row of `name`, with every column in schema order.
pub(crate) fn for_each_row(
    egraph: &EGraph,
    name: &str,
    mut f: impl FnMut(&[Value]),
) -> Result<(), Error> {
    let mut row: Vec<Value> = Vec::new();
    if is_constructor(egraph, name)? {
        egraph.constructor_enodes(name, |enode| {
            row.clear();
            row.extend_from_slice(enode.children);
            row.push(enode.eclass);
            f(&row);
        })
    } else {
        egraph.function_entries(name, |entry| {
            row.clear();
            row.extend_from_slice(entry.inputs);
            row.push(entry.output);
            f(&row);
        })
    }
}

/// Whether `name` is a constructor (or relation) table rather than a
/// `function` table. Unknown tables report `false`; the scan that follows
/// reports the missing table.
pub(crate) fn is_constructor(egraph: &EGraph, name: &str) -> Result<bool, Error> {
    Ok(egraph.read(|state| state.table_subtype(name)) == Some(FunctionSubtype::Constructor))
}
