//! Subtype-agnostic row iteration over e-graph tables.
//!
//! egglog splits table scans by subtype: [`EGraph::function_entries`] for
//! `function` tables and [`EGraph::constructor_enodes`] for constructors and
//! relations. Several commands in this crate treat both uniformly, so this
//! helper dispatches on the subtype and hands the callback the whole row —
//! inputs followed by the output (or eclass) column.

use egglog::{ApiError, EGraph, Error, Value};

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
/// `function` table.
///
/// egglog exposes no subtype accessor on [`egglog::Function`], so probe with a
/// constructor scan that stops before reading a row and read the answer off the
/// subtype check, which runs before any iteration.
pub(crate) fn is_constructor(egraph: &EGraph, name: &str) -> Result<bool, Error> {
    match egraph.constructor_enodes_while(name, |_| false) {
        Ok(()) => Ok(true),
        Err(Error::ApiError(ApiError::WrongSubtype { .. })) => Ok(false),
        Err(err) => Err(err),
    }
}
