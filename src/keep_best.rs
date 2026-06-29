//! Implementation of the `keep-best` command.
//!
//! `(keep-best "table1" "table2" ... [:extractor greedy-dag])` extracts the
//! optimal representative term for every entry in each named table, clears the
//! entire e-graph, and re-inserts only those optimal tuples. This "compacts"
//! the e-graph to the best solutions found so far.
//!
//! Each argument must evaluate to a `String` that names an existing function.

use crate::{
    extractor_option::split_trailing_extractor,
    greedy_dag_extract::{extract_best_greedy_dag, extract_best_tree},
};
use egglog::{
    ArcSort, CommandOutput, EGraph, Error, RawValues, TermDag, TermId, TypeError,
    UserDefinedCommand, Value, Write, ast::Expr, extract::TreeAdditiveCostModel, sort::S, span,
};

pub struct KeepBestCommand;

impl UserDefinedCommand for KeepBestCommand {
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        let (args, use_greedy_dag) = split_trailing_extractor(args)?;

        // Step 1: evaluate each argument to a table name string.
        let table_names: Vec<String> = args
            .iter()
            .map(|arg| {
                let (_, val) = egraph.eval_expr(arg)?;
                Ok(egraph.value_to_base::<S>(val).0)
            })
            .collect::<Result<_, Error>>()?;

        // Step 2: for each table, collect all rows and extract the optimal
        // term for every column value.
        let extracted = collect_and_extract(egraph, &table_names, use_greedy_dag)?;

        // Step 3: clear every function in the e-graph in bulk.
        //
        // `clear_function` drops the entire row buffer for a table in
        // O(1)-in-row-count time and bumps the table's generation so cached
        // indexes/subsets are lazily rebuilt. That's strictly faster than
        // staging a `remove` per row, which is what we used to do here.
        let all_funcs: Vec<String> = egraph.get_function_names();
        for name in &all_funcs {
            egraph.clear_function(name)?;
        }

        // Step 4: re-insert the optimal tuples. Evaluate each extracted term via eval_expr so
        // that constructor sub-terms are re-created bottom-up, then stage all writes in one
        // update.
        let mut rows_to_insert: Vec<(String, TableKind, Vec<Value>)> = Vec::new();
        for (table_name, kind, extracted_rows, termdag) in &extracted {
            for term_ids in extracted_rows {
                let values = eval_terms(egraph, termdag, term_ids)?;
                rows_to_insert.push((table_name.clone(), *kind, values));
            }
        }

        egraph.update(|mut state| {
            for (table_name, kind, values) in rows_to_insert {
                let Some((output, inputs)) = values.split_last() else {
                    return Err(Error::ExtractError(format!(
                        "keep-best: empty row for table {table_name}"
                    )));
                };
                match kind {
                    TableKind::Function => {
                        state.set(&table_name, RawValues(inputs.to_vec()), *output)?;
                    }
                    TableKind::Constructor => {
                        state.add(&table_name, RawValues(inputs.to_vec()))?;
                    }
                }
            }
            Ok(())
        })?;

        Ok(vec![])
    }
}

#[derive(Clone, Copy)]
enum TableKind {
    Function,
    Constructor,
}

type ExtractedTable = (String, TableKind, Vec<Vec<TermId>>, TermDag);

/// For each table, collect all rows and extract the best term for each value.
/// Returns `(table_name, rows, termdag)` triples where each row is a list of
/// `TermId`s (inputs followed by output) into the shared `termdag`.
fn collect_and_extract(
    egraph: &EGraph,
    table_names: &[String],
    use_greedy_dag: bool,
) -> Result<Vec<ExtractedTable>, Error> {
    let mut result = Vec::new();

    for table_name in table_names {
        let func = egraph
            .get_function(table_name)
            .ok_or_else(|| TypeError::UnboundFunction(table_name.clone(), span!()))?;

        let all_sorts: Vec<ArcSort> = func
            .schema()
            .input
            .iter()
            .chain(std::iter::once(&func.schema().output))
            .cloned()
            .collect();

        let mut raw_rows: Vec<Vec<Value>> = Vec::new();
        let kind = if egraph
            .function_entries(table_name, |entry| {
                let mut row = entry.inputs.to_vec();
                row.push(entry.output);
                raw_rows.push(row);
            })
            .is_ok()
        {
            TableKind::Function
        } else {
            egraph.constructor_enodes(table_name, |enode| {
                let mut row = enode.children.to_vec();
                row.push(enode.eclass);
                raw_rows.push(row);
            })?;
            TableKind::Constructor
        };

        let roots = raw_rows
            .iter()
            .flat_map(|row_vals| {
                row_vals
                    .iter()
                    .zip(all_sorts.iter())
                    .map(|(val, sort)| (sort.clone(), *val))
            })
            .collect();
        let extracted = if use_greedy_dag {
            extract_best_greedy_dag(egraph, roots, TreeAdditiveCostModel::default())
        } else {
            extract_best_tree(egraph, roots, TreeAdditiveCostModel::default())
        }
        .map_err(|_| {
            Error::ExtractError(format!(
                "keep-best: could not extract value in table {table_name}"
            ))
        })?;
        let termdag = extracted.termdag;
        let mut terms = extracted.terms.into_iter().map(|root| root.term);
        let mut extracted_rows: Vec<Vec<TermId>> = Vec::new();

        for row_vals in &raw_rows {
            let mut term_ids = Vec::new();
            for _ in row_vals {
                term_ids.push(terms.next().expect("one term per extracted table cell"));
            }
            extracted_rows.push(term_ids);
        }

        result.push((table_name.clone(), kind, extracted_rows, termdag));
    }

    Ok(result)
}

/// Evaluate a list of `TermId`s from `termdag` using `eval_expr`, returning
/// the resulting `Value`s in the same order.
fn eval_terms(
    egraph: &mut EGraph,
    termdag: &TermDag,
    term_ids: &[TermId],
) -> Result<Vec<Value>, Error> {
    term_ids
        .iter()
        .map(|tid| {
            let expr = termdag.term_to_expr(
                tid,
                egglog::prelude::Span::Rust(std::sync::Arc::new(egglog::prelude::RustSpan {
                    file: file!(),
                    line: line!(),
                    column: column!(),
                })),
            );
            let (_, val) = egraph.eval_expr(&expr)?;
            Ok(val)
        })
        .collect()
}
