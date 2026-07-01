//! Implementation of the `keep-best` command.
//!
//! `(keep-best "table1" "table2" ...)` extracts the optimal representative
//! term for every entry in each named table, clears the entire e-graph, and
//! re-inserts only those optimal tuples.  This "compacts" the e-graph to the
//! best solutions found so far.
//!
//! Each argument must evaluate to a `String` that names an existing function.

use egglog::{
    ArcSort, CommandOutput, EGraph, Error, RawValues, TermDag, TermId, TypeError,
    UserDefinedCommand, Value, Write,
    ast::Expr,
    extract::{Extractor, TreeAdditiveCostModel},
    sort::S,
    span,
};

pub struct KeepBestCommand;

impl UserDefinedCommand for KeepBestCommand {
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
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
        let extracted = collect_and_extract(egraph, &table_names)?;

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

        // Step 4: re-insert the optimal tuples. Evaluate each extracted term
        // via eval_expr so that constructor sub-terms are re-created bottom-up,
        // then stage all target-table writes in one update call.
        let mut rows_to_insert: Vec<(String, Vec<Value>)> = Vec::new();
        for (table_name, extracted_rows, termdag) in &extracted {
            for term_ids in extracted_rows {
                let values = eval_terms(egraph, termdag, term_ids)?;
                rows_to_insert.push((table_name.clone(), values));
            }
        }

        egraph.update(|mut state| {
            for (table_name, values) in &rows_to_insert {
                let (output, inputs) = values.split_last().ok_or_else(|| {
                    Error::BackendError(format!(
                        "keep-best: extracted row for table {table_name} had no output column"
                    ))
                })?;
                if let Err(err) = state.set(table_name, RawValues(inputs.to_vec()), *output) {
                    if is_constructor_subtype_error(&err) {
                        state.add(table_name, RawValues(inputs.to_vec()))?;
                    } else {
                        return Err(err);
                    }
                }
            }
            Ok(())
        })?;

        Ok(vec![])
    }
}

type ExtractedTable = (String, Vec<Vec<TermId>>, TermDag);

/// For each table, collect all rows and extract the best term for each value.
/// Returns `(table_name, rows, termdag)` triples where each row is a list of
/// `TermId`s (inputs followed by output) into the shared `termdag`.
fn collect_and_extract(
    egraph: &EGraph,
    table_names: &[String],
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

        let raw_rows = table_rows(egraph, table_name)?;

        let extractor = Extractor::compute_costs_from_rootsorts(
            Some(all_sorts.clone()),
            egraph,
            TreeAdditiveCostModel::default(),
        );
        let mut termdag = TermDag::default();
        let mut extracted_rows: Vec<Vec<TermId>> = Vec::new();

        for row_vals in &raw_rows {
            let mut term_ids = Vec::new();
            for (val, sort) in row_vals.iter().zip(all_sorts.iter()) {
                let (_, tid) = extractor
                    .extract_best_with_sort(egraph, &mut termdag, *val, sort.clone())
                    .ok_or_else(|| {
                        Error::ExtractError(format!(
                            "keep-best: could not extract value in table {table_name}"
                        ))
                    })?;
                term_ids.push(tid);
            }
            extracted_rows.push(term_ids);
        }

        result.push((table_name.clone(), extracted_rows, termdag));
    }

    Ok(result)
}

fn table_rows(egraph: &EGraph, table_name: &str) -> Result<Vec<Vec<Value>>, Error> {
    let mut raw_rows = Vec::new();
    match egraph.function_entries(table_name, |entry| {
        let mut vals = entry.inputs.to_vec();
        vals.push(entry.output);
        raw_rows.push(vals);
    }) {
        Ok(()) => Ok(raw_rows),
        Err(err) if is_constructor_subtype_error(&err) => {
            raw_rows.clear();
            egraph.constructor_enodes(table_name, |enode| {
                let mut vals = enode.children.to_vec();
                vals.push(enode.eclass);
                raw_rows.push(vals);
            })?;
            Ok(raw_rows)
        }
        Err(err) => Err(err),
    }
}

fn is_constructor_subtype_error(error: &Error) -> bool {
    if let Error::ApiError(egglog::ApiError::WrongSubtype { actual, .. }) = error {
        *actual == "constructor"
    } else {
        false
    }
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
