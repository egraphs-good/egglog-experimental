//! Implementation of the `keep-best` command.
//!
//! `(keep-best "table1" "table2" ... [:extractor greedy-dag])` extracts the
//! best representative found by the selected extractor for every entry in each
//! named table, clears the entire e-graph, and re-inserts only those tuples.
//! This "compacts" the e-graph to the best solutions found so far.
//!
//! Each argument must evaluate to a `String` that names an existing function.

use crate::DynamicCostModel;
use crate::greedy_dag_extract::{extract_best_greedy_dag, split_trailing_extractor};
use crate::table_rows::{for_each_row, is_constructor};
use egglog::{
    ArcSort, CommandOutput, EGraph, Error, RawValues, TermDag, TermId, TypeError,
    UserDefinedCommand, Value, Write, ast::Expr, sort::S, span,
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

        // Step 2: for each table, collect all rows and extract the best
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

        // Step 4: re-insert the selected tuples. Evaluate each extracted term
        // via eval_expr so that constructor sub-terms are re-created bottom-up,
        // then stage all target-table inserts in one `update` call.
        let mut rows_to_insert: Vec<(String, bool, Vec<Value>)> = Vec::new();
        for (table_name, extracted_rows, termdag) in &extracted {
            let constructor = is_constructor(egraph, table_name)?;
            for term_ids in extracted_rows {
                let values = eval_terms(egraph, termdag, term_ids)?;
                rows_to_insert.push((table_name.clone(), constructor, values));
            }
        }

        egraph.update(|mut state| {
            for (table_name, constructor, values) in &rows_to_insert {
                let (output, inputs) = values
                    .split_last()
                    .expect("extracted row has at least an output column");
                if *constructor {
                    // `add` mints (or finds) the eclass for these inputs; the
                    // union pins it to the eclass the extracted output term
                    // evaluated to, which is what the raw row insert used to do.
                    let eclass = state.add(table_name, RawValues(inputs.to_vec()))?;
                    state.union(eclass, *output)?;
                } else {
                    state.set(table_name, RawValues(inputs.to_vec()), *output)?;
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
    use_greedy_dag: bool,
) -> Result<Vec<ExtractedTable>, Error> {
    let mut result = Vec::new();

    for table_name in table_names {
        let func = egraph
            .get_function(table_name)
            .ok_or_else(|| TypeError::UnboundFunction(table_name.clone(), span!()))?;

        let all_sorts: Vec<ArcSort> = func
            .func_type()
            .input
            .iter()
            .chain(std::iter::once(&func.func_type().output))
            .cloned()
            .collect();

        let mut raw_rows: Vec<Vec<Value>> = Vec::new();
        for_each_row(egraph, table_name, |vals| {
            raw_rows.push(vals.to_vec());
        })?;

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
            extract_best_greedy_dag(egraph, roots, DynamicCostModel)
        } else {
            egraph.extract_best(roots, DynamicCostModel)
        }
        .map_err(|err| {
            Error::ExtractError(format!(
                "keep-best: could not extract value in table {table_name}: {err}"
            ))
        })?;
        let termdag = extracted.termdag;
        let extract_error = format!("keep-best: could not extract value in table {table_name}");
        let mut terms = extracted.terms.into_iter().map(move |root| {
            root.ok_or_else(|| Error::ExtractError(extract_error.clone()))
                .map(|root| root.term)
        });
        let mut extracted_rows: Vec<Vec<TermId>> = Vec::new();

        for row_vals in &raw_rows {
            let mut term_ids = Vec::new();
            for _ in row_vals {
                term_ids.push(terms.next().expect("one term per extracted table cell")?);
            }
            extracted_rows.push(term_ids);
        }

        result.push((table_name.clone(), extracted_rows, termdag));
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
