//! Implementation of the `keep-best` command.
//!
//! `(keep-best "table1" "table2" ... [:extractor greedy-dag])` extracts the
//! best representative found by the selected extractor for every entry in each
//! named table and then clears all existing rows. It rebuilds the selected
//! tuples along with any constructor rows needed by their extracted values.
//! This "compacts" the e-graph to the best solutions found so far.
//!
//! Each argument must evaluate to a `String` that names an existing function.

use crate::DynamicCostModel;
use crate::greedy_dag_extract::{extract_best_greedy_dag_with_observer, split_trailing_extractor};
use crate::table_rows::is_constructor;
use egglog::{
    ArcSort, CommandOutput, EGraph, Error, RawValues, Read, Term, TypeError, UserDefinedCommand,
    Value, Write,
    ast::{Expr, ParseError},
    extract::{DagCostModel, MonoidCost, TreeCostModelFromDag},
    sort::S,
    span,
};
use std::collections::HashSet;

/// User-defined command implementing `(keep-best "table"...)`.
///
/// For every row in the named tables, the command extracts the best term for
/// each value. It then **clears every function in the e-graph** and rebuilds
/// the extracted rows from the named tables, including any constructor rows
/// needed to represent their values.
pub struct KeepBestCommand;

impl UserDefinedCommand for KeepBestCommand {
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        let (args, use_greedy_dag) = split_trailing_extractor(args)?;

        if args.is_empty() {
            return Err(Error::ParseError(ParseError(
                span!(),
                "keep-best expects at least one table name".into(),
            )));
        }

        // Step 1: evaluate each argument to a table name string.
        let table_names: Vec<String> = args
            .iter()
            .map(|arg| {
                let (_, val) = egraph.eval_expr(arg)?;
                Ok(egraph.value_to_base::<S>(val).0)
            })
            .collect::<Result<_, Error>>()?;

        keep_best_with_cost_model(
            egraph,
            &table_names,
            use_greedy_dag,
            |_, _| Ok(DynamicCostModel),
            |_| Ok(()),
        )?;

        Ok(vec![])
    }
}

struct RetainedRow {
    table: String,
    inputs: Vec<Value>,
    output: Value,
    constructor: bool,
    subsumed: bool,
    assigned: Option<Value>,
}

/// Compact named rows using native extraction, retaining only their selected
/// producer closure. Clearing rows does not clear native value/union identity,
/// so the write plan can reconnect selected constructors to their source
/// outputs without evaluating syntax or replacing active captured classes.
/// Assigned annotations remain source C values, never aggregate objectives.
pub(crate) fn keep_best_with_cost_model<C: MonoidCost, M: DagCostModel<C>>(
    egraph: &mut EGraph,
    table_names: &[String],
    use_greedy_dag: bool,
    make_model: impl FnOnce(&EGraph, &[(ArcSort, Value)]) -> Result<M, Error>,
    mut check_cost: impl FnMut(&C) -> Result<(), Error>,
) -> Result<(), Error> {
    keep_best_with_selector(egraph, table_names, |graph, roots, observe| {
        let model = make_model(graph, &roots)?;
        let (extracted, _) = if use_greedy_dag {
            extract_best_greedy_dag_with_observer(graph, roots, model, observe)?
        } else {
            graph.extract_best_with_cost_model_and_observer(
                roots,
                TreeCostModelFromDag(model),
                observe,
            )?
        };
        for root in extracted.terms {
            let root = root.ok_or_else(|| {
                Error::ExtractError("keep-best: could not extract a selected table cell".into())
            })?;
            check_cost(&root.cost)?;
        }
        Ok(())
    })
}

/// The selection owns ranking only. This shared plan owns row preservation,
/// assigned C annotations, native captured values, subsumption and clear/write.
pub(crate) fn keep_best_with_selector(
    egraph: &mut EGraph,
    table_names: &[String],
    select: impl FnOnce(
        &EGraph,
        Vec<(ArcSort, Value)>,
        &mut dyn FnMut(
            &egglog::TermDag,
            egglog::TermId,
            &ArcSort,
            Value,
            &[Value],
        ) -> Result<Value, Error>,
    ) -> Result<(), Error>,
) -> Result<(), Error> {
    let mut rows = Vec::new();
    let mut roots = Vec::new();
    for table_name in table_names {
        let func = egraph
            .get_function(table_name)
            .ok_or_else(|| TypeError::UnboundFunction(table_name.clone(), span!()))?;

        let func_type = func.func_type();
        let all_sorts: Vec<ArcSort> = func_type
            .input
            .iter()
            .chain(std::iter::once(&func_type.output))
            .cloned()
            .collect();

        let constructor = is_constructor(egraph, table_name)?;
        let mut table_rows = Vec::new();
        if constructor {
            egraph.constructor_enodes(table_name, |row| {
                table_rows.push(RetainedRow {
                    table: table_name.clone(),
                    inputs: row.children.to_vec(),
                    output: row.eclass,
                    constructor: true,
                    subsumed: row.subsumed,
                    assigned: None,
                });
            })?;
        } else {
            egraph.function_entries(table_name, |row| {
                table_rows.push(RetainedRow {
                    table: table_name.clone(),
                    inputs: row.inputs.to_vec(),
                    output: row.output,
                    constructor: false,
                    subsumed: row.subsumed,
                    assigned: None,
                });
            })?;
        }
        let cost_table = crate::set_cost::get_cost_table_name(table_name);
        for mut row in table_rows {
            roots.extend(
                row.inputs
                    .iter()
                    .chain(std::iter::once(&row.output))
                    .zip(&all_sorts)
                    .map(|(value, sort)| (sort.clone(), *value)),
            );
            if constructor && egraph.get_function(&cost_table).is_some() {
                row.assigned = egraph
                    .read(|state| state.lookup(&cost_table, RawValues(row.inputs.clone())))?;
            }
            rows.push(row);
        }
    }
    let mut selected = Vec::new();
    let mut selected_keys = HashSet::new();
    let mut observe = |terms: &egglog::TermDag,
                       term: egglog::TermId,
                       sort: &ArcSort,
                       value: Value,
                       children: &[Value]| {
        if sort.is_eq_sort() {
            let Term::App(name, _) = terms.get(term) else {
                return Err(Error::ExtractError(
                    "keep-best: a selected class has no constructor occurrence".into(),
                ));
            };
            if selected_keys.insert((name.clone(), children.to_vec())) {
                let table = crate::set_cost::get_cost_table_name(name);
                let assigned = if egraph.get_function(&table).is_some() {
                    egraph.read(|state| state.lookup(&table, RawValues(children.to_vec())))?
                } else {
                    None
                };
                selected.push(RetainedRow {
                    table: name.clone(),
                    inputs: children.to_vec(),
                    output: value,
                    constructor: true,
                    subsumed: false,
                    assigned,
                });
            }
        }
        Ok(value)
    };
    select(egraph, roots, &mut observe)?;
    rows.extend(selected);

    // Preparation and all model/selection failures precede the destructive
    // clear. No private capture/helper table is exempted from this operation.
    for name in egraph.get_function_names() {
        egraph.clear_function(&name)?;
    }
    egraph.update(|mut state| {
        for row in &rows {
            if row.constructor {
                let output = state.add(&row.table, RawValues(row.inputs.clone()))?;
                state.union(output, row.output)?;
            } else {
                state.set(&row.table, RawValues(row.inputs.clone()), row.output)?;
            }
        }
        for row in &rows {
            if let Some(cost) = row.assigned {
                state.set(
                    &crate::set_cost::get_cost_table_name(&row.table),
                    RawValues(row.inputs.clone()),
                    cost,
                )?;
            }
        }
        for row in &rows {
            if row.subsumed {
                state.subsume(&row.table, RawValues(row.inputs.clone()))?;
            }
        }
        Ok(())
    })
}
