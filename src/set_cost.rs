//! Runtime-configurable extraction costs.
//!
//! Wrap datatype or constructor declarations in `with-dynamic-cost` to create
//! a cost table for each extractable constructor. `set-cost` updates a node's
//! cost, and the replacement `extract` command reads those costs:
//!
//! ```text
//! (with-dynamic-cost
//!   (datatype Math (Num i64) (Add Math Math)))
//! (set-cost (Num 1) 100)
//! (extract (Num 1))
//! ```
//!
//! Nodes without an assigned dynamic cost retain their normal tree-additive
//! cost. Costs must be non-negative.

use crate::{
    Error,
    greedy_dag_extract::{
        extract_best_greedy_dag, extract_variants_greedy_dag, split_trailing_extractor,
    },
};
use egglog::{
    ArcSort, CommandOutput, EGraph, Enode, RawValues, Read, TermId, UserDefinedCommand, Value,
    ast::*,
    extract::{DEFAULT_COST_MODEL, DagCostModel, DefaultCost, TreeCostModelFromDag},
    span,
    util::FreshGen,
};
use egglog_ast::span::Span;
use num::BigInt;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

/// Registers `with-dynamic-cost`, `set-cost`, and the dynamic-cost `extract`
/// command on an e-graph.
///
/// [`new_experimental_egraph`](crate::new_experimental_egraph) calls this
/// automatically.
pub fn add_set_cost(egraph: &mut EGraph) {
    egraph
        .parser
        .add_command_macro(Arc::new(SetCostDeclarations));
    egraph.parser.add_action_macro(Arc::new(SetCost));
    egraph
        .add_command("extract".into(), Arc::new(CustomExtract))
        .unwrap();
}

struct SetCost;

impl Macro<Vec<Action>> for SetCost {
    fn name(&self) -> &str {
        "set-cost"
    }

    fn parse(
        &self,
        args: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Action>, ParseError> {
        match args {
            [call, value] => {
                let (func, args, call_span) = call.expect_call("table lookup")?;
                let cost_table_name = get_cost_table_name(&func);
                let args = map_fallible(args, parser, Parser::parse_expr)?;
                let value = parser.parse_expr(value)?;

                let vs = (0..args.len())
                    .map(|_| parser.symbol_gen.fresh("set_cost_var"))
                    .collect::<Vec<_>>();
                let (args, mut actions): (Vec<Expr>, Vec<Action>) = vs
                    .into_iter()
                    .zip(args)
                    .map(|(v, e)| {
                        let span = e.span().clone();
                        (Expr::Var(span.clone(), v.clone()), Action::Let(span, v, e))
                    })
                    .unzip();

                // We don't create costs for nodes that don't exist.
                actions.push(Action::Expr(
                    span.clone(),
                    Expr::Call(call_span.clone(), func, args.clone()),
                ));
                actions.push(Action::Set(span, cost_table_name, args, value));
                Ok(actions)
            }
            _ => Err(ParseError(
                span,
                "usage: (set-cost (<table name> <expr>*) <expr>)".to_string(),
            )),
        }
    }
}

struct SetCostDeclarations;

impl Macro<Vec<Command>> for SetCostDeclarations {
    fn name(&self) -> &str {
        "with-dynamic-cost"
    }

    fn parse(
        &self,
        decls: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Command>, ParseError> {
        let decls = map_fallible(decls, parser, Parser::parse_command)?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        let mut cost_table_commands = vec![];
        for decl in decls.iter() {
            match decl {
                Command::Datatype { variants, .. } => {
                    let commands = generate_cost_table_commands_from_variants(variants);
                    cost_table_commands.extend(commands);
                }
                Command::Datatypes { datatypes, .. } => {
                    let commands =
                        datatypes.iter().flat_map(
                            |(_span, _name, subdatatypes)| match subdatatypes {
                                Subdatatypes::Variants(variants) => {
                                    generate_cost_table_commands_from_variants(variants)
                                }
                                Subdatatypes::NewSort(..) => vec![],
                            },
                        );
                    cost_table_commands.extend(commands);
                }
                Command::Constructor {
                    name,
                    schema,
                    span,
                    unextractable,
                    ..
                } => {
                    if !*unextractable {
                        let cost_table_name = get_cost_table_name(name);
                        let mut cost_table_schema = schema.clone();
                        cost_table_schema.output = "i64".into();
                        cost_table_commands.push(Command::Function {
                            span: span.clone(),
                            name: cost_table_name,
                            schema: cost_table_schema,
                            merge: None,
                            hidden: false,
                            let_binding: false,
                            term_constructor: None,
                            unextractable: false,
                        });
                    }
                }
                _ => {
                    return Err(ParseError(
                        span,
                        "Expect a datatype declaration".to_string(),
                    ));
                }
            }
        }
        let mut commands = decls;
        commands.extend(cost_table_commands);
        Ok(commands)
    }
}

fn generate_cost_table_commands_from_variants(variants: &[Variant]) -> Vec<Command> {
    variants
        .iter()
        .map(|v| {
            let cost_table_name = get_cost_table_name(&v.name);
            let cost_table_schema = Schema::new(v.types.clone(), "i64".into());

            Command::Function {
                span: v.span.clone(),
                name: cost_table_name,
                schema: cost_table_schema,
                merge: None,
                hidden: false,
                let_binding: false,
                term_constructor: None,
                unextractable: false,
            }
        })
        .collect::<Vec<_>>()
}

pub(crate) fn get_cost_table_name(name: &str) -> String {
    format!("cost_table_{name}")
}

fn map_fallible<T>(
    slice: &[Sexp],
    parser: &mut Parser,
    func: impl Fn(&mut Parser, &Sexp) -> Result<T, ParseError>,
) -> Result<Vec<T>, ParseError> {
    slice
        .iter()
        .map(|sexp| func(parser, sexp))
        .collect::<Result<_, _>>()
}

/// An extraction cost model that reads costs assigned by `set-cost`.
///
/// It falls back to the marginal costs used by [`DEFAULT_COST_MODEL`] for
/// constructors without an assigned dynamic cost. Use this model for custom
/// extractors that should agree with this crate's replacement `extract`
/// command.
#[derive(Clone)]
pub struct DynamicCostModel;

impl DagCostModel<DefaultCost> for DynamicCostModel {
    fn base_value_cost(&self, egraph: &EGraph, sort: &ArcSort, value: Value) -> DefaultCost {
        DagCostModel::base_value_cost(&DEFAULT_COST_MODEL.0, egraph, sort, value)
    }

    fn enode_cost(
        &self,
        egraph: &EGraph,
        func: &egglog::Function,
        enode: &Enode<'_>,
    ) -> DefaultCost {
        let default_cost = || DagCostModel::enode_cost(&DEFAULT_COST_MODEL.0, egraph, func, enode);
        let name = get_cost_table_name(func.name());
        if egraph.get_function(&name).is_some() {
            egraph
                .read(|state| state.lookup(&name, RawValues(enode.children.to_vec())))
                .ok()
                .flatten()
                .map(|c| {
                    let cost = egraph.value_to_base::<i64>(c);
                    assert!(cost >= 0);
                    cost as DefaultCost
                })
                .unwrap_or_else(default_cost)
        } else {
            default_cost()
        }
    }
}

/// Extraction-local default model for the encoded i64 boundary.
///
/// Storage accepts signed annotations, but this default model supports only
/// nonnegative marginals in the native tree extractor's root-sort closure.
/// Costs are validated and frozen before native extraction starts. Exact
/// accumulation avoids saturation changing candidate ranking; consumers must
/// still check that selected objectives fit their declared i64 result domain.
#[derive(Clone)]
pub(crate) struct CheckedDynamicCostModel {
    assigned: HashMap<String, HashMap<Vec<Value>, BigInt>>,
}

impl CheckedDynamicCostModel {
    pub(crate) fn for_root_sorts(
        egraph: &EGraph,
        mut pending: Vec<ArcSort>,
    ) -> Result<Self, Error> {
        let mut seen = HashSet::new();
        let mut assigned = HashMap::new();
        while let Some(sort) = pending.pop() {
            if !seen.insert(sort.name().to_owned()) {
                continue;
            }
            if sort.is_container_sort() {
                pending.extend(sort.inner_sorts());
            } else if sort.is_eq_sort() {
                for (name, func) in egraph.functions_iter().filter(|(_, func)| {
                    func.func_type().subtype == FunctionSubtype::Constructor
                        && !func.is_hidden()
                        && !func.is_unextractable()
                        && func.func_type().output.name() == sort.name()
                }) {
                    pending.extend(func.func_type().input.iter().cloned());
                    let table = get_cost_table_name(name);
                    if egraph.get_function(&table).is_none() {
                        continue;
                    }
                    let mut costs = HashMap::new();
                    let mut keys = Vec::new();
                    egraph.constructor_enodes(name, |row| {
                        if !row.subsumed {
                            keys.push(row.children.to_vec());
                        }
                    })?;
                    for key in keys {
                        if let Some(value) =
                            egraph.read(|state| state.lookup(&table, RawValues(key.clone())))?
                        {
                            let cost = egraph.value_to_base::<i64>(value);
                            if cost < 0 {
                                return Err(Error::ExtractError(format!(
                                    "the default i64 cost model does not support negative assigned costs ({cost}) in the extraction sort domain"
                                )));
                            }
                            costs.insert(key, BigInt::from(cost));
                        }
                    }
                    assigned.insert(name.to_owned(), costs);
                }
            }
        }
        Ok(Self { assigned })
    }
}

impl DagCostModel<BigInt> for CheckedDynamicCostModel {
    fn base_value_cost(&self, egraph: &EGraph, sort: &ArcSort, value: Value) -> BigInt {
        BigInt::from(DagCostModel::base_value_cost(
            &DEFAULT_COST_MODEL.0,
            egraph,
            sort,
            value,
        ))
    }

    fn enode_cost(&self, egraph: &EGraph, func: &egglog::Function, enode: &Enode<'_>) -> BigInt {
        self.assigned
            .get(func.name())
            .and_then(|costs| costs.get(enode.children))
            .cloned()
            .unwrap_or_else(|| {
                BigInt::from(DagCostModel::enode_cost(
                    &DEFAULT_COST_MODEL.0,
                    egraph,
                    func,
                    enode,
                ))
            })
    }
}

struct CustomExtract;

impl UserDefinedCommand for CustomExtract {
    fn update(
        &self,
        egraph: &mut EGraph,
        args: &[Expr],
    ) -> Result<Vec<CommandOutput>, egglog::Error> {
        let (args, use_greedy_dag) = split_trailing_extractor(args)?;
        let (expr, variants) = match args {
            [] => {
                return Err(Error::ParseError(ParseError(
                    span!(),
                    "extract expects an expression and optional variant count".into(),
                )));
            }
            [expr] => (expr, None),
            [expr, variants] => (expr, Some(variants)),
            [_, _, extra, ..] => {
                return Err(Error::ParseError(ParseError(
                    extra.span(),
                    "extract expects an expression, optional variant count, and optional :extractor"
                        .into(),
                )));
            }
        };

        let (sort, value) = egraph.eval_expr(expr)?;
        let n = variants.map(|arg| egraph.eval_expr(arg)).transpose()?;
        let n = if let Some(nv) = n {
            // TODO: egglog does not yet support u64
            if nv.0.name() != "i64" {
                let i64sort = egraph.get_arcsort_by(|s| s.name() == "i64");
                return Err(egglog::Error::TypeError(egglog::TypeError::Mismatch {
                    expr: variants.unwrap().clone(),
                    expected: i64sort,
                    actual: nv.0,
                }));
            }
            egraph.value_to_base::<i64>(nv.1)
        } else {
            0
        };

        if n < 0 {
            return Err(Error::ParseError(ParseError(
                variants.unwrap().span(),
                "Cannot extract negative number of variants".into(),
            )));
        }

        let roots = vec![(sort, value)];

        // Omitted or zero variant count means best extraction.
        if n == 0 {
            let extracted = if use_greedy_dag {
                extract_best_greedy_dag(egraph, roots, DynamicCostModel)?
            } else {
                egraph
                    .extract_best_with_cost_model(roots, TreeCostModelFromDag(DynamicCostModel))?
            };
            let root = extracted
                .terms
                .into_iter()
                .next()
                .expect("one root was requested")
                .ok_or_else(|| {
                    Error::ExtractError("Unable to find any valid extraction".to_string())
                })?;
            log::info!(
                "extracted with cost {}: {}",
                root.cost,
                extracted.termdag.to_string(root.term)
            );
            Ok(vec![CommandOutput::ExtractBest(
                extracted.termdag,
                root.cost,
                root.term,
            )])
        } else {
            let extracted = if use_greedy_dag {
                extract_variants_greedy_dag(egraph, roots, n as usize, DynamicCostModel)?
            } else {
                egraph.extract_variants_with_cost_model(
                    roots,
                    n as usize,
                    TreeCostModelFromDag(DynamicCostModel),
                )?
            };
            let terms: Vec<TermId> = extracted
                .variants
                .into_iter()
                .next()
                .expect("one root was requested")
                .into_iter()
                .map(|variant| variant.term)
                .collect();
            Ok(vec![CommandOutput::ExtractVariants(
                extracted.termdag,
                terms,
            )])
        }
    }
}
