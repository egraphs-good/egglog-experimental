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

use crate::Error;
use egglog::{
    ArcSort, CommandOutput, EGraph, Enode, RawValues, Read, UserDefinedCommand, Value,
    ast::*,
    extract::{DEFAULT_COST_MODEL, DagCostModel, DefaultCost, TreeCostModelFromDag},
    span,
    util::FreshGen,
};
use egglog_ast::span::Span;
use log::log_enabled;
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

fn get_cost_table_name(name: &str) -> String {
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

struct CustomExtract;

impl UserDefinedCommand for CustomExtract {
    fn update(
        &self,
        egraph: &mut EGraph,
        args: &[Expr],
    ) -> Result<Vec<CommandOutput>, egglog::Error> {
        match args {
            [] => {
                return Err(Error::ParseError(ParseError(
                    span!(),
                    "extract expects an expression and optional variant count".into(),
                )));
            }
            [_, _, _, ..] => {
                return Err(Error::ParseError(ParseError(
                    args[2].span(),
                    "extract expects at most two arguments".into(),
                )));
            }
            _ => {}
        }
        let (sort, value) = egraph.eval_expr(&args[0])?;
        let n = args.get(1).map(|arg| egraph.eval_expr(arg)).transpose()?;
        let n = if let Some(nv) = n {
            // TODO: egglog does not yet support u64
            if nv.0.name() != "i64" {
                let i64sort = egraph.get_arcsort_by(|s| s.name() == "i64");
                return Err(egglog::Error::TypeError(egglog::TypeError::Mismatch {
                    expr: args[1].clone(),
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
                args[1].span(),
                "Cannot extract negative number of variants".into(),
            )));
        }

        // Omitted or zero variant count means best extraction.
        if n == 0 {
            let mut extracted = egraph.extract_best_with_cost_model(
                vec![(sort, value)],
                TreeCostModelFromDag(DynamicCostModel),
            )?;
            if let Some(term) = extracted
                .terms
                .pop()
                .expect("one requested root produces one result")
            {
                if log_enabled!(log::Level::Info) {
                    log::info!(
                        "extracted with cost {}: {}",
                        term.cost,
                        extracted.termdag.to_string(term.term)
                    );
                }
                Ok(vec![CommandOutput::ExtractBest(
                    extracted.termdag,
                    term.cost,
                    term.term,
                )])
            } else {
                Err(Error::ExtractError(
                    "Unable to find any valid extraction (likely due to subsume or delete)"
                        .to_string(),
                ))
            }
        } else {
            let mut extracted = egraph.extract_variants_with_cost_model(
                vec![(sort, value)],
                n as usize,
                TreeCostModelFromDag(DynamicCostModel),
            )?;
            let terms = extracted
                .variants
                .pop()
                .expect("one requested root produces one variant list")
                .into_iter()
                .map(|term| term.term)
                .collect();
            log::info!("extracted variants:");
            Ok(vec![CommandOutput::ExtractVariants(
                extracted.termdag,
                terms,
            )])
        }
    }
}
