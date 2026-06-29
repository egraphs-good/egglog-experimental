use crate::{
    Error,
    greedy_dag_extract::{
        DagCostModel, extract_best_greedy_dag, extract_best_tree, extract_variants_greedy_dag,
        extract_variants_tree, parse_extractor_keyword,
    },
};
use egglog::{
    ArcSort, CommandOutput, EGraph, Enode, RawValues, Read, TermId, UserDefinedCommand, Value,
    ast::*,
    extract::{BaseCostModel, DefaultCost, TreeAdditiveCostModel},
    span,
    util::FreshGen,
};
use egglog_ast::span::Span;
use log::log_enabled;
use std::sync::Arc;

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

/// The cost model that handles dynamic costs. Use this cost model if you use the `with-dynamic-cost` / `set-cost`
/// extensions in your egglog program
#[derive(Clone)]
pub struct DynamicCostModel;

impl BaseCostModel<DefaultCost> for DynamicCostModel {
    fn base_value_cost(&self, egraph: &EGraph, sort: &ArcSort, value: Value) -> DefaultCost {
        BaseCostModel::base_value_cost(&TreeAdditiveCostModel {}, egraph, sort, value)
    }
}

impl DagCostModel<DefaultCost> for DynamicCostModel {
    fn marginal_enode_cost(
        &self,
        egraph: &EGraph,
        func: &egglog::Function,
        enode: &Enode<'_>,
        _child_costs: &[DefaultCost],
    ) -> DefaultCost {
        let default_cost = || {
            DagCostModel::marginal_enode_cost(
                &TreeAdditiveCostModel::default(),
                egraph,
                func,
                enode,
                &[],
            )
        };
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
        let (expr, variants, use_greedy_dag) = match args {
            [] => {
                return Err(Error::ParseError(ParseError(
                    span!(),
                    "extract expects an expression and optional variant count".into(),
                )));
            }
            [expr] => (expr, None, false),
            [expr, variants] => (expr, Some(variants), false),
            [expr, keyword, extractor] => {
                (expr, None, parse_extractor_keyword(keyword, extractor)?)
            }
            [expr, variants, keyword, extractor] => (
                expr,
                Some(variants),
                parse_extractor_keyword(keyword, extractor)?,
            ),
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
                extract_best_tree(egraph, roots, DynamicCostModel)?
            };
            let root = extracted
                .terms
                .into_iter()
                .next()
                .expect("one root was requested");
            if log_enabled!(log::Level::Info) {
                log::info!(
                    "extracted with cost {}: {}",
                    root.cost,
                    extracted.termdag.to_string(root.term)
                );
            }
            Ok(vec![CommandOutput::ExtractBest(
                extracted.termdag,
                root.cost,
                root.term,
            )])
        } else {
            let extracted = if use_greedy_dag {
                extract_variants_greedy_dag(egraph, roots, n as usize, DynamicCostModel)?
            } else {
                extract_variants_tree(egraph, roots, n as usize, DynamicCostModel)?
            };
            let terms: Vec<TermId> = extracted
                .variants
                .into_iter()
                .next()
                .expect("one root was requested")
                .into_iter()
                .map(|variant| variant.term)
                .collect();
            log::info!("extracted variants:");
            Ok(vec![CommandOutput::ExtractVariants(
                extracted.termdag,
                terms,
            )])
        }
    }
}
