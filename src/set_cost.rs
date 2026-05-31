use egglog_ast::span::Span;
use log::log_enabled;
use std::sync::Arc;

use egglog::{
    CommandOutput, EGraph, TermDag, TermId, UserDefinedCommand,
    ast::*,
    extract::{CostModel, DefaultCost, Extractor, TreeAdditiveCostModel},
    util::FreshGen,
};

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

impl CostModel<DefaultCost> for DynamicCostModel {
    fn fold(
        &self,
        _head: &str,
        children_cost: &[DefaultCost],
        head_cost: DefaultCost,
    ) -> DefaultCost {
        TreeAdditiveCostModel {}.fold(_head, children_cost, head_cost)
    }

    fn enode_cost(
        &self,
        egraph: &EGraph,
        func: &egglog::Function,
        row: &egglog::FunctionRow<'_>,
    ) -> DefaultCost {
        let name = get_cost_table_name(func.name());
        let key = row.vals.split_last().unwrap().1;
        if egraph.get_function(&name).is_some() {
            egraph
                .lookup_function(&name, key)
                .map(|c| {
                    let cost = egraph.value_to_base::<i64>(c);
                    assert!(cost >= 0);
                    cost as DefaultCost
                })
                .unwrap_or_else(|| TreeAdditiveCostModel {}.enode_cost(egraph, func, row))
        } else {
            TreeAdditiveCostModel {}.enode_cost(egraph, func, row)
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
        extract_with_cost_model(egraph, args, DynamicCostModel)
    }
}

/// Run an `(extract expr)` or `(extract expr n)` using the given cost model.
/// Parses args, evaluates n if present, and dispatches to extract-best or extract-variants.
pub(crate) fn extract_with_cost_model<CM>(
    egraph: &mut egglog::EGraph,
    args: &[Expr],
    cost_model: CM,
) -> Result<Vec<CommandOutput>, egglog::Error>
where
    CM: CostModel<DefaultCost> + Clone + 'static,
{
    let (expr, variants) = match args {
        [expr] => (expr, 0usize),
        [expr, n_expr] => {
            let (n_sort, n_val) = egraph.eval_expr(n_expr)?;
            if n_sort.name() != "i64" {
                let i64sort = egraph.get_arcsort_by(|s| s.name() == "i64");
                return Err(egglog::Error::TypeError(egglog::TypeError::Mismatch {
                    expr: n_expr.clone(),
                    expected: i64sort,
                    actual: n_sort,
                }));
            }
            let n = egraph.value_to_base::<i64>(n_val);
            assert!(n >= 0, "Cannot extract negative number of variants");
            (expr, n as usize)
        }
        _ => panic!("extract takes 1 or 2 arguments"),
    };
    let (sort, value) = egraph.eval_expr(expr)?;
    let extractor = Extractor::compute_costs_from_rootsorts(Some(vec![sort]), egraph, cost_model);
    let mut termdag = TermDag::default();
    if variants == 0 {
        if let Some((cost, term)) = extractor.extract_best(egraph, &mut termdag, value) {
            if log_enabled!(log::Level::Info) {
                log::info!("extracted with cost {cost}: {}", termdag.to_string(term));
            }
            Ok(vec![CommandOutput::ExtractBest(termdag, cost, term)])
        } else {
            Err(egglog::Error::ExtractError(
                "Unable to find any valid extraction (likely due to subsume or delete)".to_string(),
            ))
        }
    } else {
        let terms: Vec<TermId> = extractor
            .extract_variants(egraph, &mut termdag, value, variants)
            .iter()
            .map(|e| e.1)
            .collect();
        Ok(vec![CommandOutput::ExtractVariants(termdag, terms)])
    }
}
