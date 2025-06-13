use std::sync::Arc;

use egglog::{
    ast::*,
    extract::{CostModel, Extractor, TreeAdditiveCostModel},
    util::FreshGen,
    EGraph, Error, Term, TermDag, TypeError, UserDefinedCommand,
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
        "with-custom-cost"
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
    let commands = variants
        .iter()
        .map(|v| {
            let cost_table_name = get_cost_table_name(&v.name);
            let cost_table_schema = Schema::new(v.types.clone(), "i64".into());

            Command::Function {
                span: v.span.clone(),
                name: cost_table_name,
                schema: cost_table_schema,
                merge: None,
            }
        })
        .collect::<Vec<_>>();

    commands
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

struct CustomCostModel;

impl CostModel<usize> for CustomCostModel {
    fn fold(&self, _head: &str, children_cost: &[usize], head_cost: usize) -> usize {
        TreeAdditiveCostModel {}.fold(_head, children_cost, head_cost)
    }

    fn enode_cost(
        &self,
        egraph: &EGraph,
        func: &egglog::Function,
        row: &egglog::FunctionRow<'_>,
    ) -> usize {
        let name = get_cost_table_name(func.name());
        let key = row.vals.split_last().unwrap().1;
        if egraph.get_function(&name).is_some() {
            egraph
                .lookup_function(&name, key)
                .map(|c| {
                    let cost = egraph.value_to_base::<i64>(c);
                    assert!(cost >= 0);
                    cost as usize
                })
                .unwrap_or_else(|| TreeAdditiveCostModel {}.enode_cost(egraph, func, row))
        } else {
            TreeAdditiveCostModel {}.enode_cost(egraph, func, row)
        }
    }
}

struct CustomExtract;

impl UserDefinedCommand for CustomExtract {
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<(), Error> {
        assert!(args.len() <= 2);
        let (sort, value) = egraph.eval_expr(&args[0])?;
        let n = args.get(1).map(|arg| egraph.eval_expr(arg)).transpose()?;
        let n = if let Some(nv) = n {
            // TODO: egglog does not yet support u64
            if nv.0.name() != "i64" {
                let i64sort = egraph.get_arcsort_by(|s| s.name() == "i64");
                return Err(Error::TypeError(TypeError::Mismatch {
                    expr: args[1].clone(),
                    expected: i64sort,
                    actual: nv.0,
                }));
            }
            egraph.value_to_base::<i64>(nv.1)
        } else {
            0
        };

        let mut termdag = TermDag::default();

        let extractor = Extractor::compute_costs_from_rootsorts(
            Some(vec![sort.clone()]),
            egraph,
            CustomCostModel,
        );
        if n == 0 {
            if let Some((cost, term)) = extractor.extract_best(egraph, &mut termdag, value) {
                // dont turn termdag into a string if we have messages disabled for performance reasons
                if egraph.messages_enabled() {
                    let extracted = termdag.to_string(&term);
                    log::info!("extracted with cost {cost}: {extracted}");
                    egraph.print_msg(extracted);
                }
                // TODO: egraph.extract_report is private
                // A future implementation should make a egglog_experimental::EGraph
                // that provides a similar set of methods and overrides its own extract_report.
                //
                // egraph.extract_report = Some(ExtractReport::Best {
                //     termdag,
                //     cost,
                //     term,
                // });
            } else {
                return Err(Error::ExtractError(
                    "Unable to find any valid extraction (likely due to subsume or delete)"
                        .to_string(),
                ));
            }
        } else {
            if n < 0 {
                panic!("Cannot extract negative number of variants");
            }
            let terms: Vec<Term> = extractor
                .extract_variants(egraph, &mut termdag, value, n as usize)
                .iter()
                .map(|e| e.1.clone())
                .collect();
            // Same as above, avoid turning termdag into a string if we have messages disabled for performance
            if egraph.messages_enabled() {
                log::info!("extracted variants:");
                let mut msg = String::default();
                msg += "(\n";
                assert!(!terms.is_empty());
                for expr in &terms {
                    let str = termdag.to_string(expr);
                    log::info!("   {str}");
                    msg += &format!("   {str}\n");
                }
                msg += ")";
                egraph.print_msg(msg);
            }
            // TODO: Same as above. EGraph::extract_report is private.
            //
            // egraph.extract_report = Some(ExtractReport::Variants { termdag, terms });
        }
        Ok(())
    }
}
