use std::{iter, sync::Arc};

use egglog::{
    ast::{
        Action, Command, Expr, Macro, ParseError, Parser, Schema, Sexp, Span, Subdatatypes, Symbol,
        Variant,
    },
    extract::{CostModel, Extractor, TreeAdditiveCostModel},
    util::FreshGen,
    ArcSort, EGraph, Error, Term, TermDag, TypeError, UserDefinedCommand, Value,
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
    fn name(&self) -> Symbol {
        "set-cost".into()
    }

    fn parse(
        &self,
        args: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Action>, ParseError> {
        let actions = match args {
            [call, value] => {
                let (func, args, call_span) = call.expect_call("table lookup")?;
                let cost_table_name = get_cost_table_name(func);
                let args = map_fallible(args, parser, Parser::parse_expr)?;
                let value = parser.parse_expr(value)?;

                let vs = (0..args.len())
                    .map(|_| parser.symbol_gen.fresh(&"set_cost_var".into()))
                    .collect::<Vec<Symbol>>();
                let (args, mut actions): (Vec<Expr>, Vec<Action>) = vs
                    .iter()
                    .zip(args)
                    .map(|(v, e)| {
                        let span = e.span().clone();
                        (Expr::Var(span.clone(), *v), Action::Let(span, *v, e))
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
                "usage: (set (<table name> <expr>*) <expr>)".into(),
            )),
        };
        actions
    }
}

struct SetCostDeclarations;

impl Macro<Vec<Command>> for SetCostDeclarations {
    fn name(&self) -> Symbol {
        "with-custom-cost".into()
    }

    fn parse(
        &self,
        decls: &[Sexp],
        _span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Command>, ParseError> {
        let mut commands = Vec::new();
        for decl in decls {
            let (head, args, span) = decl.expect_call("datatype declaration")?;
            let command = parse_decl(head, args, span, parser)?;
            commands.extend(command);
        }
        Ok(commands)
    }
}

fn parse_decl(head: Symbol, args: &[Sexp], span: Span, parser: &mut Parser) -> Result<Vec<Command>, ParseError> {
    match head.as_str() {
        "datatype" => match args {
            [name, variants @ ..] => {
                let variants = map_fallible(variants, parser, Parser::variant)?;
                let mut commands = generate_cost_table_commands_from_variants(&variants);
                commands.insert(
                    0,
                    Command::Datatype {
                        span: span.clone(),
                        name: name.expect_atom("sort name")?,
                        variants,
                    },
                );
                Ok(commands)
            }
            _ => Err(ParseError(
                span,
                format!("usage: (datatype <name> <variant>*)"),
            )),
        },
        "datatype*" => {
            let datatypes = map_fallible(args, parser, Parser::rec_datatype)?;
            let mut commands: Vec<_> = datatypes
                .iter()
                .flat_map(|(_span, _name, subdatatypes)| match subdatatypes {
                    Subdatatypes::Variants(variants) => {
                        let commands =
                            generate_cost_table_commands_from_variants(&variants);
                        commands
                    }
                    _ => vec![],
                })
                .collect();
            commands.insert(0, Command::Datatypes { span, datatypes });
            Ok(commands)
        }
        "constructor" => {
            let result = match args {
                [name, inputs, output, rest @ ..] => {
                    let mut cost = None;
                    let mut unextractable = false;
                    match parser.parse_options(rest)?.as_slice() {
                        [] => {}
                        [(":unextractable", [])] => unextractable = true,
                        [(":cost", [c])] => cost = Some(c.expect_uint("cost")?),
                        _ => {
                            return Err(ParseError(
                                span,
                                format!("could not parse constructor options"),
                            ))
                        }
                    }

                    let name = name.expect_atom("constructor name")?;
                    let schema = parser.parse_schema(inputs, output)?;

                    let cost_table_command = if !unextractable {
                        let cost_table_name = get_cost_table_name(name);
                        let mut cost_table_schema = schema.clone();
                        cost_table_schema.output = "i64".into();

                        Some(Command::Function {
                            span: span.clone(),
                            name: cost_table_name.into(),
                            schema: cost_table_schema,
                            merge: None,
                        })
                    } else {
                        None
                    };

                    let commands: Vec<_> = iter::once(Command::Constructor {
                        span: span.clone(),
                        name,
                        schema,
                        cost,
                        unextractable,
                    })
                    .chain(cost_table_command)
                    .collect();

                    commands
                }
                _ => {
                    let a = "(constructor <name> (<input sort>*) <output sort>)";
                    let b =
                        "(constructor <name> (<input sort>*) <output sort> :cost <cost>)";
                    let c =
                        "(constructor <name> (<input sort>*) <output sort> :unextractable)";
                    return Err(ParseError(span, format!("usages:\n{a}\n{b}\n{c}")));
                }
            };
            Ok(result)
        }
        _ => Err(ParseError(
            span,
            format!("unknown declaration: {head}"),
        )),
    }
}

fn generate_cost_table_commands_from_variants(variants: &[Variant]) -> Vec<Command> {
    let commands = variants
        .iter()
        .map(|v| {
            let cost_table_name = get_cost_table_name(v.name);
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

fn get_cost_table_name(name: Symbol) -> Symbol {
    format!("cost_table_{name}").into()
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
    fn fold(&self, _head: Symbol, children_cost: &[usize], head_cost: usize) -> usize {
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
                    let cost = egraph.value_to_rust::<i64>(c);
                    assert!(cost >= 0);
                    cost as usize
                })
                .unwrap_or_else(|| TreeAdditiveCostModel {}.enode_cost(egraph, func, row))
        } else {
            TreeAdditiveCostModel {}.enode_cost(egraph, func, row)
        }
    }

    fn container_primitive(
        &self,
        egraph: &EGraph,
        sort: &ArcSort,
        value: Value,
        element_costs: &[usize],
    ) -> usize {
        TreeAdditiveCostModel {}.container_primitive(egraph, sort, value, element_costs)
    }

    fn leaf_primitive(&self, egraph: &EGraph, sort: &ArcSort, value: Value) -> usize {
        TreeAdditiveCostModel {}.leaf_primitive(egraph, sort, value)
    }
}

struct CustomExtract;

impl UserDefinedCommand for CustomExtract {
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<(), Error> {
        assert!(args.len() <= 2);
        let (sort, value) = egraph.eval_expr(&args[0])?;
        let n = args.get(1).map(|arg| egraph.eval_expr(&arg)).transpose()?;
        let n = if let Some(nv) = n {
            // TODO: egglog does not yet support u64
            if nv.0.name().as_str() != "i64" {
                let i64sort = egraph.get_arcsort_by(|s| s.name().as_str() == "i64");
                return Err(Error::TypeError(TypeError::Mismatch {
                    expr: args[1].clone(),
                    expected: i64sort,
                    actual: nv.0,
                }));
            }
            egraph.value_to_rust::<i64>(nv.1)
        } else {
            0
        };

        let mut termdag = TermDag::default();

        let extractor = Extractor::compute_costs_from_rootsorts(
            Some(vec![sort.clone()]),
            &egraph,
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
