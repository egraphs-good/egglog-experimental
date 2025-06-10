use std::{iter, sync::Arc};

use egglog::{
    ast::{
        Action, Command, Expr, Macro, ParseError, Parser, Schema, Sexp, Span, Symbol,
        Variant,
    }, extract::{Cost, CostModel, TreeAdditiveCostModel}, prelude, ArcSort, EGraph, Error, UserDefinedCommand, Value
};

pub fn add_set_cost(egraph: &mut EGraph) {
    egraph
        .parser
        .add_command_macro(Arc::new(SetCostConstructors));
    egraph.parser.add_command_macro(Arc::new(SetCostDatatypes));
    egraph.parser.add_action_macro(Arc::new(SetCost));
    egraph.add_command("extract".into(), Arc::new(CustomExtract)).unwrap();
    // TODO: we have not handled datatype*
}

pub struct SetCost;

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
                let (func, args, _) = call.expect_call("table lookup")?;
                let cost_table_name = get_cost_table_name(func);
                let args = map_fallible(args, parser, Parser::parse_expr)?;
                let value = parser.parse_expr(value)?;
                Ok(vec![Action::Set(span, cost_table_name, args, value)])
            }
            _ => Err(ParseError(
                span,
                "usage: (set (<table name> <expr>*) <expr>)".into(),
            )),
        };
        actions
    }
}

pub struct SetCostConstructors;

impl Macro<Vec<Command>> for SetCostConstructors {
    fn name(&self) -> Symbol {
        "constructor".into()
    }

    fn parse(
        &self,
        args: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Command>, ParseError> {
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
                    cost_table_schema.output = "f64".into();

                    Some(Command::Function {
                        span: span.clone(),
                        name: cost_table_name.into(),
                        schema: cost_table_schema,
                        merge: Some(Expr::Call(
                            span.clone(),
                            "min".into(),
                            vec![
                                Expr::Var(span.clone(), "old".into()),
                                Expr::Var(span.clone(), "new".into()),
                            ],
                        )),
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
                let b = "(constructor <name> (<input sort>*) <output sort> :cost <cost>)";
                let c = "(constructor <name> (<input sort>*) <output sort> :unextractable)";
                return Err(ParseError(span, format!("usages:\n{a}\n{b}\n{c}")));
            }
        };
        Ok(result)
    }
}

pub struct SetCostDatatypes;

impl SetCostDatatypes {
    pub fn variant(parser: &mut Parser, sexp: &Sexp) -> Result<Variant, ParseError> {
        let (name, tail, span) = sexp.expect_call("datatype variant")?;

        let (types, cost) = match tail {
            [types @ .., Sexp::Atom(o, _), c] if *o == ":cost".into() => {
                (types, Some(c.expect_uint("cost")?))
            }
            types => (types, None),
        };

        Ok(Variant {
            span,
            name,
            types: map_fallible(types, parser, |_, sexp| {
                sexp.expect_atom("variant argument type")
            })?,
            cost,
        })
    }
}

impl Macro<Vec<Command>> for SetCostDatatypes {
    fn name(&self) -> Symbol {
        "datatype".into()
    }

    fn parse(
        &self,
        args: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Command>, ParseError> {
        match args {
            [name, variants @ ..] => {
                let variants = map_fallible(variants, parser, Self::variant)?;
                let mut commands = variants
                    .iter()
                    .map(|v| {
                        let cost_table_name = get_cost_table_name(v.name);
                        let cost_table_schema = Schema::new(v.types.clone(), "f64".into());

                        Command::Function {
                            span: v.span.clone(),
                            name: cost_table_name,
                            schema: cost_table_schema,
                            merge: Some(Expr::Call(
                                v.span.clone(),
                                "min".into(),
                                vec![
                                    Expr::Var(v.span.clone(), "old".into()),
                                    Expr::Var(v.span.clone(), "new".into()),
                                ],
                            )),
                        }
                    })
                    .collect::<Vec<_>>();
                commands.push(Command::Datatype {
                    span: span.clone(),
                    name: name.expect_atom("sort name")?,
                    variants,
                });
                Ok(commands)
            }
            _ => Err(ParseError(
                span,
                format!("usage: (datatype <name> <variant>*)"),
            )),
        }
    }
}

fn get_cost_table_name(name: Symbol) -> Symbol {
    format!("<experimental>cost_table_{name}").into()
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

pub struct CustomCostModel;

impl CostModel for CustomCostModel {
    fn fold(&self, _head: Symbol, children_cost: &[Cost], head_cost: Cost) -> Cost {
        TreeAdditiveCostModel {}
            .fold(_head, children_cost, head_cost)
    }

    fn enode_cost(
        &self,
        egraph: &EGraph,
        func: &egglog::Function,
        // TODO: this is not exposed
        row: &egglog_bridge::FunctionRow,
    ) -> Cost {
        // TODO: I don't know what to do here.
        // prelude::query takes an mutable E-graph
        // there is lookup method.
        // eval_expr may create entries in the E-graph.
        //
        // egraph.eval_expr(expr)
        // prelude::query(
        //     egraph,
        //     func,
        //     row,
        // )
        todo!()
    }

    fn container_primitive(
        &self,
        egraph: &EGraph,
        sort: &ArcSort,
        value: Value,
        element_costs: &[Cost],
    ) -> Cost {
        TreeAdditiveCostModel {}
            .container_primitive(egraph, sort, value, element_costs)
    }

    fn leaf_primitive(&self, egraph: &EGraph, sort: &ArcSort, value: Value) -> Cost {
        TreeAdditiveCostModel {}
            .leaf_primitive(egraph, sort, value)
    }
}

pub struct CustomExtract;

impl UserDefinedCommand for CustomExtract {
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<(), Error> {
        todo!()
    }
}