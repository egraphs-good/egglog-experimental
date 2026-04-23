use egglog::ast::{Expr, Literal};
use egglog::constraint::SimpleTypeConstraint;
use egglog::prelude::Span;
use egglog::sort::{FunctionContainer, ResolvedFunction, ResolvedFunctionId, literal_sort};
use egglog::{
    ArcSort, CommandOutput, EGraph, Error, ExecutionState, Primitive, ResolvedCall, ResolvedExpr,
    SpecializedPrimitive, TypeError, UserDefinedCommand, Value,
};

pub struct RegisterPrimitive;

impl UserDefinedCommand for RegisterPrimitive {
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<Option<CommandOutput>, Error> {
        if args.len() != 4 {
            return Err(backend_error(
                args.first().map(Expr::span).unwrap_or_else(|| Span::Panic),
                format!("primitive expects 4 arguments, got {}", args.len()),
            ));
        }

        let (name_span, name) = decode_atom(&args[0], "primitive name")?;
        ensure_name_available(egraph, &name, &name_span)?;

        let input_sort_names = decode_input_sort_names(&args[1])?;
        validate_positional_vars(&args[3], input_sort_names.len())?;

        let input_sorts = input_sort_names
            .iter()
            .map(|(span, sort_name)| resolve_sort(egraph, sort_name, span))
            .collect::<Result<Vec<_>, _>>()?;
        let (output_span, output_name) = decode_atom(&args[2], "output sort")?;
        let output_sort = resolve_sort(egraph, &output_name, &output_span)?;

        let bindings: Vec<_> = input_sorts
            .iter()
            .enumerate()
            .map(|(index, sort)| (format!("_{index}"), args[3].span(), sort.clone()))
            .collect();
        let resolved_body = egraph.typecheck_expr_with_bindings_and_output(
            &args[3],
            &bindings,
            output_sort.clone(),
        )?;
        let body = compile_resolved_body(egraph, &resolved_body)?;

        let body_output = resolved_expr_output_sort(&resolved_body);
        if body_output.name() != output_sort.name() {
            return Err(TypeError::Mismatch {
                expr: args[3].clone(),
                expected: output_sort,
                actual: body_output,
            }
            .into());
        }

        egraph.add_primitive(DefinedPrimitive {
            name,
            input: input_sorts,
            output: output_sort,
            body,
        });
        Ok(None)
    }
}

#[derive(Clone)]
struct DefinedPrimitive {
    name: String,
    input: Vec<ArcSort>,
    output: ArcSort,
    body: CompiledExpr,
}

impl Primitive for DefinedPrimitive {
    fn name(&self) -> &str {
        &self.name
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn egglog::constraint::TypeConstraint> {
        let mut sorts = self.input.clone();
        sorts.push(self.output.clone());
        SimpleTypeConstraint::new(self.name(), sorts, span.clone()).into_box()
    }

    fn apply(&self, exec_state: &mut ExecutionState<'_>, args: &[Value]) -> Option<Value> {
        eval_compiled_expr(exec_state, &self.body, args)
    }
}

#[derive(Clone)]
enum CompiledExpr {
    Lit(Literal),
    Arg(usize),
    FunctionValue(ResolvedFunctionId, Vec<ArcSort>, String, Vec<CompiledExpr>),
    Primitive(SpecializedPrimitive, Vec<CompiledExpr>),
    Func(FunctionContainer, Vec<CompiledExpr>),
}

fn decode_atom(expr: &Expr, position: &str) -> Result<(Span, String), Error> {
    match expr {
        Expr::Var(span, name) => Ok((span.clone(), name.clone())),
        _ => Err(backend_error(
            expr.span(),
            format!("{position} must be an atom"),
        )),
    }
}

fn decode_input_sort_names(expr: &Expr) -> Result<Vec<(Span, String)>, Error> {
    match expr {
        Expr::Lit(_, Literal::Unit) => Ok(vec![]),
        Expr::Var(span, name) => Ok(vec![(span.clone(), name.clone())]),
        Expr::Call(span, head, args) => {
            let mut names = Vec::with_capacity(args.len() + 1);
            names.push((span.clone(), head.clone()));
            for arg in args {
                match arg {
                    Expr::Var(arg_span, name) => names.push((arg_span.clone(), name.clone())),
                    _ => {
                        return Err(backend_error(
                            arg.span(),
                            "input sort list must only contain sort atoms".to_string(),
                        ));
                    }
                }
            }
            Ok(names)
        }
        _ => Err(backend_error(
            expr.span(),
            "input sort list must be (), a sort atom, or a flat list of sort atoms".to_string(),
        )),
    }
}

fn validate_positional_vars(body: &Expr, arity: usize) -> Result<(), Error> {
    let mut failure = None;
    body.visit_vars(&mut |span, name| {
        if failure.is_some() {
            return;
        }
        let Some(index) = parse_positional_index(name) else {
            failure = Some(backend_error(
                span.clone(),
                format!(
                    "primitive body variables must be positional (_0, _1, ...), found `{name}`"
                ),
            ));
            return;
        };
        if index >= arity {
            failure = Some(backend_error(
                span.clone(),
                format!("primitive body variable `{name}` is out of range for arity {arity}"),
            ));
        }
    });
    match failure {
        Some(err) => Err(err),
        None => Ok(()),
    }
}

fn parse_positional_index(name: &str) -> Option<usize> {
    name.strip_prefix('_')?.parse().ok()
}

fn ensure_name_available(egraph: &mut EGraph, name: &str, span: &Span) -> Result<(), Error> {
    if egraph.get_sort_by_name(name).is_some() {
        return Err(TypeError::SortAlreadyBound(name.to_owned(), span.clone()).into());
    }
    if egraph.type_info().get_func_type(name).is_some() {
        return Err(TypeError::FunctionAlreadyBound(name.to_owned(), span.clone()).into());
    }
    if egraph.type_info().get_prims(name).is_some() {
        return Err(TypeError::PrimitiveAlreadyBound(name.to_owned(), span.clone()).into());
    }
    Ok(())
}

fn resolve_sort(egraph: &EGraph, name: &str, span: &Span) -> Result<ArcSort, Error> {
    egraph
        .get_sort_by_name(name)
        .cloned()
        .ok_or_else(|| TypeError::UndefinedSort(name.to_owned(), span.clone()).into())
}

fn compile_resolved_body(egraph: &mut EGraph, expr: &ResolvedExpr) -> Result<CompiledExpr, Error> {
    match expr {
        ResolvedExpr::Lit(_, literal) => Ok(CompiledExpr::Lit(literal.clone())),
        ResolvedExpr::Var(span, resolved_var) => {
            let Some(index) = parse_positional_index(&resolved_var.name) else {
                return Err(backend_error(
                    span.clone(),
                    format!(
                        "primitive body variables must be positional (_0, _1, ...), found `{}`",
                        resolved_var.name
                    ),
                ));
            };
            Ok(CompiledExpr::Arg(index))
        }
        ResolvedExpr::Call(_, ResolvedCall::Primitive(primitive), children)
            if primitive.name() == "unstable-fn" =>
        {
            compile_unstable_fn(egraph, primitive, children)
        }
        ResolvedExpr::Call(_, ResolvedCall::Primitive(primitive), children) => {
            Ok(CompiledExpr::Primitive(
                primitive.clone(),
                children
                    .iter()
                    .map(|child| compile_resolved_body(egraph, child))
                    .collect::<Result<Vec<_>, _>>()?,
            ))
        }
        ResolvedExpr::Call(_, ResolvedCall::Func(func), children) => Ok(CompiledExpr::Func(
            egraph.function_container_for_name(&func.name)?,
            children
                .iter()
                .map(|child| compile_resolved_body(egraph, child))
                .collect::<Result<Vec<_>, _>>()?,
        )),
    }
}

fn compile_unstable_fn(
    egraph: &mut EGraph,
    primitive: &SpecializedPrimitive,
    children: &[ResolvedExpr],
) -> Result<CompiledExpr, Error> {
    let [
        ResolvedExpr::Lit(_, Literal::String(name)),
        partial_children @ ..,
    ] = children
    else {
        return Err(backend_error(
            children
                .first()
                .map(ResolvedExpr::span)
                .unwrap_or_else(|| Span::Panic),
            "unstable-fn requires a literal string function name".to_string(),
        ));
    };

    let ResolvedFunction {
        id: resolved_id,
        partial_arcsorts,
        name: resolved_name,
    } = egraph.resolve_function_container_target(name, primitive)?;
    Ok(CompiledExpr::FunctionValue(
        resolved_id,
        partial_arcsorts,
        resolved_name,
        partial_children
            .iter()
            .map(|child| compile_resolved_body(egraph, child))
            .collect::<Result<Vec<_>, _>>()?,
    ))
}

fn eval_compiled_expr(
    exec_state: &mut ExecutionState<'_>,
    expr: &CompiledExpr,
    args: &[Value],
) -> Option<Value> {
    match expr {
        CompiledExpr::Lit(literal) => Some(match literal {
            Literal::Int(x) => exec_state.base_values().get::<i64>(*x),
            Literal::Float(x) => exec_state.base_values().get::<egglog::sort::F>(x.into()),
            Literal::String(x) => exec_state
                .base_values()
                .get::<egglog::sort::S>(egglog::sort::S::new(x.clone())),
            Literal::Bool(x) => exec_state.base_values().get::<bool>(*x),
            Literal::Unit => exec_state.base_values().get::<()>(()),
        }),
        CompiledExpr::Arg(index) => args.get(*index).copied(),
        CompiledExpr::FunctionValue(id, partial_arcsorts, name, children) => {
            let values = children
                .iter()
                .map(|child| eval_compiled_expr(exec_state, child, args))
                .collect::<Option<Vec<_>>>()?;
            let partial_values = partial_arcsorts
                .iter()
                .cloned()
                .zip(values)
                .collect::<Vec<_>>();
            let value = FunctionContainer(id.clone(), partial_values, name.clone());
            Some(
                exec_state
                    .clone()
                    .container_values()
                    .register_val(value, exec_state),
            )
        }
        CompiledExpr::Primitive(primitive, children) => {
            let values = children
                .iter()
                .map(|child| eval_compiled_expr(exec_state, child, args))
                .collect::<Option<Vec<_>>>()?;
            primitive.apply(exec_state, &values)
        }
        CompiledExpr::Func(action, children) => {
            let values = children
                .iter()
                .map(|child| eval_compiled_expr(exec_state, child, args))
                .collect::<Option<Vec<_>>>()?;
            action.apply(exec_state, &values)
        }
    }
}

fn resolved_expr_output_sort(expr: &ResolvedExpr) -> ArcSort {
    match expr {
        ResolvedExpr::Lit(_, literal) => literal_sort(literal),
        ResolvedExpr::Var(_, resolved_var) => resolved_var.sort.clone(),
        ResolvedExpr::Call(_, resolved_call, _) => resolved_call.output().clone(),
    }
}

fn backend_error(span: Span, message: String) -> Error {
    Error::BackendError(format!("{span}\n{message}"))
}
