use egglog::ast::{Expr, Literal};
use egglog::constraint::SimpleTypeConstraint;
use egglog::prelude::Span;
use egglog::sort::{FunctionContainer, literal_sort};
use egglog::{
    ArcSort, CommandOutput, Core, EGraph, Error, Primitive, PurePrim, PureState, ResolvedCall,
    ResolvedExpr, SpecializedPrimitive, TypeError, UserDefinedCommand, Value,
};
use std::any::TypeId;

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
        for sort in &input_sorts {
            reject_function_container_sort(
                sort,
                &args[1].span(),
                "input",
                "function-container inputs can carry table-backed functions whose reads are hidden from seminaive scheduling",
            )?;
        }
        reject_function_container_sort(
            &output_sort,
            &output_span,
            "output",
            "function-container outputs can later carry table-backed functions whose reads are hidden from seminaive scheduling",
        )?;

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
        let body = compile_resolved_body(&resolved_body)?;

        let body_output = resolved_expr_output_sort(&resolved_body);
        if body_output.name() != output_sort.name() {
            return Err(TypeError::Mismatch {
                expr: args[3].clone(),
                expected: output_sort,
                actual: body_output,
            }
            .into());
        }

        egraph.add_pure_primitive(
            DefinedPrimitive {
                name,
                input: input_sorts,
                output: output_sort,
                body,
            },
            None,
        );
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

}

impl PurePrim for DefinedPrimitive {
    fn apply<'a, 'db>(&self, mut state: PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
        eval_compiled_expr(&mut state, &self.body, args)
    }
}

#[derive(Clone)]
enum CompiledExpr {
    Lit(Literal),
    Arg(usize),
    Primitive(SpecializedPrimitive, Vec<CompiledExpr>),
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

fn reject_function_container_sort(
    sort: &ArcSort,
    span: &Span,
    role: &str,
    reason: &str,
) -> Result<(), Error> {
    if sort_contains_function_container(sort) {
        Err(backend_error(
            span.clone(),
            format!(
                "primitive {role} sort `{}` is not seminaive-safe: {reason}",
                sort.name()
            ),
        ))
    } else {
        Ok(())
    }
}

fn sort_contains_function_container(sort: &ArcSort) -> bool {
    sort.value_type() == Some(TypeId::of::<FunctionContainer>())
        || (sort.is_container_sort()
            && sort
                .inner_sorts()
                .iter()
                .any(sort_contains_function_container))
}

fn compile_resolved_body(expr: &ResolvedExpr) -> Result<CompiledExpr, Error> {
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
        ResolvedExpr::Call(_, ResolvedCall::Primitive(primitive), children) => {
            let compiled_children = children
                .iter()
                .map(compile_resolved_body)
                .collect::<Result<Vec<_>, _>>()?;
            for sort in primitive.input() {
                if sort_contains_function_container(sort) {
                    return Err(backend_error(
                        expr.span(),
                        format!(
                            "primitive body call to `{}` is not seminaive-safe: function-container arguments can carry table-backed functions whose reads are hidden from rule dependency analysis",
                            primitive.name()
                        ),
                    ));
                }
            }
            if sort_contains_function_container(primitive.output()) {
                return Err(backend_error(
                    expr.span(),
                    format!(
                        "primitive body call to `{}` is not seminaive-safe: primitive bodies may not produce function-container values",
                        primitive.name()
                    ),
                ));
            }
            Ok(CompiledExpr::Primitive(
                primitive.clone(),
                compiled_children,
            ))
        }
        ResolvedExpr::Call(span, ResolvedCall::Func(func), _) => Err(backend_error(
            span.clone(),
            format!(
                "primitive body call to table-backed function `{}` is not seminaive-safe: rule dependency analysis cannot see reads performed inside primitive bodies",
                func.name
            ),
        )),
    }
}

fn eval_compiled_expr<'a, 'db>(
    state: &mut impl Core<'a, 'db>,
    expr: &CompiledExpr,
    args: &[Value],
) -> Option<Value>
where
    'db: 'a,
{
    match expr {
        CompiledExpr::Lit(literal) => Some(match literal {
            Literal::Int(x) => state.base_values().get::<i64>(*x),
            Literal::Float(x) => state.base_values().get::<egglog::sort::F>(x.into()),
            Literal::String(x) => state
                .base_values()
                .get::<egglog::sort::S>(egglog::sort::S::new(x.clone())),
            Literal::Bool(x) => state.base_values().get::<bool>(*x),
            Literal::Unit => state.base_values().get::<()>(()),
        }),
        CompiledExpr::Arg(index) => args.get(*index).copied(),
        CompiledExpr::Primitive(primitive, children) => {
            let values = children
                .iter()
                .map(|child| eval_compiled_expr(state, child, args))
                .collect::<Option<Vec<_>>>()?;
            state.apply_primitive(primitive, &values)
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
