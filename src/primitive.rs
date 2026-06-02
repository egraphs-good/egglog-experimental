use egglog::ast::{Expr, FunctionSubtype, Literal};
use egglog::constraint::SimpleTypeConstraint;
use egglog::prelude::Span;
use egglog::sort::FunctionSort;
use egglog::{
    ArcSort, CommandOutput, Context, Core, EGraph, Error, FullPrim, FullState, Primitive, PurePrim,
    PureState, ReadPrim, ReadState, ResolvedCall, ResolvedExpr, TypeError, UserDefinedCommand,
    Value, WritePrim, WriteState,
};
use std::sync::Arc;

pub(crate) struct RegisterPrimitive;

impl UserDefinedCommand for RegisterPrimitive {
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        if args.len() != 4 {
            return Err(backend_error(
                args.first().map(Expr::span).unwrap_or_else(|| Span::Panic),
                format!("primitive expects 4 arguments, got {}", args.len()),
            ));
        }

        let (name_span, name) = decode_atom(&args[0], "primitive name")?;
        ensure_name_available(egraph, &name, &name_span)?;

        let input_sort_names = decode_input_sort_names(&args[1])?;
        let input_var_names: Vec<_> = (0..input_sort_names.len())
            .map(|index| format!("_{index}"))
            .collect();

        let input_sorts = input_sort_names
            .iter()
            .map(|(span, sort_name)| resolve_sort(egraph, sort_name, span))
            .collect::<Result<Vec<_>, _>>()?;
        let (output_span, output_name) = decode_atom(&args[2], "output sort")?;
        let output_sort = resolve_sort(egraph, &output_name, &output_span)?;

        let bindings: Vec<_> = input_var_names
            .iter()
            .zip(&input_sorts)
            .map(|(name, sort)| (name.clone(), args[3].span(), sort.clone()))
            .collect();

        let mut last_error = None;
        let mut typechecked_body = None;
        for context in [Context::Pure, Context::Read, Context::Write, Context::Full] {
            match egraph.typecheck_expr_with_bindings_and_output(
                &args[3],
                &bindings,
                output_sort.clone(),
                context,
            ) {
                Ok(resolved)
                    if matches!(
                        (required_context(egraph, &resolved), context),
                        (Context::Pure, _)
                            | (Context::Read, Context::Read | Context::Full)
                            | (Context::Write, Context::Write | Context::Full)
                            | (Context::Full, Context::Full)
                    ) =>
                {
                    typechecked_body = Some((resolved, context));
                    break;
                }
                Ok(_) => {}
                Err(err) => last_error = Some(err),
            }
        }
        let Some((body, context)) = typechecked_body else {
            return Err(last_error
                .expect("primitive body typechecking always tries at least one context")
                .into());
        };

        let (body, hidden_bindings) = egraph.prepare_unstable_fn_targets_for_eval(&body)?;
        let primitive = DefinedPrimitive {
            name,
            input_vars: input_var_names,
            input: input_sorts,
            output: output_sort,
            body,
            hidden_bindings,
        };
        match context {
            Context::Pure => egraph.add_pure_primitive(primitive, None),
            Context::Read => egraph.add_read_primitive(primitive, None),
            Context::Write => egraph.add_write_primitive(primitive, None),
            Context::Full => egraph.add_full_primitive(primitive, None),
        }
        Ok(vec![])
    }
}

#[derive(Clone)]
struct DefinedPrimitive {
    name: String,
    input_vars: Vec<String>,
    input: Vec<ArcSort>,
    output: ArcSort,
    body: ResolvedExpr,
    hidden_bindings: Vec<(String, Value)>,
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
        self.eval(&mut state, args)
    }
}

impl ReadPrim for DefinedPrimitive {
    fn apply<'a, 'db>(&self, mut state: ReadState<'a, 'db>, args: &[Value]) -> Option<Value> {
        self.eval(&mut state, args)
    }
}

impl WritePrim for DefinedPrimitive {
    fn apply<'a, 'db>(&self, mut state: WriteState<'a, 'db>, args: &[Value]) -> Option<Value> {
        self.eval(&mut state, args)
    }
}

impl FullPrim for DefinedPrimitive {
    fn apply<'a, 'db>(&self, mut state: FullState<'a, 'db>, args: &[Value]) -> Option<Value> {
        self.eval(&mut state, args)
    }
}

impl DefinedPrimitive {
    fn eval<'a, 'db>(&self, state: &mut impl Core<'a, 'db>, args: &[Value]) -> Option<Value>
    where
        'db: 'a,
    {
        let mut bindings: Vec<_> = self
            .hidden_bindings
            .iter()
            .map(|(name, value)| (name.as_str(), *value))
            .collect();
        bindings.extend(
            self.input_vars
                .iter()
                .map(String::as_str)
                .zip(args.iter().copied()),
        );
        state.eval_resolved_expr(&self.body, &bindings)
    }
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

fn required_context(egraph: &mut EGraph, expr: &ResolvedExpr) -> Context {
    match expr {
        ResolvedExpr::Lit(_, _) | ResolvedExpr::Var(_, _) => Context::Pure,
        ResolvedExpr::Call(_, resolved_call, children) => {
            let call_context = match resolved_call {
                ResolvedCall::Primitive(primitive) if primitive.name() == "unstable-fn" => {
                    match children.first() {
                        Some(ResolvedExpr::Lit(_, Literal::String(name))) => {
                            let type_info = egraph.type_info();
                            if let Some(func) = type_info.get_func_type(name) {
                                match func.subtype {
                                    FunctionSubtype::Constructor => Context::Write,
                                    FunctionSubtype::Custom => Context::Read,
                                }
                            } else if let Ok(fn_sort) = Arc::downcast::<FunctionSort>(
                                primitive.output().clone().as_arc_any(),
                            ) {
                                let types: Vec<_> = primitive
                                    .input()
                                    .iter()
                                    .skip(1)
                                    .cloned()
                                    .chain(fn_sort.inputs().iter().cloned())
                                    .chain(std::iter::once(fn_sort.output()))
                                    .collect();

                                let can_run_in = |context| {
                                    type_info.get_prims(name).into_iter().flatten().any(|p| {
                                        p.accept(&types, type_info)
                                            && p.is_valid_in_context(context)
                                    })
                                };
                                if can_run_in(Context::Pure) {
                                    Context::Pure
                                } else if can_run_in(Context::Read) && !can_run_in(Context::Write) {
                                    Context::Read
                                } else if can_run_in(Context::Write) && !can_run_in(Context::Read) {
                                    Context::Write
                                } else {
                                    Context::Full
                                }
                            } else {
                                Context::Full
                            }
                        }
                        _ => Context::Full,
                    }
                }
                ResolvedCall::Primitive(_) => Context::Pure,
                ResolvedCall::Func(func) => match func.subtype {
                    FunctionSubtype::Constructor => Context::Write,
                    FunctionSubtype::Custom => Context::Read,
                },
            };
            let mut context = call_context;
            for child in children {
                context = match (context, required_context(egraph, child)) {
                    (Context::Full, _) | (_, Context::Full) => Context::Full,
                    (Context::Read, Context::Write) | (Context::Write, Context::Read) => {
                        Context::Full
                    }
                    (Context::Read, _) | (_, Context::Read) => Context::Read,
                    (Context::Write, _) | (_, Context::Write) => Context::Write,
                    (Context::Pure, Context::Pure) => Context::Pure,
                };
            }
            context
        }
    }
}

fn backend_error(span: Span, message: String) -> Error {
    Error::BackendError(format!("{span}\n{message}"))
}
