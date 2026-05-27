use egglog::ast::{Expr, FunctionSubtype, Literal};
use egglog::constraint::SimpleTypeConstraint;
use egglog::prelude::Span;
use egglog::{
    ArcSort, CommandOutput, Context, Core, EGraph, Error, FullPrim, FullState, Primitive, PurePrim,
    PureState, ReadPrim, ReadState, ResolvedCall, ResolvedExpr, TypeError, UserDefinedCommand,
    Value, WritePrim, WriteState,
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

        let input_sorts = input_sort_names
            .iter()
            .map(|(span, sort_name)| resolve_sort(egraph, sort_name, span))
            .collect::<Result<Vec<_>, _>>()?;
        let (output_span, output_name) = decode_atom(&args[2], "output sort")?;
        let output_sort = resolve_sort(egraph, &output_name, &output_span)?;

        let input_var_names: Vec<_> = (0..input_sorts.len())
            .map(|index| format!("_{index}"))
            .collect();
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
                Ok(resolved) if required_context(&resolved).is_allowed_in(context) => {
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

        let primitive = DefinedPrimitive {
            name,
            input_vars: input_var_names,
            input: input_sorts,
            output: output_sort,
            body,
        };
        match context {
            Context::Pure => egraph.add_pure_primitive(primitive, None),
            Context::Read => egraph.add_read_primitive(primitive, None),
            Context::Write => egraph.add_write_primitive(primitive, None),
            Context::Full => egraph.add_full_primitive(primitive, None),
        }
        Ok(None)
    }
}

#[derive(Clone)]
struct DefinedPrimitive {
    name: String,
    input_vars: Vec<String>,
    input: Vec<ArcSort>,
    output: ArcSort,
    body: ResolvedExpr,
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
        let bindings: Vec<_> = self
            .input_vars
            .iter()
            .map(String::as_str)
            .zip(args.iter().copied())
            .collect();
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

#[derive(Clone, Copy, PartialEq, Eq)]
enum RequiredContext {
    Pure,
    Read,
    Write,
    Full,
}

impl RequiredContext {
    fn combine(self, other: Self) -> Self {
        match (self, other) {
            (Self::Full, _) | (_, Self::Full) => Self::Full,
            (Self::Read, Self::Write) | (Self::Write, Self::Read) => Self::Full,
            (Self::Read, _) | (_, Self::Read) => Self::Read,
            (Self::Write, _) | (_, Self::Write) => Self::Write,
            (Self::Pure, Self::Pure) => Self::Pure,
        }
    }

    fn is_allowed_in(self, context: Context) -> bool {
        match self {
            Self::Pure => true,
            Self::Read => matches!(context, Context::Read | Context::Full),
            Self::Write => matches!(context, Context::Write | Context::Full),
            Self::Full => matches!(context, Context::Full),
        }
    }
}

fn required_context(expr: &ResolvedExpr) -> RequiredContext {
    match expr {
        ResolvedExpr::Lit(_, _) | ResolvedExpr::Var(_, _) => RequiredContext::Pure,
        ResolvedExpr::Call(_, resolved_call, children) => {
            let call_context = match resolved_call {
                ResolvedCall::Primitive(_) => RequiredContext::Pure,
                ResolvedCall::Func(func) => match func.subtype {
                    FunctionSubtype::Constructor => RequiredContext::Write,
                    FunctionSubtype::Custom => RequiredContext::Read,
                },
            };
            children
                .iter()
                .map(required_context)
                .fold(call_context, RequiredContext::combine)
        }
    }
}

fn backend_error(span: Span, message: String) -> Error {
    Error::BackendError(format!("{span}\n{message}"))
}
