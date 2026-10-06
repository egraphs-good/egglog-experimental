//! `(set-effectful e)`: mark the e-class of `e` as effectful.
//!
//! Like `set-cost`, this generates a table per sort rather than asking the
//! program to declare one. A post-parse [`CommandMacro`] sees each rule and
//! top-level action with its types, replaces `(set-effectful e)` by an
//! insertion into the relation `effsafe_effectful_<Sort>` for the sort of
//! `e`, and declares that relation the first time the sort is seen. The
//! extractor reads every such relation.
//!
//! The sort of `e` comes from egglog's own typechecker: the rule's body is
//! typechecked together with one synthetic fact per `let` action and per
//! `set-effectful` argument (`(= <fresh> <expr>)`), which types primitives,
//! containers and let-bound variables the same way the rule's actions would.

use egglog::ast::{Action, Command, Expr, Fact, ParseError, Rule};
use egglog::util::SymbolGen;
use egglog::{CommandMacro, Error, TypeInfo};
use rustc_hash::FxHashMap;

/// The macro's name in programs.
pub const SET_EFFECTFUL: &str = "set-effectful";

const RELATION_PREFIX: &str = "effsafe_effectful_";

/// The generated relation holding the effectful e-classes of `sort`.
pub fn effectful_relation(sort: &str) -> String {
    format!("{RELATION_PREFIX}{sort}")
}

/// The sort whose effectful e-classes `relation` holds, if it is one of ours.
pub fn effectful_relation_sort(relation: &str) -> Option<&str> {
    relation.strip_prefix(RELATION_PREFIX)
}

/// The `set-effectful` command macro; see the module docs.
pub struct SetEffectful;

impl CommandMacro for SetEffectful {
    fn transform(
        &self,
        command: Command,
        symbol_gen: &mut SymbolGen,
        type_info: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        match command {
            Command::Rule { rule } if mentions_set_effectful(&rule.head) => {
                rewrite_rule(rule, symbol_gen, type_info)
            }
            Command::Action(Action::Expr(span, Expr::Call(call_span, head, args)))
                if head == SET_EFFECTFUL =>
            {
                let [arg] = &args[..] else {
                    return Err(usage(call_span));
                };
                let vars =
                    sorts_through_facts(&[], &[], std::slice::from_ref(arg), symbol_gen, type_info);
                let sort = sort_of(arg, &vars, type_info)?;
                let mut commands =
                    declare_if_needed(&sort, call_span.clone(), type_info, &mut Vec::new());
                commands.push(Command::Action(Action::Expr(
                    span,
                    Expr::Call(call_span, effectful_relation(&sort), args),
                )));
                Ok(commands)
            }
            other => Ok(vec![other]),
        }
    }
}

fn usage(span: egglog_ast::span::Span) -> Error {
    Error::ParseError(ParseError(
        span,
        "usage: (set-effectful <expr>) where <expr> has an eq sort".to_string(),
    ))
}

fn mentions_set_effectful(actions: &egglog::ast::Actions) -> bool {
    let mut found = false;
    actions.clone().visit_exprs(&mut |expr| {
        if let Expr::Call(_, head, _) = &expr
            && head == SET_EFFECTFUL
        {
            found = true;
        }
        expr
    });
    found
}

fn rewrite_rule(
    rule: Rule,
    symbol_gen: &mut SymbolGen,
    type_info: &TypeInfo,
) -> Result<Vec<Command>, Error> {
    // Typecheck the body first (reporting its errors as usual), then again
    // with the actions' lets and the set-effectful arguments as facts.
    type_info.typecheck_facts(symbol_gen, &rule.body)?;
    let mut marks = Vec::new();
    let mut lets = Vec::new();
    for action in rule.head.iter() {
        if let Action::Let(_, var, expr) = action {
            lets.push((var.clone(), expr.clone()));
        }
        action.clone().visit_exprs(&mut |expr| {
            if let Expr::Call(_, head, args) = &expr
                && head == SET_EFFECTFUL
                && let [arg] = &args[..]
            {
                marks.push(arg.clone());
            }
            expr
        });
    }
    let mut vars = sorts_through_facts(&rule.body, &lets, &marks, symbol_gen, type_info);
    for (var, expr) in &lets {
        if !vars.contains_key(var)
            && let Ok(sort) = sort_of(expr, &vars, type_info)
        {
            vars.insert(var.clone(), sort);
        }
    }
    let mut declared: Vec<String> = Vec::new();
    let mut commands: Vec<Command> = Vec::new();
    // Actions run in order and a `let` binds a variable for the actions after
    // it, so rewrite one action at a time and record each binding's sort.
    let mut new_actions = Vec::with_capacity(rule.head.len());
    for action in rule.head.iter() {
        let mut error: Option<Error> = None;
        let rewritten = action.clone().visit_exprs(&mut |expr| {
            if error.is_some() {
                return expr;
            }
            let Expr::Call(span, head, args) = &expr else {
                return expr;
            };
            if head != SET_EFFECTFUL {
                return expr;
            }
            let [arg] = &args[..] else {
                error = Some(usage(span.clone()));
                return expr;
            };
            match sort_of(arg, &vars, type_info) {
                Ok(sort) => {
                    commands.extend(declare_if_needed(
                        &sort,
                        span.clone(),
                        type_info,
                        &mut declared,
                    ));
                    Expr::Call(span.clone(), effectful_relation(&sort), args.clone())
                }
                Err(err) => {
                    error = Some(err);
                    expr
                }
            }
        });
        if let Some(err) = error {
            return Err(err);
        }
        new_actions.push(rewritten);
    }
    let mut head = rule.head.clone();
    head.0 = new_actions;
    commands.push(Command::Rule {
        rule: Rule { head, ..rule },
    });
    Ok(commands)
}

fn mark_name(i: usize) -> String {
    format!("__effsafe_mark_{i}")
}

/// Var-name to sort-name for every variable of `body`, for the let-bound
/// variables in `lets`, and for the fresh variable `mark_name(i)` bound to
/// `marks[i]`, found by typechecking `body` extended with one `(= <var>
/// <expr>)` fact per let and per mark. Falls back to the body alone (or
/// nothing) when the extended facts do not typecheck; the caller then reports
/// what it cannot determine.
fn sorts_through_facts(
    body: &[Fact],
    lets: &[(String, Expr)],
    marks: &[Expr],
    symbol_gen: &mut SymbolGen,
    type_info: &TypeInfo,
) -> FxHashMap<String, String> {
    let mut facts: Vec<Fact> = body.to_vec();
    for (var, expr) in lets {
        facts.push(Fact::Eq(
            expr.span(),
            Expr::Var(expr.span(), var.clone()),
            expr.clone(),
        ));
    }
    for (i, arg) in marks.iter().enumerate() {
        facts.push(Fact::Eq(
            arg.span(),
            Expr::Var(arg.span(), mark_name(i)),
            arg.clone(),
        ));
    }
    let resolved = type_info
        .typecheck_facts(symbol_gen, &facts)
        .or_else(|_| type_info.typecheck_facts(symbol_gen, body))
        .unwrap_or_default();
    let mut vars: FxHashMap<String, String> = FxHashMap::default();
    for fact in &resolved {
        fact.visit_vars(&mut |_span, var| {
            vars.insert(var.name.to_string(), var.sort.name().to_string());
        });
    }
    // The marks' sorts are also recorded under the argument's own text, so
    // `sort_of` finds them without knowing the mark numbering.
    for (i, arg) in marks.iter().enumerate() {
        if let Some(sort) = vars.get(&mark_name(i)).cloned() {
            vars.insert(format!("{arg}"), sort);
        }
    }
    vars
}

/// The sort of `expr`, or `None` when it cannot be determined. Variables come
/// from `vars` or the globals; constructor and function calls from their
/// declared output; primitive calls by trying the primitive's overloads
/// against every sort visible in the rule (the sorts of its variables), which
/// covers write primitives that the query typechecker cannot type.
fn infer_sort(
    expr: &Expr,
    vars: &FxHashMap<String, String>,
    type_info: &TypeInfo,
) -> Result<Option<String>, Error> {
    use egglog::ast::Literal;
    Ok(match expr {
        _ if vars.contains_key(&format!("{expr}")) && !matches!(expr, Expr::Lit(..)) => {
            vars.get(&format!("{expr}")).cloned()
        }
        Expr::Var(_, name) => vars.get(name).cloned().or_else(|| {
            type_info
                .get_global_sort(name)
                .map(|s| s.name().to_string())
        }),
        Expr::Lit(_, lit) => Some(
            match lit {
                Literal::Int(_) => "i64",
                Literal::Float(_) => "f64",
                Literal::String(_) => "String",
                Literal::Bool(_) => "bool",
                Literal::Unit => "Unit",
            }
            .to_string(),
        ),
        Expr::Call(span, head, args) => {
            if let Some(f) = type_info.get_func_type(head) {
                Some(f.output.name().to_string())
            } else if let Some(prims) = type_info.get_prims(head) {
                let mut arg_sorts = Vec::with_capacity(args.len());
                for arg in args {
                    let Some(sort) = infer_sort(arg, vars, type_info)? else {
                        return Ok(None);
                    };
                    let Some(sort) = type_info.get_sort_by_name(&sort) else {
                        return Ok(None);
                    };
                    arg_sorts.push(sort.clone());
                }
                let mut accepted: Vec<String> = Vec::new();
                for candidate in candidate_sorts(vars, type_info) {
                    let mut tys = arg_sorts.clone();
                    tys.push(candidate.clone());
                    if prims.iter().any(|p| p.accept(&tys, type_info))
                        && !accepted.contains(&candidate.name().to_string())
                    {
                        accepted.push(candidate.name().to_string());
                    }
                }
                match accepted.len() {
                    1 => accepted.pop(),
                    0 => None,
                    _ => {
                        return Err(Error::ParseError(ParseError(
                            span.clone(),
                            format!(
                                "set-effectful: the sort of {expr} is ambiguous ({})",
                                accepted.join(", ")
                            ),
                        )));
                    }
                }
            } else {
                None
            }
        }
    })
}

/// The sorts a primitive call in the rule could produce: those of the rule's
/// variables. (Sorts nested inside containers are not tried: egglog's
/// `inner_sorts` is not implemented for every container sort. Container
/// element access such as `vec-get` is typed through the query typechecker
/// instead.)
fn candidate_sorts(vars: &FxHashMap<String, String>, type_info: &TypeInfo) -> Vec<egglog::ArcSort> {
    let mut out: Vec<egglog::ArcSort> = Vec::new();
    for name in vars.values() {
        if out.iter().any(|s| s.name() == name) {
            continue;
        }
        if let Some(sort) = type_info.get_sort_by_name(name) {
            out.push(sort.clone());
        }
    }
    out
}

/// The sort of `expr` inside a rule whose variables have the sorts in `vars`.
fn sort_of(
    expr: &Expr,
    vars: &FxHashMap<String, String>,
    type_info: &TypeInfo,
) -> Result<String, Error> {
    if matches!(expr, Expr::Lit(..)) {
        return Err(Error::ParseError(ParseError(
            expr.span(),
            format!("set-effectful: {expr} is a literal, not an eq sort expression"),
        )));
    }
    let sort = infer_sort(expr, vars, type_info)?;
    let Some(sort) = sort else {
        return Err(Error::ParseError(ParseError(
            expr.span(),
            format!("set-effectful: cannot determine the sort of {expr}"),
        )));
    };
    match type_info.get_sort_by_name(&sort) {
        Some(s) if s.is_eq_sort() => Ok(sort),
        _ => Err(Error::ParseError(ParseError(
            expr.span(),
            format!("set-effectful: {expr} has sort {sort}, which is not an eq sort"),
        ))),
    }
}

/// A `relation` declaration for the sort's effectful table, unless it exists
/// already (declared by an earlier command, or earlier in this one).
fn declare_if_needed(
    sort: &str,
    span: egglog_ast::span::Span,
    type_info: &TypeInfo,
    declared: &mut Vec<String>,
) -> Vec<Command> {
    let name = effectful_relation(sort);
    if type_info.get_func_type(&name).is_some() || declared.contains(&name) {
        return Vec::new();
    }
    declared.push(name.clone());
    vec![Command::Relation {
        span,
        name,
        inputs: vec![sort.to_string()],
    }]
}
