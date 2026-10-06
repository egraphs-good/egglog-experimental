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
use egglog::util::{FreshGen, SymbolGen};
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
    // Lets the query typechecker could not type (write primitives) are
    // inferred here, of any sort, keeping every candidate sort of an
    // overloaded expression so that a later consumer can narrow it; only the
    // marked expressions must resolve to a single eq sort.
    for (var, expr) in &lets {
        if !vars.contains_key(var)
            && let Ok(candidates) = infer_candidates(expr, &vars, type_info)
            && !candidates.is_empty()
        {
            vars.insert(var.clone(), candidates);
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

/// Variable (or marked expression text) to its possible sort names: one entry
/// when known, several for an overloaded expression a consumer may narrow.
type Sorts = FxHashMap<String, Vec<String>>;

/// Sort names for every variable of `body`, for the let-bound variables in
/// `lets`, and for the expressions in `marks`, found by typechecking `body`
/// extended with one `(= <var> <expr>)` fact per let and one
/// `(= <fresh> <expr>)` fact per mark, the fresh names coming from the symbol
/// generator so they cannot capture a user variable. Falls back to the body
/// alone (or nothing) when the extended facts do not typecheck, in which case
/// no mark is attributed; the caller then infers what it can and reports what
/// it cannot determine.
fn sorts_through_facts(
    body: &[Fact],
    lets: &[(String, Expr)],
    marks: &[Expr],
    symbol_gen: &mut SymbolGen,
    type_info: &TypeInfo,
) -> Sorts {
    let mut facts: Vec<Fact> = body.to_vec();
    for (var, expr) in lets {
        facts.push(Fact::Eq(
            expr.span(),
            Expr::Var(expr.span(), var.clone()),
            expr.clone(),
        ));
    }
    let mark_names: Vec<String> = marks
        .iter()
        .map(|_| symbol_gen.fresh("effsafe_mark"))
        .collect();
    for (arg, name) in marks.iter().zip(&mark_names) {
        facts.push(Fact::Eq(
            arg.span(),
            Expr::Var(arg.span(), name.clone()),
            arg.clone(),
        ));
    }
    let (resolved, extended) = match type_info.typecheck_facts(symbol_gen, &facts) {
        Ok(resolved) => (resolved, true),
        Err(_) => (
            type_info
                .typecheck_facts(symbol_gen, body)
                .unwrap_or_default(),
            false,
        ),
    };
    let mut vars: Sorts = FxHashMap::default();
    for fact in &resolved {
        fact.visit_vars(&mut |_span, var| {
            vars.insert(var.name.to_string(), vec![var.sort.name().to_string()]);
        });
    }
    // The marks' sorts are also recorded under the argument's own text, so
    // `sort_of` finds them without knowing the mark numbering.
    if extended {
        for (arg, name) in marks.iter().zip(&mark_names) {
            if let Some(sort) = vars.get(name).cloned() {
                vars.insert(format!("{arg}"), sort);
            }
        }
    }
    vars
}

/// The possible sorts of `expr` (empty when none can be determined, several
/// for an overloaded primitive whose output is not pinned down yet).
/// Variables come from `vars` or the globals; constructor and function calls
/// from their declared output; primitive calls by trying the primitive's
/// overloads against every combination of the arguments' candidate sorts and
/// every registered sort as the output, which covers write primitives that
/// the query typechecker cannot type. A consumer with a fixed parameter sort
/// thereby narrows an overloaded producer (`(vec-empty)` passed to a
/// primitive taking `Exprs`).
fn infer_candidates(expr: &Expr, vars: &Sorts, type_info: &TypeInfo) -> Result<Vec<String>, Error> {
    use egglog::ast::Literal;
    /// Combinations of the arguments' candidate sorts tried for a primitive.
    const MAX_COMBINATIONS: usize = 256;
    Ok(match expr {
        _ if vars.contains_key(&format!("{expr}")) && !matches!(expr, Expr::Lit(..)) => {
            vars[&format!("{expr}")].clone()
        }
        Expr::Var(_, name) => vars.get(name).cloned().unwrap_or_else(|| {
            type_info
                .get_global_sort(name)
                .map(|s| vec![s.name().to_string()])
                .unwrap_or_default()
        }),
        Expr::Lit(_, lit) => vec![
            match lit {
                Literal::Int(_) => "i64",
                Literal::Float(_) => "f64",
                Literal::String(_) => "String",
                Literal::Bool(_) => "bool",
                Literal::Unit => "Unit",
            }
            .to_string(),
        ],
        Expr::Call(_, head, args) => {
            if let Some(f) = type_info.get_func_type(head) {
                vec![f.output.name().to_string()]
            } else if let Some(prims) = type_info.get_prims(head) {
                let mut arg_candidates: Vec<Vec<egglog::ArcSort>> = Vec::with_capacity(args.len());
                let mut combinations = 1usize;
                for arg in args {
                    let sorts: Vec<egglog::ArcSort> = infer_candidates(arg, vars, type_info)?
                        .iter()
                        .filter_map(|name| type_info.get_sort_by_name(name).cloned())
                        .collect();
                    if sorts.is_empty() {
                        return Ok(Vec::new());
                    }
                    combinations = combinations.saturating_mul(sorts.len());
                    arg_candidates.push(sorts);
                }
                if combinations > MAX_COMBINATIONS {
                    return Ok(Vec::new());
                }
                let outputs = candidate_sorts(type_info);
                let mut accepted: Vec<String> = Vec::new();
                let mut indices = vec![0usize; arg_candidates.len()];
                loop {
                    let mut tys: Vec<egglog::ArcSort> = indices
                        .iter()
                        .zip(&arg_candidates)
                        .map(|(&i, sorts)| sorts[i].clone())
                        .collect();
                    tys.push(outputs[0].clone());
                    for output in &outputs {
                        *tys.last_mut().unwrap() = output.clone();
                        if prims.iter().any(|p| p.accept(&tys, type_info))
                            && !accepted.contains(&output.name().to_string())
                        {
                            accepted.push(output.name().to_string());
                        }
                    }
                    // Next combination, odometer style.
                    let mut k = 0;
                    loop {
                        if k == indices.len() {
                            break;
                        }
                        indices[k] += 1;
                        if indices[k] < arg_candidates[k].len() {
                            break;
                        }
                        indices[k] = 0;
                        k += 1;
                    }
                    if k == indices.len() {
                        break;
                    }
                }
                accepted
            } else {
                Vec::new()
            }
        }
    })
}

/// The sorts a primitive call could produce: every registered sort.
fn candidate_sorts(type_info: &TypeInfo) -> Vec<egglog::ArcSort> {
    let mut out: Vec<egglog::ArcSort> = type_info.get_arcsorts_by(|_| true);
    out.sort_by(|a, b| a.name().cmp(b.name()));
    out.dedup_by(|a, b| a.name() == b.name());
    out
}

/// The sort of `expr` inside a rule whose variables have the sorts in `vars`,
/// which must be a single eq sort.
fn sort_of(expr: &Expr, vars: &Sorts, type_info: &TypeInfo) -> Result<String, Error> {
    if matches!(expr, Expr::Lit(..)) {
        return Err(Error::ParseError(ParseError(
            expr.span(),
            format!("set-effectful: {expr} is a literal, not an eq sort expression"),
        )));
    }
    let mut candidates = infer_candidates(expr, vars, type_info)?;
    let sort = match candidates.len() {
        1 => candidates.pop().unwrap(),
        0 => {
            return Err(Error::ParseError(ParseError(
                expr.span(),
                format!("set-effectful: cannot determine the sort of {expr}"),
            )));
        }
        _ => {
            return Err(Error::ParseError(ParseError(
                expr.span(),
                format!(
                    "set-effectful: the sort of {expr} is ambiguous ({})",
                    candidates.join(", ")
                ),
            )));
        }
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
