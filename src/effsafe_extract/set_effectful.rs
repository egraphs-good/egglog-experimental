//! `(set-effectful e)`: mark the e-class of `e` as effectful.
//!
//! Like `set-cost`, this generates a table per sort rather than asking the
//! program to declare one. A post-parse [`CommandMacro`] sees each rule and
//! top-level action with its types, replaces `(set-effectful e)` by an
//! insertion into the relation `effsafe_effectful_<Sort>` for the sort of
//! `e`, and declares that relation the first time the sort is seen. The
//! extractor reads every such relation.

use egglog::ast::{Action, Command, Expr, ParseError, Rule};
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
                let sort = sort_of(arg, &FxHashMap::default(), type_info)?;
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
    // The sorts of the rule's variables come from typechecking its body.
    let resolved = type_info.typecheck_facts(symbol_gen, &rule.body)?;
    let mut vars: FxHashMap<String, String> = FxHashMap::default();
    for fact in &resolved {
        fact.visit_vars(&mut |_span, var| {
            vars.insert(var.name.to_string(), var.sort.name().to_string());
        });
    }
    let mut declared: Vec<String> = Vec::new();
    let mut commands: Vec<Command> = Vec::new();
    let mut error: Option<Error> = None;
    let head = rule.head.clone().visit_exprs(&mut |expr| {
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
    commands.push(Command::Rule {
        rule: Rule { head, ..rule },
    });
    Ok(commands)
}

/// The sort of `expr` inside a rule whose variables have the sorts in `vars`.
fn sort_of(
    expr: &Expr,
    vars: &FxHashMap<String, String>,
    type_info: &TypeInfo,
) -> Result<String, Error> {
    let sort = match expr {
        Expr::Var(_, name) => vars.get(name).cloned().or_else(|| {
            type_info
                .get_global_sort(name)
                .map(|s| s.name().to_string())
        }),
        Expr::Call(_, head, _) => type_info
            .get_func_type(head)
            .map(|f| f.output.name().to_string()),
        Expr::Lit(..) => None,
    };
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
