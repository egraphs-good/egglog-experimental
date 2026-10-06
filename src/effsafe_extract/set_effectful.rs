//! `(set-effectful e)`: mark the e-class of `e` as effectful.
//!
//! Like `set-cost`, this generates a table per sort rather than asking the
//! program to declare one: `(set-effectful e)` becomes an insertion into the
//! relation `effsafe_effectful_<Sort>` for the sort of `e`, declared the
//! first time the sort is seen. The extractor reads every such relation.
//!
//! The sort of `e` comes from egglog's own rule typechecker
//! ([`TypeInfo::typecheck_rule`]): the macro replaces each `(set-effectful e)`
//! action by `(let <fresh> e)`, typechecks the resulting rule (body and head
//! together, in the contexts the rule's mode gives them), and reads the fresh
//! variable's sort off the resolved head. A top-level `(set-effectful e)` is
//! typed as the head of a rule with no body.

use egglog::ast::{
    Action, Actions, Command, Expr, Fact, GenericAction, ParseError, Rule, RuleEvalMode,
};
use egglog::util::{FreshGen, SymbolGen};
use egglog::{ArcSort, CommandMacro, Error, TypeInfo};
use egglog_ast::generic_ast::GenericActions;
use egglog_ast::span::Span;

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
                let (head, mut commands) = resolve_marks(&rule, symbol_gen, type_info)?;
                commands.push(Command::Rule {
                    rule: Rule { head, ..rule },
                });
                Ok(commands)
            }
            Command::Action(action)
                if mentions_set_effectful(&GenericActions(vec![action.clone()])) =>
            {
                let span = action_span(&action);
                let rule = Rule {
                    span: span.clone(),
                    head: GenericActions(vec![action]),
                    body: Vec::<Fact>::new(),
                    name: String::new(),
                    ruleset: String::new(),
                    eval_mode: RuleEvalMode::Seminaive,
                    no_decomp: false,
                    include_subsumed: false,
                };
                let (head, mut commands) = resolve_marks(&rule, symbol_gen, type_info)?;
                commands.extend(head.0.into_iter().map(Command::Action));
                Ok(commands)
            }
            other => Ok(vec![other]),
        }
    }
}

fn usage(span: Span) -> Error {
    Error::ParseError(ParseError(
        span,
        format!("usage: ({SET_EFFECTFUL} <expr>) as an action, where <expr> has an eq sort"),
    ))
}

fn action_span(action: &Action) -> Span {
    match action {
        GenericAction::Let(span, ..)
        | GenericAction::Set(span, ..)
        | GenericAction::Change(span, ..)
        | GenericAction::Union(span, ..)
        | GenericAction::Panic(span, ..)
        | GenericAction::Expr(span, ..) => span.clone(),
    }
}

fn mentions_set_effectful(actions: &Actions) -> bool {
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

/// The rule's head with every `(set-effectful e)` replaced by an insertion
/// into the relation for the sort of `e`, and the declarations of relations
/// not declared yet.
fn resolve_marks(
    rule: &Rule,
    symbol_gen: &mut SymbolGen,
    type_info: &TypeInfo,
) -> Result<(Actions, Vec<Command>), Error> {
    // The probe rule binds each marked expression to a fresh variable.
    let mut marks: Vec<(String, Span, Expr)> = Vec::new();
    let mut probe_actions = Vec::with_capacity(rule.head.len());
    for action in rule.head.iter() {
        match action {
            GenericAction::Expr(span, Expr::Call(call_span, head, args))
                if head == SET_EFFECTFUL =>
            {
                let [arg] = &args[..] else {
                    return Err(usage(call_span.clone()));
                };
                if matches!(arg, Expr::Lit(..)) {
                    return Err(Error::ParseError(ParseError(
                        arg.span(),
                        format!("{SET_EFFECTFUL}: {arg} is a literal, not an eq sort expression"),
                    )));
                }
                let fresh = symbol_gen.fresh("effsafe_mark");
                marks.push((fresh.clone(), call_span.clone(), arg.clone()));
                probe_actions.push(GenericAction::Let(span.clone(), fresh, arg.clone()));
            }
            other if mentions_set_effectful(&GenericActions(vec![other.clone()])) => {
                return Err(Error::ParseError(ParseError(
                    action_span(other),
                    format!(
                        "{SET_EFFECTFUL} must be an action of its own, not part of another action"
                    ),
                )));
            }
            other => probe_actions.push(other.clone()),
        }
    }
    let probe = Rule {
        head: GenericActions(probe_actions),
        ..rule.clone()
    };
    // The e-graph's seminaive setting only decides whether the head may read
    // the database; the sorts are the same either way, so try the strict
    // contexts first and the permissive ones if those fail.
    let resolved = match type_info.typecheck_rule(symbol_gen, &probe, true) {
        Ok(resolved) => resolved,
        Err(_) => type_info.typecheck_rule(symbol_gen, &probe, false)?,
    };
    let mut sorts: Vec<Option<ArcSort>> = vec![None; marks.len()];
    for action in resolved.head.iter() {
        if let GenericAction::Let(_, var, _) = action
            && let Some(i) = marks.iter().position(|(name, _, _)| *name == var.name)
        {
            sorts[i] = Some(var.sort.clone());
        }
    }

    // Rewrite the marks into relation insertions.
    let mut declared: Vec<String> = Vec::new();
    let mut commands: Vec<Command> = Vec::new();
    let mut marks = marks.into_iter().zip(sorts);
    let mut head = Vec::with_capacity(rule.head.len());
    for action in rule.head.iter() {
        match action {
            GenericAction::Expr(span, Expr::Call(_, name, _)) if name == SET_EFFECTFUL => {
                let ((_, call_span, arg), sort) = marks.next().expect("one mark per marked action");
                let sort = sort.expect("the typechecker binds every variable of the head");
                if !sort.is_eq_sort() {
                    return Err(Error::ParseError(ParseError(
                        arg.span(),
                        format!(
                            "{SET_EFFECTFUL}: {arg} has sort {}, which is not an eq sort",
                            sort.name()
                        ),
                    )));
                }
                commands.extend(declare_if_needed(
                    sort.name(),
                    call_span.clone(),
                    type_info,
                    &mut declared,
                ));
                head.push(GenericAction::Expr(
                    span.clone(),
                    Expr::Call(call_span, effectful_relation(sort.name()), vec![arg]),
                ));
            }
            other => head.push(other.clone()),
        }
    }
    Ok((GenericActions(head), commands))
}

/// A `relation` declaration for the sort's effectful table, unless it exists
/// already (declared by an earlier command, or earlier in this one).
fn declare_if_needed(
    sort: &str,
    span: Span,
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
