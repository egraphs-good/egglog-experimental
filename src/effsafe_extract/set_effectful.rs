//! `(set-effectful e)`: mark the e-class of `e` as effectful.
//!
//! Like `set-cost`, this generates a table per sort rather than asking the
//! program to declare one: `(set-effectful e)` becomes an insertion into the
//! relation `effsafe_effectful_<Sort>` for the sort of `e`, declared the
//! first time the sort is seen. The extractor reads every such relation.
//!
//! The sort of `e` comes from egglog's own action typechecker. A rule whose
//! actions mention `set-effectful` is turned by a [`CommandMacro`] into the
//! command `(effsafe-rule "<the rule>")`, which runs with access to the
//! e-graph: it typechecks the rule's body for the sorts of its variables,
//! inlines the rule's `let` bindings into each marked expression, and asks
//! the typechecker ([`EGraph::typecheck_expr_with_bindings_and_output`]) which
//! eq sort the expression has in the rule head's context. That is exact for
//! write primitives, literal-sensitive constraints and overloads narrowed by
//! their consumers alike. A top-level `(set-effectful e)` is a user-defined
//! command doing the same without bindings.

use egglog::ast::{Action, Command, Expr, Literal, ParseError, Parser, Rule, RuleEvalMode};
use egglog::util::SymbolGen;
use egglog::{
    ArcSort, CommandMacro, CommandOutput, Context, EGraph, Error, TypeInfo, UserDefinedCommand,
};
use egglog_ast::span::Span;
use rustc_hash::FxHashMap;

/// The macro's name in programs.
pub const SET_EFFECTFUL: &str = "set-effectful";

/// The command a rule mentioning `set-effectful` is lowered to.
pub const EFFSAFE_RULE: &str = "effsafe-rule";

const RELATION_PREFIX: &str = "effsafe_effectful_";

/// The generated relation holding the effectful e-classes of `sort`.
pub fn effectful_relation(sort: &str) -> String {
    format!("{RELATION_PREFIX}{sort}")
}

/// The sort whose effectful e-classes `relation` holds, if it is one of ours.
pub fn effectful_relation_sort(relation: &str) -> Option<&str> {
    relation.strip_prefix(RELATION_PREFIX)
}

/// Lowers a rule whose actions mention `set-effectful` to `effsafe-rule`;
/// see the module docs.
pub struct SetEffectful;

impl CommandMacro for SetEffectful {
    fn transform(
        &self,
        command: Command,
        _symbol_gen: &mut SymbolGen,
        _type_info: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        match command {
            Command::Rule { rule } if mentions_set_effectful(&rule.head) => {
                let span = rule.span.clone();
                let text = format!("{}", Command::Rule { rule });
                Ok(vec![Command::UserDefined(
                    span.clone(),
                    EFFSAFE_RULE.to_string(),
                    vec![Expr::Lit(span, Literal::String(text))],
                )])
            }
            other => Ok(vec![other]),
        }
    }
}

/// `(effsafe-rule "<rule>")`: the rule, with its `set-effectful` actions
/// rewritten into the generated relations.
pub struct EffsafeRule;

impl UserDefinedCommand for EffsafeRule {
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        let [Expr::Lit(span, Literal::String(text))] = args else {
            return Err(Error::ParseError(ParseError(
                args.first()
                    .map(|a| a.span())
                    .unwrap_or_else(|| egglog::span!()),
                format!(
                    "usage: ({EFFSAFE_RULE} \"<rule>\"), produced by rules that use {SET_EFFECTFUL}"
                ),
            )));
        };
        let mut commands = Parser::default().get_program_from_string(None, text)?;
        let Some(Command::Rule { rule }) = commands.pop() else {
            return Err(Error::ParseError(ParseError(
                span.clone(),
                format!("{EFFSAFE_RULE}: expected a rule"),
            )));
        };
        if !commands.is_empty() {
            return Err(Error::ParseError(ParseError(
                span.clone(),
                format!("{EFFSAFE_RULE}: expected exactly one rule"),
            )));
        }
        let commands = rewrite_rule(egraph, rule)?;
        egraph.run_program(commands)
    }
}

/// Top-level `(set-effectful e)`.
pub struct SetEffectfulCommand;

impl UserDefinedCommand for SetEffectfulCommand {
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        let [arg] = args else {
            return Err(usage(
                args.first()
                    .map(|a| a.span())
                    .unwrap_or_else(|| egglog::span!()),
            ));
        };
        let span = arg.span();
        let sort = mark_sort(egraph, arg, &[], Context::Full)?;
        let mut commands = Vec::new();
        declare_if_needed(egraph, &sort, span.clone(), &mut Vec::new(), &mut commands);
        commands.push(Command::Action(Action::Expr(
            span.clone(),
            Expr::Call(span, effectful_relation(sort.name()), vec![arg.clone()]),
        )));
        egraph.run_program(commands)
    }
}

fn usage(span: Span) -> Error {
    Error::ParseError(ParseError(
        span,
        format!("usage: ({SET_EFFECTFUL} <expr>) where <expr> has an eq sort"),
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

/// The rule with every `(set-effectful e)` replaced by an insertion into the
/// relation for the sort of `e`, preceded by the relations' declarations.
fn rewrite_rule(egraph: &mut EGraph, rule: Rule) -> Result<Vec<Command>, Error> {
    // The sorts of the rule's variables, from typechecking its body.
    let mut symbol_gen = SymbolGen::new(egraph.parser.symbol_gen.reserved_prefix().to_string());
    let resolved = egraph
        .type_info()
        .typecheck_facts(&mut symbol_gen, &rule.body)?;
    let mut bindings: Vec<(String, Span, ArcSort)> = Vec::new();
    for fact in &resolved {
        fact.visit_vars(&mut |span, var| {
            if !bindings.iter().any(|(name, _, _)| *name == var.name) {
                bindings.push((var.name.to_string(), span.clone(), var.sort.clone()));
            }
        });
    }
    let context = match rule.eval_mode {
        RuleEvalMode::Naive => Context::Full,
        _ => Context::Write,
    };

    // Let bindings are inlined into the marked expressions, so that the
    // typechecker sees each expression whole, in context, and can narrow
    // overloads by their consumers.
    let mut lets: FxHashMap<String, Expr> = FxHashMap::default();
    let mut declared: Vec<String> = Vec::new();
    let mut commands: Vec<Command> = Vec::new();
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
            let probe = inline_lets(arg, &lets);
            match mark_sort(egraph, &probe, &bindings, context) {
                Ok(sort) => {
                    declare_if_needed(egraph, &sort, span.clone(), &mut declared, &mut commands);
                    Expr::Call(span.clone(), effectful_relation(sort.name()), args.clone())
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
        if let Action::Let(_, var, expr) = action {
            let inlined = inline_lets(expr, &lets);
            lets.insert(var.clone(), inlined);
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

/// `expr` with the rule's earlier `let` bindings substituted.
fn inline_lets(expr: &Expr, lets: &FxHashMap<String, Expr>) -> Expr {
    expr.clone().visit_exprs(&mut |e| match &e {
        Expr::Var(_, name) => lets.get(name).cloned().unwrap_or(e),
        _ => e,
    })
}

/// The eq sort of `expr` under `bindings` in `context`, by asking the
/// typechecker for every eq sort; exactly one must fit.
fn mark_sort(
    egraph: &mut EGraph,
    expr: &Expr,
    bindings: &[(String, Span, ArcSort)],
    context: Context,
) -> Result<ArcSort, Error> {
    if matches!(expr, Expr::Lit(..)) {
        return Err(Error::ParseError(ParseError(
            expr.span(),
            format!("{SET_EFFECTFUL}: {expr} is a literal, not an eq sort expression"),
        )));
    }
    let mut eq_sorts: Vec<ArcSort> = egraph.type_info().get_arcsorts_by(|s| s.is_eq_sort());
    eq_sorts.sort_by(|a, b| a.name().cmp(b.name()));
    eq_sorts.dedup_by(|a, b| a.name() == b.name());
    let mut accepted: Vec<ArcSort> = Vec::new();
    let mut last_error = None;
    for sort in eq_sorts {
        match egraph.typecheck_expr_with_bindings_and_output(expr, bindings, sort.clone(), context)
        {
            Ok(_) => accepted.push(sort),
            Err(err) => last_error = Some(err),
        }
    }
    match accepted.len() {
        1 => Ok(accepted.pop().unwrap()),
        0 => Err(Error::ParseError(ParseError(
            expr.span(),
            match last_error {
                Some(err) => format!("{SET_EFFECTFUL}: {expr} does not have an eq sort: {err}"),
                None => format!("{SET_EFFECTFUL}: {expr} does not have an eq sort"),
            },
        ))),
        _ => Err(Error::ParseError(ParseError(
            expr.span(),
            format!(
                "{SET_EFFECTFUL}: the sort of {expr} is ambiguous ({})",
                accepted
                    .iter()
                    .map(|s| s.name().to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        ))),
    }
}

/// A `relation` declaration for the sort's effectful table, unless it exists
/// already (declared by an earlier command, or earlier in this one).
fn declare_if_needed(
    egraph: &EGraph,
    sort: &ArcSort,
    span: Span,
    declared: &mut Vec<String>,
    commands: &mut Vec<Command>,
) {
    let name = effectful_relation(sort.name());
    if egraph.get_function(&name).is_some() || declared.contains(&name) {
        return;
    }
    declared.push(name.clone());
    commands.push(Command::Relation {
        span,
        name,
        inputs: vec![sort.name().to_string()],
    });
}
