//! `(set-effectful e)`: mark the e-class of `e` as effectful.
//!
//! Like `set-cost`, this generates a table per sort rather than asking the
//! program to declare one: `(set-effectful e)` becomes an insertion into the
//! relation `effsafe_effectful_<Sort>` for the sort of `e`, declared the
//! first time the sort is seen. The extractor reads every such relation.
//!
//! The sort of `e` comes from egglog's own rule typechecker
//! ([`TypeInfo::typecheck_rule`]), applied when the rule is run rather than
//! when it is parsed: a [`CommandMacro`] lowers a rule whose head mentions
//! `set-effectful` to `(effsafe-rule <id>)`, keeping the parsed rule in a
//! process-local table, and that command, with the e-graph at hand, replaces
//! each `(set-effectful e)` action by `(let <fresh> e)`, typechecks the probe
//! rule with the e-graph's actual seminaive setting, reads the fresh variables'
//! sorts off the resolved head and runs the rewritten rule. If `e` is an
//! overloaded expression that the plain `let` leaves ambiguous, the command
//! retries with the mark written as an insertion into the generated relation
//! of each eq sort in turn (declaring the relations under `push`/`pop`, so
//! trials leave nothing behind), which lets the eq-sort requirement take part
//! in the inference. Doing all this at run time means declarations emitted by
//! other macros for the same rule (`unstable-fresh!`'s generated constructor,
//! say) are already in place.
//! A top-level `(set-effectful e)` is a user-defined command typed the same
//! way, as the head of a rule with no body in the top-level (`Full`) context.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{LazyLock, Mutex};

use egglog::ast::{
    Action, Command, Expr, Fact, GenericAction, Literal, ParseError, ResolvedRule, Rule,
    RuleEvalMode,
};
use egglog::util::{FreshGen, SymbolGen};
use egglog::{ArcSort, CommandMacro, CommandOutput, EGraph, Error, TypeInfo, UserDefinedCommand};
use egglog_ast::generic_ast::GenericActions;
use egglog_ast::span::Span;

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

/// Rules lowered to `effsafe-rule`, by id. Rules are plain data and a
/// program is run by one process, so this is the simplest faithful way to
/// hand the parsed rule (with the internal symbols other macros gave it) from
/// the macro to the command.
static PENDING_RULES: LazyLock<Mutex<HashMap<u64, Rule>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));
static NEXT_RULE_ID: AtomicU64 = AtomicU64::new(0);

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
                let id = NEXT_RULE_ID.fetch_add(1, Ordering::Relaxed);
                PENDING_RULES.lock().unwrap().insert(id, rule);
                Ok(vec![Command::UserDefined(
                    span.clone(),
                    EFFSAFE_RULE.to_string(),
                    vec![Expr::Lit(span, Literal::Int(id as i64))],
                )])
            }
            other => Ok(vec![other]),
        }
    }
}

/// `(effsafe-rule <id>)`: the lowered rule, with its `set-effectful` actions
/// rewritten into the generated relations.
pub struct EffsafeRule;

impl UserDefinedCommand for EffsafeRule {
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        let span = args
            .first()
            .map(|a| a.span())
            .unwrap_or_else(|| egglog::span!());
        let [Expr::Lit(_, Literal::Int(id))] = args else {
            return Err(Error::ParseError(ParseError(
                span,
                format!("usage: ({EFFSAFE_RULE} <id>), produced by rules that use {SET_EFFECTFUL}"),
            )));
        };
        let rule = PENDING_RULES
            .lock()
            .unwrap()
            .get(&(*id as u64))
            .cloned()
            .ok_or_else(|| {
                Error::ParseError(ParseError(
                    span,
                    format!("{EFFSAFE_RULE}: unknown rule {id}; this command is produced by rules that use {SET_EFFECTFUL}"),
                ))
            })?;
        let global_seminaive = egraph.seminaive;
        let (mut commands, rule) = rewrite_rule(egraph, rule, global_seminaive)?;
        commands.push(Command::Rule { rule });
        egraph.run_program(commands)
    }
}

/// Top-level `(set-effectful e)`.
pub struct SetEffectfulCommand;

impl UserDefinedCommand for SetEffectfulCommand {
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        let span = args
            .first()
            .map(|a| a.span())
            .unwrap_or_else(|| egglog::span!());
        let [arg] = args else {
            return Err(usage(span));
        };
        let rule = Rule {
            span: span.clone(),
            head: GenericActions(vec![GenericAction::Expr(
                span.clone(),
                Expr::Call(span, SET_EFFECTFUL.to_string(), vec![arg.clone()]),
            )]),
            body: Vec::<Fact>::new(),
            name: String::new(),
            ruleset: String::new(),
            eval_mode: RuleEvalMode::Seminaive,
            no_decomp: false,
            include_subsumed: false,
        };
        // Top-level actions run in the Full context, which typecheck_rule
        // uses for the head when the e-graph is not seminaive.
        let (mut commands, rule) = rewrite_rule(egraph, rule, false)?;
        commands.extend(rule.head.0.into_iter().map(Command::Action));
        egraph.run_program(commands)
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

/// The declarations of the generated relations the rule needs (those not
/// declared yet), and the rule with every `(set-effectful e)` replaced by an
/// insertion into the relation for the sort of `e`.
fn rewrite_rule(
    egraph: &mut EGraph,
    rule: Rule,
    global_seminaive: bool,
) -> Result<(Vec<Command>, Rule), Error> {
    // Fresh names carry the parser's reserved prefix, so they cannot be user
    // variables.
    let mut symbol_gen = SymbolGen::new(egraph.parser.symbol_gen.reserved_prefix().to_string());

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
                probe_actions.push(GenericAction::Let(span.clone(), fresh.clone(), arg.clone()));
                marks.push((fresh, call_span.clone(), arg.clone()));
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
    let resolved =
        match egraph
            .type_info()
            .typecheck_rule(&mut symbol_gen, &probe, global_seminaive)
        {
            Ok(resolved) => resolved,
            Err(err) => resolve_by_eq_sort(
                egraph,
                &probe,
                &marks,
                global_seminaive,
                &mut symbol_gen,
            )
            .map_err(|retry_err| {
                Error::ParseError(ParseError(
                    rule.span.clone(),
                    format!(
                        "{SET_EFFECTFUL}: the rule does not typecheck with its marked expressions \
                         as eq sorts: {err}{retry_err}"
                    ),
                ))
            })?,
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
                declare_if_needed(
                    egraph,
                    &sort,
                    call_span.clone(),
                    &mut declared,
                    &mut commands,
                );
                head.push(GenericAction::Expr(
                    span.clone(),
                    Expr::Call(call_span, effectful_relation(sort.name()), vec![arg]),
                ));
            }
            other => head.push(other.clone()),
        }
    }
    Ok((
        commands,
        Rule {
            head: GenericActions(head),
            ..rule
        },
    ))
}

/// When the plain probe leaves a marked expression ambiguous (an overload
/// between an eq sort and others), find the eq sort by trying, for one mark at
/// a time, the mark written as an insertion into the generated relation of
/// each eq sort; exactly one sort must make the rule typecheck. The relations
/// are declared for the trials under `push`/`pop`, so nothing is left behind.
/// Returns the resolved probe rule with that mark so constrained (and the
/// other marks as plain `let`s). On `Err`, the string explains what failed and
/// is appended to the original typechecking error.
fn resolve_by_eq_sort(
    egraph: &mut EGraph,
    probe: &Rule,
    marks: &[(String, Span, Expr)],
    global_seminaive: bool,
    symbol_gen: &mut SymbolGen,
) -> Result<ResolvedRule, String> {
    let mut eq_sorts: Vec<ArcSort> = egraph.type_info().get_arcsorts_by(|s| s.is_eq_sort());
    eq_sorts.sort_by(|a, b| a.name().cmp(b.name()));
    eq_sorts.dedup_by(|a, b| a.name() == b.name());
    let push_pop = |egraph: &mut EGraph, command: Command| {
        egraph
            .run_program(vec![command])
            .map(|_| ())
            .map_err(|e| format!(" (while probing eq sorts: {e})"))
    };
    push_pop(egraph, Command::Push(1))?;
    let mut outcome: Result<ResolvedRule, String> = Err(String::new());
    'marks: for (i, (fresh, call_span, _)) in marks.iter().enumerate() {
        let mut fits: Vec<(ArcSort, ResolvedRule)> = Vec::new();
        for sort in &eq_sorts {
            let relation = effectful_relation(sort.name());
            if egraph.get_function(&relation).is_none()
                && let Err(e) = push_pop(
                    egraph,
                    Command::Relation {
                        span: call_span.clone(),
                        name: relation.clone(),
                        inputs: vec![sort.name().to_string()],
                    },
                )
            {
                outcome = Err(e);
                break 'marks;
            }
            // The probe with this mark's `let` followed by the insertion.
            let mut head = Vec::with_capacity(probe.head.len() + 1);
            for action in probe.head.iter() {
                head.push(action.clone());
                if let GenericAction::Let(span, var, _) = action
                    && var == fresh
                {
                    head.push(GenericAction::Expr(
                        span.clone(),
                        Expr::Call(
                            call_span.clone(),
                            relation.clone(),
                            vec![Expr::Var(call_span.clone(), fresh.clone())],
                        ),
                    ));
                }
            }
            let trial = Rule {
                head: GenericActions(head),
                ..probe.clone()
            };
            if let Ok(resolved) =
                egraph
                    .type_info()
                    .typecheck_rule(symbol_gen, &trial, global_seminaive)
            {
                fits.push((sort.clone(), resolved));
            }
        }
        match fits.len() {
            1 => {
                outcome = Ok(fits.pop().unwrap().1);
                break 'marks;
            }
            0 => {
                if i + 1 == marks.len() {
                    outcome = Err(" (no eq sort fits any marked expression)".to_string());
                }
            }
            _ => {
                outcome = Err(format!(
                    " (the marked expression {} could have any of the eq sorts {})",
                    marks[i].2,
                    fits.iter()
                        .map(|(s, _)| s.name().to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
                break 'marks;
            }
        }
    }
    push_pop(egraph, Command::Pop(probe.span.clone(), 1))?;
    outcome
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
