//! The `run-schedule` command: an extended scheduling language for egglog.
//!
//! `run-schedule` takes one or more *schedule expressions* and runs them in
//! order against the e-graph, returning the combined [`RunReport`] (plus any
//! per-command outputs such as `print-size` results). It is registered as a
//! user-defined command by [`new_experimental_egraph`](crate::new_experimental_egraph)
//! and is the experimental counterpart to core egglog's built-in `run-schedule`.
//!
//! # Schedule expressions
//!
//! A schedule expression is one of:
//!
//! - **`ruleset`** — a bare ruleset name (a [`Var`](egglog::ast::Expr::Var)),
//!   e.g. `my-rules`. Runs one step of that ruleset.
//! - **`(run [ruleset] [:until cond])`** — run one step of `ruleset` (or the
//!   empty/default ruleset if omitted). With `:until cond`, the step is skipped
//!   once `cond` already holds (`cond` is checked as a [`Check`](egglog::ast::Command::Check)).
//! - **`(run-with scheduler [ruleset] [:until cond])`** — like `run`, but drives
//!   the ruleset with a named scheduler previously bound by `let-scheduler`.
//! - **`(let-scheduler name (scheduler-kind args...))`** — bind `name` to a fresh
//!   scheduler instance (e.g. `(back-off :match-limit 1000 :ban-length 5 :node-limit 5000)`). A
//!   binding inside `run-schedule` is scoped to its enclosing block; a top-level
//!   binding persists on the e-graph.
//! - **`(seq step...)`** — run each step once, in order.
//! - **`(saturate step...)`** — repeatedly run the body until it makes no further
//!   progress (the accumulated report's `can_stop` is set).
//! - **`(repeat n step...)`** — run the body `n` times.
//! - **`(saturate () (max-iterations n) (until fact...) (body step...))`** —
//!   explicit loop options; the bound and guard are optional. Exact repetition
//!   uses `(repeat () (times n) (until fact...) (body step...))`.
//! - **`(eval expr...)`** — evaluate each `expr` in the full read/write
//!   (FullState) context and add the resulting terms to the e-graph, the
//!   schedule-step analogue of a top-level expression like `(Add (Num 1) (Num 2))`.
//!   Because evaluation has full database access, the expressions may also call
//!   reading primitives such as `(get-size!)` that are not admissible from an
//!   ordinary action context.
//! - **A forwarded command** — a fixed allowlist of side-effecting commands
//!   (`print-size`, `print-function`, `extract`, `push`, `pop`, `union`, `set`,
//!   `delete`, `subsume`, `panic`) and any registered user-defined command
//!   (e.g. `keep-best`, `multi-extract`, or a nested `run-schedule`). These are
//!   forwarded by re-parsing the s-expression through
//!   [`parse_and_run_program`](egglog::EGraph::parse_and_run_program); any other
//!   head (rule declarations, `let` bindings, function definitions, …) is rejected.
//!
//! # Example
//!
//! ```text
//! (run-schedule
//!   (repeat 3
//!     (push)
//!     (eval (Add (Num 1) (Num 2)))   ; add a term to the e-graph
//!     (saturate (run math-rules))    ; rewrite to fixpoint
//!     (keep-best "Target")           ; compact to best representatives
//!     (pop)))
//! ```
use std::{collections::HashMap, sync::Mutex};

use egglog::{
    CommandOutput, ExecutionEvent, UserDefinedCommand,
    ast::{Action, Command, Expr, Fact, Literal, ParseError},
    prelude::Span,
    scheduler::{Scheduler, SchedulerId},
    span,
};
use egglog_reports::RunReport;
use lazy_static::lazy_static;

#[derive(Clone, Copy)]
pub(crate) struct SchedulerBinding {
    pub id: SchedulerId,
    // Unknown native factories are conservative, not proof of saturation.
    pub resource_limited: bool,
}

pub(crate) type PermanentSchedulerState = HashMap<String, SchedulerBinding>;
pub(crate) use schedulers::BackOffScheduler;

pub(crate) struct LoopHeader<'a> {
    pub exact: bool,
    pub bound: Option<u64>,
    pub until: Option<Vec<Fact>>,
    pub body: &'a [Expr],
}

// Unit was never an executable schedule step or an integer Repeat count.
// Decode this opt-in grammar once for native validation, execution and Source.
pub(crate) fn loop_header(expr: &Expr) -> Result<Option<LoopHeader<'_>>, egglog::Error> {
    let Expr::Call(span, head, args) = expr else {
        return Ok(None);
    };
    if !matches!(head.as_str(), "repeat" | "saturate")
        || !matches!(args.first(), Some(Expr::Lit(_, Literal::Unit)))
    {
        return Ok(None);
    }
    let invalid =
        || egglog::Error::ParseError(ParseError(span.clone(), "Invalid loop header".into()));
    let exact = head == "repeat";
    let mut bound = None;
    let mut until = None;
    let mut body = None;
    for field in &args[1..] {
        let Expr::Call(_, name, values) = field else {
            return Err(invalid());
        };
        match name.as_str() {
            "times" | "max-iterations" if bound.is_none() && (name == "times") == exact => {
                let [Expr::Lit(_, Literal::Int(count))] = values.as_slice() else {
                    return Err(invalid());
                };
                let count = u64::try_from(*count).map_err(|_| invalid())?;
                if !exact && count == 0 {
                    return Err(invalid());
                }
                bound = Some(count);
            }
            "until" if until.is_none() => {
                until = Some(
                    values
                        .iter()
                        .map(|expr| match expr {
                            Expr::Call(span, name, args) if name == "=" => {
                                let [left, right] = args.as_slice() else {
                                    return Err(invalid());
                                };
                                Ok(Fact::Eq(span.clone(), left.clone(), right.clone()))
                            }
                            _ => Ok(Fact::Fact(expr.clone())),
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                );
            }
            "body" if body.is_none() => body = Some(values.as_slice()),
            _ => return Err(invalid()),
        }
    }
    if exact && bound.is_none() {
        return Err(invalid());
    }
    Ok(Some(LoopHeader {
        exact,
        bound,
        until,
        body: body.ok_or_else(invalid)?,
    }))
}

// Shallow views borrow each frontend's existing nodes. The fold, not either
// producer, owns continuation, pre-check placement and error-safe lexical scope.
pub(crate) enum Control<'a, N> {
    Leaf,
    Sequence(&'a [N]),
    Repeat(&'a [N], u64),
    Saturate(&'a [N], Option<u64>),
}

#[derive(Clone, Copy)]
pub(crate) enum ControlStop {
    Count,
    Bound,
    Saturated,
    Until,
    SchedulerLimit,
}

#[derive(Default)]
pub(crate) struct ControlReport {
    pub report: RunReport,
    pub resource_limited: bool,
}

pub(crate) trait ControlContext {
    type Node;
    type Error;
    type Scope;

    fn view<'a>(&self, node: &'a Self::Node) -> Result<Control<'a, Self::Node>, Self::Error>;
    fn enter_scope(&mut self) -> Self::Scope;
    fn leave_scope(&mut self, scope: Self::Scope);
    fn leaf(
        &mut self,
        node: &Self::Node,
        path: &[usize],
        iterations: &[u64],
    ) -> Result<ControlReport, Self::Error>;
    fn until(
        &mut self,
        node: &Self::Node,
        path: &[usize],
        iterations: &[u64],
    ) -> Result<bool, Self::Error>;
    fn completed(
        &mut self,
        node: &Self::Node,
        path: &[usize],
        iterations: &[u64],
        report: &ControlReport,
        count: u64,
        stop: ControlStop,
    ) -> Result<(), Self::Error>;
}

pub(crate) fn fold_control<C: ControlContext>(
    context: &mut C,
    node: &C::Node,
    path: &mut Vec<usize>,
    iterations: &mut Vec<u64>,
) -> Result<ControlReport, C::Error> {
    let (body, bound, exact) = match context.view(node)? {
        Control::Leaf => return context.leaf(node, path, iterations),
        Control::Sequence(body) => {
            let scope = context.enter_scope();
            let result = fold_list(context, body, path, iterations);
            context.leave_scope(scope);
            return result;
        }
        Control::Repeat(body, count) => (body, Some(count), true),
        Control::Saturate(body, bound) => (body, bound, false),
    };
    let mut total = ControlReport::default();
    let mut count = 0;
    let stop = loop {
        if bound == Some(count) {
            break if exact {
                ControlStop::Count
            } else {
                ControlStop::Bound
            };
        }
        if context.until(node, path, iterations)? {
            break ControlStop::Until;
        }
        let scope = context.enter_scope();
        iterations.push(count);
        let result = fold_list(context, body, path, iterations);
        iterations.pop();
        context.leave_scope(scope);
        let next = result?;
        // Historical union retains earlier cannot-stop flags. Only this complete
        // iteration decides whether an early-stopping loop can finish now.
        let can_stop = next.report.can_stop;
        total.resource_limited |= next.resource_limited;
        total.report.union(next.report);
        count += 1;
        if !exact && can_stop {
            break if total.resource_limited {
                ControlStop::SchedulerLimit
            } else {
                ControlStop::Saturated
            };
        }
    };
    context.completed(node, path, iterations, &total, count, stop)?;
    Ok(total)
}

fn fold_list<C: ControlContext>(
    context: &mut C,
    body: &[C::Node],
    path: &mut Vec<usize>,
    iterations: &mut Vec<u64>,
) -> Result<ControlReport, C::Error> {
    let mut total = ControlReport::default();
    for (index, child) in body.iter().enumerate() {
        path.push(index);
        let result = fold_control(context, child, path, iterations);
        path.pop();
        let next = result?;
        total.resource_limited |= next.resource_limited;
        total.report.union(next.report);
    }
    Ok(total)
}

/// The `run-schedule` user-defined command.
///
/// See the [module-level documentation](self) for the full schedule language.
pub struct RunExtendedSchedule;

/// User-defined command implementing
/// `(let-scheduler name (scheduler-kind args...))`.
///
/// A top-level binding persists on the e-graph and can be used by later
/// `run-schedule` commands. See the [module documentation](self) for scoped
/// bindings inside a schedule.
pub struct LetSchedulerCommand;

/// Factory interface for constructing a scheduler from parsed egglog
/// arguments.
///
/// Scheduler registration uses [`add_scheduler_builder`], which accepts the
/// equivalent closure directly.
pub trait SchedulerGen {
    /// Creates a fresh scheduler for `egraph` from `args`.
    fn new_scheduler(&self, egraph: &egglog::EGraph, args: &[Expr]) -> Box<dyn Scheduler>;
}

type SchedulerBuilder = Box<
    dyn Fn(
            &egglog::EGraph,
            &egglog::ast::Span,
            &[Expr],
        ) -> Result<Box<dyn Scheduler>, egglog::Error>
        + Send
        + Sync,
>;

struct ScheduleState {
    schedulers: Vec<(String, SchedulerId)>,
    changed: bool,
    partial: RunReport,
}

// Compile actions and opt-in header descendants before a schedule anchor,
// including dead Repeat0 bodies. The ordered clone retains declaration/stack
// context without executing bodies or constructing schedulers.
fn validate_action_steps(egraph: &mut egglog::EGraph, roots: &[Expr]) -> Result<(), egglog::Error> {
    enum Pending<'a> {
        Step(&'a Expr, bool),
        Leave(usize),
        Restore(Box<egglog::EGraph>),
    }
    let mut pending: Vec<_> = roots
        .iter()
        .rev()
        .map(|expr| Pending::Step(expr, false))
        .collect();
    let mut commands = vec![];
    let mut bindings = vec![];
    let mut compiler = egraph.clone();
    while let Some(next) = pending.pop() {
        let (expr, strict) = match next {
            Pending::Step(expr, strict) => (expr, strict),
            Pending::Leave(mark) => {
                bindings.truncate(mark);
                continue;
            }
            Pending::Restore(outer) => {
                compiler.validate_program(std::mem::take(&mut commands))?;
                compiler = *outer;
                continue;
            }
        };
        let invalid =
            || egglog::Error::ParseError(ParseError(expr.span(), "Invalid schedule".into()));
        let header = loop_header(expr)?;
        let skipped = header.as_ref().is_some_and(|header| {
            header.exact && header.bound == Some(0)
                || header.until.as_ref().is_some_and(Vec::is_empty)
        }) || matches!(expr, Expr::Call(_, head, args) if head == "repeat"
            && matches!(args.first(), Some(Expr::Lit(_, Literal::Int(count))) if *count <= 0));
        if skipped {
            // Validate dead descendants without leaking their stack/declaration
            // metadata into subsequent steps.
            compiler = compiler.validate_program(std::mem::take(&mut commands))?;
            pending.push(Pending::Restore(Box::new(compiler.clone())));
        }
        if let Some(header) = header {
            if let Some(until) = header.until {
                commands.push(Command::Check(expr.span(), until));
            }
            pending.push(Pending::Leave(bindings.len()));
            pending.extend(
                header
                    .body
                    .iter()
                    .rev()
                    .map(|expr| Pending::Step(expr, true)),
            );
            continue;
        }
        if let Expr::Var(_, ruleset) = expr {
            if strict {
                commands.push(Command::RunSchedule(egglog::ast::Schedule::Run(
                    expr.span(),
                    egglog::ast::RunConfig {
                        ruleset: ruleset.clone(),
                        until: None,
                    },
                )));
            }
            continue;
        }
        let Expr::Call(_, head, args) = expr else {
            if strict {
                return Err(invalid());
            }
            continue;
        };
        match head.as_str() {
            "seq" | "saturate" => {
                pending.push(Pending::Leave(bindings.len()));
                pending.extend(args.iter().rev().map(|expr| Pending::Step(expr, strict)));
            }
            "repeat" => {
                if strict && !matches!(args.first(), Some(Expr::Lit(_, Literal::Int(_)))) {
                    return Err(invalid());
                }
                pending.push(Pending::Leave(bindings.len()));
                pending.extend(
                    args.iter()
                        .skip(1)
                        .rev()
                        .map(|expr| Pending::Step(expr, strict)),
                );
            }
            "fail" => {
                if strict && args.len() != 1 {
                    return Err(invalid());
                }
                pending.extend(args.iter().rev().map(|expr| Pending::Step(expr, strict)));
            }
            "let-scheduler" => {
                let [Expr::Var(_, name), Expr::Call(_, factory, _)] = args.as_slice() else {
                    if strict {
                        return Err(invalid());
                    }
                    continue;
                };
                if strict
                    && (bindings.contains(name)
                        || !scheduler_libs.lock().unwrap().contains_key(factory))
                {
                    return Err(invalid());
                }
                bindings.push(name.clone());
            }
            "run" | "run-with" if strict => {
                let rest = if head == "run-with" {
                    let [Expr::Var(_, scheduler), rest @ ..] = args.as_slice() else {
                        return Err(invalid());
                    };
                    compiler = compiler.validate_program(std::mem::take(&mut commands))?;
                    if !bindings.contains(scheduler)
                        && !compiler
                            .extension_state::<PermanentSchedulerState>()
                            .is_some_and(|state| state.contains_key(scheduler))
                    {
                        return Err(egglog::Error::ParseError(ParseError(
                            expr.span(),
                            format!("Unknown scheduler: {scheduler}"),
                        )));
                    }
                    rest
                } else {
                    args.as_slice()
                };
                let (ruleset, rest) = match rest {
                    [Expr::Var(_, name), rest @ ..] if name != ":until" => (name.as_str(), rest),
                    _ => ("", rest),
                };
                let until = match rest {
                    [] => None,
                    [Expr::Var(_, option), condition] if option == ":until" => {
                        Some(vec![Fact::Fact(condition.clone())])
                    }
                    _ => return Err(invalid()),
                };
                commands.push(Command::RunSchedule(egglog::ast::Schedule::Run(
                    expr.span(),
                    egglog::ast::RunConfig {
                        ruleset: ruleset.into(),
                        until,
                    },
                )));
            }
            "eval" => commands.extend(
                args.iter()
                    .map(|expr| Command::Action(Action::Expr(expr.span(), expr.clone()))),
            ),
            // This declaration's prepare hook registers only on the disposable
            // compiler, so subsequent actions see it without executing its body.
            "primitive" | "push" | "pop" | "set" | "delete" | "subsume" | "union" | "panic" => {
                commands.extend(egraph.parse_program(None, &expr.to_string())?)
            }
            _ if strict => {
                if egraph.has_command(head) {
                    // Preserve opaque native forwarding; never execute a
                    // callback merely to validate a dead body.
                } else if matches!(head.as_str(), "print-size" | "print-function" | "extract") {
                    commands.extend(egraph.parse_program(None, &expr.to_string())?);
                } else {
                    return Err(invalid());
                }
            }
            _ => (),
        }
    }
    compiler.validate_program(commands)?;
    Ok(())
}

lazy_static! {
    static ref scheduler_libs: Mutex<HashMap<String, SchedulerBuilder>> = {
        Mutex::new(HashMap::from_iter([(
            "back-off".into(),
            Box::new(schedulers::new_back_off_scheduler) as SchedulerBuilder,
        )]))
    };
}

/// Registers a scheduler constructor for use by `let-scheduler`.
///
/// The builder receives the current e-graph, the scheduler expression's source
/// span, and its unevaluated arguments. Registration is process-global;
/// registering the same name again replaces the previous builder.
pub fn add_scheduler_builder(name: String, builder: SchedulerBuilder) {
    scheduler_libs.lock().unwrap().insert(name, builder);
}

fn build_scheduler(
    egraph: &egglog::EGraph,
    span: &Span,
    name: &str,
    args: &[Expr],
) -> Result<Box<dyn Scheduler>, egglog::Error> {
    let libs = scheduler_libs.lock().unwrap();
    match libs.get(name) {
        Some(builder) => builder(egraph, span, args),
        None => Err(egglog::Error::ParseError(ParseError(
            span.clone(),
            format!("Unknown scheduler: {name}"),
        ))),
    }
}

impl ScheduleState {
    fn new() -> Self {
        Self {
            schedulers: vec![],
            changed: false,
            partial: RunReport::default(),
        }
    }

    // Current limitation: because it relies on the publicly available Rust APIs to access
    // the egraph, it has to split the same schedule into multiple runs. This means
    // - the same condition may be compiled and type checked multiple times
    // - the logging information may show that multiple schedules are run, but they
    //   are actually the same schedule.
    fn run(
        &mut self,
        egraph: &mut egglog::EGraph,
        arg: &Expr,
    ) -> Result<(Vec<CommandOutput>, RunReport), egglog::Error> {
        let mut context = NativeSchedule {
            state: self,
            egraph,
            outputs: vec![],
        };
        let report = fold_control(&mut context, arg, &mut vec![], &mut vec![])?;
        Ok((context.outputs, report.report))
    }

    fn run_leaf(
        &mut self,
        egraph: &mut egglog::EGraph,
        arg: &Expr,
    ) -> Result<(Vec<CommandOutput>, RunReport), egglog::Error> {
        let err = || {
            Err(egglog::Error::ParseError(ParseError(
                arg.span(),
                "Invalid schedule".into(),
            )))
        };

        if let Expr::Var(_, ruleset) = arg {
            return Ok((vec![], observed_run(egraph, arg.span(), ruleset, None)?));
        }

        let Expr::Call(span, head, exprs) = arg else {
            return err();
        };

        if head == "fail" {
            let mut child = arg;
            let mut spans = vec![];
            while let Expr::Call(span, head, args) = child {
                if head != "fail" {
                    break;
                }
                let [next] = args.as_slice() else {
                    return err();
                };
                spans.push(span.clone());
                child = next;
            }
            if matches!(child, Expr::Call(_, head, _) if matches!(head.as_str(), "seq" | "repeat" | "saturate" | "run" | "run-with" | "eval"))
            {
                let previous = std::mem::take(&mut self.changed);
                let previous_report = std::mem::take(&mut self.partial);
                let mut context = (self, child);
                let result = egraph.with_schedule_envelope(
                    &spans,
                    &mut context,
                    |graph, (state, child)| state.run(graph, child).map(|(_, report)| report),
                    |_, _| {},
                    |(state, _), event| {
                        if let ExecutionEvent::ActionsFinished { changed, .. } = event {
                            state.changed |= changed;
                        }
                    },
                );
                let changed = context.0.changed;
                context.0.changed |= previous;
                let mut report = std::mem::replace(&mut context.0.partial, previous_report);
                // An enclosing Fail may catch this error. Retain the actual
                // completed prefix's continuation even when no full report exists.
                if result.is_err() {
                    context.0.partial.union(report.clone());
                }
                result?;
                report.updated |= changed;
                report.can_stop &= !changed;
                return Ok((vec![], report));
            }
        }

        match head.as_str() {
            "let-scheduler" => match exprs.as_slice() {
                [
                    Expr::Var(_, name),
                    Expr::Call(scheduler_span, scheduler_name, args),
                ] => {
                    if self.schedulers.iter().any(|(n, _)| n == name) {
                        return Err(egglog::Error::ParseError(ParseError(
                            span.clone(),
                            format!("Scheduler {name} already exists"),
                        )));
                    }
                    let scheduler = build_scheduler(egraph, scheduler_span, scheduler_name, args)?;
                    let id = egraph.add_scheduler(scheduler);
                    self.schedulers.push((name.clone(), id));
                    Ok((vec![], RunReport::default()))
                }
                _ => err(),
            },
            "run" | "run-with" => {
                let mut scheduler = None;
                let exprs: &[egglog::ast::Expr] = if head.as_str() == "run-with" {
                    let Some((Expr::Var(scheduler_span, scheduler_name), rest)) =
                        exprs.split_first()
                    else {
                        return err();
                    };
                    scheduler = Some(
                        self.schedulers
                            .iter()
                            .rfind(|(n, _)| n == scheduler_name)
                            .map(|(_, id)| *id)
                            .or_else(|| {
                                egraph
                                    .extension_state::<PermanentSchedulerState>()
                                    .and_then(|state| state.get(scheduler_name).map(|b| b.id))
                            })
                            .ok_or_else(|| {
                                egglog::Error::ParseError(ParseError(
                                    scheduler_span.clone(),
                                    format!("Unknown scheduler: {scheduler_name}"),
                                ))
                            })?,
                    );
                    rest
                } else {
                    &exprs[..]
                };
                // Parsing
                let (ruleset, rest) = match exprs.first() {
                    None => ("", exprs),
                    Some(Expr::Var(_span, v)) if *v == ":until" => ("", exprs),
                    Some(Expr::Var(_span, ruleset)) => (ruleset.as_str(), &exprs[1..]),
                    Some(expr) => {
                        return Err(egglog::Error::ParseError(ParseError(
                            expr.span(),
                            "Expected ruleset name or :until clause in run schedule".into(),
                        )));
                    }
                };

                let until = match rest {
                    [] => None,
                    [Expr::Var(_span, ut), cond] if ut == ":until" => Some(cond.clone()),
                    _ => return err(),
                };

                if let Some(until) = until {
                    let span = until.span();
                    match egraph.check_condition_observed(
                        span,
                        vec![Fact::Fact(until)],
                        &mut |_| (),
                    ) {
                        Ok(()) => return Ok((vec![], RunReport::default())),
                        Err(egglog::Error::CheckError(..)) => (),
                        Err(error) => return Err(error),
                    }
                }

                let report = observed_run(egraph, span.clone(), ruleset, scheduler)?;
                Ok((vec![], report))
            }
            // (eval <expr> ...): evaluate each expression and add the resulting
            // terms to the e-graph — the schedule-step analogue of a top-level
            // expression such as `(Add (Num 1) (Num 2))`. Evaluation happens in
            // the full read/write (FullState) context, so the expressions may
            // also call reading primitives like `(get-size!)` that are not
            // admissible from an ordinary action context.
            "eval" => {
                let mut changed = false;
                for expr in exprs {
                    egraph.run_program_observed(
                        vec![Command::Action(Action::Expr(expr.span(), expr.clone()))],
                        &mut |_, _, _| {},
                        &mut |_, event| {
                            if let ExecutionEvent::ActionsFinished { changed: next, .. } = event {
                                changed |= next;
                                self.changed |= next;
                            }
                        },
                    )?;
                }
                Ok((
                    vec![],
                    RunReport {
                        updated: changed,
                        can_stop: !changed,
                        ..Default::default()
                    },
                ))
            }
            // Allowlisted commands forwarded via parse roundtrip.
            // User-defined commands are also allowed (run-schedule, multi-extract, keep-best, ...).
            // Anything else (rule declarations, let bindings, function definitions, ...) is rejected.
            _ if matches!(
                head.as_str(),
                "print-size"
                    | "print-function"
                    | "extract"
                    | "push"
                    | "pop"
                    | "union"
                    | "set"
                    | "delete"
                    | "subsume"
                    | "panic"
                    | "fail"
            ) || egraph.has_command(head) =>
            {
                let commands = egraph.parse_program(None, &arg.to_string())?;
                let mut report = RunReport::default();
                let mut cmd_outputs = Vec::new();
                let mut changed = false;
                let result = egraph.run_program_observed(
                    commands,
                    &mut |_, _, output| {
                        if let CommandOutput::RunSchedule(r) = output {
                            report.union(r);
                        } else {
                            cmd_outputs.push(output);
                        }
                    },
                    &mut |_, event| {
                        if let ExecutionEvent::ActionsFinished { changed: next, .. } = event {
                            changed |= next;
                        }
                    },
                );
                self.changed |= changed;
                result?;
                report.updated |= changed;
                report.can_stop &= !changed;
                Ok((cmd_outputs, report))
            }
            _ => err(),
        }
    }
}

struct NativeSchedule<'a> {
    state: &'a mut ScheduleState,
    egraph: &'a mut egglog::EGraph,
    outputs: Vec<CommandOutput>,
}

impl ControlContext for NativeSchedule<'_> {
    type Node = Expr;
    type Error = egglog::Error;
    type Scope = usize;

    fn view<'a>(&self, node: &'a Expr) -> Result<Control<'a, Expr>, egglog::Error> {
        if let Some(header) = loop_header(node)? {
            return Ok(if header.exact {
                Control::Repeat(header.body, header.bound.expect("required count"))
            } else {
                Control::Saturate(header.body, header.bound)
            });
        }
        Ok(match node {
            Expr::Call(_, name, body) if name == "seq" => Control::Sequence(body),
            Expr::Call(_, name, body) if name == "saturate" => Control::Saturate(body, None),
            Expr::Call(_, name, body) if name == "repeat" => match body.as_slice() {
                [Expr::Lit(_, Literal::Int(count)), body @ ..] => {
                    Control::Repeat(body, (*count).max(0) as u64)
                }
                _ => {
                    return Err(egglog::Error::ParseError(ParseError(
                        node.span(),
                        "Invalid schedule".into(),
                    )));
                }
            },
            _ => Control::Leaf,
        })
    }

    fn enter_scope(&mut self) -> usize {
        self.state.schedulers.len()
    }
    fn leave_scope(&mut self, mark: usize) {
        self.state.schedulers.truncate(mark);
    }

    fn leaf(
        &mut self,
        node: &Expr,
        _: &[usize],
        _: &[u64],
    ) -> Result<ControlReport, egglog::Error> {
        let (outputs, report) = self.state.run_leaf(self.egraph, node)?;
        self.state.changed |= report.updated;
        self.state.partial.union(report.clone());
        self.outputs.extend(outputs);
        Ok(ControlReport {
            report,
            resource_limited: false,
        })
    }

    fn until(&mut self, node: &Expr, _: &[usize], _: &[u64]) -> Result<bool, egglog::Error> {
        let Some(until) = loop_header(node)?.and_then(|header| header.until) else {
            return Ok(false);
        };
        match self
            .egraph
            .check_condition_observed(node.span(), until, &mut |event| {
                if let ExecutionEvent::ActionsFinished { changed, .. } = event {
                    self.state.changed |= changed;
                }
            }) {
            Ok(()) => Ok(true),
            Err(egglog::Error::CheckError(..)) => Ok(false),
            Err(error) => Err(error),
        }
    }
    fn completed(
        &mut self,
        _: &Expr,
        _: &[usize],
        _: &[u64],
        _: &ControlReport,
        _: u64,
        _: ControlStop,
    ) -> Result<(), egglog::Error> {
        Ok(())
    }
}

// Both schedule frontends enter the same native observed Run boundary. Policies
// are call-local; scheduler instances and residual matches remain on the graph.
fn observed_run(
    egraph: &mut egglog::EGraph,
    span: Span,
    ruleset: &str,
    scheduler: Option<SchedulerId>,
) -> Result<RunReport, egglog::Error> {
    let mut report = None;
    egraph.run_program_embedded_observed(
        vec![Command::RunSchedule(egglog::ast::Schedule::Run(
            span,
            egglog::ast::RunConfig {
                ruleset: ruleset.into(),
                until: None,
            },
        ))],
        &mut |_, origin, output| {
            if origin == egglog::ExecutionOrigin::Requested
                && let CommandOutput::RunSchedule(next) = output
            {
                report = Some(next);
            }
        },
        &mut |_, _| (),
        &|_, _| scheduler,
    )?;
    Ok(report.expect("successful native Run emits a report"))
}

impl UserDefinedCommand for RunExtendedSchedule {
    fn update(
        &self,
        egraph: &mut egglog::EGraph,
        args: &[Expr],
    ) -> Result<Vec<CommandOutput>, egglog::Error> {
        validate_action_steps(egraph, args)?;
        let mut context = (ScheduleState::new(), Vec::new());
        egraph.with_schedule_envelope(
            &[],
            &mut context,
            |graph, (schedule, outputs)| {
                let mut report = RunReport::default();
                for arg in args {
                    let (step_outputs, step_report) = schedule.run(graph, arg)?;
                    outputs.extend(step_outputs);
                    report.union(step_report);
                }
                Ok(report)
            },
            |(_, outputs), report| {
                outputs.push(CommandOutput::RunSchedule(
                    report.expect("unwrapped schedule completed").clone(),
                ))
            },
            |_, _| (),
        )?;
        Ok(context.1)
    }
}

impl UserDefinedCommand for LetSchedulerCommand {
    fn update(
        &self,
        egraph: &mut egglog::EGraph,
        args: &[Expr],
    ) -> Result<Vec<CommandOutput>, egglog::Error> {
        match args {
            [
                Expr::Var(span, name),
                Expr::Call(scheduler_span, scheduler_name, scheduler_args),
            ] => {
                if egraph
                    .extension_state::<PermanentSchedulerState>()
                    .and_then(|state| state.get(name).copied())
                    .is_some()
                {
                    return Err(egglog::Error::ParseError(ParseError(
                        span.clone(),
                        format!("Scheduler {name} already exists"),
                    )));
                }

                let scheduler =
                    build_scheduler(egraph, scheduler_span, scheduler_name, scheduler_args)?;
                let id = egraph.add_scheduler(scheduler);
                egraph
                    .extension_state_or_default::<PermanentSchedulerState>()
                    .insert(
                        name.clone(),
                        SchedulerBinding {
                            id,
                            resource_limited: true,
                        },
                    );
                Ok(vec![])
            }
            invalid => Err(egglog::Error::ParseError(ParseError(
                invalid.first().map_or_else(|| span!(), Expr::span),
                "Invalid let-scheduler command".into(),
            ))),
        }
    }
}

pub(crate) fn parse_tags(
    span: &egglog::ast::Span,
    args: &[Expr],
) -> Result<HashMap<String, Literal>, egglog::Error> {
    if !args.len().is_multiple_of(2) {
        return Err(egglog::Error::ParseError(ParseError(
            span.clone(),
            "Scheduler tags must be key/value pairs".into(),
        )));
    }
    let mut tags = HashMap::new();
    for arg in args.chunks(2) {
        let Expr::Var(ref tag_span, ref tag_name) = arg[0] else {
            return Err(egglog::Error::ParseError(ParseError(
                arg[0].span(),
                "Invalid scheduler tag name".into(),
            )));
        };
        let Expr::Lit(_, lit) = &arg[1] else {
            return Err(egglog::Error::ParseError(ParseError(
                arg[1].span(),
                format!("Invalid value for scheduler tag {tag_name}"),
            )));
        };
        if tags.contains_key(tag_name) {
            return Err(egglog::Error::ParseError(ParseError(
                tag_span.clone(),
                format!("Scheduler tag {tag_name} already exists"),
            )));
        }
        tags.insert(tag_name.to_string(), lit.clone());
    }
    Ok(tags)
}

mod schedulers {
    use std::collections::HashMap;

    use egglog::{
        ast::{Expr, Literal},
        scheduler::{Matches, Scheduler, SchedulerContext},
    };
    use log::{debug, info};

    use crate::parse_tags;

    fn parse_usize_tag(
        tags: &HashMap<String, Literal>,
        tag: &str,
        span: &egglog::ast::Span,
    ) -> Result<Option<usize>, egglog::Error> {
        tags.get(tag)
            .map(|lit| match lit {
                Literal::Int(n) if *n < 0 => {
                    Err(egglog::Error::ParseError(egglog::ast::ParseError(
                        span.clone(),
                        format!("Scheduler {tag} must be non-negative"),
                    )))
                }
                Literal::Int(n) => usize::try_from(*n).map_err(|_| {
                    egglog::Error::ParseError(egglog::ast::ParseError(
                        span.clone(),
                        format!("Scheduler {tag} is too large for this platform"),
                    ))
                }),
                _ => Err(egglog::Error::ParseError(egglog::ast::ParseError(
                    span.clone(),
                    format!("Scheduler {tag} must be an integer"),
                ))),
            })
            .transpose()
    }

    pub(super) fn new_back_off_scheduler(
        _egraph: &egglog::EGraph,
        span: &egglog::ast::Span,
        args: &[Expr],
    ) -> Result<Box<dyn Scheduler>, egglog::Error> {
        let tags = parse_tags(span, args)?;
        if let Some(tag) = tags
            .keys()
            .find(|tag| !matches!(tag.as_str(), ":match-limit" | ":ban-length" | ":node-limit"))
        {
            return Err(egglog::Error::ParseError(egglog::ast::ParseError(
                span.clone(),
                format!("Unknown back-off scheduler tag {tag}"),
            )));
        }
        let default_match_limit = parse_usize_tag(&tags, ":match-limit", span)?;
        let default_ban_length = parse_usize_tag(&tags, ":ban-length", span)?;
        let node_limit = parse_usize_tag(&tags, ":node-limit", span)?;
        Ok(Box::new(BackOffScheduler::new(
            default_match_limit,
            default_ban_length,
            node_limit,
        )))
    }

    #[derive(Debug, Clone)]
    pub struct BackOffScheduler {
        default_match_limit: usize,
        default_ban_length: usize,
        /// Soft threshold for the number of e-nodes. Once an observed count
        /// reaches it, rules are delayed instead of applied. A selected rule
        /// may insert any number of nodes, and the deferred rebuild may change
        /// the count again.
        node_limit: Option<usize>,
        stats: HashMap<String, RuleStats>,
    }

    #[derive(Debug, Clone)]
    struct RuleStats {
        iteration: usize,
        times_applied: usize,
        banned_until: usize,
        times_banned: usize,
        match_limit: usize,
        ban_length: usize,
    }

    impl BackOffScheduler {
        pub(crate) fn new(
            match_limit: Option<usize>,
            ban_length: Option<usize>,
            node_limit: Option<usize>,
        ) -> Self {
            Self {
                default_match_limit: match_limit.unwrap_or(1000),
                default_ban_length: ban_length.unwrap_or(5),
                node_limit,
                stats: HashMap::new(),
            }
        }

        fn get_stats(&mut self, rule: String) -> &mut RuleStats {
            self.stats.entry(rule).or_insert_with(|| RuleStats {
                times_applied: 0,
                banned_until: 0,
                times_banned: 0,
                match_limit: self.default_match_limit,
                ban_length: self.default_ban_length,
                iteration: 0,
            })
        }
    }

    impl Scheduler for BackOffScheduler {
        fn can_stop(&mut self, ctx: &SchedulerContext<'_>, rules: &[&str], _ruleset: &str) -> bool {
            // At the node limit, further iterations cannot make progress:
            // every rule would be delayed. Report saturation even though
            // banned rules may be pending.
            if let Some(node_limit) = self.node_limit {
                let nodes = ctx.num_nodes();
                if nodes >= node_limit {
                    info!("Node limit reached ({nodes} >= {node_limit}); stopping");
                    return true;
                }
            }
            let stats = &mut self.stats;
            let n_stats = stats.len();

            let mut banned: Vec<(&str, RuleStats)> = rules
                .iter()
                .filter_map(|rule| {
                    let s = stats.remove(*rule).unwrap();
                    if s.banned_until > s.iteration {
                        Some((*rule, s))
                    } else {
                        None
                    }
                })
                .collect();

            let result = if banned.is_empty() {
                true
            } else {
                let min_delta = banned
                    .iter()
                    .map(|(_, s)| {
                        assert!(s.banned_until >= s.iteration);
                        s.banned_until - s.iteration
                    })
                    .min()
                    .expect("banned cannot be empty here");

                let mut unbanned = vec![];
                for (name, s) in &mut banned {
                    s.banned_until -= min_delta;
                    if s.banned_until == s.iteration {
                        unbanned.push(*name);
                    }
                }

                assert!(!unbanned.is_empty());
                info!(
                    "Banned {}/{}, fast-forwarded by {} to unban {}",
                    banned.len(),
                    n_stats,
                    min_delta,
                    unbanned.join(", "),
                );

                false
            };

            // Recover the banned stats
            for (rule, s) in banned {
                stats.insert(rule.to_owned(), s);
            }

            result
        }

        fn filter_matches(
            &mut self,
            ctx: &SchedulerContext<'_>,
            rule: &str,
            _ruleset: &str,
            matches: &mut Matches,
        ) -> bool {
            let node_limit = self.node_limit;
            let total_len: usize = matches.match_size();
            let stats = self.get_stats(rule.to_owned());
            stats.iteration += 1;

            if stats.iteration < stats.banned_until {
                debug!(
                    "Skipping {} ({}-{}), banned until {}...",
                    rule, stats.times_applied, stats.times_banned, stats.banned_until,
                );
                return false;
            }

            let threshold = stats
                .match_limit
                .checked_shl(stats.times_banned as u32)
                .unwrap();
            if total_len > threshold {
                let ban_length = stats.ban_length << stats.times_banned;
                stats.times_banned += 1;
                stats.banned_until = stats.iteration + ban_length;
                info!(
                    "Banning {} ({}-{}) for {} iters: {} < {}",
                    rule, stats.times_applied, stats.times_banned, ban_length, threshold, total_len,
                );
                return false;
            }

            // Earlier rule actions are visible here. Rebuilding may later move
            // the count in either direction.
            if let Some(node_limit) = node_limit {
                let nodes = ctx.num_nodes();
                if nodes >= node_limit {
                    debug!(
                        "Delaying {}: at node limit ({} >= {})",
                        rule, nodes, node_limit
                    );
                    return false;
                }
            }

            stats.times_applied += 1;
            debug!(
                "Choosing all matches for {} ({}-{})",
                rule, stats.times_applied, stats.times_banned
            );
            matches.choose_all();
            true
        }
    }
}
