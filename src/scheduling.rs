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
//!   scheduler instance (e.g. `(back-off :match-limit 1000 :ban-length 5)`).
//!   The binding is scoped to the enclosing `seq`/`saturate`/`repeat` block.
//! - **`(seq step...)`** — run each step once, in order.
//! - **`(saturate step...)`** — repeatedly run the body until it makes no further
//!   progress (the accumulated report's `can_stop` is set).
//! - **`(repeat n step...)`** — run the body `n` times.
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
    CommandOutput, UserDefinedCommand,
    ast::{Command, Expr, Fact, Literal, ParseError},
    prelude::{Span, run_ruleset},
    scheduler::{Scheduler, SchedulerId},
    span,
};
use egglog_reports::RunReport;
use lazy_static::lazy_static;

type PermanentSchedulerState = HashMap<String, SchedulerId>;

/// The `run-schedule` user-defined command.
///
/// See the [module-level documentation](self) for the full schedule language.
pub struct RunExtendedSchedule;

pub struct LetSchedulerCommand;

pub trait SchedulerGen {
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
}

lazy_static! {
    static ref scheduler_libs: Mutex<HashMap<String, SchedulerBuilder>> = {
        Mutex::new(HashMap::from_iter([(
            "back-off".into(),
            Box::new(schedulers::new_back_off_scheduler) as SchedulerBuilder,
        )]))
    };
}

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
        Self { schedulers: vec![] }
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
        let err = || {
            Err(egglog::Error::ParseError(ParseError(
                arg.span(),
                "Invalid schedule".into(),
            )))
        };

        if let Expr::Var(_, ruleset) = arg {
            let output = run_ruleset(egraph, ruleset.as_str())?;
            if let [CommandOutput::RunSchedule(report)] = output.as_slice() {
                return Ok((vec![], report.clone()));
            }
            return Err(egglog::Error::ParseError(ParseError(
                arg.span(),
                format!("Expected ruleset {ruleset} to produce one RunSchedule output"),
            )));
        }

        let Expr::Call(span, head, exprs) = arg else {
            return err();
        };

        macro_rules! new_scope {
            ($f:expr) => {{
                let curr_scope = self.schedulers.len();
                let res: Result<(Vec<CommandOutput>, RunReport), egglog::Error> = $f();
                self.schedulers.truncate(curr_scope);
                res
            }};
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
                                    .and_then(|state| state.get(scheduler_name).copied())
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
                    if egraph
                        .run_program(vec![Command::Check(span, vec![Fact::Fact(until)])])
                        .is_ok()
                    {
                        return Ok((vec![], RunReport::default()));
                    }
                }

                let report = if let Some(scheduler) = scheduler {
                    egraph.step_rules_with_scheduler(scheduler, ruleset)?
                } else {
                    egraph.step_rules(ruleset)?
                };
                Ok((vec![], report))
            }
            "saturate" => {
                let mut all_outputs: Vec<CommandOutput> = vec![];
                let mut report = RunReport::default();
                loop {
                    let (iter_outputs, iter_report) = new_scope!(|| {
                        let mut iter_outputs: Vec<CommandOutput> = vec![];
                        let mut iter_report = RunReport::default();
                        for expr in exprs {
                            let (step_outputs, step_report) = self.run(egraph, expr)?;
                            iter_outputs.extend(step_outputs);
                            iter_report.union(step_report);
                        }
                        Ok((iter_outputs, iter_report))
                    })?;
                    let should_stop = iter_report.can_stop;
                    all_outputs.extend(iter_outputs);
                    report.union(iter_report);
                    if should_stop {
                        break;
                    }
                }
                Ok((all_outputs, report))
            }
            "seq" => {
                new_scope!(|| {
                    let mut all_outputs: Vec<CommandOutput> = vec![];
                    let mut report = RunReport::default();
                    for expr in exprs {
                        let (step_outputs, step_report) = self.run(egraph, expr)?;
                        all_outputs.extend(step_outputs);
                        report.union(step_report);
                    }
                    Ok((all_outputs, report))
                })
            }
            "repeat" => match exprs.as_slice() {
                [Expr::Lit(_span, Literal::Int(n)), rest @ ..] => {
                    let mut all_outputs: Vec<CommandOutput> = vec![];
                    let mut report = RunReport::default();
                    for _ in 0..*n {
                        let (iter_outputs, iter_report) = new_scope!(|| {
                            let mut iter_outputs: Vec<CommandOutput> = vec![];
                            let mut iter_report = RunReport::default();
                            for expr in rest {
                                let (step_outputs, step_report) = self.run(egraph, expr)?;
                                iter_outputs.extend(step_outputs);
                                iter_report.union(step_report);
                            }
                            Ok((iter_outputs, iter_report))
                        })?;
                        all_outputs.extend(iter_outputs);
                        report.union(iter_report);
                    }
                    Ok((all_outputs, report))
                }
                _ => err(),
            },
            // (eval <expr> ...): evaluate each expression and add the resulting
            // terms to the e-graph — the schedule-step analogue of a top-level
            // expression such as `(Add (Num 1) (Num 2))`. Evaluation happens in
            // the full read/write (FullState) context, so the expressions may
            // also call reading primitives like `(get-size!)` that are not
            // admissible from an ordinary action context.
            "eval" => {
                for expr in exprs {
                    egraph.eval_expr(expr)?;
                }
                Ok((vec![], RunReport::default()))
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
            ) || egraph.has_command(head) =>
            {
                let outputs = egraph.parse_and_run_program(None, &format!("{}", arg))?;
                let mut report = RunReport::default();
                let mut cmd_outputs = Vec::new();
                for output in outputs {
                    if let CommandOutput::RunSchedule(r) = output {
                        report.union(r);
                    } else {
                        cmd_outputs.push(output);
                    }
                }
                Ok((cmd_outputs, report))
            }
            _ => err(),
        }
    }
}

impl UserDefinedCommand for RunExtendedSchedule {
    fn update(
        &self,
        egraph: &mut egglog::EGraph,
        args: &[Expr],
    ) -> Result<Vec<CommandOutput>, egglog::Error> {
        let mut schedule = ScheduleState::new();
        let mut report = RunReport::default();
        let mut outputs: Vec<CommandOutput> = Vec::new();
        for arg in args {
            let (step_outputs, step_report) = schedule.run(egraph, arg)?;
            outputs.extend(step_outputs);
            report.union(step_report);
        }
        outputs.push(CommandOutput::RunSchedule(report));
        Ok(outputs)
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
                    .insert(name.clone(), id);
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
        scheduler::{Matches, Scheduler},
    };
    use log::{debug, info};

    use crate::parse_tags;

    pub(super) fn new_back_off_scheduler(
        _egraph: &egglog::EGraph,
        span: &egglog::ast::Span,
        args: &[Expr],
    ) -> Result<Box<dyn Scheduler>, egglog::Error> {
        let tags = parse_tags(span, args)?;
        let default_match_limit = tags
            .get(":match-limit")
            .map(|lit| match lit {
                Literal::Int(n) if *n >= 0 => Ok(*n as usize),
                Literal::Int(_) => Err(egglog::Error::ParseError(egglog::ast::ParseError(
                    span.clone(),
                    "Scheduler :match-limit must be non-negative".into(),
                ))),
                _ => Err(egglog::Error::ParseError(egglog::ast::ParseError(
                    span.clone(),
                    "Scheduler :match-limit must be an integer".into(),
                ))),
            })
            .transpose()?
            .unwrap_or(1000);
        let default_ban_length = tags
            .get(":ban-length")
            .map(|lit| match lit {
                Literal::Int(n) if *n >= 0 => Ok(*n as usize),
                Literal::Int(_) => Err(egglog::Error::ParseError(egglog::ast::ParseError(
                    span.clone(),
                    "Scheduler :ban-length must be non-negative".into(),
                ))),
                _ => Err(egglog::Error::ParseError(egglog::ast::ParseError(
                    span.clone(),
                    "Scheduler :ban-length must be an integer".into(),
                ))),
            })
            .transpose()?
            .unwrap_or(5);
        Ok(Box::new(BackOffScheduler {
            default_match_limit,
            default_ban_length,
            stats: HashMap::new(),
        }))
    }

    #[derive(Debug, Clone)]
    pub struct BackOffScheduler {
        default_match_limit: usize,
        default_ban_length: usize,
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
        fn can_stop(&mut self, rules: &[&str], _ruleset: &str) -> bool {
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

        fn filter_matches(&mut self, rule: &str, _ruleset: &str, matches: &mut Matches) -> bool {
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
            let total_len: usize = matches.match_size();
            if total_len > threshold {
                let ban_length = stats.ban_length << stats.times_banned;
                stats.times_banned += 1;
                stats.banned_until = stats.iteration + ban_length;
                info!(
                    "Banning {} ({}-{}) for {} iters: {} < {}",
                    rule, stats.times_applied, stats.times_banned, ban_length, threshold, total_len,
                );
                false
            } else {
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
}
