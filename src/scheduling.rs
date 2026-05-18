use std::{
    collections::HashMap,
    sync::{Arc, Mutex},
};

use egglog::{
    CommandOutput, EGraphId, UserDefinedCommand,
    ast::{Command, Expr, Fact, Literal, ParseError},
    prelude::{RustSpan, Span},
    prelude::run_ruleset,
    scheduler::{Scheduler, SchedulerId},
};
use egglog_reports::RunReport;
use lazy_static::lazy_static;

/// Top-level scheduler names are stored in the command layer and validated
/// against both the current e-graph owner and scheduler allocation token before
/// use because raw scheduler ids can be reused across clones and `push`/`pop`.
pub type PermanentSchedulers = Arc<Mutex<PermanentSchedulerState>>;

type EGraphOwner = EGraphId;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct SchedulerToken(u64);

#[derive(Clone, Copy, Debug)]
struct SchedulerBinding {
    id: SchedulerId,
    token: SchedulerToken,
}

#[derive(Default)]
pub struct PermanentSchedulerState {
    next_token: u64,
    bindings: HashMap<EGraphOwner, HashMap<String, SchedulerBinding>>,
    allocations: HashMap<(EGraphOwner, SchedulerId), SchedulerToken>,
}

impl PermanentSchedulerState {
    fn record_scheduler(&mut self, owner: EGraphOwner, id: SchedulerId) -> SchedulerToken {
        let token = SchedulerToken(self.next_token);
        self.next_token = self
            .next_token
            .checked_add(1)
            .expect("scheduler token counter overflowed");
        self.allocations.insert((owner, id), token);
        token
    }

    fn get_binding(&self, owner: EGraphOwner, name: &str) -> Option<SchedulerBinding> {
        self.bindings
            .get(&owner)
            .and_then(|bindings| bindings.get(name).copied())
    }

    fn insert_binding(&mut self, owner: EGraphOwner, name: String, binding: SchedulerBinding) {
        self.bindings
            .entry(owner)
            .or_default()
            .insert(name, binding);
    }

    fn remove_binding(&mut self, owner: EGraphOwner, name: &str) {
        if let Some(bindings) = self.bindings.get_mut(&owner) {
            bindings.remove(name);
        }
    }

    fn binding_is_current(&self, owner: EGraphOwner, binding: SchedulerBinding) -> bool {
        self.allocations.get(&(owner, binding.id)).copied() == Some(binding.token)
    }
}

fn egraph_owner(egraph: &egglog::EGraph) -> EGraphOwner {
    egraph.instance_id()
}

pub struct RunExtendedSchedule {
    permanent_schedulers: PermanentSchedulers,
}

pub struct LetSchedulerCommand {
    permanent_schedulers: PermanentSchedulers,
}

pub trait SchedulerGen {
    fn new_scheduler(&self, egraph: &egglog::EGraph, args: &[Expr]) -> Box<dyn Scheduler>;
}

type SchedulerBuilder = Box<dyn Fn(&egglog::EGraph, &[Expr]) -> Box<dyn Scheduler> + Send + Sync>;

struct ScheduleState {
    permanent_schedulers: PermanentSchedulers,
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

impl ScheduleState {
    fn new(permanent_schedulers: PermanentSchedulers) -> Self {
        Self {
            permanent_schedulers,
            schedulers: vec![],
        }
    }

    fn lookup_scheduler(
        &self,
        egraph: &egglog::EGraph,
        span: &egglog::ast::Span,
        name: &str,
    ) -> Result<SchedulerId, egglog::Error> {
        if let Some(id) = self
            .schedulers
            .iter()
            .rfind(|(n, _)| n == name)
            .map(|(_, id)| *id)
        {
            return Ok(id);
        }

        let owner = egraph_owner(egraph);
        let permanent_schedulers = self.permanent_schedulers.lock().unwrap();
        match permanent_schedulers.get_binding(owner, name) {
            Some(binding)
                if egraph.contains_scheduler(binding.id)
                    && permanent_schedulers.binding_is_current(owner, binding) =>
            {
                Ok(binding.id)
            }
            Some(_) => Err(egglog::Error::ParseError(ParseError(
                span.clone(),
                format!("Unknown scheduler: {name}"),
            ))),
            None => Err(egglog::Error::ParseError(ParseError(
                span.clone(),
                format!("Unknown scheduler: {name}"),
            ))),
        }
    }

    // Current limitation: because it relies on the publicly available Rust APIs to access
    // the egraph, it has to split the same schedule into multiple runs. This means
    // - the same condition may be compiled and type checked multiple times
    // - the logging information may show that multiple schedules are run, but they
    //   are actually the same schedule.
    fn run(&mut self, egraph: &mut egglog::EGraph, arg: &Expr) -> Result<RunReport, egglog::Error> {
        let err = || {
            Err(egglog::Error::ParseError(ParseError(
                arg.span(),
                "Invalid schedule".into(),
            )))
        };

        if let Expr::Var(_, ruleset) = arg {
            let output = run_ruleset(egraph, ruleset.as_str())?;
            assert!(output.len() == 1);
            if let CommandOutput::RunSchedule(report) = &output[0] {
                return Ok(report.clone());
            }
            panic!("Expected a RunSchedule, got {:?}", output[0]);
        }

        let Expr::Call(span, head, exprs) = arg else {
            return err();
        };

        macro_rules! new_scope {
            ($f:expr) => {{
                let curr_scope = self.schedulers.len();
                let res: Result<RunReport, egglog::Error> = $f();
                self.schedulers.truncate(curr_scope);
                res
            }};
        }

        match head.as_str() {
            "let-scheduler" => match exprs.as_slice() {
                [Expr::Var(_, name), Expr::Call(_, scheduler_name, args)] => {
                    if self.schedulers.iter().any(|(n, _)| n == name) {
                        return Err(egglog::Error::ParseError(ParseError(
                            span.clone(),
                            format!("Scheduler {name} already exists"),
                        )));
                    }
                    let scheduler =
                        (scheduler_libs.lock().unwrap().get(scheduler_name).unwrap())(egraph, args);
                    let owner = egraph_owner(egraph);
                    let id = egraph.add_scheduler(scheduler);
                    self.permanent_schedulers
                        .lock()
                        .unwrap()
                        .record_scheduler(owner, id);
                    self.schedulers.push((name.clone(), id));
                    Ok(RunReport::default())
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
                    scheduler =
                        Some(self.lookup_scheduler(egraph, scheduler_span, scheduler_name)?);
                    rest
                } else {
                    &exprs[..]
                };
                // Parsing
                let (ruleset, rest) = match exprs.first() {
                    None => ("", exprs),
                    Some(Expr::Var(_span, v)) if *v == ":until" => ("", exprs),
                    Some(Expr::Var(_span, ruleset)) => (ruleset.as_str(), &exprs[1..]),
                    _ => unreachable!(),
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
                        return Ok(RunReport::default());
                    }
                }

                if let Some(scheduler) = scheduler {
                    egraph.step_rules_with_scheduler(scheduler, ruleset)
                } else {
                    // Running the ruleset
                    egraph.step_rules(ruleset)
                }
            }
            "saturate" => {
                let mut report = RunReport::default();
                loop {
                    let iter_report = new_scope!(|| {
                        let mut iter_report = RunReport::default();
                        for expr in exprs {
                            let res = self.run(egraph, expr)?;
                            iter_report.union(res);
                        }
                        Ok(iter_report)
                    })?;
                    if !iter_report.updated {
                        break;
                    }
                    report.union(iter_report);
                }
                Ok(report)
            }
            "seq" => {
                new_scope!(|| {
                    let mut report = RunReport::default();
                    for expr in exprs {
                        // Recursively run each expression in the sequence
                        let res = self.run(egraph, expr)?;
                        report.union(res);
                    }
                    Ok(report)
                })
            }
            "repeat" => {
                match exprs.as_slice() {
                    [Expr::Lit(_span, Literal::Int(n)), rest @ ..] => {
                        let mut report = RunReport::default();
                        for _ in 0..*n {
                            let sub_report = new_scope!(|| {
                                let mut report = RunReport::default();
                                // Recursively run the rest of the expressions
                                for expr in rest {
                                    let res = self.run(egraph, expr)?;
                                    report.union(res);
                                }
                                Ok(report)
                            })?;
                            report.union(sub_report);
                        }
                        Ok(report)
                    }
                    _ => err(),
                }
            }
            _ => Err(egglog::Error::ParseError(ParseError(
                span.clone(),
                "Invalid schedule".into(),
            ))),
        }
    }
}

impl UserDefinedCommand for RunExtendedSchedule {
    fn update(
        &self,
        egraph: &mut egglog::EGraph,
        args: &[Expr],
    ) -> Result<Option<CommandOutput>, egglog::Error> {
        let mut schedule = ScheduleState::new(self.permanent_schedulers.clone());
        let mut report = RunReport::default();
        for arg in args {
            report.union(schedule.run(egraph, arg)?);
        }
        Ok(Some(CommandOutput::RunSchedule(report)))
    }
}

impl RunExtendedSchedule {
    pub fn new(permanent_schedulers: PermanentSchedulers) -> Self {
        Self {
            permanent_schedulers,
        }
    }
}

impl UserDefinedCommand for LetSchedulerCommand {
    fn update(
        &self,
        egraph: &mut egglog::EGraph,
        args: &[Expr],
    ) -> Result<Option<CommandOutput>, egglog::Error> {
        match args {
            [
                Expr::Var(span, name),
                Expr::Call(_, scheduler_name, scheduler_args),
            ] => {
                let owner = egraph_owner(egraph);
                {
                    let mut permanent_schedulers = self.permanent_schedulers.lock().unwrap();
                    if let Some(binding) = permanent_schedulers.get_binding(owner, name) {
                        if egraph.contains_scheduler(binding.id)
                            && permanent_schedulers.binding_is_current(owner, binding)
                        {
                            return Err(egglog::Error::ParseError(ParseError(
                                span.clone(),
                                format!("Scheduler {name} already exists"),
                            )));
                        }
                        permanent_schedulers.remove_binding(owner, name);
                    }
                }

                let scheduler = {
                    let libs = scheduler_libs.lock().unwrap();
                    let Some(builder) = libs.get(scheduler_name) else {
                        return Err(egglog::Error::ParseError(ParseError(
                            span.clone(),
                            format!("Unknown scheduler: {scheduler_name}"),
                        )));
                    };
                    builder(egraph, scheduler_args)
                };
                let id = egraph.add_scheduler(scheduler);
                let mut permanent_schedulers = self.permanent_schedulers.lock().unwrap();
                let token = permanent_schedulers.record_scheduler(owner, id);
                permanent_schedulers.insert_binding(
                    owner,
                    name.clone(),
                    SchedulerBinding { id, token },
                );
                Ok(None)
            }
            [expr, ..] => Err(egglog::Error::ParseError(ParseError(
                expr.span(),
                "Invalid let-scheduler command".into(),
            ))),
            [] => Err(egglog::Error::ParseError(ParseError(
                Span::Rust(Arc::new(RustSpan {
                    file: "egglog-experimental",
                    line: 0,
                    column: 0,
                })),
                "Invalid let-scheduler command".into(),
            ))),
        }
    }
}

impl LetSchedulerCommand {
    pub fn new(permanent_schedulers: PermanentSchedulers) -> Self {
        Self {
            permanent_schedulers,
        }
    }
}

pub(crate) fn parse_tags(args: &[Expr]) -> HashMap<String, Literal> {
    let mut tags = HashMap::new();
    assert!(args.len().is_multiple_of(2));
    for arg in args.chunks(2) {
        let Expr::Var(_, ref tag_name) = arg[0] else {
            panic!("Invalid tag name: {:?}", arg[0]);
        };
        let Expr::Lit(_, lit) = &arg[1] else {
            panic!("Invalid tag value: {:?}", arg[1]);
        };
        if tags.contains_key(&tag_name.to_string()) {
            panic!("Tag name already exists: {:?}", tag_name);
        }
        tags.insert(tag_name.to_string(), lit.clone());
    }
    tags
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
        args: &[Expr],
    ) -> Box<dyn Scheduler> {
        let tags = parse_tags(args);
        let default_match_limit = tags
            .get(":match-limit")
            .map(|lit| {
                let Literal::Int(n) = lit else {
                    panic!("Invalid match limit: {:?}", lit);
                };
                *n as usize
            })
            .unwrap_or(1000);
        let default_ban_length = tags
            .get(":ban-length")
            .map(|lit| {
                let Literal::Int(n) = lit else {
                    panic!("Invalid ban length: {:?}", lit);
                };
                *n as usize
            })
            .unwrap_or(5);
        Box::new(BackOffScheduler {
            default_match_limit,
            default_ban_length,
            stats: HashMap::new(),
        })
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
