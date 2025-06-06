use std::collections::HashMap;

use egglog::{
    ast::{Command, Expr, Fact, Facts, Literal, Macro, ParseError, Parser, Sexp, Span, Symbol},
    query, run_ruleset,
    scheduler::{Scheduler, SchedulerId},
    RunReport, UserDefinedCommand,
};

pub struct RunExtendedSchedule;

pub trait SchedulerGen {
    fn new_scheduler(&self, egraph: &egglog::EGraph, args: &[Expr]) -> Box<dyn Scheduler>;
}

#[derive(Default)]
struct ScheduleState {
    schedulers: Vec<(Symbol, SchedulerId)>,
    scheduler_libs: HashMap<Symbol, Box<dyn SchedulerGen>>,
}

impl ScheduleState {
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
            run_ruleset(egraph, ruleset.as_str())?;

            return Ok(egraph.get_run_report().clone().unwrap());
        }

        let Expr::Call(span, head, exprs) = arg else {
            return err();
        };
        match head.as_str() {
            "let-scheduler" => match exprs.as_slice() {
                [Expr::Var(_, name), Expr::Call(_, scheduler_name, args)] => {
                    if self.schedulers.iter().any(|(n, _)| n == name) {
                        return Err(egglog::Error::ParseError(ParseError(
                            span.clone(),
                            "Scheduler name already exists".into(),
                        )));
                    }
                    let scheduler = self
                        .scheduler_libs
                        .get(scheduler_name)
                        .unwrap()
                        .new_scheduler(egraph, args);
                    let id = egraph.add_scheduler(scheduler);
                    self.schedulers.push((name.clone(), id));
                    Ok(RunReport::default())
                }
                _ => err(),
            },
            "run" | "run-with" => {
                let mut scheduler = None;
                let exprs = if head.as_str() == "run-with" {
                    let Expr::Var(_, schedule_name) = exprs[0] else {
                        return err();
                    };
                    scheduler = Some(
                        self.schedulers
                            .iter()
                            .rfind(|(n, _)| *n == schedule_name)
                            .unwrap()
                            .1,
                    );
                    &exprs[1..]
                } else {
                    &exprs[..]
                };
                // Parsing
                let (ruleset, rest) = match exprs.first() {
                    None => ("".into(), &exprs[..]),
                    Some(Expr::Var(_span, v)) if *v == ":until".into() => ("".into(), &exprs[..]),
                    Some(Expr::Var(_span, ruleset)) => (*ruleset, &exprs[1..]),
                    _ => unreachable!(),
                };

                let until = match rest {
                    [] => None,
                    [Expr::Var(_span, ut), cond] if *ut == ":until".into() => Some(cond.clone()),
                    _ => return err(),
                };

                if let Some(until) = until {
                    // Parse the facts from the `until` expression
                    let res = query(egraph, &[], Facts(vec![Fact::Fact(until)]))?;
                    if res.iter().next().is_none() {
                        return Ok(RunReport::default());
                    }
                }

                let run_report = if let Some(scheduler) = scheduler {
                    egraph.step_rules_with_scheduler(scheduler, ruleset.clone())
                } else {
                    // Running the ruleset
                    egraph.step_rules(ruleset)
                };

                Ok(run_report)
            }
            "saturate" => {
                let mut report = RunReport::default();
                loop {
                    let mut iter_report = RunReport::default();
                    for expr in exprs {
                        let res = self.run(egraph, expr)?;
                        iter_report.union(&res);
                    }
                    if !iter_report.updated {
                        break;
                    }
                    report.union(&iter_report);
                }
                Ok(report)
            }
            "seq" => {
                let mut report = RunReport::default();
                for expr in exprs {
                    // Recursively run each expression in the sequence
                    let res = self.run(egraph, expr)?;
                    report.union(&res);
                }
                Ok(report)
            }
            "repeat" => {
                match exprs.as_slice() {
                    [Expr::Lit(_span, Literal::Int(n)), rest @ ..] => {
                        let mut report = RunReport::default();
                        for _ in 0..*n {
                            // Recursively run the rest of the expressions
                            for expr in rest {
                                let res = self.run(egraph, expr)?;
                                report.union(&res);
                            }
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
    fn update(&self, egraph: &mut egglog::EGraph, args: &[Expr]) -> Result<(), egglog::Error> {
        let mut schedule = ScheduleState::default();
        for arg in args {
            schedule.run(egraph, arg)?;
        }
        Ok(())
    }
}

pub struct Scheduling;

impl Macro<Vec<Command>> for Scheduling {
    fn name(&self) -> Symbol {
        "run-schedule".into()
    }

    fn parse(
        &self,
        args: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Command>, egglog::ast::ParseError> {
        // let schedules = map_fallible(args, parser, parse_schedule)?;
        let args = args
            .iter()
            .map(|arg| parser.parse_expr(arg))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(vec![Command::UserDefined(
            span,
            "run-schedule*".into(),
            args.to_vec(),
        )])
    }
}
