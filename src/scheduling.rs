use egglog::{
    ast::{Command, Expr, Fact, Facts, Literal, Macro, ParseError, Parser, Sexp, Span, Symbol},
    query, run_ruleset, RunReport, UserDefinedCommand,
};

pub struct RunExtendedSchedule;

struct ScheduleState {}

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
            "saturate" => {
                let mut report = RunReport::default();
                loop {
                    let mut iter_report= RunReport::default();
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
            "run" => {
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

                // Running the ruleset
                run_ruleset(egraph, ruleset.as_str())?;

                Ok(egraph.get_run_report().clone().unwrap())
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
        let mut schedule = ScheduleState {};
        for arg in args {
            schedule.run(egraph, arg)?;
        }
        Ok(())
    }
}

pub enum ExtendedSchedule {
    Saturate(Span, Box<ExtendedSchedule>),
    Repeat(Span, usize, Box<ExtendedSchedule>),
    Run(Span, usize),
    Sequence(Span, Vec<ExtendedSchedule>),
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
