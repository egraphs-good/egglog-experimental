use std::{process::Command, sync::{Arc, Mutex}};

use egglog::ast::{Expr, Macro, ParseError, Parser, RunConfig, Schedule, Sexp, Span, Symbol};


pub enum ExtendedSchedule {
    Saturate(Span, Box<ExtendedSchedule>),
    Repeat(Span, usize, Box<ExtendedSchedule>),
    Run(Span, usize),
    Sequence(Span, Vec<ExtendedSchedule>),
}

pub struct SchedulingInner {
    counter: usize,
    schedule: ExtendedSchedule,
    exprs: Vec<Expr>,
}

struct Scheduling(Arc<Mutex<SchedulingInner>>);

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
        let schedules = map_fallible(args, parser, parse_schedule)?;

        todo!()
    }
}

// helper for mapping a function that returns `Result`
// copied from egglog
fn map_fallible<T>(
    slice: &[Sexp],
    parser: &mut Parser,
    func: impl Fn(&mut Parser, &Sexp) -> Result<T, ParseError>,
) -> Result<Vec<T>, ParseError> {
    slice
        .iter()
        .map(|sexp| func(parser, sexp))
        .collect::<Result<_, _>>()
}

macro_rules! error {
    ($span:expr, $($fmt:tt)*) => {
        Err(ParseError($span, format!($($fmt)*)))
    };
}

fn parse_schedule(parser: &mut Parser, sexp: &Sexp) -> Result<ExtendedSchedule, ParseError> {
    if let Sexp::Atom(ruleset, span) = sexp {
        return Ok(ExtendedSchedule::Run(
            span.clone(),
            RunConfig {
                ruleset: *ruleset,
                until: None,
            },
        ));
    }

    let (head, tail, span) = sexp.expect_call("schedule")?;

    Ok(match head.into() {
        "saturate" => ExtendedSchedule::Saturate(
            span.clone(),
            Box::new(ExtendedSchedule::Sequence(
                span,
                map_fallible(tail, parser, parse_schedule)?,
            )),
        ),
        "seq" => ExtendedSchedule::Sequence(span, map_fallible(tail, parser, parse_schedule)?),
        "repeat" => match tail {
            [limit, tail @ ..] => ExtendedSchedule::Repeat(
                span.clone(),
                limit.expect_uint("number of iterations")?,
                Box::new(ExtendedSchedule::Sequence(
                    span,
                    map_fallible(tail, parser, parse_schedule)?,
                )),
            ),
            _ => return error!(span, "usage: (repeat <number of iterations> <schedule>*)"),
        },
        "run" => {
            let has_ruleset = match tail.first() {
                None => false,
                Some(Sexp::Atom(o, _)) if *o == ":until".into() => false,
                _ => true,
            };

            let (ruleset, rest) = if has_ruleset {
                (tail[0].expect_atom("ruleset name")?, &tail[1..])
            } else {
                ("".into(), tail)
            };

            let until = match parser.parse_options(rest)?.as_slice() {
                [] => None,
                [(":until", facts)] => Some(map_fallible(facts, parser, |parser, sexp| {
                    parser.parse_fact(sexp)
                })?),
                _ => return error!(span, "could not parse run options"),
            };

            ExtendedSchedule::Run(span, RunConfig { ruleset, until })
        }
        _ => return error!(span, "expected either saturate, seq, repeat, or run"),
    })
}
