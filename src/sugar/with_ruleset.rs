use egglog::ast::*;

pub struct WithRuleset;

impl Macro<Vec<Command>> for WithRuleset {
    fn get_head(&self) -> String {
        "with-ruleset".to_string()
    }

    fn parse(
        &self,
        args: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Command>, ParseError> {
        match args {
            [Sexp::Atom(ruleset, _), rest @ ..] => {
                let ruleset = *ruleset;
                let parsed_cmds = rest
                    .iter()
                    .map(|c| parser.parse_command(c))
                    .collect::<Result<Vec<_>, _>>()?;
                parsed_cmds
                    .into_iter()
                    .flatten()
                    .map(|cmd| {
                        Ok(match cmd {
                            Command::Rule {
                                ruleset: rule_ruleset,
                                name,
                                rule,
                            } => {
                                if rule_ruleset != "".into() {
                                    return Err(ParseError::new(
                                        rule.span,
                                        "expected rules in `with-ruleset` to have empty ruleset",
                                    ));
                                }

                                Command::Rule {
                                    ruleset,
                                    name,
                                    rule: rule.clone(),
                                }
                            }
                            Command::Rewrite(rule_ruleset, rewrite, subsume) => {
                                if rule_ruleset != "".into() {
                                    return Err(ParseError::new(
                                        rewrite.span,
                                        "expected rules in `with-ruleset` to have empty ruleset",
                                    ));
                                }

                                Command::Rewrite(ruleset, rewrite, subsume)
                            }
                            Command::BiRewrite(rule_ruleset, rewrite) => {
                                if rule_ruleset != "".into() {
                                    return Err(ParseError::new(
                                        rewrite.span,
                                        "expected rules in `with-ruleset` to have empty ruleset",
                                    ));
                                }

                                Command::BiRewrite(ruleset, rewrite)
                            }
                            _ => {
                                // Ideally the span should be the current command's span (i.e. cmd.span()),
                                // but currently not all of our commands have a span field.
                                return Err(ParseError::new(
                                    span.clone(),
                                    "expected rule or rewrite",
                                ));
                            }
                        })
                    })
                    .collect()
            }
            _ => Err(ParseError::new(
                span,
                "expected (with-ruleset <ruleset> <command>*)",
            )),
        }
    }
}
