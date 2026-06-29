use std::path::PathBuf;

use egglog::{
    ArcSort, CommandOutput, Error, TermDag, TermId, Value,
    ast::{Command, Expr, sanitize_internal_names},
    prelude::Span,
    span,
};
use egglog_experimental::*;
use libtest_mimic::Trial;

#[derive(Clone)]
struct Run {
    path: PathBuf,
    desugar: bool,
}

impl Run {
    fn run(&self) {
        let program = std::fs::read_to_string(&self.path)
            .unwrap_or_else(|err| panic!("Couldn't read {:?}: {:?}", self.path, err));

        if !self.desugar {
            self.test_program(
                self.path.to_str().map(String::from),
                &program,
                "Top level error",
            );
        } else {
            let mut egraph = new_experimental_egraph();
            let resolved = egraph
                .resolve_program(self.path.to_str().map(String::from), &program)
                .unwrap();
            let desugared_str = sanitize_internal_names(&resolved)
                .iter()
                .map(|cmd| cmd.to_string())
                .collect::<Vec<_>>()
                .join("\n");

            self.test_program(
                None,
                &desugared_str,
                "ERROR after parse, to_string, and parse again.",
            );
        }
    }

    fn test_program(&self, filename: Option<String>, program: &str, message: &str) {
        let mut egraph = new_experimental_egraph();
        let parsed = match egraph.parse_program(filename, program) {
            Ok(parsed) => parsed,
            Err(err) => {
                if !self.should_fail() {
                    panic!("{}: {err}", message)
                }
                return;
            }
        };
        match run_program_with_extract_checks(&mut egraph, parsed) {
            Ok(outputs) => {
                if self.should_fail() {
                    panic!(
                        "Program should have failed! Instead, logged:\n {}",
                        outputs
                            .iter()
                            .map(|output| output.to_string())
                            .collect::<Vec<_>>()
                            .join("\n")
                    );
                } else {
                    for output in outputs {
                        print!("  {}", output);
                    }
                    // Test graphviz dot generation
                    let mut serialized = egraph
                        .serialize(SerializeConfig {
                            max_functions: Some(40),
                            max_calls_per_function: Some(40),
                            ..Default::default()
                        })
                        .egraph;
                    serialized.to_dot();
                    // Also try splitting and inlining
                    serialized.split_classes(|id, _| egraph.from_node_id(id).is_primitive());
                    serialized.inline_leaves();
                    serialized.to_dot();
                }
            }
            Err(err) => {
                if !self.should_fail() {
                    panic!("{}: {err}", message)
                }
            }
        };
    }

    fn into_trial(self) -> Trial {
        let name = self.name().to_string();
        Trial::test(name, move || {
            self.run();
            Ok(())
        })
    }

    fn name(&self) -> impl std::fmt::Display + '_ {
        struct Wrapper<'a>(&'a Run);
        impl std::fmt::Display for Wrapper<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let stem = self.0.path.file_stem().unwrap();
                let stem_str = stem.to_string_lossy().replace(['.', '-', ' '], "_");
                write!(f, "{stem_str}")?;
                if self.0.desugar {
                    write!(f, "_resugar")?;
                }
                Ok(())
            }
        }
        Wrapper(self)
    }

    fn should_fail(&self) -> bool {
        self.path.to_string_lossy().contains("fail-typecheck")
    }
}

fn run_program_with_extract_checks(
    egraph: &mut EGraph,
    program: Vec<Command>,
) -> Result<Vec<CommandOutput>, Error> {
    let mut outputs = Vec::new();

    for command in program {
        let extract = extract_command_parts(&command);
        let command_outputs = egraph.run_program(vec![command])?;

        let Some((span, args, root, has_extractor)) = extract else {
            outputs.extend(command_outputs);
            continue;
        };

        validate_extract_outputs(egraph, &command_outputs, &root)?;
        outputs.extend(command_outputs);

        if !has_extractor {
            let mut dag_args = args;
            dag_args.push(Expr::Var(span.clone(), ":extractor".to_owned()));
            dag_args.push(Expr::Var(span.clone(), "greedy-dag".to_owned()));
            let dag_outputs = egraph.run_program(vec![Command::UserDefined(
                span,
                "extract".to_owned(),
                dag_args,
            )])?;
            validate_extract_outputs(egraph, &dag_outputs, &root)?;
            outputs.extend(dag_outputs);
        }
    }

    Ok(outputs)
}

fn extract_command_parts(command: &Command) -> Option<(Span, Vec<Expr>, Expr, bool)> {
    match command {
        Command::UserDefined(span, name, args) if name == "extract" => args.first().map(|root| {
            (
                span.clone(),
                args.clone(),
                root.clone(),
                extract_args_have_extractor(args),
            )
        }),
        _ => None,
    }
}

fn extract_args_have_extractor(args: &[Expr]) -> bool {
    args.iter()
        .any(|arg| matches!(arg, Expr::Var(_, keyword) if keyword == ":extractor"))
}

fn validate_extract_outputs(
    egraph: &mut EGraph,
    outputs: &[CommandOutput],
    root: &Expr,
) -> Result<(), Error> {
    let mut saw_extract = false;
    for output in outputs {
        match output {
            CommandOutput::ExtractBest(termdag, _cost, term) => {
                validate_extracted_term(egraph, root, termdag, *term)?;
                saw_extract = true;
            }
            CommandOutput::ExtractVariants(termdag, terms) => {
                for term in terms {
                    validate_extracted_term(egraph, root, termdag, *term)?;
                }
                saw_extract = true;
            }
            _ => {}
        }
    }
    if saw_extract {
        Ok(())
    } else {
        Err(Error::ExtractError(
            "extract command should produce an extract output".to_owned(),
        ))
    }
}

fn validate_extracted_term(
    egraph: &mut EGraph,
    root: &Expr,
    termdag: &TermDag,
    term: TermId,
) -> Result<(), Error> {
    let (root_sort, root_value) = egraph.eval_expr(root)?;
    let extracted_expr = termdag.term_to_expr(&term, span!());
    let (extracted_sort, extracted_value) = egraph.eval_expr(&extracted_expr)?;

    if root_sort.name() != extracted_sort.name() {
        return Err(Error::ExtractError(format!(
            "extracted term sort should match root expression sort: root {root:?}, extracted {extracted_expr}"
        )));
    }
    if canonical(egraph, &root_sort, root_value)
        != canonical(egraph, &extracted_sort, extracted_value)
    {
        return Err(Error::ExtractError(format!(
            "extracted term should be equal to root expression: root {root:?}, extracted {extracted_expr}"
        )));
    }

    Ok(())
}

fn canonical(egraph: &EGraph, sort: &ArcSort, value: Value) -> Value {
    egraph.canonical_value(sort, value)
}

fn generate_tests(glob: &str) -> Vec<Trial> {
    let mut trials = vec![];
    let mut push_trial = |run: Run| trials.push(run.into_trial());

    for entry in glob::glob(glob).unwrap() {
        let run = Run {
            path: entry.unwrap().clone(),
            desugar: false,
        };
        // let should_fail = run.should_fail();

        push_trial(run.clone());

        // Temporarily removed due to egglog changes. TODO: uncomment once egglog desugar is fixed
        // if !should_fail {
        //     push_trial(Run {
        //         desugar: true,
        //         ..run.clone()
        //     });
        // }
    }

    trials
}

fn main() {
    let args = libtest_mimic::Arguments::from_args();
    let tests = generate_tests("tests/**/*.egg");
    libtest_mimic::run(&args, tests).exit();
}
