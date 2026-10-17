use std::collections::VecDeque;
use std::path::PathBuf;

use egglog::{
    CommandOutput, Error,
    ast::{Command, Expr, sanitize_internal_names},
    extract::TreeCostModelFromDag,
    span,
};
use egglog_experimental::*;
use egglog_experimental::{
    proto as pb,
    protobuf::{
        Engine,
        source::{Renderer, Source, Submission},
    },
};
use libtest_mimic::Trial;
use prost::Message;

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
        // Validate from the same pre-command state without letting test
        // instrumentation mutate the program's real e-graph.
        let mut validation_egraph = extract.as_ref().map(|_| egraph.clone());
        let command_outputs = egraph.run_program(vec![command])?;

        let Some(extract) = extract else {
            outputs.extend(command_outputs);
            continue;
        };

        validate_extract_outputs(
            validation_egraph.as_mut().unwrap(),
            &extract,
            extracted_exprs(&command_outputs)?,
        )?;
        outputs.extend(command_outputs);
    }

    Ok(outputs)
}

struct ExtractCheck {
    root: Expr,
    variants: Option<Expr>,
    use_greedy_dag: bool,
}

fn extract_command_parts(command: &Command) -> Option<ExtractCheck> {
    match command {
        Command::Extract(_, root, variants) => Some(ExtractCheck {
            root: root.clone(),
            variants: Some(variants.clone()),
            use_greedy_dag: false,
        }),
        Command::UserDefined(_, name, args) if name == "extract" => {
            let use_greedy_dag = matches!(
                args.last_chunk::<2>(),
                Some([Expr::Var(_, keyword), Expr::Var(..)]) if keyword == ":extractor"
            );
            let positional = if use_greedy_dag {
                args.get(..args.len() - 2)?
            } else {
                args
            };
            match positional {
                [root] => Some(ExtractCheck {
                    root: root.clone(),
                    variants: None,
                    use_greedy_dag,
                }),
                [root, variants] => Some(ExtractCheck {
                    root: root.clone(),
                    variants: Some(variants.clone()),
                    use_greedy_dag,
                }),
                _ => None,
            }
        }
        _ => None,
    }
}

fn validate_extract_outputs(
    egraph: &mut EGraph,
    extract: &ExtractCheck,
    requested_exprs: Vec<Expr>,
) -> Result<(), Error> {
    // Evaluate the potentially stateful root exactly once, then invoke the
    // opposite extractor directly so both algorithms see that same value.
    let (root_sort, root_value) = egraph.eval_expr(&extract.root)?;
    let nvariants = if let Some(variants) = &extract.variants {
        let (_, value) = egraph.eval_expr(variants)?;
        usize::try_from(egraph.value_to_base::<i64>(value)).map_err(|_| {
            Error::ExtractError("extract variant count must be nonnegative".to_owned())
        })?
    } else {
        0
    };

    let roots = vec![(root_sort.clone(), root_value)];
    let paired_exprs = if nvariants == 0 {
        let extracted = if extract.use_greedy_dag {
            egraph.extract_best_with_cost_model(roots, TreeCostModelFromDag(DynamicCostModel))?
        } else {
            extract_best_greedy_dag(egraph, roots, DynamicCostModel)?
        };
        let root = extracted
            .terms
            .into_iter()
            .next()
            .expect("one root was requested")
            .ok_or_else(|| Error::ExtractError("paired extractor returned no term".to_owned()))?;
        vec![extracted.termdag.term_to_expr(&root.term, span!())]
    } else {
        let extracted = if extract.use_greedy_dag {
            egraph.extract_variants_with_cost_model(
                roots,
                nvariants,
                TreeCostModelFromDag(DynamicCostModel),
            )?
        } else {
            extract_variants_greedy_dag(egraph, roots, nvariants, DynamicCostModel)?
        };
        let variants = extracted
            .variants
            .into_iter()
            .next()
            .expect("one root was requested");
        variants
            .into_iter()
            .map(|variant| extracted.termdag.term_to_expr(&variant.term, span!()))
            .collect()
    };

    if requested_exprs.is_empty() != paired_exprs.is_empty() {
        return Err(Error::ExtractError(
            "only one extractor returned variants for the requested root".to_owned(),
        ));
    }

    for extracted_expr in requested_exprs.iter().chain(&paired_exprs) {
        let (extracted_sort, extracted_value) = egraph.eval_expr(extracted_expr)?;
        if root_sort.name() != extracted_sort.name() || root_value != extracted_value {
            return Err(Error::ExtractError(format!(
                "extractor returned a term unequal to the requested root: root {:?}, extracted {extracted_expr:?}",
                extract.root
            )));
        }
    }

    Ok(())
}

fn extracted_exprs(outputs: &[CommandOutput]) -> Result<Vec<Expr>, Error> {
    let mut saw_extract = false;
    let mut extracted = Vec::new();
    for output in outputs {
        match output {
            CommandOutput::ExtractBest(termdag, _cost, term) => {
                extracted.push(termdag.term_to_expr(term, span!()));
                saw_extract = true;
            }
            CommandOutput::ExtractVariants(termdag, terms) => {
                for term in terms {
                    extracted.push(termdag.term_to_expr(term, span!()));
                }
                saw_extract = true;
            }
            _ => {}
        }
    }
    if saw_extract {
        Ok(extracted)
    } else {
        Err(Error::ExtractError(
            "extract command should produce an extract output".to_owned(),
        ))
    }
}

struct ProtoRun {
    path: PathBuf,
    include_base: PathBuf,
    core: bool,
    roundtrip: bool,
    mode: pb::ExecutionMode,
}

impl ProtoRun {
    fn run(&self) -> Result<(), String> {
        let mut program = std::fs::read_to_string(&self.path).map_err(|error| error.to_string())?;
        let filename = Some(self.path.to_string_lossy().into_owned());
        if self.roundtrip {
            let mut source = if self.core {
                Source::new_core(filename.clone(), &program)
            } else {
                Source::new(filename.clone(), &program)
            }
            .and_then(|source| source.with_include_base(&self.include_base))
            .map_err(|error| format!("source admission before resugaring: {error}"))?;
            let mut renderer = if self.core {
                Renderer::core()
            } else {
                Renderer::default()
            };
            program.clear();
            while let Some(phase) = source.next_submission() {
                let phase =
                    phase.map_err(|error| format!("source export before resugaring: {error}"))?;
                program.push_str(
                    &renderer
                        .render_submission(&phase)
                        .map_err(|error| format!("source rendering: {error}"))?,
                );
            }
        }
        let mut native = if self.core {
            EGraph::default()
        } else {
            new_experimental_egraph()
        };
        native = match self.mode {
            pb::ExecutionMode::Normal => native,
            pb::ExecutionMode::TermEncoding => native.with_term_encoding_enabled(),
            pb::ExecutionMode::Proofs => native.with_proofs_enabled(),
            pb::ExecutionMode::ProofTesting => native.with_proofs_enabled().with_proof_testing(),
        };
        let negative = self
            .path
            .components()
            .any(|part| part.as_os_str() == "fail-typecheck");
        let parsed = native.parse_program(filename.clone(), &program);
        let source = if self.core {
            Source::new_core(filename, &program)
        } else {
            Source::new(filename, &program)
        }
        .and_then(|source| source.with_include_base(&self.include_base));
        let (mut commands, mut source) = match (parsed, source) {
            (Ok(commands), Ok(source)) => (
                commands
                    .into_iter()
                    .map(|command| (command, 0))
                    .collect::<VecDeque<_>>(),
                source,
            ),
            (Err(expected), Err(actual))
                if negative && expected.to_string() == actual.to_string() =>
            {
                return Ok(());
            }
            (Err(expected), _) => return Err(format!("native parse failure: {expected}")),
            (_, Err(actual)) => return Err(format!("source admission: {actual}")),
        };
        let mut engine = Engine::default();
        let request = pb::CreateEGraphRequest {
            sorts: vec![pb::Sort {
                kind: Some(pb::sort::Kind::Family(pb::HostSort {
                    name: "i64".into(),
                    args: vec![],
                })),
                ..Default::default()
            }],
            options: Some(pb::EGraphOptions {
                cost_sort: Some(0),
                execution_mode: self.mode.into(),
            }),
            ..Default::default()
        };
        let response = engine
            .create(&request.encode_to_vec())
            .map_err(|error| format!("adapter creation: {error}"))?;
        let mut egraph_id = pb::CreateEGraphResponse::decode(response.as_slice())
            .map_err(|error| error.to_string())?
            .egraph_id;
        let mut saved = vec![];
        let mut index = 0;
        while let Some(phase) = source.next_submission() {
            let command = next_native_command(&mut native, &mut commands, &self.include_base)
                .ok_or("source emitted more phases than authored commands")?;
            let extract = command.as_ref().ok().and_then(extract_command_parts);
            let mut validation = extract.as_ref().map(|_| native.clone());
            let expected = command.and_then(|command| {
                native
                    .run_program(vec![command])
                    .map_err(|error| error.to_string())
            });
            let actual = phase
                .map_err(|error| format!("source export: {error}"))
                .and_then(|phase| {
                    let phase = match phase {
                        Submission::Program(program) => program,
                        Submission::Push(count) => {
                            for _ in 0..count {
                                let bytes = engine
                                    .clone_egraph(
                                        &pb::CloneEGraphRequest { egraph_id }.encode_to_vec(),
                                    )
                                    .map_err(|error| format!("scope clone: {error}"))?;
                                saved.push(egraph_id);
                                egraph_id = pb::CloneEGraphResponse::decode(bytes.as_slice())
                                    .map_err(|error| error.to_string())?
                                    .egraph_id;
                            }
                            return Ok(pb::RunProgramResponse::default());
                        }
                        Submission::Pop { count, span } => {
                            for _ in 0..count {
                                let saved_id = saved
                                    .pop()
                                    .ok_or_else(|| Error::Pop(span.clone()).to_string())?;
                                let bytes = engine
                                    .return_to(
                                        &pb::ReturnToEGraphRequest {
                                            active_id: egraph_id,
                                            saved_id,
                                        }
                                        .encode_to_vec(),
                                    )
                                    .map_err(|error| format!("scope return: {error}"))?;
                                pb::ReturnToEGraphResponse::decode(bytes.as_slice())
                                    .map_err(|error| error.to_string())?;
                                egraph_id = saved_id;
                            }
                            return Ok(pb::RunProgramResponse::default());
                        }
                    };
                    let request = pb::RunProgramRequest {
                        egraph_id,
                        program: Some(phase),
                        profile: true,
                        include_run_reports: false,
                    };
                    let bytes = engine
                        .run(&request.encode_to_vec())
                        .map_err(|error| format!("byte transport: {error}"))?;
                    let response = pb::RunProgramResponse::decode(bytes.as_slice())
                        .map_err(|error| format!("response decode: {error}"))?;
                    if let Some(error) = &response.error {
                        Err(format!(
                            "adapter {:?}: {}",
                            pb::ErrorCode::try_from(error.code),
                            error.message
                        ))
                    } else {
                        Ok(response)
                    }
                });
            match (expected, actual) {
                (Ok(_), Ok(response)) => {
                    if let Some(extract) = extract {
                        let mut expressions = vec![];
                        let mut saw_extract = false;
                        for output in &response.outputs {
                            if let Some(pb::command_output::Kind::Extraction(result)) = &output.kind
                            {
                                saw_extract = true;
                                for root in &result.roots {
                                    for term in &root.variants {
                                        expressions
                                            .push(frozen_expression(&response, term.term, 0)?);
                                    }
                                }
                            }
                        }
                        if !saw_extract {
                            return Err(format!(
                                "command {index}: protobuf extraction output missing"
                            ));
                        }
                        validate_extract_outputs(
                            validation.as_mut().unwrap(),
                            &extract,
                            expressions,
                        )
                        .map_err(|error| {
                            format!("command {index}: decoded extraction validation: {error}")
                        })?;
                    }
                }
                (Err(expected), Err(actual)) if negative => {
                    if actual.contains(&expected.to_string()) {
                        return Ok(());
                    }
                    return Err(format!(
                        "command {index}: negative error boundary differs\nnative: {expected}\nprotobuf: {actual}"
                    ));
                }
                (Ok(_), Err(actual))
                    if self.path.ends_with("relation-query-allowed.egg")
                        && actual.contains("relation predicates cannot be used as values") =>
                {
                    return Ok(());
                }
                (Err(expected), _) => {
                    return Err(format!(
                        "command {index}: native baseline failed: {expected}"
                    ));
                }
                (_, Err(actual)) => return Err(format!("command {index}: {actual}")),
            }
            index += 1;
        }
        if next_native_command(&mut native, &mut commands, &self.include_base).is_some() {
            return Err("source ended before the authored commands".into());
        }
        if negative {
            return Err("negative corpus case unexpectedly succeeded".into());
        }
        if self.path.ends_with("relation-query-allowed.egg") {
            return Err("legacy relation-value equality unexpectedly succeeded".into());
        }
        Ok(())
    }
}

// Independently expand native Include leaves using the real parser and an
// explicit dialect base. This keeps the same leaf/error oracle boundary as
// Source without changing the process cwd or executing a replacement program.
fn next_native_command(
    graph: &mut EGraph,
    commands: &mut VecDeque<(Command, usize)>,
    include_base: &std::path::Path,
) -> Option<Result<Command, String>> {
    loop {
        let (command, depth) = commands.pop_front()?;
        let Command::Include(span, file) = command else {
            return Some(Ok(command));
        };
        if depth >= 256 {
            return Some(Err("native oracle include nesting exceeds 256".into()));
        }
        let contents = match std::fs::read_to_string(include_base.join(&file)) {
            Ok(contents) => contents,
            Err(error) => return Some(Err(Error::IoError(file.into(), error, span).to_string())),
        };
        let included = match graph.parse_program(Some(file), &contents) {
            Ok(included) => included,
            Err(error) => return Some(Err(error.to_string())),
        };
        for command in included.into_iter().rev() {
            commands.push_front((command, depth + 1));
        }
    }
}

// Decode finite extraction data for the existing native equality/paired-extractor
// assertions. The byte engine remains the treatment; native evaluation is only
// the independent oracle used to check the returned terms.
fn frozen_expression(
    response: &pb::RunProgramResponse,
    index: u32,
    depth: usize,
) -> Result<Expr, String> {
    use egglog::ast::Literal;
    use pb::primitive_value::Value as V;
    if depth > 256 {
        return Err("decoded extraction exceeds depth 256".into());
    }
    let node = response
        .nodes
        .get(index as usize)
        .ok_or("extracted node index out of bounds")?;
    let call = |name: &str, children: &[u32]| -> Result<Expr, String> {
        Ok(Expr::Call(
            span!(),
            name.into(),
            children
                .iter()
                .map(|child| frozen_expression(response, *child, depth + 1))
                .collect::<Result<_, _>>()?,
        ))
    };
    match node.kind.as_ref() {
        Some(pb::node::Kind::Call(value)) => call(&value.func, &value.args),
        Some(pb::node::Kind::PrimitiveValue(value)) => match value.value.as_ref() {
            Some(V::I64(value)) => Ok(Expr::Lit(span!(), Literal::Int(*value))),
            Some(V::F64Bits(value)) => Ok(Expr::Lit(
                span!(),
                Literal::Float(f64::from_bits(*value).into()),
            )),
            Some(V::String(value)) => Ok(Expr::Lit(span!(), Literal::String(value.clone()))),
            Some(V::Bool(value)) => Ok(Expr::Lit(span!(), Literal::Bool(*value))),
            Some(V::Unit(_)) => Ok(Expr::Lit(span!(), Literal::Unit)),
            Some(V::Vec(list)) => call("vec-of", &list.items),
            Some(V::Set(list)) => call("set-of", &list.items),
            Some(V::Multiset(list)) => call("multiset-of", &list.items),
            Some(V::Pair(pair)) => call(
                "pair",
                &[
                    pair.first.ok_or("missing Pair first")?,
                    pair.second.ok_or("missing Pair second")?,
                ],
            ),
            Some(V::Maybe(maybe)) => call(
                if maybe.value.is_some() {
                    "maybe-some"
                } else {
                    "maybe-none"
                },
                &maybe.value.into_iter().collect::<Vec<_>>(),
            ),
            Some(V::Map(map)) => {
                let mut result = Expr::Call(span!(), "map-empty".into(), vec![]);
                for entry in &map.entries {
                    result = Expr::Call(
                        span!(),
                        "map-insert".into(),
                        vec![
                            result,
                            frozen_expression(
                                response,
                                entry.key.ok_or("missing Map key")?,
                                depth + 1,
                            )?,
                            frozen_expression(
                                response,
                                entry.value.ok_or("missing Map value")?,
                                depth + 1,
                            )?,
                        ],
                    );
                }
                Ok(result)
            }
            other => Err(format!(
                "extraction oracle decoder does not yet support {other:?}"
            )),
        },
        other => Err(format!("extraction returned a non-value node: {other:?}")),
    }
}

fn protobuf_trials(root: &std::path::Path, core: bool) -> Vec<Trial> {
    let mut trials = vec![];
    for entry in glob::glob(&format!("{}/**/*.egg", root.display())).unwrap() {
        let path = entry.unwrap();
        if path
            .parent()
            .is_some_and(|parent| parent.ends_with("header"))
            || path.ends_with("gemma.egg")
            || path.ends_with("gemma4_moe.egg")
        {
            continue;
        }
        let negative = path
            .components()
            .any(|part| part.as_os_str() == "fail-typecheck");
        let requires_proofs = core
            && path
                .parent()
                .is_some_and(|parent| parent.ends_with("proofs"));
        for roundtrip in [false, true] {
            if roundtrip && (negative || path.ends_with("relation-query-allowed.egg")) {
                continue;
            }
            let run = ProtoRun {
                path: path.clone(),
                include_base: root.join(".."),
                core,
                roundtrip,
                mode: if requires_proofs {
                    pb::ExecutionMode::Proofs
                } else {
                    pb::ExecutionMode::Normal
                },
            };
            let relative = path
                .strip_prefix(root)
                .unwrap()
                .with_extension("")
                .to_string_lossy()
                .into_owned();
            let name = format!(
                "protobuf/{}/{relative}/{}{}{}",
                if core { "core" } else { "experimental" },
                if requires_proofs { "proofs" } else { "normal" },
                if roundtrip { "/resugar" } else { "" },
                if path.ends_with("relation-query-allowed.egg") {
                    "/rejects_relation_values"
                } else {
                    ""
                }
            );
            trials.push(Trial::test(name, move || run.run().map_err(Into::into)));
        }
    }
    trials
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
    let mut tests = generate_tests("tests/**/*.egg");
    tests.extend(protobuf_trials(std::path::Path::new("tests"), false));
    if let Some(root) = std::env::var_os("EGGLOG_PROTO_CORE_TESTS") {
        tests.extend(protobuf_trials(std::path::Path::new(&root), true));
    }
    libtest_mimic::run(&args, tests).exit();
}
