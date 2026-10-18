use std::collections::{HashMap, HashSet, VecDeque};
use std::path::PathBuf;

use egglog::{
    ArcSort, CommandOutput, Error, ResolvedExpr,
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
            ExtractedExpressions::Native(extracted_exprs(&command_outputs)?),
        )?;
        outputs.extend(command_outputs);
    }

    Ok(outputs)
}

struct ExtractCheck {
    root: Expr,
    additional_roots: Vec<Expr>,
    variants: Option<Expr>,
    count_first: bool,
    use_greedy_dag: bool,
}

fn extract_command_parts(command: &Command) -> Option<ExtractCheck> {
    match command {
        Command::Extract(_, root, variants) => Some(ExtractCheck {
            root: root.clone(),
            additional_roots: vec![],
            variants: Some(variants.clone()),
            count_first: false,
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
                    additional_roots: vec![],
                    variants: None,
                    count_first: false,
                    use_greedy_dag,
                }),
                [root, variants] => Some(ExtractCheck {
                    root: root.clone(),
                    additional_roots: vec![],
                    variants: Some(variants.clone()),
                    count_first: false,
                    use_greedy_dag,
                }),
                _ => None,
            }
        }
        Command::UserDefined(_, name, args) if name == "multi-extract" => {
            let parsed = egglog_experimental::parse_multi_extract_args(args).ok()?;
            Some(ExtractCheck {
                root: parsed.roots[0].clone(),
                additional_roots: parsed.roots[1..].to_vec(),
                variants: Some(parsed.variants.clone()),
                count_first: true,
                use_greedy_dag: parsed.greedy,
            })
        }
        _ => None,
    }
}

enum ExtractedExpressions<'a> {
    Native(Vec<Vec<Expr>>),
    Frozen(&'a pb::RunProgramResponse, Vec<u32>),
    FrozenGroups(&'a pb::RunProgramResponse, Vec<Vec<u32>>),
}

fn validate_extract_outputs(
    egraph: &mut EGraph,
    extract: &ExtractCheck,
    requested: ExtractedExpressions<'_>,
) -> Result<(), Error> {
    let count = |egraph: &mut EGraph| -> Result<usize, Error> {
        let Some(variants) = &extract.variants else {
            return Ok(0);
        };
        let (sort, value) = egraph.eval_expr(variants)?;
        if sort.name() != "i64" {
            return Err(Error::ExtractError(
                "extract variant count must have i64 sort".into(),
            ));
        }
        let count = usize::try_from(egraph.value_to_base::<i64>(value))
            .map_err(|_| Error::ExtractError("extract variant count must be nonnegative".into()))?;
        if extract.count_first && count == 0 {
            return Err(Error::ExtractError(
                "multi-extract requires a positive number of variants".into(),
            ));
        }
        Ok(count)
    };
    // Multi-extract evaluates its count before all roots. Single extract's
    // existing root-before-count order is different and remains unchanged.
    let nvariants = extract.count_first.then(|| count(egraph)).transpose()?;
    let roots = std::iter::once(&extract.root)
        .chain(&extract.additional_roots)
        .map(|root| egraph.eval_expr(root))
        .collect::<Result<Vec<_>, _>>()?;
    let nvariants = match nvariants {
        Some(count) => count,
        None => count(egraph)?,
    };
    // Invoke the paired extractor once, after every stateful root was evaluated.
    let paired_exprs = if nvariants == 0 {
        let extracted = if extract.use_greedy_dag {
            egraph.extract_best_with_cost_model(
                roots.clone(),
                TreeCostModelFromDag(DynamicCostModel),
            )?
        } else {
            extract_best_greedy_dag(egraph, roots.clone(), DynamicCostModel)?
        };
        extracted
            .terms
            .into_iter()
            .map(|root| {
                let root = root.ok_or_else(|| {
                    Error::ExtractError("paired extractor returned no term".into())
                })?;
                Ok(vec![extracted.termdag.term_to_expr(&root.term, span!())])
            })
            .collect::<Result<Vec<_>, Error>>()?
    } else {
        let extracted = if extract.use_greedy_dag {
            egraph.extract_variants_with_cost_model(
                roots.clone(),
                nvariants,
                TreeCostModelFromDag(DynamicCostModel),
            )?
        } else {
            extract_variants_greedy_dag(egraph, roots.clone(), nvariants, DynamicCostModel)?
        };
        extracted
            .variants
            .into_iter()
            .map(|variants| {
                variants
                    .into_iter()
                    .map(|variant| extracted.termdag.term_to_expr(&variant.term, span!()))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    };
    let requested = match requested {
        ExtractedExpressions::Frozen(response, terms) => {
            ExtractedExpressions::FrozenGroups(response, vec![terms])
        }
        other => other,
    };
    let groups = match &requested {
        ExtractedExpressions::Native(groups) => groups.len(),
        ExtractedExpressions::FrozenGroups(_, groups) => groups.len(),
        ExtractedExpressions::Frozen(..) => unreachable!(),
    };
    if groups != roots.len() || paired_exprs.len() != roots.len() {
        return Err(Error::ExtractError(
            "extraction oracle root group count differs".into(),
        ));
    }
    let portable = matches!(&requested, ExtractedExpressions::FrozenGroups(..));
    let mut decoder = if let ExtractedExpressions::FrozenGroups(response, _) = &requested {
        let mut callables = HashMap::new();
        for (physical, function) in egraph.functions_iter() {
            if let Some(egglog::ast::TableName::Public(logical)) = &function.func_type().table_name
                && callables
                    .insert(logical.clone(), physical.clone())
                    .is_some()
            {
                return Err(Error::ExtractError(format!(
                    "extraction oracle ambiguous public callable {logical:?}"
                )));
            }
        }
        // One allowance covers all roots and variants, including repeated DAG
        // edges and synthesized reconstruction nodes.
        Some(FrozenDecoder {
            response,
            callables,
            remaining: 65_536,
        })
    } else {
        None
    };
    for (index, ((root_sort, root_value), paired_exprs)) in
        roots.into_iter().zip(paired_exprs).enumerate()
    {
        let mut contextual_functions = false;
        let mut requested_values = vec![];
        match &requested {
            ExtractedExpressions::Native(expressions) => {
                if expressions[index].len() > nvariants.max(1) {
                    return Err(Error::ExtractError(
                        "extraction oracle variant count exceeds request".into(),
                    ));
                }
                for expr in &expressions[index] {
                    let (sort, value) = egraph.eval_expr(expr)?;
                    requested_values.push((expr.clone(), sort, value));
                }
            }
            ExtractedExpressions::FrozenGroups(response, terms) => {
                if terms[index].len() > nvariants.max(1) {
                    return Err(Error::ExtractError(
                        "extraction oracle variant count exceeds request".into(),
                    ));
                }
                let decoder = decoder.as_mut().unwrap();
                for term in &terms[index] {
                    let mut annotations = vec![];
                    let mut expr = decoder
                        .expression(*term, 0, &mut annotations)
                        .map_err(Error::ExtractError)?;
                    let has_partial_call = annotations.iter().flatten().any(|index| {
                        matches!(
                            response.nodes[*index as usize].kind.as_ref(),
                            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                                value: Some(pb::primitive_value::Value::PartialCall(_)),
                            }))
                        )
                    });
                    let (sort, value) = if has_partial_call {
                        contextual_functions = true;
                        let resolved = egraph
                            .typecheck_expr_with_bindings_and_output(
                                &expr,
                                &[],
                                root_sort.clone(),
                                egglog::Context::Full,
                            )
                            .map_err(|error| {
                                Error::ExtractError(format!(
                                    "contextual function-value extraction oracle: {error}"
                                ))
                            })?;
                        let mut annotations = annotations.into_iter();
                        specialize_frozen_expression(
                            egraph,
                            response,
                            &mut expr,
                            &resolved,
                            &mut annotations,
                        )
                        .map_err(Error::ExtractError)?;
                        if annotations.next().is_some() {
                            return Err(Error::ExtractError(
                            "extraction oracle annotation traversal differs from native expression"
                                .into(),
                        ));
                        }
                        egraph.eval_expr_with_output(&expr, root_sort.clone())?
                    } else {
                        egraph.eval_expr(&expr)?
                    };
                    requested_values.push((expr, sort, value));
                }
            }
            ExtractedExpressions::Frozen(..) => unreachable!(),
        }

        if requested_values.is_empty() != paired_exprs.is_empty() {
            return Err(Error::ExtractError(
                "only one extractor returned variants for the requested root".to_owned(),
            ));
        }

        for expr in paired_exprs {
            let (sort, value) = if contextual_functions {
                egraph.eval_expr_with_output(&expr, root_sort.clone())?
            } else {
                egraph.eval_expr(&expr)?
            };
            requested_values.push((expr, sort, value));
        }
        let expected_shape = portable
            .then(|| {
                egraph
                    .authoring_type_info()
                    .native_sort_pattern(&root_sort)
                    .map_err(Error::ExtractError)
            })
            .transpose()?;
        for (extracted_expr, extracted_sort, extracted_value) in requested_values {
            let same_sort = if let Some(expected_shape) = &expected_shape {
                *expected_shape
                    == egraph
                        .authoring_type_info()
                        .native_sort_pattern(&extracted_sort)
                        .map_err(Error::ExtractError)?
            } else {
                root_sort.name() == extracted_sort.name()
            };
            if !same_sort || root_value != extracted_value {
                return Err(Error::ExtractError(format!(
                    "extractor returned a term unequal to the requested root: root {:?}, extracted {extracted_expr:?}",
                    std::iter::once(&extract.root)
                        .chain(&extract.additional_roots)
                        .nth(index)
                        .unwrap()
                )));
            }
        }
    }

    Ok(())
}

fn extracted_exprs(outputs: &[CommandOutput]) -> Result<Vec<Vec<Expr>>, Error> {
    let mut saw_extract = false;
    let mut extracted = Vec::new();
    for output in outputs {
        match output {
            CommandOutput::ExtractBest(termdag, _cost, term) => {
                extracted.push(vec![termdag.term_to_expr(term, span!())]);
                saw_extract = true;
            }
            CommandOutput::ExtractVariants(termdag, terms) => {
                extracted.push(
                    terms
                        .iter()
                        .map(|term| termdag.term_to_expr(term, span!()))
                        .collect(),
                );
                saw_extract = true;
            }
            CommandOutput::UserDefined(output) => {
                if let Some(output) = output
                    .as_ref()
                    .as_any()
                    .downcast_ref::<egglog_experimental::MultiExtractOutput>()
                {
                    extracted.extend(output.terms.iter().map(|terms| {
                        terms
                            .iter()
                            .map(|term| output.termdag.term_to_expr(term, span!()))
                            .collect()
                    }));
                    saw_extract = true;
                }
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
        let grounding = self.core
            && self.mode == pb::ExecutionMode::Normal
            && self
                .path
                .parent()
                .is_some_and(|p| p.ends_with("fail-typecheck"))
            && matches!(
                self.path.file_name().and_then(|name| name.to_str()),
                Some(
                    "ungrounded-0.egg"
                        | "ungrounded-1.egg"
                        | "ungrounded-2.egg"
                        | "ungrounded-3.egg"
                        | "ungrounded-4.egg"
                )
            );
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
                if negative && !grounding && expected.to_string() == actual.to_string() =>
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
                ..Default::default()
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
            let rule_kind = command.as_ref().ok().and_then(|command| match command {
                Command::Rule { .. } => Some(false),
                Command::BiRewrite(..) => Some(true),
                _ => None,
            });
            let mut native_ungrounded = false;
            let expected = command.and_then(|command| {
                native.run_program(vec![command]).map_err(|error| {
                    native_ungrounded =
                        matches!(&error, Error::TypeError(egglog::TypeError::Ungrounded(..)));
                    error.to_string()
                })
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
                    let emits_rule = matches!(
                        (rule_kind, phase.rules.as_slice()),
                        (
                            Some(false),
                            [pb::RuleDecl {
                                kind: Some(pb::rule_decl::Kind::Rule(_)),
                                ..
                            }]
                        ) | (
                            Some(true),
                            [pb::RuleDecl {
                                kind: Some(pb::rule_decl::Kind::Birewrite(_)),
                                ..
                            }]
                        )
                    );
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
                    if grounding && native_ungrounded {
                        if !emits_rule
                            || !response.outputs.is_empty()
                            || !response
                                .ruleset_publication
                                .as_ref()
                                .is_some_and(|p| p.names.is_empty())
                            || !response.error.as_ref().is_some_and(|e| {
                                e.code == i32::from(pb::ErrorCode::InvalidProgram)
                                    && e.location.is_none()
                            })
                        {
                            return Err(format!(
                                "grounding rejection boundary differs: {response:?}"
                            ));
                        }
                        return Ok(response);
                    }
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
                (Err(_), Ok(response))
                    if grounding && native_ungrounded && response.error.is_some() =>
                {
                    return Ok(());
                }
                (Ok(_), Ok(response)) => {
                    if let Some(extract) = extract {
                        let mut terms = vec![];
                        let mut saw_extract = false;
                        for output in &response.outputs {
                            if let Some(pb::command_output::Kind::Extraction(result)) = &output.kind
                            {
                                if saw_extract {
                                    return Err(format!(
                                        "command {index}: multiple protobuf extraction outputs"
                                    ));
                                }
                                saw_extract = true;
                                for root in &result.roots {
                                    terms
                                        .push(root.variants.iter().map(|term| term.term).collect());
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
                            ExtractedExpressions::FrozenGroups(&response, terms),
                        )
                        .map_err(|error| {
                            format!("command {index}: decoded extraction validation: {error}")
                        })?;
                    }
                }
                (Err(expected), Err(actual)) if negative => {
                    if !grounding && actual.contains(&expected.to_string()) {
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
struct FrozenDecoder<'a> {
    response: &'a pb::RunProgramResponse,
    callables: HashMap<String, String>,
    remaining: usize,
}

impl FrozenDecoder<'_> {
    // Record every actual Expr node in postorder. Generated reconstruction
    // nodes have no wire annotation, but consume the same expansion allowance.
    fn generated(
        &mut self,
        expr: Expr,
        depth: usize,
        annotations: &mut Vec<Option<u32>>,
    ) -> Result<Expr, String> {
        if depth > 256 {
            return Err("extraction oracle reconstructed expression exceeds depth 256".into());
        }
        self.remaining = self
            .remaining
            .checked_sub(1)
            .ok_or("extraction oracle expansion exceeds 65536 Expr nodes across variants")?;
        annotations.push(None);
        Ok(expr)
    }

    fn call(
        &mut self,
        name: &str,
        children: &[u32],
        depth: usize,
        annotations: &mut Vec<Option<u32>>,
    ) -> Result<Expr, String> {
        let children = children
            .iter()
            .map(|child| self.expression(*child, depth + 1, annotations))
            .collect::<Result<_, _>>()?;
        self.generated(
            Expr::Call(span!(), name.into(), children),
            depth,
            annotations,
        )
    }

    fn expression(
        &mut self,
        index: u32,
        depth: usize,
        annotations: &mut Vec<Option<u32>>,
    ) -> Result<Expr, String> {
        use egglog::ast::Literal;
        use pb::primitive_value::Value as V;
        if depth > 256 {
            return Err("extraction oracle decoded expression exceeds depth 256".into());
        }
        let response = self.response;
        let node = response
            .nodes
            .get(index as usize)
            .ok_or("extracted node index out of bounds")?;
        let result = match node.kind.as_ref() {
            Some(pb::node::Kind::Call(value)) => {
                // Public table provenance is not a native expression alias.
                // Only returned Call references cross that namespace boundary;
                // generated builtin calls and ordinary String data stay native.
                let name = self
                    .callables
                    .get(&value.func)
                    .unwrap_or(&value.func)
                    .clone();
                self.call(&name, &value.args, depth, annotations)
            }
            Some(pb::node::Kind::PrimitiveValue(value)) => match value.value.as_ref() {
                Some(V::I64(value)) => {
                    self.generated(Expr::Lit(span!(), Literal::Int(*value)), depth, annotations)
                }
                Some(V::F64Bits(value)) => self.generated(
                    Expr::Lit(span!(), Literal::Float(f64::from_bits(*value).into())),
                    depth,
                    annotations,
                ),
                Some(V::String(value)) => self.generated(
                    Expr::Lit(span!(), Literal::String(value.clone())),
                    depth,
                    annotations,
                ),
                Some(V::Bool(value)) => self.generated(
                    Expr::Lit(span!(), Literal::Bool(*value)),
                    depth,
                    annotations,
                ),
                Some(V::Unit(_)) => {
                    self.generated(Expr::Lit(span!(), Literal::Unit), depth, annotations)
                }
                // Reconstruct exact values from the structured payload using native
                // builtin identities, without printing or parsing an expression.
                Some(exact @ (V::BigInt(_) | V::BigRat(_) | V::Rational(_))) => {
                    let expected = match exact {
                        V::BigInt(_) => "BigInt",
                        V::BigRat(_) => "BigRat",
                        _ => "Rational",
                    };
                    if !matches!(
                        self.response
                            .sorts
                            .get(node.sort_id as usize)
                            .and_then(|sort| sort.kind.as_ref()),
                        Some(pb::sort::Kind::Family(family))
                            if family.name == expected && family.args.is_empty()
                    ) {
                        return Err("extraction oracle exact numeric payload/sort mismatch".into());
                    }
                    match exact {
                        V::BigInt(value) => {
                            let text = self.generated(
                                Expr::Lit(span!(), Literal::String(value.clone())),
                                depth + 1,
                                annotations,
                            )?;
                            self.generated(
                                Expr::Call(
                                    span!(),
                                    "egglog.core.bigint.from_string".into(),
                                    vec![text],
                                ),
                                depth,
                                annotations,
                            )
                        }
                        V::BigRat(value) => {
                            let mut parts = vec![];
                            for part in [&value.numerator, &value.denominator] {
                                let text = self.generated(
                                    Expr::Lit(span!(), Literal::String(part.clone())),
                                    depth + 2,
                                    annotations,
                                )?;
                                parts.push(self.generated(
                                    Expr::Call(
                                        span!(),
                                        "egglog.core.bigint.from_string".into(),
                                        vec![text],
                                    ),
                                    depth + 1,
                                    annotations,
                                )?);
                            }
                            self.generated(
                                Expr::Call(span!(), "egglog.core.bigrat.make".into(), parts),
                                depth,
                                annotations,
                            )
                        }
                        V::Rational(value) => {
                            let numerator = self.generated(
                                Expr::Lit(span!(), Literal::Int(value.numerator)),
                                depth + 1,
                                annotations,
                            )?;
                            let denominator = self.generated(
                                Expr::Lit(span!(), Literal::Int(value.denominator)),
                                depth + 1,
                                annotations,
                            )?;
                            self.generated(
                                Expr::Call(
                                    span!(),
                                    "egglog.experimental.rational.make".into(),
                                    vec![numerator, denominator],
                                ),
                                depth,
                                annotations,
                            )
                        }
                        _ => unreachable!("matched exact numeric value"),
                    }
                }
                Some(V::PartialCall(value)) => {
                    let target = self.generated(
                        Expr::Lit(span!(), Literal::String(value.func.clone())),
                        depth + 1,
                        annotations,
                    )?;
                    let mut arguments = vec![target];
                    for child in &value.args {
                        arguments.push(self.expression(*child, depth + 1, annotations)?);
                    }
                    self.generated(
                        Expr::Call(span!(), "unstable-fn".into(), arguments),
                        depth,
                        annotations,
                    )
                }
                Some(V::Vec(list)) => self.call("vec-of", &list.items, depth, annotations),
                Some(V::Set(list)) => self.call("set-of", &list.items, depth, annotations),
                Some(V::Multiset(list)) => {
                    self.call("multiset-of", &list.items, depth, annotations)
                }
                Some(V::Pair(pair)) => self.call(
                    "pair",
                    &[
                        pair.first.ok_or("missing Pair first")?,
                        pair.second.ok_or("missing Pair second")?,
                    ],
                    depth,
                    annotations,
                ),
                Some(V::Maybe(maybe)) => self.call(
                    if maybe.value.is_some() {
                        "maybe-some"
                    } else {
                        "maybe-none"
                    },
                    &maybe.value.into_iter().collect::<Vec<_>>(),
                    depth,
                    annotations,
                ),
                Some(V::Map(map)) => {
                    // The left-associated reconstruction adds one AST level per
                    // entry even when the wire map itself is shallow.
                    let empty_depth = depth
                        .checked_add(map.entries.len())
                        .ok_or("extraction oracle Map reconstruction depth overflow")?;
                    let mut result = self.generated(
                        Expr::Call(span!(), "map-empty".into(), vec![]),
                        empty_depth,
                        annotations,
                    )?;
                    for (position, entry) in map.entries.iter().enumerate() {
                        let child_depth = empty_depth - position;
                        let key = self.expression(
                            entry.key.ok_or("missing Map key")?,
                            child_depth,
                            annotations,
                        )?;
                        let value = self.expression(
                            entry.value.ok_or("missing Map value")?,
                            child_depth,
                            annotations,
                        )?;
                        result = self.generated(
                            Expr::Call(span!(), "map-insert".into(), vec![result, key, value]),
                            child_depth - 1,
                            annotations,
                        )?;
                    }
                    Ok(result)
                }
                other => Err(format!(
                    "extraction oracle decoder does not yet support {other:?}"
                )),
            },
            other => Err(format!("extraction returned a non-value node: {other:?}")),
        }?;
        *annotations
            .last_mut()
            .ok_or("extraction oracle missing reconstructed node")? = Some(index);
        Ok(result)
    }
}

// Check erased annotations against the native solver's actual choices. Only
// function constructor spelling is changed, using that exact contextual sort;
// target strings and capture expressions remain the returned wire data.
fn specialize_frozen_expression(
    egraph: &EGraph,
    response: &pb::RunProgramResponse,
    expr: &mut Expr,
    resolved: &ResolvedExpr,
    annotations: &mut impl Iterator<Item = Option<u32>>,
) -> Result<(), String> {
    match (&mut *expr, resolved) {
        (Expr::Call(_, _, children), ResolvedExpr::Call(_, _, typed_children))
            if children.len() == typed_children.len() =>
        {
            for (child, typed) in children.iter_mut().zip(typed_children) {
                specialize_frozen_expression(egraph, response, child, typed, annotations)?;
            }
        }
        (Expr::Lit(..), ResolvedExpr::Lit(..)) => (),
        _ => return Err("extraction oracle native resolution changed expression structure".into()),
    }
    let annotation = annotations
        .next()
        .ok_or("extraction oracle annotation traversal ended early")?;
    let Some(index) = annotation else {
        return Ok(());
    };
    let node = &response.nodes[index as usize];
    let sort: ArcSort = match resolved {
        ResolvedExpr::Lit(_, literal) => egglog::sort::literal_sort(literal),
        ResolvedExpr::Call(_, call, _) => call.output().clone(),
        ResolvedExpr::Var(..) => return Err("extraction oracle resolved a non-closed value".into()),
    };
    let mut native_sorts = vec![];
    let native = egraph.export_sort(&sort, &mut native_sorts)?;
    if !same_frozen_sort(
        &response.sorts,
        node.sort_id,
        &native_sorts,
        native,
        0,
        &mut HashSet::new(),
    )? {
        return Err(format!(
            "extraction oracle node {index} annotation differs from contextual native sort {}",
            sort.name(),
        ));
    }
    if matches!(
        node.kind.as_ref(),
        Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::PartialCall(_)),
        }))
    ) {
        let function = sort
            .as_arc_any()
            .downcast::<egglog::sort::FunctionSort>()
            .map_err(
                |_| "extraction oracle PartialCall requires contextual native function sort",
            )?;
        let Expr::Call(_, name, _) = expr else {
            return Err("extraction oracle PartialCall reconstruction is not a call".into());
        };
        *name = egglog::sort::FunctionSort::constructor_alias(function.name());
    }
    Ok(())
}

// Sort names are presentation metadata for applied families and functions.
// Equality sorts retain nominal identity. Memoized pairs bound DAG comparison
// without choosing any native registration from structural resemblance.
fn same_frozen_sort(
    wire: &[pb::Sort],
    wire_index: u32,
    native: &[pb::Sort],
    native_index: u32,
    depth: usize,
    compared: &mut HashSet<(u32, u32)>,
) -> Result<bool, String> {
    if depth > 256 {
        return Err("extraction oracle sort comparison exceeds depth 256".into());
    }
    if !compared.insert((wire_index, native_index)) {
        return Ok(true);
    }
    if compared.len() > 65_536 {
        return Err("extraction oracle sort comparison exceeds 65536 pairs".into());
    }
    let wire_kind = wire
        .get(wire_index as usize)
        .and_then(|sort| sort.kind.as_ref())
        .ok_or("extraction oracle sort index out of bounds or missing kind")?;
    let native_kind = native
        .get(native_index as usize)
        .and_then(|sort| sort.kind.as_ref())
        .ok_or("extraction oracle native sort index out of bounds or missing kind")?;
    let pairs = match (wire_kind, native_kind) {
        (pb::sort::Kind::Eq(left), pb::sort::Kind::Eq(right)) => return Ok(left == right),
        (pb::sort::Kind::Family(left), pb::sort::Kind::Family(right))
            if left.name == right.name && left.args.len() == right.args.len() =>
        {
            left.args
                .iter()
                .zip(&right.args)
                .map(|(a, b)| (*a, *b))
                .collect::<Vec<_>>()
        }
        (pb::sort::Kind::Func(left), pb::sort::Kind::Func(right))
            if left.params.len() == right.params.len() =>
        {
            left.params
                .iter()
                .zip(&right.params)
                .map(|(a, b)| (*a, *b))
                .chain([(left.result, right.result)])
                .collect::<Vec<_>>()
        }
        _ => return Ok(false),
    };
    for (wire_child, native_child) in pairs {
        if !same_frozen_sort(wire, wire_child, native, native_child, depth + 1, compared)? {
            return Ok(false);
        }
    }
    Ok(true)
}

// Small real byte extractions feed the SAME independent oracle as the corpus.
// This fixture owns setup/transport only; it does not decode or evaluate terms.
struct PartialCallOracleCase {
    native: EGraph,
    extract: ExtractCheck,
    response: pb::RunProgramResponse,
    terms: Vec<u32>,
}

fn partial_call_oracle_case(setup: &str) -> Result<PartialCallOracleCase, String> {
    let mut native = new_experimental_egraph();
    native
        .parse_and_run_program(None, setup)
        .map_err(|error| error.to_string())?;
    let root = native
        .parser
        .get_expr_from_string(None, "(oracle_root)")
        .map_err(|error| error.to_string())?;
    let mut engine = Engine::default();
    let created = engine
        .create(
            &pb::CreateEGraphRequest {
                sorts: vec![pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "i64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                }],
                options: Some(pb::EGraphOptions {
                    cost_sort: Some(0),
                    execution_mode: pb::ExecutionMode::Normal.into(),
                    ..Default::default()
                }),
                ..Default::default()
            }
            .encode_to_vec(),
        )
        .map_err(|error| error.to_string())?;
    let id = pb::CreateEGraphResponse::decode(created.as_slice())
        .map_err(|error| error.to_string())?
        .egraph_id;
    let text = format!("{setup}\n(extract (oracle_root))");
    let mut extraction = None;
    for phase in Source::new(None, &text).map_err(|error| error.to_string())? {
        let bytes = engine
            .run(
                &pb::RunProgramRequest {
                    egraph_id: id,
                    program: Some(phase.map_err(|error| error.to_string())?),
                    profile: true,
                    include_run_reports: false,
                }
                .encode_to_vec(),
            )
            .map_err(|error| error.to_string())?;
        let response =
            pb::RunProgramResponse::decode(bytes.as_slice()).map_err(|error| error.to_string())?;
        if let Some(error) = &response.error {
            return Err(format!("PartialCall canary byte treatment: {error:?}"));
        }
        if response
            .outputs
            .iter()
            .any(|output| matches!(output.kind, Some(pb::command_output::Kind::Extraction(_))))
        {
            if extraction.replace(response).is_some() {
                return Err("PartialCall canary produced multiple extraction responses".into());
            }
        }
    }
    let response = extraction.ok_or("PartialCall canary produced no extraction response")?;
    let terms = response
        .outputs
        .iter()
        .filter_map(|output| match &output.kind {
            Some(pb::command_output::Kind::Extraction(result)) => Some(result),
            _ => None,
        })
        .flat_map(|result| &result.roots)
        .flat_map(|root| &root.variants)
        .map(|term| term.term)
        .collect::<Vec<_>>();
    if terms.len() != 1
        || !matches!(
            response
                .nodes
                .get(terms[0] as usize)
                .and_then(|node| node.kind.as_ref()),
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::PartialCall(_))
            }))
        )
    {
        return Err("PartialCall canary must return one actual frozen function value".into());
    }
    Ok(PartialCallOracleCase {
        native,
        response,
        terms,
        extract: ExtractCheck {
            additional_roots: vec![],
            count_first: false,
            root,
            variants: None,
            use_greedy_dag: false,
        },
    })
}

fn partial_call_oracle_trials() -> Vec<Trial> {
    let mut trials = vec![];
    for (name, setup, shared) in [
        (
            "zero-captures",
            "(sort Expected (UnstableFn (i64 i64) i64)) (function oracle_root () Expected :merge old) (set (oracle_root) (unstable-fn \"+\"))",
            false,
        ),
        (
            "all-shared-captures",
            "(sort Expected (UnstableFn () i64)) (function oracle_root () Expected :merge old) (set (oracle_root) (unstable-fn \"+\" 2 2))",
            true,
        ),
        (
            "nested-capture",
            "(sort Unary (UnstableFn (i64) i64)) (sort Expected (UnstableFn () i64)) (function oracle_root () Expected :merge old) (set (oracle_root) (unstable-fn \"unstable-app\" (unstable-fn \"+\" 1) 2))",
            false,
        ),
    ] {
        trials.push(Trial::test(
            format!("oracle/partial-call/{name}"),
            move || {
                let mut case = partial_call_oracle_case(setup)?;
                let (_, value) = case
                    .native
                    .eval_expr(&case.extract.root)
                    .map_err(|error| error.to_string())?;
                let native_target = case
                    .native
                    .value_to_container::<egglog::sort::FunctionContainer>(value)
                    .unwrap()
                    .2
                    .clone();
                let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::PartialCall(call)),
                })) = &case.response.nodes[case.terms[0] as usize].kind
                else {
                    unreachable!()
                };
                let (expected_native, expected_wire) = if name == "nested-capture" {
                    ("unstable-app", "egglog.core.fn.apply")
                } else {
                    ("+", "egglog.core.i64.add")
                };
                assert_eq!(native_target, expected_native);
                assert_eq!(
                    call.func, expected_wire,
                    "wire target is resolved, not an overloaded source alias"
                );
                // Native ResolvedFunction interning keys runtime IDs and capture
                // sorts, not spelling; the oracle below must still compare raw
                // Values successfully across these actual differing spellings.
                if shared {
                    let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::PartialCall(call)),
                    })) = &case.response.nodes[case.terms[0] as usize].kind
                    else {
                        unreachable!()
                    };
                    assert_eq!(call.args.len(), 2);
                    assert_eq!(
                        call.args[0], call.args[1],
                        "actual encoder shares equal frozen capture nodes"
                    );
                }
                validate_extract_outputs(
                    &mut case.native,
                    &case.extract,
                    ExtractedExpressions::Frozen(&case.response, case.terms.clone()),
                )
                .map_err(|error| error.to_string())?;
                if name == "zero-captures" {
                    let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::PartialCall(call)),
                    })) = &mut case.response.nodes[case.terms[0] as usize].kind else {
                        unreachable!()
                    };
                    call.func = "egglog.core.i64.sub".into();
                    let error = validate_extract_outputs(&mut case.native, &case.extract, ExtractedExpressions::Frozen(&case.response, case.terms)).unwrap_err();
                    assert!(error.to_string().contains("term unequal to the requested root"), "same-signature target change must not be replaced with the baseline target: {error}");
                    let mut floating = partial_call_oracle_case("(sort Expected (UnstableFn (f64 f64) f64)) (function oracle_root () Expected :merge old) (set (oracle_root) (unstable-fn \"+\"))")?;
                    let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::PartialCall(call)),
                    })) = &floating.response.nodes[floating.terms[0] as usize].kind else {
                        unreachable!()
                    };
                    assert_eq!(call.func, "egglog.core.f64.add");
                    validate_extract_outputs(&mut floating.native, &floating.extract, ExtractedExpressions::Frozen(&floating.response, floating.terms))
                        .map_err(|error| error.to_string())?;
                }
                Ok(())
            },
        ));
    }
    trials.push(Trial::test("oracle/partial-call/expected-competing-aliases", || {
        for declarations in [
            "(sort Other (UnstableFn (i64 i64) i64)) (sort Expected (UnstableFn (i64 i64) i64))",
            "(sort Expected (UnstableFn (i64 i64) i64)) (sort Other (UnstableFn (i64 i64) i64))",
        ] {
            let mut case = partial_call_oracle_case(&format!("{declarations} (function oracle_root () Expected :merge old) (set (oracle_root) (unstable-fn \"+\"))"))?;
            validate_extract_outputs(&mut case.native, &case.extract, ExtractedExpressions::Frozen(&case.response, case.terms))
                .map_err(|error| error.to_string())?;
        }
        Ok(())
    }));
    trials.push(Trial::test("oracle/partial-call/nominal-annotation-mismatch", || {
        let mut case = partial_call_oracle_case("(datatype A (A0)) (datatype B (B0)) (sort Expected (UnstableFn () A)) (function oracle_root () Expected :merge old) (set (oracle_root) (unstable-fn \"A0\"))")?;
        validate_extract_outputs(&mut case.native, &case.extract, ExtractedExpressions::Frozen(&case.response, case.terms.clone()))
            .map_err(|error| error.to_string())?;
        let mut changed = false;
        for sort in &mut case.response.sorts {
            if matches!(&sort.kind, Some(pb::sort::Kind::Eq(name)) if name == "A") {
                sort.kind = Some(pb::sort::Kind::Eq("B".into()));
                changed = true;
            }
        }
        assert!(changed, "real extraction exports the nominal A annotation");
        let error = validate_extract_outputs(&mut case.native, &case.extract, ExtractedExpressions::Frozen(&case.response, case.terms)).unwrap_err();
        assert!(error.to_string().contains("annotation differs"), "{error}");
        Ok(())
    }));
    trials.push(Trial::test("oracle/partial-call/underdetermined-capture-capability", || {
        // Root/output fixes the nullary result but not the captured Vec alias.
        // This remains an explicit capability error, never a corpus pass.
        let single_alias = "(sort First (Vec i64)) (sort Expected (UnstableFn () i64)) (function captured () First :merge old) (set (captured) (vec-of 1)) (function oracle_root () Expected :merge old) (set (oracle_root) (unstable-fn \"vec-length\" (captured)))";
        let mut positive = partial_call_oracle_case(single_alias)?;
        validate_extract_outputs(&mut positive.native, &positive.extract, ExtractedExpressions::Frozen(&positive.response, positive.terms))
            .map_err(|error| error.to_string())?;
        let mut case = partial_call_oracle_case("(sort First (Vec i64)) (sort Second (Vec i64)) (sort Expected (UnstableFn () i64)) (function captured () First :merge old) (set (captured) (vec-of 1)) (function oracle_root () Expected :merge old) (set (oracle_root) (unstable-fn \"vec-length\" (captured)))")?;
        let decoded = FrozenDecoder { response: &case.response, callables: HashMap::new(), remaining: 65_536 }
            .expression(case.terms[0], 0, &mut vec![])?;
        let root_sort = case.native.eval_expr(&case.extract.root).map_err(|error| error.to_string())?.0;
        let inference = case.native.typecheck_expr_with_bindings_and_output(&decoded, &[], root_sort, egglog::Context::Full).unwrap_err();
        assert!(matches!(&inference, egglog::TypeError::InferenceFailure(Expr::Var(_, name)) if name.starts_with("@vec-of")), "expected native inference failure at reconstructed Vec capture, got {inference:?}");
        let error = validate_extract_outputs(&mut case.native, &case.extract, ExtractedExpressions::Frozen(&case.response, case.terms)).unwrap_err();
        let message = error.to_string();
        assert!(message.contains("contextual function-value extraction oracle") && message.contains("Failed to infer a type for: @vec-of"), "{error}");
        Ok(())
    }));
    trials.push(Trial::test(
        "oracle/partial-call/expansion-depth-bounds",
        || {
            let mut response = pb::RunProgramResponse {
                sorts: vec![
                    pb::Sort {
                        kind: Some(pb::sort::Kind::Family(pb::HostSort {
                            name: "i64".into(),
                            args: vec![],
                        })),
                        ..Default::default()
                    },
                    pb::Sort {
                        kind: Some(pb::sort::Kind::Func(pb::FuncSort {
                            params: vec![0, 0],
                            result: 0,
                        })),
                        ..Default::default()
                    },
                ],
                nodes: vec![pb::Node {
                    sort_id: 1,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::PartialCall(pb::Call {
                            func: "+".into(),
                            args: vec![],
                        })),
                    })),
                    ..Default::default()
                }],
                ..Default::default()
            };
            let mut decoder = FrozenDecoder {
                response: &response,
                callables: HashMap::new(),
                remaining: 65_536,
            };
            let mut annotations = vec![];
            // Two generated Expr nodes per zero-capture variant; one aggregate
            // allowance must reach zero rather than reset for every root/variant.
            for _ in 0..32_768 {
                annotations.clear();
                decoder.expression(0, 0, &mut annotations)?;
                assert_eq!(annotations.len(), 2);
            }
            assert_eq!(decoder.remaining, 0);
            assert!(
                decoder
                    .expression(0, 0, &mut annotations)
                    .unwrap_err()
                    .contains("65536 Expr nodes across variants")
            );
            // Adversarial repeated capture edges must count their unfolded size,
            // not just the16 distinct wire nodes. No native evaluation is needed.
            for child in 0..15 {
                response.nodes.push(pb::Node {
                    sort_id: 1,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::PartialCall(pb::Call {
                            func: "combine".into(),
                            args: vec![child, child],
                        })),
                    })),
                    ..Default::default()
                });
            }
            let mut decoder = FrozenDecoder {
                response: &response,
                callables: HashMap::new(),
                remaining: 65_536,
            };
            assert!(
                decoder
                    .expression(15, 0, &mut vec![])
                    .unwrap_err()
                    .contains("65536 Expr nodes")
            );
            for child in 15..257 {
                response.nodes.push(pb::Node {
                    sort_id: 1,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::PartialCall(pb::Call {
                            func: "nested".into(),
                            args: vec![child],
                        })),
                    })),
                    ..Default::default()
                });
            }
            let mut decoder = FrozenDecoder {
                response: &response,
                callables: HashMap::new(),
                remaining: 65_536,
            };
            assert!(
                decoder
                    .expression(257, 0, &mut vec![])
                    .unwrap_err()
                    .contains("depth 256")
            );
            // A shallow wire Map still reconstructs a deep left-associated
            // insert spine. Its AST depth must not be measured as wire depth.
            let mut map = pb::RunProgramResponse {
                sorts: vec![
                    response.sorts[0].clone(),
                    pb::Sort {
                        kind: Some(pb::sort::Kind::Family(pb::HostSort {
                            name: "Map".into(),
                            args: vec![0, 0],
                        })),
                        ..Default::default()
                    },
                ],
                nodes: (0..257)
                    .map(|value| pb::Node {
                        sort_id: 0,
                        kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                            value: Some(pb::primitive_value::Value::I64(value)),
                        })),
                        ..Default::default()
                    })
                    .collect(),
                ..Default::default()
            };
            map.nodes.push(pb::Node {
                sort_id: 1,
                kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Map(pb::MapValue {
                        entries: (0..257)
                            .map(|index| pb::MapEntry {
                                key: Some(index),
                                value: Some(index),
                            })
                            .collect(),
                    })),
                })),
                ..Default::default()
            });
            let mut decoder = FrozenDecoder {
                response: &map,
                callables: HashMap::new(),
                remaining: 65_536,
            };
            assert!(
                decoder
                    .expression(257, 0, &mut vec![])
                    .unwrap_err()
                    .contains("reconstructed expression exceeds depth 256")
            );
            Ok(())
        },
    ));
    trials.push(Trial::test(
        "oracle/partial-call/expected-eval-normal-only",
        || {
            use egglog::ast::Literal;
            for mode in 0..4 {
                let mut graph = match mode {
                    0 => new_experimental_egraph(),
                    1 => new_experimental_egraph().with_term_encoding_enabled(),
                    2 => new_experimental_egraph().with_proofs_enabled(),
                    _ => new_experimental_egraph()
                        .with_proofs_enabled()
                        .with_proof_testing(),
                };
                let expected = graph.get_sort_by_name("i64").unwrap().clone();
                let result =
                    graph.eval_expr_with_output(&Expr::Lit(span!(), Literal::Int(1)), expected);
                if mode == 0 {
                    let (sort, value) = result.map_err(|error| error.to_string())?;
                    assert_eq!(sort.name(), "i64");
                    assert_eq!(graph.value_to_base::<i64>(value), 1);
                } else {
                    let error = result.unwrap_err();
                    assert!(
                        error.to_string().contains("requires normal execution mode"),
                        "{error}"
                    );
                }
            }
            Ok(())
        },
    ));
    trials
}

fn public_callable_oracle_trial() -> Trial {
    Trial::test("oracle/call/public-table-provenance", || {
        let authored = "(datatype E (Num i64) (Other i64)) (extract (Num (get-size! \"Num\")))";
        let mut renderer = Renderer::default();
        let mut rendered = String::new();
        for phase in Source::new(None, authored).map_err(|error| error.to_string())? {
            rendered.push_str(
                &renderer
                    .render(&phase.map_err(|error| error.to_string())?)
                    .map_err(|error| error.to_string())?,
            );
        }
        let mut native = new_experimental_egraph();
        let mut commands = native
            .parse_program(None, &rendered)
            .map_err(|error| error.to_string())?
            .into_iter();
        let mut engine = Engine::default();
        let created = engine
            .create(
                &pb::CreateEGraphRequest {
                    sorts: vec![pb::Sort {
                        kind: Some(pb::sort::Kind::Family(pb::HostSort {
                            name: "i64".into(),
                            args: vec![],
                        })),
                        ..Default::default()
                    }],
                    options: Some(pb::EGraphOptions {
                        cost_sort: Some(0),
                        ..Default::default()
                    }),
                    ..Default::default()
                }
                .encode_to_vec(),
            )
            .map_err(|error| error.to_string())?;
        let id = pb::CreateEGraphResponse::decode(created.as_slice())
            .map_err(|error| error.to_string())?
            .egraph_id;
        let mut saw_declaration = false;
        let mut saw_extract = false;
        for phase in Source::new(None, &rendered).map_err(|error| error.to_string())? {
            let program = phase.map_err(|error| error.to_string())?;
            for declaration in &program.declarations {
                if let Some(pb::declaration::Kind::Constructor(constructor)) = &declaration.kind
                    && constructor.name == "Num"
                {
                    assert_eq!(constructor.inputs.len(), 1);
                    assert!(
                        matches!(&program.sorts[constructor.inputs[0].sort as usize].kind,
                        Some(pb::sort::Kind::Family(family)) if family.name == "i64" && family.args.is_empty())
                    );
                    assert!(matches!(
                        &program.sorts[constructor.output as usize].kind,
                        Some(pb::sort::Kind::Eq(_))
                    ));
                    saw_declaration = true;
                }
            }
            let command = commands.next().ok_or("missing native canary command")?;
            let extract = extract_command_parts(&command);
            let validation = extract.as_ref().map(|_| native.clone());
            native
                .run_program(vec![command])
                .map_err(|error| error.to_string())?;
            let bytes = engine
                .run(
                    &pb::RunProgramRequest {
                        egraph_id: id,
                        program: Some(program),
                        profile: true,
                        include_run_reports: false,
                    }
                    .encode_to_vec(),
                )
                .map_err(|error| error.to_string())?;
            let mut response = pb::RunProgramResponse::decode(bytes.as_slice())
                .map_err(|error| error.to_string())?;
            assert!(response.error.is_none(), "{response:?}");
            let Some(extract) = extract else { continue };
            assert!(!saw_extract);
            saw_extract = true;
            let validation = validation.unwrap();
            let mut physical = vec![];
            for logical in ["Num", "Other"] {
                let matches = validation
                    .functions_iter()
                    .filter(|(_, function)| {
                        matches!(&function.func_type().table_name,
                        Some(egglog::ast::TableName::Public(name)) if name == logical)
                    })
                    .collect::<Vec<_>>();
                assert_eq!(matches.len(), 1);
                let (name, function) = matches[0];
                assert_ne!(name, logical);
                assert!(validation.get_function(logical).is_none());
                assert_eq!(function.func_type().input.len(), 1);
                assert_eq!(function.func_type().input[0].name(), "i64");
                assert!(function.func_type().output.is_eq_sort());
                assert_eq!(validation.get_size(name), 0);
                physical.push((name.clone(), function.func_type().output.name().to_string()));
            }
            assert_eq!(physical[0].1, physical[1].1);
            let terms = response
                .outputs
                .iter()
                .filter_map(|output| match &output.kind {
                    Some(pb::command_output::Kind::Extraction(result)) => Some(result),
                    _ => None,
                })
                .flat_map(|result| &result.roots)
                .flat_map(|root| &root.variants)
                .map(|variant| variant.term)
                .collect::<Vec<_>>();
            assert_eq!(terms.len(), 1);
            let root = terms[0] as usize;
            let Some(pb::node::Kind::Call(call)) = &response.nodes[root].kind else {
                return Err("canary did not return a constructor Call".into());
            };
            assert_eq!(call.func, "Num");
            assert_eq!(call.args.len(), 1);
            assert!(matches!(
                &response.nodes[call.args[0] as usize].kind,
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::I64(0)),
                }))
            ));
            assert!(
                matches!(&response.sorts[response.nodes[root].sort_id as usize].kind,
                Some(pb::sort::Kind::Eq(name)) if name == &physical[0].1)
            );
            validate_extract_outputs(
                &mut validation.clone(),
                &extract,
                ExtractedExpressions::Frozen(&response, terms.clone()),
            )
            .map_err(|error| error.to_string())?;
            for (target, expected_error) in [
                ("Other", "term unequal to the requested root"),
                ("missing-callable", "Unbound function missing-callable"),
            ] {
                let Some(pb::node::Kind::Call(call)) = &mut response.nodes[root].kind else {
                    unreachable!()
                };
                call.func = target.into();
                let error = validate_extract_outputs(
                    &mut validation.clone(),
                    &extract,
                    ExtractedExpressions::Frozen(&response, terms.clone()),
                )
                .unwrap_err();
                assert!(error.to_string().contains(expected_error), "{error}");
            }
        }
        assert!(saw_declaration && saw_extract);
        assert!(commands.next().is_none());
        Ok(())
    })
}

fn multi_extract_oracle_trial() -> Trial {
    Trial::test("oracle/multi-extract/ordered-groups", || {
        let setup = "(datatype E (A) (B) (Hidden :unextractable)) (A) (B) (Hidden)";
        let mut native = new_experimental_egraph();
        native
            .parse_and_run_program(None, setup)
            .map_err(|e| e.to_string())?;
        let command = native
            .parse_program(None, "(multi-extract 1 (A) (B) (Hidden) 42 (A))")
            .map_err(|e| e.to_string())?
            .remove(0);
        let extract = extract_command_parts(&command)
            .ok_or("multi-extract oracle did not recognize command")?;
        let outputs = native
            .clone()
            .run_program(vec![command])
            .map_err(|e| e.to_string())?;
        validate_extract_outputs(
            &mut native.clone(),
            &extract,
            ExtractedExpressions::Native(extracted_exprs(&outputs).map_err(|e| e.to_string())?),
        )
        .map_err(|e| e.to_string())?;
        let mut engine = Engine::default();
        let created = engine
            .create(
                &pb::CreateEGraphRequest {
                    sorts: vec![pb::Sort {
                        kind: Some(pb::sort::Kind::Family(pb::HostSort {
                            name: "i64".into(),
                            args: vec![],
                        })),
                        ..Default::default()
                    }],
                    options: Some(pb::EGraphOptions {
                        cost_sort: Some(0),
                        ..Default::default()
                    }),
                    ..Default::default()
                }
                .encode_to_vec(),
            )
            .map_err(|e| e.to_string())?;
        let id = pb::CreateEGraphResponse::decode(created.as_slice())
            .map_err(|e| e.to_string())?
            .egraph_id;
        for phase in Source::new(None, setup).map_err(|e| e.to_string())? {
            let bytes = engine
                .run(
                    &pb::RunProgramRequest {
                        egraph_id: id,
                        program: Some(phase.map_err(|e| e.to_string())?),
                        profile: true,
                        ..Default::default()
                    }
                    .encode_to_vec(),
                )
                .map_err(|e| e.to_string())?;
            let response =
                pb::RunProgramResponse::decode(bytes.as_slice()).map_err(|e| e.to_string())?;
            assert!(response.error.is_none(), "{response:?}");
        }
        let program = pb::Program {
            ir_version: 1,
            sorts: vec![
                pb::Sort {
                    kind: Some(pb::sort::Kind::Eq("E".into())),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "i64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
            ],
            nodes: ["A", "B", "Hidden"]
                .into_iter()
                .map(|name| pb::Node {
                    kind: Some(pb::node::Kind::Call(pb::Call {
                        func: name.into(),
                        args: vec![],
                    })),
                    ..Default::default()
                })
                .chain([pb::Node {
                    sort_id: 1,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::I64(42)),
                    })),
                    ..Default::default()
                }])
                .collect(),
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Extract(pb::Extract {
                    roots: vec![0, 1, 2, 3, 0],
                    variants: 1,
                    extractor: pb::Extractor::Tree.into(),
                    ..Default::default()
                })),
                ..Default::default()
            }],
            ..Default::default()
        };
        let bytes = engine
            .run(
                &pb::RunProgramRequest {
                    egraph_id: id,
                    program: Some(program),
                    profile: true,
                    ..Default::default()
                }
                .encode_to_vec(),
            )
            .map_err(|e| e.to_string())?;
        let response =
            pb::RunProgramResponse::decode(bytes.as_slice()).map_err(|e| e.to_string())?;
        assert!(response.error.is_none(), "{response:?}");
        let [output] = response.outputs.as_slice() else {
            panic!("{response:?}")
        };
        let Some(pb::command_output::Kind::Extraction(result)) = &output.kind else {
            panic!("{output:?}")
        };
        assert_eq!(
            result
                .roots
                .iter()
                .map(|root| root.variants.len())
                .collect::<Vec<_>>(),
            [1, 1, 0, 1, 1]
        );
        let groups = result
            .roots
            .iter()
            .map(|root| {
                root.variants
                    .iter()
                    .map(|term| term.term)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        validate_extract_outputs(
            &mut native.clone(),
            &extract,
            ExtractedExpressions::FrozenGroups(&response, groups.clone()),
        )
        .map_err(|e| e.to_string())?;
        for mutation in 0..4 {
            let mut changed = groups.clone();
            match mutation {
                0 => changed.swap(0, 1),
                1 => {
                    changed.remove(2);
                }
                2 => changed.swap(2, 3),
                _ => changed.push(vec![]),
            }
            assert!(
                validate_extract_outputs(
                    &mut native.clone(),
                    &extract,
                    ExtractedExpressions::FrozenGroups(&response, changed)
                )
                .is_err(),
                "group mutation {mutation}"
            );
        }
        for target in ["B", "missing-callable"] {
            let mut changed = response.clone();
            let Some(pb::node::Kind::Call(call)) = &mut changed.nodes[groups[0][0] as usize].kind
            else {
                unreachable!()
            };
            call.func = target.into();
            assert!(
                validate_extract_outputs(
                    &mut native.clone(),
                    &extract,
                    ExtractedExpressions::FrozenGroups(&changed, groups.clone())
                )
                .is_err(),
                "target {target}"
            );
        }
        let command = native
            .parse_program(None, "(multi-extract 32769 (A) (A))")
            .map_err(|e| e.to_string())?
            .remove(0);
        let budget = extract_command_parts(&command).unwrap();
        let error = validate_extract_outputs(
            &mut native,
            &budget,
            ExtractedExpressions::FrozenGroups(&response, vec![vec![groups[0][0]; 32769]; 2]),
        )
        .unwrap_err();
        assert!(
            error.to_string().contains("exceeds 65536"),
            "one budget across groups: {error}"
        );
        Ok(())
    })
}

fn protobuf_trials(root: &std::path::Path, core: bool) -> Vec<Trial> {
    let mut trials = vec![];
    for entry in glob::glob(&format!("{}/**/*.egg", root.display())).unwrap() {
        let path = entry.unwrap();
        if path
            .parent()
            .is_some_and(|parent| parent.ends_with("header"))
        {
            continue;
        }
        let large = path.ends_with("gemma.egg") || path.ends_with("gemma4_moe.egg");
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
            // Large application fixtures remain selectable with --ignored.
            trials.push(
                Trial::test(name, move || run.run().map_err(Into::into)).with_ignored_flag(large),
            );
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
    tests.extend(partial_call_oracle_trials());
    tests.push(public_callable_oracle_trial());
    tests.push(multi_extract_oracle_trial());
    tests.extend(protobuf_trials(std::path::Path::new("tests"), false));
    if let Some(root) = std::env::var_os("EGGLOG_PROTO_CORE_TESTS") {
        tests.extend(protobuf_trials(std::path::Path::new(&root), true));
    }
    libtest_mimic::run(&args, tests).exit();
}
