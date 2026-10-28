//! In-process compatibility adapter for encoded protobuf requests.
//!
//! This executable slice supports concrete equality/scalar/Vec/Pair/Map/Maybe sorts,
//! constructors, functions, Unit-annotated relation predicates, ordered actions,
//! content-keyed rule groups, checks, requested proofs, table sizes and logical
//! table rows in all four modes. Extraction remains ordinary-mode only.
//! Unsupported forms fail explicitly before installation.
//! Explicit native extensions may additionally supply inert host-value codecs.
//! Detailed timing and native reports are collected only when requested.
//!
//! Decoded protobuf messages supply all authored semantics. Native ASTs exist
//! during validation and execution; the native engine retains its compiled
//! state, with derived indexes for names and diagnostics. No source or previously
//! supplied AST is accepted by this boundary.

use crate::builtin::{PortableEGraph, PortablePrimitive, PortableTypeInfo};
use std::cell::RefCell;
use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::fmt;
use std::ops::ControlFlow;
use std::sync::Arc;

use crate::proto as pb;
use crate::scheduling::{
    self, Control, ControlContext, ControlReport, ControlStop, PermanentSchedulerState,
    SchedulerBinding,
};
use egglog::ast::{self, Action, Command, Expr, Fact, Literal};
use egglog::{ArcSort, EGraph, Term, TermDag, TermId, Value, span};
use egglog::{ExecutionEvent, ExecutionOrigin, RepeatContinuation};
use egglog_ast::span::{EgglogSpan, SrcFile};
#[cfg(test)]
use prost::Message;

pub mod cost_model;
mod freeze;
pub(crate) mod graph;
mod history;
mod proof;
mod report;
mod rules;
pub mod source;
pub mod value;

// Native input paths paired with the actual wire command and its relative
// list path. This is request-local correspondence, not another control tree.
type ScheduleSites<'a> = HashMap<Vec<usize>, (&'a pb::Command, Vec<u32>)>;
type ExecutionFailureSite = (pb::CommandLocation, Option<pb::Span>);

#[derive(Default)]
struct ScheduleMeasurements {
    failure: Option<ExecutionFailureSite>,
    changed: bool,
}

struct OutputStream<'a> {
    emit: &'a mut dyn FnMut(pb::RunProgramResponse) -> ControlFlow<()>,
    cancelled: bool,
}

impl OutputStream<'_> {
    fn flush(
        &mut self,
        response: &mut pb::RunProgramOutput,
        context: &RequestOccurrences,
    ) -> Result<(), egglog::Error> {
        if !response.outputs.is_empty() {
            self.cancelled = (self.emit)(pb::RunProgramResponse {
                result: Some(pb::run_program_response::Result::Output(std::mem::take(
                    response,
                ))),
                files: context.files.clone(),
            })
            .is_break();
        }
        if self.cancelled {
            Err(egglog::Error::BackendError("execution cancelled".into()))
        } else {
            Ok(())
        }
    }
}

// Fail is path-transparent; only ordered command lists add a path component.
// These static sites also address Actions nested in controls, whose runtime
// Union value frame is independently renewed for each iteration.
fn action_sites(commands: &[pb::Command]) -> impl Iterator<Item = (Vec<u32>, &pb::Action)> {
    let mut pending: Vec<_> = commands
        .iter()
        .enumerate()
        .rev()
        .map(|(index, command)| (vec![index as u32], command))
        .collect();
    std::iter::from_fn(move || {
        loop {
            let (path, command) = pending.pop()?;
            match &command.kind {
                Some(pb::command::Kind::Action(action)) => return Some((path, action)),
                Some(pb::command::Kind::Fail(child)) => pending.push((path, child)),
                Some(pb::command::Kind::Loop(pb::Loop { body, .. })) => {
                    pending.extend(body.iter().enumerate().rev().map(|(index, child)| {
                        let mut child_path = path.clone();
                        child_path.push(index as u32);
                        (child_path, child)
                    }));
                }
                _ => (),
            }
        }
    })
}

fn command_tree(commands: &[pb::Command]) -> impl Iterator<Item = &pb::Command> {
    let mut pending: Vec<_> = commands.iter().rev().collect();
    std::iter::from_fn(move || {
        let command = pending.pop()?;
        match &command.kind {
            Some(pb::command::Kind::Fail(child)) => pending.push(child.as_ref()),
            Some(pb::command::Kind::Loop(body)) => pending.extend(body.body.iter().rev()),
            _ => (),
        }
        Some(command)
    })
}

/// A rejected transport, source conversion, or lifecycle operation, separate
/// from execution errors returned in encoded responses.
#[derive(Debug)]
pub struct TransportError(String);

impl fmt::Display for TransportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl std::error::Error for TransportError {}

impl From<prost::DecodeError> for TransportError {
    fn from(error: prost::DecodeError) -> Self {
        Self(error.to_string())
    }
}

/// A collection of native e-graphs accessible only through encoded requests.
#[derive(Default)]
pub struct Engine {
    next_id: u64,
    next_cost_model: u64,
    graphs: HashMap<u64, Session>,
    // Input ownership never enters Session's compile-only preparation clones.
    histories: HashMap<u64, history::HistoryLog>,
    extension: Option<Arc<dyn NativeExtension>>,
    builtins: Option<Arc<pb::BuiltinCatalog>>,
}

/// Explicit native code availability, independent of any wire declaration.
/// Implementations must keep inspection/lowering inert and append only helper
/// records to the ephemeral execution program, never alter authored records.
pub trait NativeExtension: Send + Sync {
    /// Register real native sorts/primitives before mode selection and handle
    /// allocation. No authored commands or payloads are executed here.
    fn initialize(&self, graph: &mut EGraph) -> Result<(), String>;

    /// Lower one inert custom value to an ordinary native-provider call.
    /// Append helper records only; the input sort is the actual registered sort.
    fn lower_custom_value(
        &self,
        graph: &EGraph,
        native_sort: &ArcSort,
        value: &pb::CustomValue,
        span: Option<pb::Span>,
        destination: &mut pb::Program,
    ) -> Result<pb::Call, String>;

    /// Inspect a recognized native value without invoking arbitrary native
    /// reconstruction. Used by extraction, owned callback observations and Freeze.
    fn encode_observed_custom_value(
        &self,
        _graph: &EGraph,
        _sort: &ArcSort,
        _value: Value,
    ) -> Result<Option<pb::CustomValue>, String> {
        Ok(None)
    }
}

#[derive(Clone)]
struct Session {
    graph: EGraph,
    extension: Option<Arc<dyn NativeExtension>>,
    mode: pb::ExecutionMode,
    // Installed user definitions, never builtin descriptors or execution ASTs.
    definitions: pb::Program,
    builtins: Arc<pb::BuiltinCatalog>,
    names: NativeNames,
    // Monotonic namespace stamp for this graph's prepared requests.
    request: u64,
    registry: rules::Registry,
    // Successfully registered closed container aliases, including encoded modes
    // where physical TypeInfo is not the authoring type environment.
    sorts: HashSet<String>,
    cost_models: HashMap<String, Arc<dyn cost_model::NativeCostModel>>,
}

struct Installation {
    command: Option<Command>,
    source_declaration: Option<u32>,
    span: Option<pb::Span>,
    declaration: Option<usize>,
}

struct Prepared {
    definitions: pb::Program,
    request: u64,
    installations: Vec<Installation>,
    materialized: Vec<Command>,
    // Canonical declaration indices whose native installation is still pending.
    pending_declarations: HashSet<usize>,
    context: RequestOccurrences,
    bindings: Vec<pb::RulesetBinding>,
}

#[derive(Default)]
struct NativeSpans(RefCell<Vec<Option<Arc<SrcFile>>>>);

#[derive(Default)]
struct RequestOccurrences {
    request: u64,
    registry: rules::Registry,
    candidates: Vec<rules::Candidate>,
    candidate_offsets: HashMap<rules::Site, std::ops::Range<usize>>,
    literal_rules: HashMap<rules::Site, Vec<usize>>,
    selection: String,
    files: Vec<pb::SourceFile>,
    // Indexed by the execution arena, not the response's merged source files.
    native_spans: NativeSpans,
    diagnostics: bool,
    scoped_actions: HashSet<Vec<u32>>,
    action_dags: HashMap<Vec<u32>, HashSet<u32>>,
    extraction_dags: HashMap<u32, HashSet<u32>>,
    union_values: HashMap<u32, Value>,
}

fn execution_error(
    error: egglog::Error,
    files: &mut Vec<pb::SourceFile>,
    span: Option<pb::Span>,
    location: Option<pb::CommandLocation>,
) -> pb::Error {
    let native_origin = match &error {
        egglog::Error::CheckError(_, span)
        | egglog::Error::NoSuchRuleset(_, span)
        | egglog::Error::ExpectFail(span)
        | egglog::Error::Panic { span, .. }
        | egglog::Error::ProofError { span, .. } => Some(span),
        _ => None,
    };
    let span = native_origin
        .and_then(|origin| {
            let ast::Span::Egglog(origin) = origin else {
                return None;
            };
            let source = pb::SourceFile {
                name: origin.file.name.clone().unwrap_or_default(),
                contents: Some(origin.file.contents.clone()),
            };
            let file = match files.iter().position(|file| file == &source) {
                Some(file) => file,
                None => {
                    files.push(source);
                    files.len() - 1
                }
            };
            Some(pb::Span {
                file: u32::try_from(file).ok()?,
                start: u32::try_from(origin.i).ok()?,
                end: u32::try_from(origin.j).ok()?,
            })
        })
        .or(span);
    pb::Error {
        code: if matches!(error, egglog::Error::CheckError(..)) {
            pb::ErrorCode::CheckFailed.into()
        } else {
            pb::ErrorCode::RuntimeFailure.into()
        },
        message: error.to_string(),
        span,
        location,
    }
}

// Keep validation failures structured while allowing syntax validators to
// supply ordinary diagnostic strings. Engine text is never parsed for a code.
#[derive(Debug)]
struct PreparationError(Box<pb::Error>);

impl From<String> for PreparationError {
    fn from(message: String) -> Self {
        Self(Box::new(pb::Error {
            code: pb::ErrorCode::InvalidProgram.into(),
            message,
            ..Default::default()
        }))
    }
}

impl From<&str> for PreparationError {
    fn from(message: &str) -> Self {
        Self(Box::new(pb::Error {
            code: pb::ErrorCode::InvalidProgram.into(),
            message: message.into(),
            ..Default::default()
        }))
    }
}

impl Engine {
    /// Provision an engine-local model name through the native host extension.
    /// An in-flight extraction and cloned handles retain their own Arc owner.
    pub fn register_cost_model(
        &mut self,
        handle: u64,
        model: Arc<dyn cost_model::NativeCostModel>,
    ) -> Result<String, TransportError> {
        let session = self
            .graphs
            .get_mut(&handle)
            .ok_or_else(|| TransportError("unknown egraph handle".into()))?;
        self.next_cost_model = self
            .next_cost_model
            .checked_add(1)
            .ok_or_else(|| TransportError("cost model name space exhausted".into()))?;
        let name = format!("host-model-{}", self.next_cost_model);
        session.cost_models.insert(name.clone(), model);
        Ok(name)
    }

    /// Release only this handle's registration. A clone or active extraction
    /// may still own the model; no borrowed callback frame is retained.
    pub fn release_cost_model(&mut self, handle: u64, name: &str) -> Result<(), TransportError> {
        let session = self
            .graphs
            .get_mut(&handle)
            .ok_or_else(|| TransportError("unknown egraph handle".into()))?;
        session
            .cost_models
            .remove(name)
            .ok_or_else(|| TransportError(format!("unknown cost model {name}")))?;
        Ok(())
    }

    /// Uses the supplied registrar on fresh graphs; clones retain registered
    /// native state and the same capability without replaying registration.
    pub fn with_extension(extension: Arc<dyn NativeExtension>) -> Self {
        Self {
            extension: Some(extension),
            ..Self::default()
        }
    }

    fn create_request(
        &mut self,
        request: pb::CreateEGraphRequest,
    ) -> Result<pb::CreateEGraphResponse, TransportError> {
        let mode =
            pb::ExecutionMode::try_from(request.options.as_ref().map_or(0, |o| o.execution_mode))
                .map_err(|_| TransportError("unknown execution mode".into()))?;
        let seminaive = request
            .options
            .as_ref()
            .and_then(|options| options.seminaive)
            .unwrap_or(true);
        let no_decomp = request.no_decomp;
        if request.sorts.iter().any(|sort| {
            matches!(
                sort.kind,
                Some(pb::sort::Kind::Eq(_) | pb::sort::Kind::Var(_))
            )
        }) {
            return Err(TransportError(
                "creation requires closed backend-provided sorts".into(),
            ));
        }
        let cost = request
            .options
            .and_then(|options| options.cost_sort)
            .and_then(|index| request.sorts.get(index as usize));
        if !matches!(cost.and_then(|sort| sort.kind.as_ref()), Some(pb::sort::Kind::Application(family)) if family.name == "i64" && family.args.is_empty())
        {
            return Err(TransportError(
                "this adapter currently requires the i64 cost sort".into(),
            ));
        }
        let program = pb::Program {
            sorts: request.sorts,
            files: request.files,
            ..Default::default()
        };
        let native_spans = NativeSpans::default();
        let mut graph = crate::new_experimental_egraph();
        // Provider setup and the original proof typechecking clone inherit the
        // byte adapter's off policy, before any optional native work can run.
        graph.set_report_level(egglog_reports::ReportLevel::Off);
        graph.seminaive = seminaive;
        graph.no_decomp = no_decomp;
        if let Some(extension) = &self.extension {
            extension.initialize(&mut graph).map_err(TransportError)?;
        }
        let mut graph = match mode {
            pb::ExecutionMode::Normal => graph,
            pb::ExecutionMode::TermEncoding => graph.with_term_encoding_enabled(),
            pb::ExecutionMode::Proofs => graph.with_proofs_enabled(),
            pb::ExecutionMode::ProofTesting => graph.with_proofs_enabled().with_proof_testing(),
        };
        let builtins = match &self.builtins {
            Some(catalog) => catalog.clone(),
            None => {
                let catalog = crate::builtin::configured_catalog(&graph).map_err(TransportError)?;
                self.builtins = Some(catalog.clone());
                catalog
            }
        };
        for (index, sort) in program.sorts.iter().enumerate() {
            validate_nullary_family(graph.type_info(), sort).map_err(TransportError)?;
            let name = sort_name(&program.sorts, index as u32).map_err(TransportError)?;
            let native = graph
                .get_sort_by_name(&name)
                .ok_or_else(|| TransportError(format!("unknown creation sort {name}")))?;
            if native.is_eq_sort() != matches!(sort.kind, Some(pb::sort::Kind::Eq(_))) {
                return Err(TransportError(format!(
                    "creation sort kind mismatch for {name}"
                )));
            }
            native_span(&program, sort.span.as_ref(), &native_spans).map_err(TransportError)?;
        }
        if let Some(threads) = request.threads {
            if cfg!(target_family = "wasm") && threads > 1 {
                return Err(TransportError(
                    "native wasm execution supports at most one thread".into(),
                ));
            }
            graph.set_num_threads(
                usize::try_from(threads)
                    .map_err(|_| TransportError("thread count exceeds native usize".into()))?,
            );
        }
        graph.set_report_level(egglog_reports::ReportLevel::Off);
        let threads = u64::try_from(graph.num_threads())
            .map_err(|_| TransportError("native thread count exceeds uint64".into()))?;
        self.next_id = self
            .next_id
            .checked_add(1)
            .ok_or_else(|| TransportError("handle space exhausted".into()))?;
        self.graphs.insert(
            self.next_id,
            Session {
                graph,
                extension: self.extension.clone(),
                mode,
                definitions: pb::Program::default(),
                builtins,
                names: NativeNames::default(),
                request: 0,
                registry: rules::Registry::default(),
                sorts: HashSet::new(),
                cost_models: HashMap::new(),
            },
        );
        Ok(pb::CreateEGraphResponse {
            egraph_id: self.next_id,
            threads,
        })
    }

    fn clone_request(
        &mut self,
        request: pb::CloneEGraphRequest,
    ) -> Result<pb::CloneEGraphResponse, TransportError> {
        let graph = self
            .graphs
            .get(&request.egraph_id)
            .ok_or_else(|| TransportError("unknown egraph_id".into()))?
            .clone();
        self.next_id = self
            .next_id
            .checked_add(1)
            .ok_or_else(|| TransportError("handle space exhausted".into()))?;
        self.graphs.insert(self.next_id, graph);
        if let Some(history) = self.histories.get(&request.egraph_id).cloned() {
            self.histories.insert(self.next_id, history);
        }
        Ok(pb::CloneEGraphResponse {
            egraph_id: self.next_id,
        })
    }

    fn destroy_request(
        &mut self,
        request: pb::DestroyEGraphRequest,
    ) -> Result<pb::DestroyEGraphResponse, TransportError> {
        let graph = self
            .graphs
            .remove(&request.egraph_id)
            .ok_or_else(|| TransportError("unknown egraph_id".into()))?;
        self.histories.remove(&request.egraph_id);
        drop(graph);
        Ok(pb::DestroyEGraphResponse {})
    }

    fn run_request(
        &mut self,
        request: pb::RunProgramRequest,
    ) -> Result<Vec<pb::RunProgramResponse>, TransportError> {
        let mut frames = Vec::new();
        self.run_request_stream(request, &mut |frame| {
            frames.push(frame);
            ControlFlow::Continue(())
        })?;
        Ok(frames)
    }

    fn run_request_stream(
        &mut self,
        request: pb::RunProgramRequest,
        emit: &mut dyn FnMut(pb::RunProgramResponse) -> ControlFlow<()>,
    ) -> Result<(), TransportError> {
        let original = self
            .histories
            .contains_key(&request.egraph_id)
            .then(|| request.program.clone())
            .flatten();
        let session = self
            .graphs
            .get_mut(&request.egraph_id)
            .ok_or_else(|| TransportError("unknown egraph_id".into()))?;
        let Some(mut program) = request.program else {
            let _ = emit(pb::RunProgramResponse {
                result: Some(pb::run_program_response::Result::Error(pb::Error {
                    code: pb::ErrorCode::InvalidProgram.into(),
                    message: "missing program".into(),
                    ..Default::default()
                })),
                files: vec![],
            });
            return Ok(());
        };
        session.graph.set_report_level(if request.diagnostics {
            egglog_reports::ReportLevel::StageInfo
        } else {
            egglog_reports::ReportLevel::Off
        });
        let prepared = match session.prepare(&mut program) {
            Ok(prepared) => prepared,
            Err(error) => {
                session
                    .graph
                    .set_report_level(egglog_reports::ReportLevel::Off);
                let _ = emit(pb::RunProgramResponse {
                    result: Some(pb::run_program_response::Result::Error(*error.0)),
                    files: program.files,
                });
                return Ok(());
            }
        };
        if let Some(original) = original {
            self.histories
                .get_mut(&request.egraph_id)
                .unwrap()
                .append(history::capture(original, &session.registry).map_err(TransportError)?);
        }
        let mut response = pb::RunProgramOutput::default();
        let mut context = match session.install(prepared, &mut response) {
            Ok(context) => context,
            Err((error, files)) => {
                session
                    .graph
                    .set_report_level(egglog_reports::ReportLevel::Off);
                if !response.outputs.is_empty() {
                    let _ = emit(pb::RunProgramResponse {
                        result: Some(pb::run_program_response::Result::Output(response)),
                        files: files.clone(),
                    });
                }
                let _ = emit(pb::RunProgramResponse {
                    result: Some(pb::run_program_response::Result::Error(*error)),
                    files,
                });
                return Ok(());
            }
        };
        context.diagnostics = request.diagnostics;
        let mut stream = OutputStream {
            emit,
            cancelled: false,
        };
        let mut failure = None;
        for (index, command) in program.commands.iter().enumerate() {
            let location = pb::CommandLocation {
                path: vec![index as u32],
                iterations: vec![],
            };
            let mut failure_site = None;
            let result = session.execute(
                &program,
                command,
                &mut context,
                &location,
                &mut response,
                &mut failure_site,
                &mut stream,
            );
            if stream.cancelled {
                break;
            }
            if let Err(error) = result {
                let (location, span) = failure_site.unwrap_or_else(|| {
                    (
                        location,
                        match &command.kind {
                            Some(pb::command::Kind::Action(action)) => action.span.or(command.span),
                            _ => command.span,
                        },
                    )
                });
                failure = Some(execution_error(
                    error,
                    &mut context.files,
                    span,
                    Some(location),
                ));
                break;
            }
        }
        session.registry = std::mem::take(&mut context.registry);
        session
            .graph
            .set_report_level(egglog_reports::ReportLevel::Off);
        if stream.cancelled {
            return Err(TransportError("execution cancelled".into()));
        }
        if let Some(error) = failure {
            if !response.outputs.is_empty() {
                // Work is complete: declining a terminal delivery cannot hide
                // the actual error or invalidate the already-completed prefix.
                let _ = (stream.emit)(pb::RunProgramResponse {
                    result: Some(pb::run_program_response::Result::Output(response)),
                    files: context.files.clone(),
                });
            }
            let _ = (stream.emit)(pb::RunProgramResponse {
                result: Some(pb::run_program_response::Result::Error(error)),
                files: context.files,
            });
        } else {
            let files = if response.outputs.is_empty() {
                vec![]
            } else {
                context.files
            };
            let _ = (stream.emit)(pb::RunProgramResponse {
                result: Some(pb::run_program_response::Result::Output(response)),
                files,
            });
        }
        Ok(())
    }
}

impl Session {
    fn install(
        &mut self,
        prepared: Prepared,
        response: &mut pb::RunProgramOutput,
    ) -> Result<RequestOccurrences, (Box<pb::Error>, Vec<pb::SourceFile>)> {
        let Prepared {
            mut definitions,
            request,
            installations,
            mut pending_declarations,
            mut context,
            bindings,
            ..
        } = prepared;
        self.request = request;
        let mut failure = None;
        for installation in installations {
            let (result, registered, _) = if let Some(command) = &installation.command {
                NativeExecutor {
                    graph: &mut self.graph,
                    mode: self.mode,
                    names: &self.names,
                }
                .run_observed(
                    vec![command.clone()],
                    None,
                    &mut context,
                    response,
                    None,
                )
            } else {
                (Ok(()), true, None)
            };
            if registered {
                if let Some(index) = installation.declaration {
                    pending_declarations.remove(&index);
                }
                if let Some(Command::Sort {
                    name,
                    presort_and_args: Some(_),
                    ..
                }) = installation.command
                {
                    self.sorts.insert(name);
                }
            }
            if let Err(error) = result {
                failure = Some((error, installation.span));
                break;
            }
        }
        // Retain completed declarations even when a later native installation fails.
        definitions.declarations = std::mem::take(&mut definitions.declarations)
            .into_iter()
            .enumerate()
            .filter_map(|(index, d)| (!pending_declarations.contains(&index)).then_some(d))
            .collect();
        self.definitions = definitions;
        self.names = project_names(
            &mut pb::Program::default(),
            &self.definitions,
            &self.builtins,
        );
        if failure.is_none() {
            let candidates = std::mem::take(&mut context.candidates);
            let mut ranges: Vec<_> = context
                .candidate_offsets
                .iter()
                .map(|(site, range)| (site.clone(), range.clone()))
                .collect();
            ranges.sort_by(|a, b| a.0.cmp(&b.0));
            let mut registry = std::mem::take(&mut context.registry);
            let result = registry.install(
                &candidates,
                &ranges,
                &bindings,
                &mut NativeExecutor {
                    graph: &mut self.graph,
                    mode: self.mode,
                    names: &self.names,
                },
                &mut context,
                response,
            );
            context.candidates = candidates;
            context.registry = registry;
            if let Err(error) = result {
                failure = Some((error, None));
            }
        }
        self.registry = context.registry.clone();
        match failure {
            Some((error, span)) => {
                let error = execution_error(error, &mut context.files, span, None);
                Err((Box::new(error), context.files))
            }
            None => Ok(context),
        }
    }

    // One disposable native compiler owns setup, rule and command validation.
    // Its runtime state and backend IDs are never adopted by the live graph.
    fn prepare(&self, program: &mut pb::Program) -> Result<Prepared, PreparationError> {
        let mut binding_names = HashSet::new();
        for binding in &program.rulesets {
            if binding.value.is_none() {
                return Err("missing ruleset binding value".into());
            }
            if !binding_names.insert(&binding.name) {
                return Err("duplicate ruleset binding name".into());
            }
        }
        for command in command_tree(&program.commands) {
            if let Some(pb::command::Kind::Run(run)) = &command.kind
                && run
                    .rulesets
                    .iter()
                    .any(|selection| selection.kind.is_none())
            {
                return Err("missing ruleset selection kind".into());
            }
        }
        if program
            .sorts
            .iter()
            .any(|sort| matches!(sort.kind, Some(pb::sort::Kind::Var(_))))
        {
            return Err("input Programs contain only concrete sorts".into());
        }
        for node in &program.nodes {
            let call = match &node.kind {
                Some(pb::node::Kind::Call(call)) => Some(call),
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::PartialCall(call)),
                })) => Some(call),
                _ => None,
            };
            if call.is_some_and(|call| {
                matches!(call.func.as_str(), "egglog.core.fn.apply" | "unstable-app")
                    || self
                        .graph
                        .authoring_type_info()
                        .builtin_description(&call.func)
                        .is_ok_and(|description| {
                            matches!(
                                description.typing,
                                egglog::builtin::BuiltinTyping::FunctionApplication
                            )
                        })
            }) {
                return Err("function application requires Apply, not a named callable".into());
            }
        }
        let mut authored_input = program.clone();
        let rule_files = Arc::new(std::mem::take(&mut authored_input.files));
        let native_spans = NativeSpans::default();
        validate_relation_uses(program, &self.definitions)?;
        for rule in graph::rules(program) {
            if let Some(pb::rule::Kind::Rule(rule)) = &rule.kind {
                validate_legacy_union_scope(program, &rule.head)?;
            }
        }
        let mut staged = self.clone();
        staged.request = staged
            .request
            .checked_add(1)
            .ok_or("request identity space exhausted")?;
        // Native registrations remain authoritative even for empty requests.
        staged.graph.type_info().builtin_catalog()?;
        for declaration in &program.declarations {
            let name = match &declaration.kind {
                Some(pb::declaration::Kind::Constructor(c)) => &c.name,
                Some(pb::declaration::Kind::Function(f)) => &f.name,
                Some(pb::declaration::Kind::Relation(r)) => &r.name,
                Some(pb::declaration::Kind::UserDefinedPrimitive(p)) => &p.name,
                _ => continue,
            };
            if self
                .builtins
                .primitives
                .iter()
                .any(|primitive| &primitive.name == name)
            {
                return Err(format!("user callable conflicts with builtin {name}").into());
            }
        }
        let mut next_declaration = staged.definitions.declarations.len();
        let added =
            crate::builtin::definitions::reconcile_declarations(program, &mut staged.definitions)?;
        let declaration_indices: Vec<_> = added
            .iter()
            .map(|added| {
                added.then(|| {
                    let index = next_declaration;
                    next_declaration += 1;
                    index
                })
            })
            .collect();
        let mut pending_declarations = HashSet::new();
        let mut installations = vec![];
        staged.names = project_names(program, &staged.definitions, &self.builtins);
        let mut authored = staged.definitions.clone();
        project_names(&mut authored, &staged.definitions, &self.builtins);
        let signatures: HashMap<_, _> = authored
            .declarations
            .iter()
            .filter_map(|d| match &d.kind {
                Some(pb::declaration::Kind::Constructor(c)) => Some((
                    &c.name,
                    &c.inputs,
                    Some(c.output),
                    Some(ast::FunctionSubtype::Constructor),
                )),
                Some(pb::declaration::Kind::Function(f)) => Some((
                    &f.name,
                    &f.inputs,
                    Some(f.output),
                    Some(ast::FunctionSubtype::Custom),
                )),
                Some(pb::declaration::Kind::UserDefinedPrimitive(p)) => {
                    Some((&p.name, &p.inputs, Some(p.output), None))
                }
                Some(pb::declaration::Kind::Relation(r)) => Some((
                    &r.name,
                    &r.inputs,
                    None,
                    Some(ast::FunctionSubtype::Constructor),
                )),
                _ => None,
            })
            .map(|(name, inputs, output, subtype)| {
                Ok((
                    name.clone(),
                    (
                        match output {
                            Some(output) => signature(&authored, inputs, output)?,
                            // Unit is only a wire annotation. Native Relation
                            // installs its own row sort; no Unit-valued native
                            // function or row-result conversion is fabricated.
                            None => ast::Schema {
                                input: inputs
                                    .iter()
                                    .map(|arg| sort_name(&authored.sorts, arg.sort))
                                    .collect::<Result<_, _>>()?,
                                output: "Unit".into(),
                            },
                        },
                        subtype,
                    ),
                ))
            })
            .collect::<Result<_, String>>()?;
        let constructor_targets: HashSet<_> = authored
            .declarations
            .iter()
            .filter_map(|declaration| match &declaration.kind {
                Some(pb::declaration::Kind::Constructor(constructor)) => {
                    Some(constructor.name.clone())
                }
                _ => None,
            })
            .collect();
        for (declaration, added) in program.declarations.iter().zip(&added) {
            if !added {
                continue;
            }
            let name = match &declaration.kind {
                Some(pb::declaration::Kind::EqSort(s)) => &s.name,
                Some(pb::declaration::Kind::Constructor(f)) => &f.name,
                Some(pb::declaration::Kind::Function(f)) => &f.name,
                Some(pb::declaration::Kind::Relation(r)) => &r.name,
                Some(pb::declaration::Kind::UserDefinedPrimitive(p)) => &p.name,
                _ => continue,
            };
            if staged.graph.get_sort_by_name(name).is_some()
                || staged.graph.get_function(name).is_some()
                || staged.graph.type_info().is_primitive(name)
            {
                return Err(format!("native declaration namespace collision: {name}").into());
            }
        }
        for (index, (declaration, added)) in program.declarations.iter().zip(&added).enumerate() {
            if !added {
                continue;
            }
            if let Some(pb::declaration::Kind::EqSort(sort)) = &declaration.kind {
                if sort.name.is_empty() {
                    return Err("equality sort name must not be empty".into());
                }
                let command = Command::Sort {
                    span: native_span(program, declaration.span.as_ref(), &native_spans)?,
                    name: sort.name.clone(),
                    presort_and_args: None,
                    uf: None,
                    proof_func: None,
                    container_rebuild: None,
                    proof_constructors: None,
                    unionable: true,
                };
                staged
                    .graph
                    .compile_program_observed(vec![command.clone()], &mut |_, _| {})
                    .map_err(|error| error.to_string())?;
                pending_declarations.insert(declaration_indices[index].unwrap());
                installations.push(Installation {
                    command: Some(command),
                    source_declaration: Some(index as u32),
                    span: declaration.span,
                    declaration: declaration_indices[index],
                });
            }
        }
        // Canonical definitions above retain the submitted Custom records.
        // Only this execution copy receives provider-owned inert helper nodes.
        lower_custom_values(program, &mut staged.graph, staged.extension.as_deref())?;
        // Container payloads may introduce the Pair/Vec sorts used to construct
        // a Map. Only this staged execution copy receives those helper records.
        let sort_sites = lower_container_values(program)?;
        let materialized_sorts =
            materialize_sorts(program, &mut staged.graph, &mut staged.sorts, &native_spans)?;
        let mut materialized = vec![];
        for (index, command) in materialized_sorts {
            materialized.push(command.clone());
            let site = sort_sites[index as usize];
            installations.push(Installation {
                command: Some(command),
                source_declaration: None,
                span: program.sorts[site as usize].span,
                declaration: None,
            });
        }
        for (index, sort) in program.sorts.iter().enumerate() {
            validate_nullary_family(staged.graph.type_info(), sort)?;
            native_span(program, sort.span.as_ref(), &native_spans)?;
            let Some(name) =
                structural_sort_name(&program.sorts, index as u32, &mut HashSet::new())?
            else {
                continue;
            };
            let equality = staged.names.sorts.contains_key(&name);
            if !equality
                && !staged.sorts.contains(&name)
                && staged.graph.get_sort_by_name(&name).is_none()
            {
                return Err(format!("unknown sort {name}").into());
            }
            if equality != matches!(sort.kind, Some(pb::sort::Kind::Eq(_))) {
                return Err(format!("sort kind mismatch for {name}").into());
            }
        }
        lower_applications(program)?;
        validate_node_graph(program, &native_spans)?;
        let mut action_dags = classify_action_dags(program)?;
        let extraction_dags = if self.mode == pb::ExecutionMode::Normal {
            let roots = command_tree(&program.commands)
                .filter_map(|command| match &command.kind {
                    Some(pb::command::Kind::Extract(extract)) => Some(extract.roots.as_slice()),
                    _ => None,
                })
                .flatten()
                .map(|root| (*root, vec![*root]));
            classify_value_dags(program, roots)?
        } else {
            HashMap::new()
        };
        let mut scoped_actions = classify_union_actions(
            program,
            &constructor_targets,
            self.mode == pb::ExecutionMode::Normal,
        )?;
        if !scoped_actions.is_empty() && self.mode != pb::ExecutionMode::Normal {
            return Err("scoped actions require normal execution mode".into());
        }
        action_dags.retain(|path, _| !scoped_actions.contains(path));
        scoped_actions.extend(action_dags.keys().cloned());
        lower_builtin_calls(program, &staged.graph, &signatures)?;
        for index in declaration_order(program, &mut staged.graph)? {
            let declaration = &program.declarations[index];
            if !added[index] {
                continue;
            }
            let span = native_span(program, declaration.span.as_ref(), &native_spans)?;
            let command = match declaration
                .kind
                .as_ref()
                .ok_or("missing declaration kind")?
            {
                pb::declaration::Kind::EqSort(_) => continue,
                pb::declaration::Kind::Constructor(constructor) => {
                    if constructor.name.is_empty() {
                        return Err("constructor name must not be empty".into());
                    }
                    let output = program
                        .sorts
                        .get(constructor.output as usize)
                        .ok_or("constructor output sort out of bounds")?;
                    if !matches!(output.kind, Some(pb::sort::Kind::Eq(_))) {
                        return Err("constructor output must be an equality sort".into());
                    }
                    let cost = constructor
                        .cost
                        .map(|index| -> Result<u64, String> {
                            let node = program
                                .nodes
                                .get(index as usize)
                                .ok_or("cost index out of bounds")?;
                            match &node.kind {
                                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                                    value: Some(pb::primitive_value::Value::I64(cost)),
                                })) if *cost >= 0 && node_sort(program, index)? == "i64" => {
                                    Ok(*cost as u64)
                                }
                                _ => Err(
                                    "constructor costs currently require a nonnegative inert i64"
                                        .into(),
                                ),
                            }
                        })
                        .transpose()?;
                    Command::Constructor {
                        span,
                        name: constructor.name.clone(),
                        table_name: Some(native_table_name(
                            declaration,
                            &staged.names.callables[&constructor.name],
                        )),
                        schema: signature(program, &constructor.inputs, constructor.output)?,
                        cost,
                        unextractable: constructor.unextractable,
                        hidden: constructor.hidden,
                        let_binding: false,
                        term_constructor: None,
                    }
                }
                pb::declaration::Kind::Function(function) => {
                    if function.name.is_empty() {
                        return Err("function name must not be empty".into());
                    }
                    let schema = signature(program, &function.inputs, function.output)?;
                    if let Some(index) = function.merge {
                        if node_sort(program, index)? != schema.output {
                            return Err("merge output sort mismatch".into());
                        }
                        let mut bindings = HashMap::from([
                            ("old".into(), schema.output.clone()),
                            ("new".into(), schema.output.clone()),
                        ]);
                        check_variables(program, &[index], &mut bindings, false)?;
                        // Native function validation resolves this deferred body
                        // in Context::Write: builtin calls retain their actual
                        // capabilities, and callable backends are installed first.
                    }
                    Command::Function {
                        span,
                        name: function.name.clone(),
                        table_name: Some(native_table_name(
                            declaration,
                            &staged.names.callables[&function.name],
                        )),
                        schema,
                        merge: function
                            .merge
                            .map(|index| {
                                expression(program, index, &mut HashSet::new(), &native_spans)
                            })
                            .transpose()?,
                        hidden: function.hidden,
                        let_binding: false,
                        term_constructor: None,
                        unextractable: true,
                    }
                }
                pb::declaration::Kind::UserDefinedPrimitive(primitive) => {
                    primitive_command(program, primitive, span, &native_spans)?
                }
                pb::declaration::Kind::Relation(relation) => Command::Relation {
                    span,
                    name: relation.name.clone(),
                    table_name: Some(native_table_name(
                        declaration,
                        &staged.names.callables[&relation.name],
                    )),
                    inputs: relation
                        .inputs
                        .iter()
                        .map(|arg| sort_name(&program.sorts, arg.sort))
                        .collect::<Result<_, _>>()?,
                },
            };
            if self.mode == pb::ExecutionMode::Normal
                && let Command::Constructor { name, schema, .. } = &command
            {
                let cost_table = crate::set_cost::get_cost_table_name(name);
                if staged.graph.get_function(&cost_table).is_some()
                    || staged.graph.type_info().is_primitive(&cost_table)
                    || staged.graph.get_sort_by_name(&cost_table).is_some()
                {
                    return Err(
                        format!("native cost table namespace collision: {cost_table}").into(),
                    );
                }
                let cost_table = Command::Function {
                    span: native_span(program, declaration.span.as_ref(), &native_spans)?,
                    name: cost_table,
                    table_name: Some(ast::TableName::Internal(
                        crate::set_cost::get_cost_table_name(&staged.names.callables[name]),
                    )),
                    schema: ast::Schema::new(schema.input.clone(), "i64".into()),
                    merge: Some(Expr::Var(span!(), "new".into())),
                    hidden: true,
                    let_binding: false,
                    term_constructor: None,
                    unextractable: true,
                };
                staged
                    .graph
                    .compile_program_observed(vec![cost_table.clone()], &mut |_, _| {})
                    .map_err(|error| error.to_string())?;
                installations.push(Installation {
                    command: Some(cost_table),
                    source_declaration: Some(index as u32),
                    span: declaration.span,
                    declaration: None,
                });
            }
            staged
                .graph
                .compile_program_observed(vec![command.clone()], &mut |_, _| {})
                .map_err(|error| error.to_string())?;
            pending_declarations.insert(declaration_indices[index].unwrap());
            installations.push(Installation {
                command: Some(command),
                source_declaration: Some(index as u32),
                span: declaration.span,
                declaration: declaration_indices[index],
            });
        }
        for (index, node) in program.nodes.iter().enumerate() {
            if let Some(pb::node::Kind::GetCost(call)) = &node.kind {
                if self.mode != pb::ExecutionMode::Normal {
                    return Err("cost reads currently require normal execution mode".into());
                }
                let (signature, _) = signatures
                    .get(&call.func)
                    .ok_or_else(|| format!("unknown cost target {}", call.func))?;
                if !constructor_targets.contains(&call.func) {
                    return Err("GetCost requires a constructor target".into());
                }
                if node_sort(program, index as u32)? != "i64"
                    || signature.input.len() != call.args.len()
                {
                    return Err("GetCost signature mismatch".into());
                }
                for (argument, expected) in call.args.iter().zip(&signature.input) {
                    if node_sort(program, *argument)? != *expected {
                        return Err(format!("cost argument sort mismatch for {}", call.func).into());
                    }
                }
            }
            if let Some(pb::node::Kind::Call(call)) = &node.kind
                && let Some((signature, _)) = signatures.get(&call.func)
            {
                if signature.input.len() != call.args.len()
                    || signature.output != sort_name(&program.sorts, node.sort_id)?
                {
                    return Err(format!("call signature mismatch for {}", call.func).into());
                }
                for (argument, expected) in call.args.iter().zip(&signature.input) {
                    if node_sort(program, *argument)? != *expected {
                        return Err(format!("argument sort mismatch for {}", call.func).into());
                    }
                }
            }
        }
        for action in command_tree(&program.commands)
            .filter_map(|command| match &command.kind {
                Some(pb::command::Kind::Action(action)) => Some(action),
                _ => None,
            })
            .chain(graph::rules(program).flat_map(|rule| match &rule.kind {
                Some(pb::rule::Kind::Rule(body)) => body.head.as_slice(),
                _ => &[],
            }))
        {
            let (call, expected) = match &action.kind {
                Some(pb::action::Kind::Subsume(call)) => {
                    (call, Some(ast::FunctionSubtype::Constructor))
                }
                Some(pb::action::Kind::Set(set)) => (
                    set.target.as_ref().ok_or("missing set target")?,
                    Some(ast::FunctionSubtype::Custom),
                ),
                Some(pb::action::Kind::Delete(call)) => (call, None),
                Some(pb::action::Kind::SetCost(set)) => {
                    if self.mode != pb::ExecutionMode::Normal {
                        return Err("cost writes currently require normal execution mode".into());
                    }
                    if node_sort(program, set.cost.ok_or("missing cost value")?)? != "i64" {
                        return Err("assigned cost must have the handle's i64 cost sort".into());
                    }
                    (
                        set.target.as_ref().ok_or("missing cost target")?,
                        Some(ast::FunctionSubtype::Constructor),
                    )
                }
                _ => continue,
            };
            let (_, subtype) = signatures.get(&call.func).ok_or_else(|| {
                PreparationError(Box::new(pb::Error {
                    code: pb::ErrorCode::RuntimeFailure.into(),
                    message: format!("unknown action target {}", call.func),
                    span: action.span,
                    ..Default::default()
                }))
            })?;
            if subtype.is_none() || expected.is_some_and(|expected| *subtype != Some(expected)) {
                return Err(format!("invalid action target subtype: {}", call.func).into());
            }
            if matches!(action.kind, Some(pb::action::Kind::SetCost(_)))
                && !constructor_targets.contains(&call.func)
            {
                return Err("SetCost requires a constructor target".into());
            }
        }
        for rule in graph::rules(program) {
            if let Some(pb::rule::Kind::Rewrite(rewrite)) = &rule.kind
                && rewrite.subsume
            {
                let lhs = program
                    .nodes
                    .get(rewrite.lhs as usize)
                    .ok_or("rewrite lhs out of bounds")?;
                let Some(pb::node::Kind::Call(call)) = &lhs.kind else {
                    return Err("subsuming rewrite lhs must be a constructor call".into());
                };
                if !signatures
                    .get(&call.func)
                    .is_some_and(|(_, subtype)| *subtype == Some(ast::FunctionSubtype::Constructor))
                {
                    return Err("subsuming rewrite lhs must be a constructor call".into());
                }
            }
        }
        let mut context = RequestOccurrences {
            request: staged.request,
            registry: self.registry.clone(),
            native_spans,
            scoped_actions,
            action_dags,
            extraction_dags,
            files: program.files.clone(),
            ..Default::default()
        };
        // Setup already compiled on this context. Compile every rule literal
        // and command, including unentered loop bodies, without replaying it.
        context.selection = format!("__protobuf_validation_{}", staged.request);
        let mut validation = vec![Command::AddRuleset(
            ast::Span::Panic,
            context.selection.clone(),
        )];
        let mut offset = 0;
        for (site, value) in rules::collections(program) {
            let end = offset + value.rules.len();
            context.candidate_offsets.insert(site, offset..end);
            offset = end;
        }
        for (index, (rule, authored_rule)) in graph::rules(program)
            .zip(graph::rules(&authored_input))
            .enumerate()
        {
            let name = format!("__protobuf_{}_rule_{index}", staged.request);
            let holder = format!("{name}_holder");
            let mut commands = vec![Command::AddRuleset(
                native_span(program, rule.span.as_ref(), &context.native_spans)?,
                holder.clone(),
            )];
            commands.extend(
                lower_rule(
                    program,
                    rule,
                    &holder,
                    &name,
                    &context.native_spans,
                    |name| {
                        staged.graph.authoring_type_info().is_global(name)
                            || staged.graph.get_sort_by_name(name).is_some()
                            || staged
                                .graph
                                .authoring_type_info()
                                .get_func_type(name)
                                .is_some()
                            || staged.graph.authoring_type_info().is_primitive(name)
                    },
                )?
                .into_iter()
                .map(|command| lower_rule_cost_deletes(command, &constructor_targets, self.mode)),
            );
            validation.extend(commands.clone());
            let record = graph::rule(&authored_input, authored_rule)?;
            let key = graph::rule_key(&record)?;
            context.candidates.push(rules::Candidate {
                key,
                record: Arc::new(graph::RuleRecord {
                    program: record,
                    files: rule_files.clone(),
                }),
                name,
                commands,
            });
        }
        let mut schedulers: HashSet<_> = self
            .graph
            .extension_state::<PermanentSchedulerState>()
            .into_iter()
            .flat_map(|state| state.keys().cloned())
            .collect();
        let mut conditions = vec![];
        for (index, command) in program.commands.iter().enumerate() {
            native_span(program, command.span.as_ref(), &context.native_spans)?;
            validation.extend(staged.validate_control(
                program,
                command,
                &context,
                &mut schedulers,
                false,
                &mut conditions,
                &[index as u32],
            )?);
        }
        staged
            .graph
            .compile_program_observed(validation, &mut |_, _| {})
            .map_err(|error| error.to_string())?;
        for (span, facts) in conditions {
            staged
                .graph
                .compile_condition(span, facts)
                .map_err(|error| error.to_string())?;
        }
        let mut values = HashMap::new();
        for (path, action) in action_sites(&program.commands) {
            if context.scoped_actions.contains(&path) && !context.action_dags.contains_key(&path) {
                eval_scoped_action(
                    &mut staged.graph,
                    program,
                    action,
                    &mut values,
                    false,
                    context.action_dags.get(&path),
                    &mut |_| {},
                    &context.native_spans,
                )
                .map_err(|error| error.to_string())?;
            }
        }
        for command in command_tree(&program.commands) {
            if let Some(pb::command::Kind::Extract(extract)) = &command.kind {
                for root in &extract.roots {
                    if let Some(closed) = context.extraction_dags.get(root) {
                        eval_extract_root(
                            &mut staged.graph,
                            program,
                            *root,
                            Some(closed),
                            false,
                            &context.native_spans,
                        )
                        .map_err(|error| error.to_string())?;
                    }
                }
            }
        }
        // Model metadata sees the same fully compiled context. The graph
        // remains disposable and never enters Prepared.
        for command in command_tree(&program.commands) {
            let (model, extractor) = match &command.kind {
                Some(pb::command::Kind::Extract(extract)) => {
                    (&extract.cost_model, extract.extractor)
                }
                Some(pb::command::Kind::KeepBest(keep)) => (&keep.cost_model, keep.extractor),
                _ => continue,
            };
            if !model.is_empty() {
                staged
                    .resolve_cost_model(model, extractor)
                    .map_err(|mut error| {
                        error.0.span = command.span;
                        error
                    })?;
            }
        }
        // Only rendering needs the filtered declaration view. All runtime sites
        // above were captured against the original submitted indices.
        program.declarations = std::mem::take(&mut program.declarations)
            .into_iter()
            .zip(added)
            .filter_map(|(declaration, added)| added.then_some(declaration))
            .collect();
        Ok(Prepared {
            definitions: staged.definitions,
            request: staged.request,
            installations,
            materialized,
            pending_declarations,
            context,
            bindings: program.rulesets.clone(),
        })
    }

    fn lower_command<'a>(
        &self,
        program: &pb::Program,
        command: &'a pb::Command,
        context: &RequestOccurrences,
        sites: &mut ScheduleSites<'a>,
    ) -> Result<Vec<Command>, PreparationError> {
        if matches!(
            command.kind,
            Some(
                pb::command::Kind::Run(_)
                    | pb::command::Kind::Check(_)
                    | pb::command::Kind::Stats(_)
                    | pb::command::Kind::TableSizes(_)
            )
        ) {
            return lower_native_observation(&self.graph, program, command, context, sites);
        }
        let span = native_span(program, command.span.as_ref(), &context.native_spans)?;
        let command = match command.kind.as_ref().ok_or("missing command kind")? {
            pb::command::Kind::Fail(child) => {
                if !matches!(
                    &child.kind,
                    Some(
                        pb::command::Kind::Fail(_)
                            | pb::command::Kind::Action(_)
                            | pb::command::Kind::Check(_)
                            | pb::command::Kind::Prove(_)
                            | pb::command::Kind::ProveExists(_)
                            | pb::command::Kind::Run(_)
                            | pb::command::Kind::Loop(_)
                            | pb::command::Kind::Stats(_)
                            | pb::command::Kind::TableSizes(_)
                    )
                ) {
                    return Err("Fail requires a supported native command; observation wrappers are not implemented".into());
                }
                let [child]: [Command; 1] = self
                    .lower_command(program, child, context, sites)?
                    .try_into()
                    .map_err(|_| "Fail requires exactly one native command")?;
                Command::Fail(span, Box::new(child))
            }
            pb::command::Kind::Action(action) => {
                return Ok(lower_action(program, action, &context.native_spans)?
                    .into_iter()
                    .map(Command::Action)
                    .collect());
            }
            pb::command::Kind::Prove(prove) => Command::Prove(
                span,
                facts(program, &prove.facts, &context.native_spans, None, |name| {
                    self.graph.authoring_type_info().is_global(name)
                        || self.graph.get_sort_by_name(name).is_some()
                        || self
                            .graph
                            .authoring_type_info()
                            .get_func_type(name)
                            .is_some()
                        || self.graph.authoring_type_info().is_primitive(name)
                })?
                .0,
            ),
            pb::command::Kind::ProveExists(prove) => {
                let name = self
                    .names
                    .callables
                    .get(&prove.constructor)
                    .ok_or_else(|| {
                        PreparationError(Box::new(pb::Error {
                            code: pb::ErrorCode::RuntimeFailure.into(),
                            message: format!("unknown constructor {}", prove.constructor),
                            span: command.span,
                            ..Default::default()
                        }))
                    })?;
                if !self.definitions.declarations.iter().any(|d| matches!(&d.kind, Some(pb::declaration::Kind::Constructor(c)) if &c.name == name)) {
                    return Err("prove-exists requires a constructor".into());
                }
                Command::ProveExists(span, prove.constructor.clone())
            }
            pb::command::Kind::Extract(extract) => {
                if self.mode != pb::ExecutionMode::Normal {
                    return Err(
                        "encoded-mode extraction requires native observation support".into(),
                    );
                }
                if extract.roots.is_empty()
                    || extract.variants == 0
                    || !matches!(
                        pb::Extractor::try_from(extract.extractor),
                        Ok(pb::Extractor::Tree | pb::Extractor::GreedyDag)
                    )
                {
                    return Err("extraction requires roots, a positive variant count, and a specified extractor".into());
                }
                return extract
                    .roots
                    .iter()
                    .filter(|index| !context.extraction_dags.contains_key(*index))
                    .map(|index| {
                        Ok(Command::Action(Action::Expr(
                            span.clone(),
                            expression(
                                program,
                                *index,
                                &mut HashSet::new(),
                                &context.native_spans,
                            )?,
                        )))
                    })
                    .collect();
            }
            pb::command::Kind::KeepBest(keep) => {
                if self.mode != pb::ExecutionMode::Normal {
                    return Err("encoded-mode KeepBest is not supported".into());
                }
                if keep.tables.is_empty()
                    || keep.tables.iter().any(String::is_empty)
                    || !matches!(
                        pb::Extractor::try_from(keep.extractor),
                        Ok(pb::Extractor::Tree | pb::Extractor::GreedyDag)
                    )
                {
                    return Err("KeepBest requires tables and a specified extractor".into());
                }
                for table in &keep.tables {
                    let logical = self.names.callables.get(table);
                    if !self.definitions.declarations.iter().any(|declaration| {
                        match &declaration.kind {
                            Some(pb::declaration::Kind::Constructor(row)) => {
                                logical == Some(&row.name)
                            }
                            Some(pb::declaration::Kind::Function(row)) => {
                                logical == Some(&row.name)
                            }
                            Some(pb::declaration::Kind::Relation(row)) => {
                                logical == Some(&row.name)
                            }
                            _ => false,
                        }
                    }) {
                        return Err(PreparationError(Box::new(pb::Error {
                            code: pb::ErrorCode::RuntimeFailure.into(),
                            message: format!("unknown table {table}"),
                            span: command.span,
                            ..Default::default()
                        })));
                    }
                }
                return Ok(vec![]);
            }
            pb::command::Kind::TableRows(print) => {
                if print.table.is_empty() {
                    return Err("table name must not be empty".into());
                }
                let logical = self.names.callables.get(&print.table).ok_or_else(|| {
                    PreparationError(Box::new(pb::Error {
                        code: pb::ErrorCode::RuntimeFailure.into(),
                        message: format!("unknown table {}", print.table),
                        span: command.span,
                        ..Default::default()
                    }))
                })?;
                stored_table_signature(&self.definitions, logical)?;
                return Ok(vec![]);
            }
            pb::command::Kind::Freeze(_) | pb::command::Kind::Explain(_) => return Ok(vec![]),
            _ => {
                return Err(
                    "this command kind is not supported by the initial byte adapter".into(),
                );
            }
        };
        Ok(vec![command])
    }

    // Compile every admitted descendant, even in Repeat0, without executing
    // bindings, queries or scheduler state on a disposable compiler clone.
    #[allow(clippy::too_many_arguments)]
    fn validate_control(
        &mut self,
        program: &pb::Program,
        command: &pb::Command,
        context: &RequestOccurrences,
        schedulers: &mut HashSet<String>,
        in_loop: bool,
        conditions: &mut Vec<(ast::Span, Vec<Fact>)>,
        path: &[u32],
    ) -> Result<Vec<Command>, PreparationError> {
        let span = native_span(program, command.span.as_ref(), &context.native_spans)?;
        match command.kind.as_ref().ok_or("missing command kind")? {
            pb::command::Kind::BindScheduler(bind) => {
                wire_back_off(bind)?;
                if !schedulers.insert(bind.name.clone()) {
                    return Err(format!("scheduler {} already exists", bind.name).into());
                }
                Ok(vec![])
            }
            pb::command::Kind::Run(run) => {
                if !run.scheduler.is_empty() && !schedulers.contains(&run.scheduler) {
                    return Err(PreparationError(Box::new(pb::Error {
                        code: pb::ErrorCode::RuntimeFailure.into(),
                        message: format!("unknown scheduler {}", run.scheduler),
                        span: command.span,
                        ..Default::default()
                    })));
                }
                self.lower_command(program, command, context, &mut HashMap::new())
            }
            pb::command::Kind::Loop(body) => {
                let (body, until) = (&body.body, &body.until);
                let mut commands = vec![];
                if !until.is_empty() {
                    conditions.push((
                        span,
                        facts(program, until, &context.native_spans, None, |name| {
                            self.graph.authoring_type_info().is_global(name)
                                || self.graph.get_sort_by_name(name).is_some()
                                || self
                                    .graph
                                    .authoring_type_info()
                                    .get_func_type(name)
                                    .is_some()
                                || self.graph.authoring_type_info().is_primitive(name)
                        })?
                        .0,
                    ));
                }
                let mut nested = schedulers.clone();
                for (index, child) in body.iter().enumerate() {
                    let mut child_path = path.to_vec();
                    child_path.push(index as u32);
                    commands.extend(self.validate_control(
                        program,
                        child,
                        context,
                        &mut nested,
                        true,
                        conditions,
                        &child_path,
                    )?);
                }
                Ok(commands)
            }
            pb::command::Kind::Fail(child)
                if control_command(child)
                    || context.scoped_actions.contains(path)
                    || in_loop
                        && matches!(
                            &child.kind,
                            Some(
                                pb::command::Kind::Action(_)
                                    | pb::command::Kind::Fail(_)
                                    | pb::command::Kind::Check(_)
                                    | pb::command::Kind::Stats(_)
                                    | pb::command::Kind::TableSizes(_)
                            )
                        ) =>
            {
                self.validate_control(
                    program, child, context, schedulers, in_loop, conditions, path,
                )
            }
            pb::command::Kind::Action(action) if context.action_dags.contains_key(path) => {
                Ok(vec![Command::ActionScope(
                    span,
                    ast::GenericActions(
                        action_dag_actions(
                            program,
                            action,
                            |name| {
                                self.graph.type_info().is_global(name)
                                    || self.graph.get_sort_by_name(name).is_some()
                                    || self.graph.type_info().get_func_type(name).is_some()
                                    || self.graph.type_info().is_primitive(name)
                            },
                            &context.native_spans,
                            &mut HashMap::new(),
                            &mut 0,
                        )?
                        .0,
                    ),
                )])
            }
            pb::command::Kind::Action(_) if context.scoped_actions.contains(path) => Ok(vec![]),
            pb::command::Kind::Action(_) => {
                self.lower_command(program, command, context, &mut HashMap::new())
            }
            pb::command::Kind::Check(_)
            | pb::command::Kind::Stats(_)
            | pb::command::Kind::TableSizes(_)
                if !in_loop || self.mode == pb::ExecutionMode::Normal =>
            {
                self.lower_command(program, command, context, &mut HashMap::new())
            }
            pb::command::Kind::Freeze(_) | pb::command::Kind::Explain(_)
                if self.mode == pb::ExecutionMode::Normal =>
            {
                Ok(vec![])
            }
            _ if in_loop => {
                Err("loop body command has no supported native mutation-progress witness".into())
            }
            _ => self.lower_command(program, command, context, &mut HashMap::new()),
        }
    }

    fn lower_run<'a>(
        program: &pb::Program,
        command: &'a pb::Command,
        context: &RequestOccurrences,
        sites: &mut ScheduleSites<'a>,
    ) -> Result<ast::Schedule, PreparationError> {
        let span = native_span(program, command.span.as_ref(), &context.native_spans)?;
        sites.insert(vec![], (command, vec![]));
        match command.kind.as_ref().ok_or("missing schedule command")? {
            pb::command::Kind::Run(_) => {
                let native = &context.selection;
                Ok(ast::Schedule::Run(
                    span,
                    ast::RunConfig {
                        ruleset: native.clone(),
                        until: None,
                    },
                ))
            }
            _ => Err("expected Run leaf".into()),
        }
    }

    // Keep the authored site, failure prefix and synchronous output sink explicit.
    #[allow(clippy::too_many_arguments)]
    fn execute(
        &mut self,
        program: &pb::Program,
        command: &pb::Command,
        context: &mut RequestOccurrences,
        location: &pb::CommandLocation,
        response: &mut pb::RunProgramOutput,
        failure_site: &mut Option<ExecutionFailureSite>,
        stream: &mut OutputStream<'_>,
    ) -> Result<(), egglog::Error> {
        let output = match command.kind.as_ref().unwrap() {
            pb::command::Kind::Fail(child) if context.scoped_actions.contains(&location.path) => {
                let result = self.execute(
                    program,
                    child,
                    context,
                    location,
                    response,
                    failure_site,
                    stream,
                );
                *failure_site = None;
                if result.is_ok() {
                    return Err(egglog::Error::ExpectFail(
                        native_span(program, command.span.as_ref(), &context.native_spans)
                            .expect("validated span"),
                    ));
                }
                None
            }
            kind if control_command(command)
                || matches!(kind, pb::command::Kind::BindScheduler(_)) =>
            {
                let measurements = RefCell::new(ScheduleMeasurements::default());
                let mut anchor = command;
                let mut fail_spans = vec![];
                while let Some(pb::command::Kind::Fail(child)) = &anchor.kind {
                    fail_spans.push(
                        native_span(program, anchor.span.as_ref(), &context.native_spans)
                            .expect("validated span"),
                    );
                    anchor = child;
                }
                let mut envelope = WireEnvelope {
                    mode: self.mode,
                    names: &self.names,
                    program,
                    context,
                    response,
                    root: location,
                    stream,
                    definitions: &self.definitions,
                    extension: self.extension.as_ref(),
                    measurements: &measurements,
                    export_error: None,
                    suppressed: !fail_spans.is_empty(),
                    anchor,
                    bindings: vec![],
                    partial: ControlReport::default(),
                };
                let result = if matches!(kind, pb::command::Kind::BindScheduler(_)) {
                    envelope.execute(&mut self.graph).map(|_| ())
                } else {
                    self.graph.with_schedule_envelope(
                        &fail_spans,
                        &mut envelope,
                        |graph, state| state.execute(graph),
                        |state, report| state.complete(report),
                        |state, event| {
                            state.measurements.borrow_mut().observe(
                                event,
                                state.mode,
                                Some(state.root),
                                &HashMap::new(),
                            )
                        },
                    )
                };
                let result = result.and_then(|()| envelope.export_error.take().map_or(Ok(()), Err));
                let measurements = measurements.into_inner();
                *failure_site = measurements.failure.clone();
                result?;
                None
            }
            pb::command::Kind::Freeze(_) => {
                Some(pb::command_output::Kind::Snapshot(freeze::export(
                    freeze::View {
                        graph: &self.graph,
                        names: &self.names,
                        definitions: &self.definitions,
                        mode: self.mode,
                        extension: self.extension.as_ref(),
                    },
                    &context.registry,
                )?))
            }
            pb::command::Kind::Explain(explain) => Some(pb::command_output::Kind::Diagnostic(
                report::explain(&self.graph, &context.registry, &explain.groups)?,
            )),
            pb::command::Kind::Action(action)
                if context.scoped_actions.contains(&location.path) =>
            {
                let mut measurements = ScheduleMeasurements::default();
                let result = eval_scoped_action(
                    &mut self.graph,
                    program,
                    action,
                    &mut context.union_values,
                    true,
                    context.action_dags.get(&location.path),
                    &mut |event| {
                        measurements.observe(event, self.mode, Some(location), &HashMap::new())
                    },
                    &context.native_spans,
                );
                *failure_site = measurements.failure.clone();
                result?;
                None
            }
            pb::command::Kind::Extract(extract) if !extract.cost_model.is_empty() => {
                Some(pb::command_output::Kind::Extraction(
                    self.extract_host_model(program, extract, response, context)?,
                ))
            }
            pb::command::Kind::Extract(extract) => {
                let roots = extract
                    .roots
                    .iter()
                    .map(|index| {
                        eval_extract_root(
                            &mut self.graph,
                            program,
                            *index,
                            context.extraction_dags.get(index),
                            true,
                            &context.native_spans,
                        )
                        .map(|root| root.expect("executed extraction root"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let mut encoded = HashMap::new();
                let model = crate::set_cost::CheckedDynamicCostModel::for_root_sorts(
                    &self.graph,
                    roots.iter().map(|(sort, _)| sort.clone()).collect(),
                )?;
                let observe = |terms: &TermDag,
                               term: TermId,
                               sort: &ArcSort,
                               value: Value,
                               children: &[u32]| {
                    encode_term(
                        self,
                        terms,
                        term,
                        sort,
                        value,
                        children,
                        response,
                        &mut encoded,
                    )
                };
                let variants = usize::try_from(extract.variants).map_err(|_| {
                    egglog::Error::ExtractError("variant count exceeds native usize".into())
                })?;
                let (extracted, nodes) = if extract.extractor == i32::from(pb::Extractor::GreedyDag)
                {
                    crate::greedy_dag_extract::extract_variants_greedy_dag_with_observer(
                        &self.graph,
                        roots,
                        variants,
                        model,
                        observe,
                    )?
                } else {
                    self.graph.extract_variants_with_cost_model_and_observer(
                        roots,
                        variants,
                        egglog::extract::TreeCostModelFromDag(model),
                        observe,
                    )?
                };
                let mut output = pb::ExtractResult::default();
                for (variants, nodes) in extracted.variants.iter().zip(nodes) {
                    let mut root = pb::ExtractedRoot::default();
                    for (variant, term) in variants.iter().zip(nodes) {
                        let cost = i64::try_from(&variant.cost).map_err(|_| {
                            egglog::Error::ExtractError(
                                "default extraction objective is outside its declared i64 result domain".into(),
                            )
                        })?;
                        let cost_sort = encode_sort(
                            &self.graph,
                            &self.names,
                            &self.graph.get_sort_by_name("i64").unwrap().clone(),
                            response,
                        )?;
                        let cost_index = response.nodes.len() as u32;
                        response.nodes.push(pb::Node {
                            sort_id: cost_sort,
                            kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                                value: Some(pb::primitive_value::Value::I64(cost)),
                            })),
                            ..Default::default()
                        });
                        root.variants.push(pb::ExtractedTerm {
                            term,
                            cost: Some(cost_index),
                        });
                    }
                    output.roots.push(root);
                }
                Some(pb::command_output::Kind::Extraction(output))
            }
            pb::command::Kind::KeepBest(keep) if !keep.cost_model.is_empty() => {
                self.keep_best_host_model(keep)?;
                None
            }
            pb::command::Kind::KeepBest(keep) => {
                crate::keep_best::keep_best_with_cost_model(
                    &mut self.graph,
                    &keep.tables,
                    keep.extractor == i32::from(pb::Extractor::GreedyDag),
                    |graph, roots| {
                        crate::set_cost::CheckedDynamicCostModel::for_root_sorts(
                            graph,
                            roots.iter().map(|(sort, _)| sort.clone()).collect(),
                        )
                    },
                    |cost| {
                        i64::try_from(cost).map(|_| ()).map_err(|_| {
                            egglog::Error::ExtractError(
                                "default extraction objective is outside its declared i64 result domain".into(),
                            )
                        })
                    },
                )?;
                None
            }
            pb::command::Kind::TableRows(print) => {
                let logical = self
                    .names
                    .callables
                    .get(&print.table)
                    .unwrap_or(&print.table);
                let (expected_inputs, expected_output) =
                    stored_table_signature(&self.definitions, logical)
                        .map_err(egglog::Error::ExtractError)?;
                let relation = expected_output.is_none();
                let mut rows: Vec<(Vec<Value>, Value, bool)> = vec![];
                let (input_sorts, output_sort) = if self.mode == pb::ExecutionMode::Normal {
                    let function = self.graph.get_function(&print.table).unwrap();
                    if crate::table_rows::is_constructor(&self.graph, &print.table)? {
                        self.graph.constructor_enodes(&print.table, |row| {
                            rows.push((row.children.to_vec(), row.eclass, row.subsumed))
                        })?;
                    } else {
                        self.graph.function_entries(&print.table, |row| {
                            rows.push((row.inputs.to_vec(), row.output, row.subsumed))
                        })?;
                    }
                    (
                        function.func_type().input.clone(),
                        function.func_type().output.clone(),
                    )
                } else {
                    // Encoded term tables retain history and can have private
                    // result columns. Only their metadata-linked live views
                    // contain the logical rows requested by this command.
                    let mut views = self.graph.functions_iter().filter(|(_, function)| {
                        function.term_constructor() == Some(print.table.as_str())
                    });
                    let (_, view) = views.next().ok_or_else(|| {
                        egglog::Error::ExtractError("encoded table has no native view".into())
                    })?;
                    if views.next().is_some()
                        || view.func_type().input.len() != expected_inputs.len() + 1
                    {
                        return Err(egglog::Error::ExtractError(
                            "encoded table view signature is incompatible".into(),
                        ));
                    }
                    let input_sorts = view.func_type().input[..expected_inputs.len()].to_vec();
                    let output_sort = view.func_type().input.last().unwrap().clone();
                    let mut checked_sorts = vec![];
                    let mut exported = pb::RunProgramOutput::default();
                    for (sort, expected) in input_sorts
                        .iter()
                        .chain(expected_output.map(|_| &output_sort))
                        .zip(
                            expected_inputs
                                .iter()
                                .map(|arg| arg.sort)
                                .chain(expected_output),
                        )
                    {
                        let expected = crate::builtin::import_sort(
                            &self.definitions.sorts,
                            expected,
                            &mut checked_sorts,
                        )
                        .map_err(egglog::Error::ExtractError)?;
                        let actual = encode_sort(&self.graph, &self.names, sort, &mut exported)?;
                        let actual = crate::builtin::import_sort(
                            &exported.sorts,
                            actual,
                            &mut checked_sorts,
                        )
                        .map_err(egglog::Error::ExtractError)?;
                        if actual != expected {
                            return Err(egglog::Error::ExtractError(
                                "encoded table view column sort mismatch".into(),
                            ));
                        }
                    }
                    let limit = print.max_rows.map_or(usize::MAX, |limit| {
                        usize::try_from(limit).unwrap_or(usize::MAX)
                    });
                    if limit != 0 {
                        self.graph.function_entries_while(view.name(), |row| {
                            let (value, args) =
                                row.inputs.split_last().expect("validated view signature");
                            rows.push((args.to_vec(), *value, row.subsumed));
                            rows.len() < limit
                        })?;
                    }
                    (input_sorts, output_sort)
                };
                if let Some(max_rows) = print.max_rows {
                    rows.truncate(usize::try_from(max_rows).unwrap_or(usize::MAX));
                }
                let roots = rows
                    .iter()
                    .flat_map(|(args, value, _)| {
                        args.iter()
                            .zip(&input_sorts)
                            .map(|(value, sort)| (sort.clone(), *value))
                            // A relation's native row class is not a value in
                            // the public IR. Observe inputs only, never extract
                            // or encode that hidden class or its private sort.
                            .chain((!relation).then(|| (output_sort.clone(), *value)))
                    })
                    .collect();
                let mut encoded = HashMap::new();
                let (_, nodes) = self.graph.extract_best_with_cost_model_and_observer(
                    roots,
                    egglog::extract::DEFAULT_COST_MODEL,
                    |terms, term, sort, value, children| {
                        encode_term(
                            self,
                            terms,
                            term,
                            sort,
                            value,
                            children,
                            response,
                            &mut encoded,
                        )
                    },
                )?;
                let mut terms = nodes.iter();
                let mut output = pb::TableRows {
                    table: self
                        .names
                        .callables
                        .get(&print.table)
                        .unwrap_or(&print.table)
                        .clone(),
                    rows: vec![],
                };
                let relation_output = if relation && !rows.is_empty() {
                    let unit = self.graph.get_sort_by_name("Unit").unwrap();
                    let sort_id = encode_sort(&self.graph, &self.names, unit, response)?;
                    let term = response.nodes.len() as u32;
                    response.nodes.push(pb::Node {
                        sort_id,
                        kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                            value: Some(pb::primitive_value::Value::Unit(pb::Unit {})),
                        })),
                        ..Default::default()
                    });
                    Some(pb::TableCell {
                        kind: Some(pb::table_cell::Kind::Term(term)),
                    })
                } else {
                    None
                };
                for (_, _, subsumed) in rows {
                    let mut cells = vec![];
                    for sort in input_sorts
                        .iter()
                        .chain((!relation).then_some(&output_sort))
                    {
                        let kind = match terms.next().unwrap() {
                            Some(term) => pb::table_cell::Kind::Term(*term),
                            None => pb::table_cell::Kind::UnavailableSort(encode_sort(
                                &self.graph,
                                &self.names,
                                sort,
                                response,
                            )?),
                        };
                        cells.push(pb::TableCell { kind: Some(kind) });
                    }
                    let output_cell = if relation {
                        relation_output.unwrap()
                    } else {
                        cells.pop().unwrap()
                    };
                    output.rows.push(pb::FunctionRow {
                        args: cells,
                        output: Some(output_cell),
                        subsumed,
                    });
                }
                Some(pb::command_output::Kind::TableRows(output))
            }
            _ => {
                let mut sites = HashMap::new();
                let commands = self
                    .lower_command(program, command, context, &mut sites)
                    .expect("validated command");
                let (result, _, failure) = NativeExecutor {
                    graph: &mut self.graph,
                    mode: self.mode,
                    names: &self.names,
                }
                .run_observed(
                    commands,
                    Some(RequestedObservation {
                        command,
                        location,
                        sites: &sites,
                    }),
                    context,
                    response,
                    None,
                );
                *failure_site = failure;
                result?;
                None
            }
        };
        if let Some(kind) = output {
            response.outputs.push(pb::CommandOutput {
                kind: Some(kind),
                location: Some(location.clone()),
            });
        }
        stream.flush(response, context)
    }
}

struct NativeExecutor<'a> {
    graph: &'a mut EGraph,
    mode: pb::ExecutionMode,
    names: &'a NativeNames,
}

#[derive(Clone, Copy)]
struct RequestedObservation<'a> {
    command: &'a pb::Command,
    location: &'a pb::CommandLocation,
    sites: &'a ScheduleSites<'a>,
}

struct ScheduleCapture<'a> {
    measurements: &'a RefCell<ScheduleMeasurements>,
    scheduler: Option<egglog::scheduler::SchedulerId>,
    report: &'a mut Option<egglog_reports::RunReport>,
    emit_outputs: bool,
}

impl NativeExecutor<'_> {
    // Aggregate leaves synchronously, before native schedule union, and publish
    // each requested anchor immediately. No leaf-event history or outer timings
    // are synthesized; failure cannot erase a completed output or pretend to be zero.
    fn run_observed(
        &mut self,
        commands: Vec<Command>,
        requested: Option<RequestedObservation<'_>>,
        context: &mut RequestOccurrences,
        response: &mut pb::RunProgramOutput,
        control: Option<ScheduleCapture<'_>>,
    ) -> (
        Result<(), egglog::Error>,
        bool,
        Option<ExecutionFailureSite>,
    ) {
        let location = requested.map(|requested| requested.location);
        let empty_sites = HashMap::new();
        let sites = requested.map_or(&empty_sites, |requested| requested.sites);
        let selected_sizes = requested.and_then(|requested| match &requested.command.kind {
            Some(pb::command::Kind::TableSizes(print)) => Some(print),
            _ => None,
        });
        let mut pending_sizes = vec![];
        let owned_measurements = RefCell::new(ScheduleMeasurements::default());
        let (measurements, scheduler, mut captured, emit_outputs) = match control {
            Some(ScheduleCapture {
                measurements,
                scheduler,
                report,
                emit_outputs,
            }) => (measurements, scheduler, Some(report), emit_outputs),
            None => (&owned_measurements, None, None, true),
        };
        let embedded = captured.is_some();
        let mut registered = false;
        let mut actions_observed = false;
        let mut actions_changed = false;
        let mut export_error = None;
        let mut output = |cause: usize, origin, output| {
            if origin != ExecutionOrigin::Requested {
                return;
            }
            if !emit_outputs && !matches!(&output, egglog::CommandOutput::RunSchedule(_)) {
                return;
            }
            let Some(location) = location else {
                return;
            };
            let mut run_report = None;
            let kind = match output {
                egglog::CommandOutput::RunSchedule(report) => {
                    if let Some(captured) = captured.as_mut() {
                        **captured = Some(report);
                        return;
                    }
                    if context.diagnostics {
                        match report::export(&report) {
                            Ok(detail) => run_report = Some(detail),
                            Err(error) => {
                                export_error = Some(egglog::Error::BackendError(error));
                                return;
                            }
                        }
                    }
                    pb::command_output::Kind::Run(pb::RunResult {
                        updated: report.updated,
                        can_stop: report.can_stop,
                    })
                }
                sizes @ (egglog::CommandOutput::PrintFunctionSize(_)
                | egglog::CommandOutput::PrintAllFunctionsSize(_)) => {
                    let Some(print) = selected_sizes else {
                        return;
                    };
                    let tables = match sizes {
                        egglog::CommandOutput::PrintFunctionSize(rows) => {
                            pending_sizes.push((print.tables[cause].clone(), rows));
                            if cause + 1 != print.tables.len() {
                                return;
                            }
                            std::mem::take(&mut pending_sizes)
                        }
                        egglog::CommandOutput::PrintAllFunctionsSize(tables) => {
                            let mut tables: Vec<_> = tables
                                .into_iter()
                                .filter_map(|(name, rows)| {
                                    self.names
                                        .callables
                                        .get(&name)
                                        .map(|name| (name.clone(), rows))
                                })
                                .collect();
                            tables.sort_by(|(a, _), (b, _)| a.cmp(b));
                            tables
                        }
                        _ => unreachable!(),
                    };
                    let sizes = tables
                        .into_iter()
                        .map(|(table, rows)| {
                            Ok(pb::TableSize {
                                table,
                                rows: u64::try_from(rows)?,
                            })
                        })
                        .collect::<Result<Vec<_>, std::num::TryFromIntError>>();
                    match sizes {
                        Ok(sizes) => pb::command_output::Kind::Sizes(pb::TableSizes { sizes }),
                        Err(_) => {
                            export_error = Some(egglog::Error::BackendError(
                                "native table size exceeds uint64".into(),
                            ));
                            return;
                        }
                    }
                }
                egglog::CommandOutput::OverallStatistics(report) => match report::export(&report) {
                    Ok(detail) => pb::command_output::Kind::Diagnostic(detail),
                    Err(error) => {
                        export_error = Some(egglog::Error::BackendError(error));
                        return;
                    }
                },
                egglog::CommandOutput::ProveExists {
                    proof_store,
                    proof_id,
                } => match proof::export(&proof_store, proof_id) {
                    Ok(proof) => pb::command_output::Kind::Proof(proof),
                    Err(error) => {
                        export_error = Some(egglog::Error::BackendError(error));
                        return;
                    }
                },
                _ => return,
            };
            response.outputs.push(pb::CommandOutput {
                kind: Some(kind),
                location: Some(location.clone()),
            });
            if let Some(diagnostic) = run_report {
                response.outputs.push(pb::CommandOutput {
                    kind: Some(pb::command_output::Kind::Diagnostic(diagnostic)),
                    location: Some(location.clone()),
                });
            }
        };
        let mut observe = |_: usize, event: ExecutionEvent<'_>| {
            if let ExecutionEvent::ActionsFinished { changed, .. } = event {
                actions_observed = true;
                actions_changed |= changed;
            }
            if matches!(
                event,
                ExecutionEvent::CommandCompleted {
                    origin: ExecutionOrigin::Requested,
                    ..
                }
            ) {
                registered = true;
            }
            measurements
                .borrow_mut()
                .observe(event, self.mode, location, sites);
        };
        let mut result = if embedded {
            self.graph.run_program_embedded_observed(
                commands,
                &mut output,
                &mut observe,
                &|_, _| scheduler,
            )
        } else {
            self.graph.run_program_observed_with_policies(
                commands,
                &mut output,
                &mut observe,
                &|_, _| RepeatContinuation::CanStop,
                &|_, _| scheduler,
            )
        };
        if let (
            Err(egglog::Error::TypeError(egglog::TypeError::UnboundFunction(name, _))),
            Some(print),
        ) = (&mut result, selected_sizes)
            && let Some(authored) = print
                .tables
                .iter()
                .find(|table| native_name("call", table) == *name)
        {
            *name = authored.clone();
        }
        if matches!(result, Err(egglog::Error::ExpectFail(_))) {
            measurements.borrow_mut().failure = None;
        }
        let failure = measurements.borrow().failure.clone();
        if actions_observed && let Some(captured) = captured.as_mut() {
            let report = captured.get_or_insert_with(Default::default);
            report.updated |= actions_changed;
            report.can_stop &= !actions_changed;
        }
        (
            result.and_then(|()| export_error.map_or(Ok(()), Err)),
            registered,
            failure,
        )
    }
}

impl ScheduleMeasurements {
    fn observe(
        &mut self,
        event: ExecutionEvent<'_>,
        _mode: pb::ExecutionMode,
        location: Option<&pb::CommandLocation>,
        sites: &ScheduleSites<'_>,
    ) {
        match event {
            ExecutionEvent::ActionsFinished { changed, .. } => self.changed |= changed,
            ExecutionEvent::RunFinished {
                result: Ok(report), ..
            } => self.changed |= report.updated,
            ExecutionEvent::CommandCompleted {
                origin: ExecutionOrigin::Requested,
                ..
            } => self.failure = None,
            ExecutionEvent::RunFinished {
                schedule,
                result: Err(_),
                ..
            } if self.failure.is_none() => {
                self.failure = schedule.and_then(|schedule| {
                    let (command, path) = sites.get(schedule.path)?;
                    let mut nested = location?.clone();
                    nested.path.extend(path);
                    nested
                        .iterations
                        .extend(schedule.iterations.iter().map(|i| *i as u64));
                    Some((nested, command.span))
                });
            }
            _ => (),
        }
    }
}

fn control_command(command: &pb::Command) -> bool {
    match &command.kind {
        Some(pb::command::Kind::Run(_) | pb::command::Kind::Loop(_)) => true,
        Some(pb::command::Kind::Fail(child)) => control_command(child),
        _ => false,
    }
}

fn lower_native_observation<'a>(
    graph: &EGraph,
    program: &pb::Program,
    command: &'a pb::Command,
    context: &RequestOccurrences,
    sites: &mut ScheduleSites<'a>,
) -> Result<Vec<Command>, PreparationError> {
    let span = native_span(program, command.span.as_ref(), &context.native_spans)?;
    Ok(match command.kind.as_ref().ok_or("missing command kind")? {
        pb::command::Kind::Run(_) => vec![Command::RunSchedule(Session::lower_run(
            program, command, context, sites,
        )?)],
        pb::command::Kind::Check(check) => {
            vec![Command::Check(
                span,
                facts(program, &check.facts, &context.native_spans, None, |name| {
                    graph.authoring_type_info().is_global(name)
                        || graph.get_sort_by_name(name).is_some()
                        || graph.authoring_type_info().get_func_type(name).is_some()
                        || graph.authoring_type_info().is_primitive(name)
                })?
                .0,
            )]
        }
        pb::command::Kind::Stats(_) => vec![Command::PrintOverallStatistics(span, None)],
        pb::command::Kind::TableSizes(print) => {
            if print.tables.iter().any(String::is_empty) {
                return Err("table name must not be empty".into());
            }
            if print.tables.is_empty() {
                vec![Command::PrintSize(span, None)]
            } else {
                print
                    .tables
                    .iter()
                    .map(|table| Command::PrintSize(span.clone(), Some(native_name("call", table))))
                    .collect()
            }
        }
        _ => return Err("unsupported native observation leaf".into()),
    })
}

fn wire_back_off(
    bind: &pb::BindScheduler,
) -> Result<(scheduling::BackOffScheduler, bool), PreparationError> {
    if bind.name.is_empty() {
        return Err("scheduler name must not be empty".into());
    }
    let Some(options) = bind.back_off.as_ref() else {
        return Err("missing scheduler configuration".into());
    };
    let [matches, bans, nodes] =
        [options.match_limit, options.ban_length, options.node_limit].map(|limit| {
            limit
                .map(usize::try_from)
                .transpose()
                .map_err(|_| PreparationError::from("scheduler limit exceeds native usize"))
        });
    Ok((
        scheduling::BackOffScheduler::new(matches?, bans?, nodes?),
        // A zero ban can also permit stopping with deferred matches: native
        // can_stop has no outstanding ban to distinguish that resource policy.
        options.node_limit.is_some() || options.ban_length == Some(0),
    ))
}

struct WireSchedule<'a, 'stream> {
    executor: NativeExecutor<'a>,
    program: &'a pb::Program,
    context: &'a mut RequestOccurrences,
    response: &'a mut pb::RunProgramOutput,
    root: &'a pb::CommandLocation,
    stream: &'a mut OutputStream<'stream>,
    definitions: &'a pb::Program,
    extension: Option<&'a Arc<dyn NativeExtension>>,
    measurements: &'a RefCell<ScheduleMeasurements>,
    bindings: Vec<(String, SchedulerBinding)>,
    suppressed: bool,
    partial: &'a mut ControlReport,
}

struct WireEnvelope<'a, 'stream> {
    mode: pb::ExecutionMode,
    names: &'a NativeNames,
    program: &'a pb::Program,
    context: &'a mut RequestOccurrences,
    response: &'a mut pb::RunProgramOutput,
    root: &'a pb::CommandLocation,
    stream: &'a mut OutputStream<'stream>,
    definitions: &'a pb::Program,
    extension: Option<&'a Arc<dyn NativeExtension>>,
    measurements: &'a RefCell<ScheduleMeasurements>,
    export_error: Option<egglog::Error>,
    suppressed: bool,
    anchor: &'a pb::Command,
    bindings: Vec<(String, SchedulerBinding)>,
    partial: ControlReport,
}

impl WireEnvelope<'_, '_> {
    fn execute(&mut self, graph: &mut EGraph) -> Result<egglog_reports::RunReport, egglog::Error> {
        let mut control = WireSchedule {
            executor: NativeExecutor {
                graph,
                mode: self.mode,
                names: self.names,
            },
            program: self.program,
            context: self.context,
            response: self.response,
            root: self.root,
            stream: self.stream,
            definitions: self.definitions,
            extension: self.extension,
            measurements: self.measurements,
            bindings: self.bindings.clone(),
            suppressed: self.suppressed,
            partial: &mut self.partial,
        };
        scheduling::fold_control(&mut control, self.anchor, &mut vec![], &mut vec![])
            .map(|report| report.report)
    }

    fn complete(&mut self, report: Option<&egglog_reports::RunReport>) {
        let Some(report) = report else {
            self.measurements.borrow_mut().failure = None;
            return;
        };
        let kind = pb::command_output::Kind::Run(pb::RunResult {
            updated: report.updated,
            can_stop: report.can_stop,
        });
        self.export_error = self.output(kind, report).err();
    }

    fn output(
        &mut self,
        kind: pb::command_output::Kind,
        report: &egglog_reports::RunReport,
    ) -> Result<(), egglog::Error> {
        let run_report = self
            .context
            .diagnostics
            .then(|| report::export(report))
            .transpose()
            .map_err(egglog::Error::BackendError)?;
        self.response.outputs.push(pb::CommandOutput {
            kind: Some(kind),
            location: Some(self.root.clone()),
        });
        if let Some(diagnostic) = run_report {
            self.response.outputs.push(pb::CommandOutput {
                kind: Some(pb::command_output::Kind::Diagnostic(diagnostic)),
                location: Some(self.root.clone()),
            });
        }
        Ok(())
    }
}

impl WireSchedule<'_, '_> {
    fn location(&self, path: &[usize], iterations: &[u64]) -> pb::CommandLocation {
        let mut location = self.root.clone();
        location.path.extend(path.iter().map(|index| *index as u32));
        location.iterations.extend(iterations);
        location
    }
}

impl ControlContext for WireSchedule<'_, '_> {
    type Node = pb::Command;
    type Error = egglog::Error;
    type Scope = (usize, HashMap<u32, Value>);

    fn view<'a>(&self, node: &'a pb::Command) -> Result<Control<'a, pb::Command>, egglog::Error> {
        Ok(match node.kind.as_ref().expect("validated command") {
            pb::command::Kind::Loop(body) => Control::Loop(&body.body, body.max_iterations),
            _ => Control::Leaf,
        })
    }

    fn enter_scope(&mut self) -> Self::Scope {
        (
            self.bindings.len(),
            std::mem::take(&mut self.context.union_values),
        )
    }

    fn leave_scope(&mut self, (mark, parent): Self::Scope) {
        self.bindings.truncate(mark);
        self.context.union_values = parent;
    }

    fn leaf(
        &mut self,
        node: &pb::Command,
        path: &[usize],
        iterations: &[u64],
    ) -> Result<ControlReport, egglog::Error> {
        if self.stream.cancelled {
            return Err(egglog::Error::BackendError("execution cancelled".into()));
        }
        let location = self.location(path, iterations);
        if let Some(pb::command::Kind::Fail(_)) = &node.kind {
            let mut anchor = node;
            let mut fail_spans = vec![];
            while let Some(pb::command::Kind::Fail(child)) = &anchor.kind {
                fail_spans.push(
                    native_span(
                        self.program,
                        anchor.span.as_ref(),
                        &self.context.native_spans,
                    )
                    .expect("validated span"),
                );
                anchor = child;
            }
            let previous = std::mem::take(&mut self.measurements.borrow_mut().changed);
            let mut envelope = WireEnvelope {
                mode: self.executor.mode,
                names: self.executor.names,
                program: self.program,
                context: self.context,
                response: self.response,
                root: &location,
                stream: self.stream,
                definitions: self.definitions,
                extension: self.extension,
                measurements: self.measurements,
                export_error: None,
                suppressed: true,
                anchor,
                bindings: self.bindings.clone(),
                partial: ControlReport::default(),
            };
            let result = self.executor.graph.with_schedule_envelope(
                &fail_spans,
                &mut envelope,
                |graph, state| state.execute(graph),
                |state, report| state.complete(report),
                |state, event| {
                    state.measurements.borrow_mut().observe(
                        event,
                        state.mode,
                        Some(state.root),
                        &HashMap::new(),
                    )
                },
            );
            let changed = self.measurements.borrow().changed;
            self.measurements.borrow_mut().changed |= previous;
            let mut partial = std::mem::take(&mut envelope.partial);
            partial.report.updated |= changed;
            partial.report.can_stop &= !changed;
            self.partial.report.union(partial.report.clone());
            self.partial.resource_limited |= partial.resource_limited;
            if result.is_err() && self.measurements.borrow().failure.is_none() {
                self.measurements.borrow_mut().failure = Some((location, node.span));
            }
            if self.stream.cancelled {
                return Err(egglog::Error::BackendError("execution cancelled".into()));
            }
            result?;
            return Ok(partial);
        }
        if let Some(pb::command::Kind::BindScheduler(bind)) = &node.kind {
            let (scheduler, resource_limited) = wire_back_off(bind).expect("validated scheduler");
            let binding = SchedulerBinding {
                id: self.executor.graph.add_scheduler(Box::new(scheduler)),
                resource_limited,
            };
            if self.root.iterations.is_empty() && iterations.is_empty() {
                self.executor
                    .graph
                    .extension_state_or_default::<PermanentSchedulerState>()
                    .insert(bind.name.clone(), binding);
            } else {
                self.bindings.push((bind.name.clone(), binding));
            }
            return Ok(ControlReport::default());
        }
        if let Some(pb::command::Kind::Run(run)) = &node.kind {
            let mut registry = std::mem::take(&mut self.context.registry);
            let indices = registry.resolve(&run.rulesets, &location.path, self.context);
            let result =
                registry.selection(indices, &mut self.executor, self.context, self.response);
            self.context.registry = registry;
            let selection = result?;
            self.context.selection = selection;
        }
        if let Some(pb::command::Kind::Freeze(_)) = &node.kind {
            if !self.suppressed {
                let snapshot = freeze::export(
                    freeze::View {
                        graph: self.executor.graph,
                        names: self.executor.names,
                        definitions: self.definitions,
                        mode: self.executor.mode,
                        extension: self.extension,
                    },
                    &self.context.registry,
                )?;
                self.response.outputs.push(pb::CommandOutput {
                    kind: Some(pb::command_output::Kind::Snapshot(snapshot)),
                    location: Some(location),
                });
                self.stream.flush(self.response, self.context)?;
            }
            return Ok(ControlReport::default());
        }
        if let Some(pb::command::Kind::Explain(explain)) = &node.kind {
            if !self.suppressed {
                let diagnostic =
                    report::explain(self.executor.graph, &self.context.registry, &explain.groups)?;
                self.response.outputs.push(pb::CommandOutput {
                    kind: Some(pb::command_output::Kind::Diagnostic(diagnostic)),
                    location: Some(location),
                });
                self.stream.flush(self.response, self.context)?;
            }
            return Ok(ControlReport::default());
        }
        let binding = match &node.kind {
            Some(pb::command::Kind::Run(run)) if !run.scheduler.is_empty() => Some(
                self.bindings
                    .iter()
                    .rfind(|(name, _)| name == &run.scheduler)
                    .map(|(_, binding)| *binding)
                    .or_else(|| {
                        self.executor
                            .graph
                            .extension_state::<PermanentSchedulerState>()
                            .and_then(|state| state.get(&run.scheduler).copied())
                    })
                    .expect("validated visible scheduler"),
            ),
            _ => None,
        };
        if let Some(pb::command::Kind::Action(action)) = &node.kind
            && self.context.scoped_actions.contains(&location.path)
        {
            let mut changed = false;
            let result = eval_scoped_action(
                self.executor.graph,
                self.program,
                action,
                &mut self.context.union_values,
                true,
                self.context.action_dags.get(&location.path),
                &mut |event| {
                    if let ExecutionEvent::ActionsFinished { changed: next, .. } = event {
                        changed |= next;
                    }
                    self.measurements.borrow_mut().observe(
                        event,
                        self.executor.mode,
                        Some(&location),
                        &HashMap::new(),
                    );
                },
                &self.context.native_spans,
            );
            if result.is_err() {
                self.measurements.borrow_mut().failure =
                    Some((location, action.span.or(node.span)));
            }
            result?;
            let report = egglog_reports::RunReport {
                updated: changed,
                can_stop: !changed,
                ..Default::default()
            };
            self.partial.report.union(report.clone());
            return Ok(ControlReport {
                report,
                resource_limited: false,
            });
        }
        let mut sites = HashMap::new();
        let commands = if let Some(pb::command::Kind::Action(action)) = &node.kind {
            lower_action(self.program, action, &self.context.native_spans)
                .expect("validated action")
                .into_iter()
                .map(Command::Action)
                .collect()
        } else {
            lower_native_observation(
                self.executor.graph,
                self.program,
                node,
                self.context,
                &mut sites,
            )
            .expect("validated leaf")
        };
        let mut report = None;
        let (result, _, _) = self.executor.run_observed(
            commands,
            Some(RequestedObservation {
                command: node,
                location: &location,
                sites: &sites,
            }),
            self.context,
            self.response,
            Some(ScheduleCapture {
                measurements: self.measurements,
                scheduler: binding.map(|binding| binding.id),
                report: &mut report,
                emit_outputs: !self.suppressed,
            }),
        );
        if !self.suppressed {
            self.stream.flush(self.response, self.context)?;
        }
        if result.is_err() && self.measurements.borrow().failure.is_none() {
            let span = match &node.kind {
                Some(pb::command::Kind::Action(action)) => action.span.or(node.span),
                _ => node.span,
            };
            self.measurements.borrow_mut().failure = Some((location, span));
        }
        result?;
        let report = report.unwrap_or_default();
        let resource_limited = binding.is_some_and(|binding| binding.resource_limited);
        self.partial.report.union(report.clone());
        self.partial.resource_limited |= resource_limited;
        Ok(ControlReport {
            report,
            resource_limited,
        })
    }

    fn until(
        &mut self,
        node: &pb::Command,
        path: &[usize],
        iterations: &[u64],
    ) -> Result<bool, egglog::Error> {
        let until = match &node.kind {
            Some(pb::command::Kind::Loop(body)) => &body.until,
            _ => unreachable!(),
        };
        if until.is_empty() {
            return Ok(false);
        }
        let location = self.location(path, iterations);
        let conditions = facts(
            self.program,
            until,
            &self.context.native_spans,
            None,
            |name| {
                self.executor.graph.authoring_type_info().is_global(name)
                    || self.executor.graph.get_sort_by_name(name).is_some()
                    || self
                        .executor
                        .graph
                        .authoring_type_info()
                        .get_func_type(name)
                        .is_some()
                    || self.executor.graph.authoring_type_info().is_primitive(name)
            },
        )
        .expect("validated until")
        .0;
        let result = self.executor.graph.check_condition_observed(
            native_span(self.program, node.span.as_ref(), &self.context.native_spans)
                .expect("validated span"),
            conditions,
            &mut |event| {
                self.measurements.borrow_mut().observe(
                    event,
                    self.executor.mode,
                    Some(&location),
                    &HashMap::new(),
                )
            },
        );
        match result {
            Ok(()) => Ok(true),
            Err(egglog::Error::CheckError(..)) => {
                self.measurements.borrow_mut().failure = None;
                Ok(false)
            }
            Err(error) => {
                self.measurements.borrow_mut().failure = Some((location, node.span));
                Err(error)
            }
        }
    }

    fn completed(
        &mut self,
        _: &pb::Command,
        _: &[usize],
        _: &[u64],
        _: &ControlReport,
        _: u64,
        _: ControlStop,
    ) -> Result<(), egglog::Error> {
        Ok(())
    }
}

// Derived reverse indexes only; the stored generated declarations retain their
// public names. Never decode arbitrary native symbols merely by their prefix.
#[derive(Clone, Default)]
struct NativeNames {
    sorts: HashMap<String, String>,
    callables: HashMap<String, String>,
}

// Keep reflected priority separate from private callable identity. Absence and
// an explicit same-key default agree; even Public(key) remains an explicit alias.
fn native_table_name(declaration: &pb::Declaration, key: &str) -> ast::TableName {
    match &declaration.table_name {
        Some(pb::declaration::TableName::PublicAlias(name)) => ast::TableName::Public(name.clone()),
        Some(pb::declaration::TableName::DefaultName(name)) => {
            ast::TableName::Default(name.clone())
        }
        None => ast::TableName::Default(key.to_owned()),
    }
}

// Namespace tags separate sorts, callables, and query leaves. Hex is injective
// over UTF-8 and always a native source atom, including for punctuation names.
fn native_name(namespace: &str, logical: &str) -> String {
    use std::fmt::Write;
    let mut result = format!("__egglog_proto_{namespace}_");
    for byte in logical.bytes() {
        write!(result, "{byte:02x}").unwrap();
    }
    result
}

// Project the ephemeral execution copy, not the canonical declaration store.
// Unknown user references are projected too: they must not access a physical
// symbol by spelling it, and native validation will reject the unbound name.
// Private-looking spellings are ordinary logical names, including source that
// was rendered earlier. They receive the same projection, never prefix decoding.
fn project_names(
    program: &mut pb::Program,
    definitions: &pb::Program,
    builtins: &pb::BuiltinCatalog,
) -> NativeNames {
    let mut names = NativeNames::default();
    let host_keys: HashSet<_> = builtins
        .primitives
        .iter()
        .map(|p| p.name.as_str())
        .collect();
    for declaration in &definitions.declarations {
        match &declaration.kind {
            Some(pb::declaration::Kind::EqSort(s)) => {
                names
                    .sorts
                    .insert(native_name("sort", &s.name), s.name.clone());
            }
            Some(pb::declaration::Kind::Constructor(f)) => {
                names
                    .callables
                    .insert(native_name("call", &f.name), f.name.clone());
            }
            Some(pb::declaration::Kind::Function(f)) => {
                names
                    .callables
                    .insert(native_name("call", &f.name), f.name.clone());
            }
            Some(pb::declaration::Kind::Relation(r)) => {
                names
                    .callables
                    .insert(native_name("call", &r.name), r.name.clone());
            }
            Some(pb::declaration::Kind::UserDefinedPrimitive(p)) => {
                names
                    .callables
                    .insert(native_name("call", &p.name), p.name.clone());
            }
            _ => (),
        }
    }
    let project_call = |name: &mut String| {
        if !host_keys.contains(name.as_str()) {
            *name = native_name("call", name);
        }
    };
    for sort in &mut program.sorts {
        if let Some(pb::sort::Kind::Eq(name)) = &mut sort.kind {
            *name = native_name("sort", name);
        }
    }
    for declaration in &mut program.declarations {
        if let Some(pb::declaration::Kind::EqSort(sort)) = &mut declaration.kind {
            sort.name = native_name("sort", &sort.name);
        }
    }
    // PrintSize selects logical tables until lower_native_observation projects
    // them. Source relocation, in contrast, must relocate those selectors too.
    map_callable_names(program, project_call, |_| {});
    names
}

// Relocate structural callable references only. Strings remain ordinary data.
fn map_callable_names(
    program: &mut pb::Program,
    mut project_call: impl FnMut(&mut String),
    mut project_size: impl FnMut(&mut String),
) {
    for declaration in &mut program.declarations {
        match &mut declaration.kind {
            Some(pb::declaration::Kind::Constructor(f)) => project_call(&mut f.name),
            Some(pb::declaration::Kind::Function(f)) => project_call(&mut f.name),
            Some(pb::declaration::Kind::Relation(r)) => project_call(&mut r.name),
            Some(pb::declaration::Kind::UserDefinedPrimitive(p)) => project_call(&mut p.name),
            _ => (),
        }
    }
    for node in &mut program.nodes {
        if let Some(pb::node::Kind::Call(call) | pb::node::Kind::GetCost(call)) = &mut node.kind {
            project_call(&mut call.func);
        } else if let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::PartialCall(call)),
        })) = &mut node.kind
        {
            project_call(&mut call.func);
        }
    }
    let mut rules: Vec<_> = program
        .rulesets
        .iter_mut()
        .filter_map(|binding| binding.value.as_mut())
        .flat_map(|ruleset| &mut ruleset.rules)
        .collect();
    let mut commands: Vec<_> = program.commands.iter_mut().collect();
    let mut actions = vec![];
    while let Some(command) = commands.pop() {
        match &mut command.kind {
            Some(pb::command::Kind::Fail(child)) => commands.push(child.as_mut()),
            Some(pb::command::Kind::Loop(body)) => commands.extend(body.body.iter_mut()),
            Some(pb::command::Kind::Action(action)) => actions.push(action),
            Some(pb::command::Kind::Run(run)) => {
                for selection in &mut run.rulesets {
                    if let Some(pb::ruleset_selection::Kind::Ruleset(value)) = &mut selection.kind {
                        rules.extend(&mut value.rules);
                    }
                }
            }
            Some(pb::command::Kind::TableSizes(print)) => {
                for table in &mut print.tables {
                    project_size(table);
                }
            }
            Some(pb::command::Kind::TableRows(print)) => project_call(&mut print.table),
            Some(pb::command::Kind::KeepBest(keep)) => {
                for table in &mut keep.tables {
                    project_call(table);
                }
            }
            Some(pb::command::Kind::ProveExists(prove)) => project_call(&mut prove.constructor),
            _ => (),
        }
    }
    let rule_actions = rules
        .into_iter()
        .filter_map(|rule| match &mut rule.kind {
            Some(pb::rule::Kind::Rule(body)) => Some(&mut body.head),
            _ => None,
        })
        .flatten();
    for action in rule_actions.chain(actions) {
        match &mut action.kind {
            Some(pb::action::Kind::Set(set)) => {
                if let Some(call) = &mut set.target {
                    project_call(&mut call.func);
                }
            }
            Some(pb::action::Kind::SetCost(set)) => {
                if let Some(call) = &mut set.target {
                    project_call(&mut call.func);
                }
            }
            Some(pb::action::Kind::Delete(call) | pb::action::Kind::Subsume(call)) => {
                project_call(&mut call.func)
            }
            _ => (),
        }
    }
}

fn structural_sort_name(
    sorts: &[pb::Sort],
    index: u32,
    active: &mut HashSet<u32>,
) -> Result<Option<String>, String> {
    if active.len() >= 256 || !active.insert(index) {
        return Err("cyclic or too-deep sort".into());
    }
    let sort = sorts
        .get(index as usize)
        .ok_or("sort index out of bounds")?;
    let result = match sort.kind.as_ref() {
        Some(pb::sort::Kind::Eq(name)) if !name.is_empty() => Ok(Some(name.clone())),
        Some(pb::sort::Kind::Var(_)) => Ok(None),
        Some(pb::sort::Kind::Func(function)) => {
            let mut name = String::from("__egglog_proto_fn");
            for child in function.params.iter().chain([&function.result]) {
                let Some(child) = structural_sort_name(sorts, *child, active)? else {
                    active.remove(&index);
                    return Ok(None);
                };
                if name.len() + child.len() > 65_536 {
                    return Err("native sort name exceeds adapter limit".into());
                }
                name.push_str(&format!("_{}_{}", child.len(), child));
            }
            Ok(Some(name))
        }
        Some(pb::sort::Kind::Application(family))
            if matches!(family.name.as_str(), "Vec" | "Set" | "MultiSet" | "Maybe")
                && family.args.len() == 1 =>
        {
            structural_sort_name(sorts, family.args[0], active).and_then(|child| {
                child
                    .map(|child| {
                        if child.len() > 65_536 {
                            return Err("native sort name exceeds adapter limit".into());
                        }
                        Ok(format!(
                            "__egglog_proto_{}_{}_{}",
                            family.name.to_ascii_lowercase(),
                            child.len(),
                            child
                        ))
                    })
                    .transpose()
            })
        }
        Some(pb::sort::Kind::Application(family))
            if matches!(family.name.as_str(), "Pair" | "Map") && family.args.len() == 2 =>
        {
            let first = structural_sort_name(sorts, family.args[0], active)?;
            let second = structural_sort_name(sorts, family.args[1], active)?;
            first
                .zip(second)
                .map(|(first, second)| {
                    if first.len() + second.len() > 65_536 {
                        return Err("native sort name exceeds adapter limit".into());
                    }
                    Ok(format!(
                        "__egglog_proto_{}_{}_{}_{}_{}",
                        family.name.to_ascii_lowercase(),
                        first.len(),
                        first,
                        second.len(),
                        second
                    ))
                })
                .transpose()
        }
        Some(pb::sort::Kind::Application(family))
            if family.args.is_empty() && !family.name.is_empty() =>
        {
            Ok(Some(family.name.clone()))
        }
        _ => Err(
            "only equality, scalar, Vec, Set, MultiSet, Pair, Map and Maybe sorts are supported yet".into(),
        ),
    };
    active.remove(&index);
    result
}

// A wire spelling alone cannot introduce a native host sort, or reinterpret a
// native equality/container sort as a nullary host value.
fn validate_nullary_family(types: &egglog::TypeInfo, sort: &pb::Sort) -> Result<(), String> {
    let Some(pb::sort::Kind::Application(family)) = &sort.kind else {
        return Ok(());
    };
    if !family.args.is_empty() {
        return Ok(());
    }
    let native = types
        .get_sort_by_name(&family.name)
        .ok_or_else(|| format!("unknown host sort family {}", family.name))?;
    if native.is_eq_sort()
        || native.is_container_sort()
        || native.value_type().is_none()
        || !types
            .registered_builtin_family(&family.name)
            .is_ok_and(|registered| registered.arity == 0)
    {
        return Err(format!(
            "incompatible nullary host sort family {}",
            family.name
        ));
    }
    Ok(())
}

fn sort_name(sorts: &[pb::Sort], index: u32) -> Result<String, String> {
    structural_sort_name(sorts, index, &mut HashSet::new())?
        .ok_or_else(|| "runtime sort contains an open type parameter".into())
}

// Observation requires a concrete stored signature, even when its row limit
// is zero. This check uses authored records only: preparation must not scan or
// require native views that pending declarations have not installed yet.
fn stored_table_signature<'a>(
    definitions: &'a pb::Program,
    name: &str,
) -> Result<(&'a [pb::Arg], Option<u32>), String> {
    let (inputs, output) = definitions
        .declarations
        .iter()
        .find_map(|declaration| match &declaration.kind {
            Some(pb::declaration::Kind::Constructor(row)) if row.name == name => {
                Some((row.inputs.as_slice(), Some(row.output)))
            }
            Some(pb::declaration::Kind::Function(row)) if row.name == name => {
                Some((row.inputs.as_slice(), Some(row.output)))
            }
            Some(pb::declaration::Kind::Relation(row)) if row.name == name => {
                Some((row.inputs.as_slice(), None))
            }
            _ => None,
        })
        .ok_or_else(|| format!("{name} is not a stored table"))?;
    for sort in inputs.iter().map(|arg| arg.sort).chain(output) {
        sort_name(&definitions.sorts, sort)?;
    }
    Ok((inputs, output))
}

// Declarations install before use. Named computed bodies need their native
// callees registered first; cycles remain unsupported, never a retry/eval loop.
fn declaration_order(program: &pb::Program, graph: &mut EGraph) -> Result<Vec<usize>, String> {
    let mut order: Vec<_> = program
        .declarations
        .iter()
        .enumerate()
        .filter(|(_, d)| {
            !matches!(
                d.kind,
                Some(
                    pb::declaration::Kind::Function(_)
                        | pb::declaration::Kind::UserDefinedPrimitive(_)
                )
            )
        })
        .map(|(i, _)| i)
        .collect();
    let names: HashMap<_, _> = program
        .declarations
        .iter()
        .enumerate()
        .filter_map(|(i, d)| match &d.kind {
            Some(pb::declaration::Kind::Function(f)) => Some((f.name.as_str(), i)),
            Some(pb::declaration::Kind::UserDefinedPrimitive(p)) => Some((p.name.as_str(), i)),
            _ => None,
        })
        .collect();
    let mut pending = vec![];
    let mut installed = HashSet::new();
    for (i, d) in program.declarations.iter().enumerate() {
        let (name, body, primitive) = match &d.kind {
            Some(pb::declaration::Kind::Function(f)) => (f.name.as_str(), f.merge, false),
            Some(pb::declaration::Kind::UserDefinedPrimitive(p)) => (
                p.name.as_str(),
                Some(p.body.ok_or("missing primitive body")?),
                true,
            ),
            _ => continue,
        };
        // Compatible resupply already has runtime backends, not just signature headers.
        if graph.get_function(name).is_some()
            || graph
                .type_info()
                .get_prims(name)
                .is_some_and(|primitives| !primitives.is_empty())
        {
            installed.insert(i);
            order.push(i);
            continue;
        }
        let mut nodes: Vec<_> = body.into_iter().collect();
        let mut seen = HashSet::new();
        let mut dependencies = HashSet::new();
        while let Some(node) = nodes.pop() {
            if !seen.insert(node) {
                continue;
            }
            let node = program
                .nodes
                .get(node as usize)
                .ok_or("declaration body node out of bounds")?;
            let call = match &node.kind {
                Some(pb::node::Kind::Call(call)) => Some(call),
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::PartialCall(call)),
                })) => Some(call),
                Some(pb::node::Kind::Union(_)) if primitive => {
                    return Err("Union in primitive bodies is not supported yet".into());
                }
                _ => None,
            };
            if let Some(call) = call {
                nodes.extend(&call.args);
                if let Some(dependency) = names.get(call.func.as_str()) {
                    dependencies.insert(*dependency);
                }
            }
        }
        pending.push((i, dependencies));
    }
    extend_declaration_order(pending, installed, &mut order)?;
    Ok(order)
}

fn extend_declaration_order(
    pending: Vec<(usize, HashSet<usize>)>,
    installed: HashSet<usize>,
    order: &mut Vec<usize>,
) -> Result<(), String> {
    let count = order.len() + pending.len();
    let mut dependents = vec![vec![]; count];
    let mut remaining = vec![0usize; count];
    let mut ready = BinaryHeap::new();
    for (index, dependencies) in pending {
        #[cfg(test)]
        tests::DECLARATION_ORDER_WORK.with(|work| work.set(work.get() + 1));
        for dependency in dependencies {
            #[cfg(test)]
            tests::DECLARATION_ORDER_WORK.with(|work| work.set(work.get() + 1));
            if !installed.contains(&dependency) {
                dependents[dependency].push(index);
                remaining[index] += 1;
            }
        }
        if remaining[index] == 0 {
            ready.push(Reverse(index));
        }
    }
    while let Some(Reverse(index)) = ready.pop() {
        #[cfg(test)]
        tests::DECLARATION_ORDER_WORK.with(|work| work.set(work.get() + 1));
        order.push(index);
        for &dependent in &dependents[index] {
            #[cfg(test)]
            tests::DECLARATION_ORDER_WORK.with(|work| work.set(work.get() + 1));
            remaining[dependent] -= 1;
            if remaining[dependent] == 0 {
                ready.push(Reverse(dependent));
            }
        }
    }
    if order.len() != count {
        return Err(
            "recursive program-defined primitives or function merges are not supported yet".into(),
        );
    }
    Ok(())
}

fn primitive_command(
    program: &pb::Program,
    primitive: &pb::UserDefinedPrimitive,
    span: ast::Span,
    native_spans: &NativeSpans,
) -> Result<Command, String> {
    let schema = signature(program, &primitive.inputs, primitive.output)?;
    let body = primitive.body.ok_or("missing primitive body")?;
    if node_sort(program, body)? != schema.output {
        return Err("primitive body output sort mismatch".into());
    }
    let mut bindings = schema
        .input
        .iter()
        .enumerate()
        .map(|(index, sort)| (format!("_{index}"), sort.clone()))
        .collect();
    check_variables(program, &[body], &mut bindings, false)?;
    let inputs = match schema.input.as_slice() {
        [] => Expr::Lit(span.clone(), Literal::Unit),
        [sort] => Expr::Var(span.clone(), sort.clone()),
        [first, rest @ ..] => Expr::Call(
            span.clone(),
            first.clone(),
            rest.iter()
                .map(|sort| Expr::Var(span.clone(), sort.clone()))
                .collect(),
        ),
    };
    Ok(Command::UserDefined(
        span.clone(),
        "primitive".into(),
        vec![
            Expr::Var(span.clone(), primitive.name.clone()),
            inputs,
            Expr::Var(span, schema.output),
            expression(program, body, &mut HashSet::new(), native_spans)?,
        ],
    ))
}

// Materialization runs on staged state. Open patterns remain in their signature
// arenas; only closed shapes install native sorts, in child-before-parent order.
fn materialize_sorts(
    program: &pb::Program,
    graph: &mut EGraph,
    known: &mut HashSet<String>,
    native_spans: &NativeSpans,
) -> Result<Vec<(u32, Command)>, String> {
    fn visit(
        program: &pb::Program,
        index: u32,
        graph: &mut EGraph,
        commands: &mut Vec<(u32, Command)>,
        seen: &mut HashSet<u32>,
        known: &mut HashSet<String>,
        native_spans: &NativeSpans,
    ) -> Result<(), String> {
        if !seen.insert(index) {
            return Ok(());
        }
        let name = structural_sort_name(&program.sorts, index, &mut HashSet::new())?;
        let Some(name) = name else {
            return Ok(());
        };
        let (presort, children) = match &program.sorts[index as usize].kind {
            Some(pb::sort::Kind::Application(family)) if !family.args.is_empty() => {
                (family.name.as_str(), family.args.clone())
            }
            Some(pb::sort::Kind::Func(function)) => (
                "UnstableFn",
                function
                    .params
                    .iter()
                    .chain([&function.result])
                    .copied()
                    .collect(),
            ),
            _ => return Ok(()),
        };
        for child in &children {
            visit(program, *child, graph, commands, seen, known, native_spans)?;
        }
        if known.contains(&name) {
            return Ok(());
        }
        if let Some(existing) = graph.get_sort_by_name(&name) {
            let mut expected = vec![];
            let expected_id = crate::builtin::import_sort(&program.sorts, index, &mut expected)?;
            if graph.export_sort(existing, &mut expected)? != expected_id {
                return Err("private sort name collision".into());
            }
            return Ok(());
        }
        known.insert(name.clone());
        let args = if presort == "UnstableFn" {
            let (result, params) = children.split_last().unwrap();
            let inputs = match params.split_first() {
                Some((first, rest)) => Expr::Call(
                    span!(),
                    sort_name(&program.sorts, *first)?,
                    rest.iter()
                        .map(|i| sort_name(&program.sorts, *i).map(|name| Expr::Var(span!(), name)))
                        .collect::<Result<_, _>>()?,
                ),
                None => Expr::Lit(span!(), Literal::Unit),
            };
            vec![
                inputs,
                Expr::Var(span!(), sort_name(&program.sorts, *result)?),
            ]
        } else {
            children
                .iter()
                .map(|i| sort_name(&program.sorts, *i).map(|name| Expr::Var(span!(), name)))
                .collect::<Result<_, _>>()?
        };
        let command = Command::Sort {
            span: native_span(
                program,
                program.sorts[index as usize].span.as_ref(),
                native_spans,
            )?,
            name,
            presort_and_args: Some((presort.into(), args)),
            uf: None,
            proof_func: None,
            container_rebuild: None,
            proof_constructors: None,
            unionable: true,
        };
        graph
            .compile_program_observed(vec![command.clone()], &mut |_, _| {})
            .map_err(|e| e.to_string())?;
        commands.push((index, command));
        Ok(())
    }
    let mut commands = vec![];
    let mut seen = HashSet::new();
    for index in 0..program.sorts.len() {
        visit(
            program,
            index as u32,
            graph,
            &mut commands,
            &mut seen,
            known,
            native_spans,
        )?;
    }
    Ok(commands)
}

// Validate intrinsic typing before replacing only the execution copy with the
// existing native application operation. Public descriptors and saved inputs
// never contain that internal callable.
fn native_apply(
    program: &pb::Program,
    node: &pb::Node,
    apply: &pb::Apply,
) -> Result<pb::Call, String> {
    let function = apply.function.ok_or("Apply requires a function")?;
    let function_node = program
        .nodes
        .get(function as usize)
        .ok_or("Apply function index out of bounds")?;
    let Some(pb::sort::Kind::Func(signature)) = program
        .sorts
        .get(function_node.sort_id as usize)
        .and_then(|sort| sort.kind.as_ref())
    else {
        return Err("Apply requires a function sort".into());
    };
    if apply.args.len() != signature.params.len()
        || sort_name(&program.sorts, node.sort_id)? != sort_name(&program.sorts, signature.result)?
    {
        return Err("Apply signature mismatch".into());
    }
    for (argument, parameter) in apply.args.iter().zip(&signature.params) {
        if node_sort(program, *argument)? != sort_name(&program.sorts, *parameter)? {
            return Err("Apply argument sort mismatch".into());
        }
    }
    Ok(pb::Call {
        func: "unstable-app".into(),
        args: std::iter::once(function)
            .chain(apply.args.iter().copied())
            .collect(),
    })
}

fn lower_applications(program: &mut pb::Program) -> Result<(), String> {
    let replacements = program
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(index, node)| match &node.kind {
            Some(pb::node::Kind::Apply(apply)) => {
                Some(native_apply(program, node, apply).map(|call| (index, call)))
            }
            _ => None,
        })
        .collect::<Result<Vec<_>, _>>()?;
    for (index, call) in replacements {
        program.nodes[index].kind = Some(pb::node::Kind::Call(call));
    }
    Ok(())
}

// This ephemeral lowering copy is never emitted as wire IR. Complete annotations
// choose compiler instance keys before the native AST drops result types.
fn lower_builtin_calls(
    program: &mut pb::Program,
    graph: &EGraph,
    signatures: &HashMap<String, (ast::Schema, Option<ast::FunctionSubtype>)>,
) -> Result<(), String> {
    let mut replacements = vec![];
    for (index, node) in program.nodes.iter().enumerate() {
        let (call, function) = match &node.kind {
            Some(pb::node::Kind::Call(call)) => (call, None),
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::PartialCall(call)),
            })) => {
                let Some(pb::sort::Kind::Func(function)) = program
                    .sorts
                    .get(node.sort_id as usize)
                    .and_then(|sort| sort.kind.as_ref())
                else {
                    return Err("partial call requires a function sort".into());
                };
                (call, Some(function))
            }
            _ => continue,
        };
        {
            if (function.is_none() && signatures.contains_key(&call.func))
                || call.func == "unstable-app"
            {
                continue;
            }
            let mut args: Vec<_> = call
                .args
                .iter()
                .map(|i| {
                    program
                        .nodes
                        .get(*i as usize)
                        .map(|n| n.sort_id)
                        .ok_or("node index out of bounds")
                })
                .collect::<Result<_, _>>()?;
            let output = if let Some(function) = function {
                args.extend(&function.params);
                function.result
            } else {
                node.sort_id
            };
            let sorts = args
                .iter()
                .copied()
                .chain([output])
                .map(|i| sort_name(&program.sorts, i))
                .collect::<Result<Vec<_>, String>>()?;
            if let Some((signature, _)) = signatures.get(&call.func) {
                if signature
                    .input
                    .iter()
                    .chain([&signature.output])
                    .ne(sorts.iter())
                {
                    return Err(format!("partial call signature mismatch for {}", call.func));
                }
                continue;
            }
            replacements.push((
                index,
                graph.resolve_builtin_call(
                    program,
                    &call.func,
                    &args,
                    output,
                    &sorts.iter().map(String::as_str).collect::<Vec<_>>(),
                )?,
            ));
        }
    }
    for (index, name) in replacements {
        let call = match &mut program.nodes[index].kind {
            Some(pb::node::Kind::Call(call)) => call,
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::PartialCall(call)),
            })) => call,
            _ => unreachable!(),
        };
        call.func = name;
    }
    Ok(())
}

// Lower only an ephemeral projection: canonical definitions keep their opaque
// payloads. The provider receives the validated native type context, never IDs
// or values copied from a different graph.
fn lower_custom_values(
    program: &mut pb::Program,
    graph: &mut EGraph,
    extension: Option<&dyn NativeExtension>,
) -> Result<(), String> {
    for index in 0..program.nodes.len() {
        let node = &program.nodes[index];
        let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Custom(value)),
        })) = &node.kind
        else {
            continue;
        };
        let name = sort_name(&program.sorts, node.sort_id)?;
        let native_sort = graph
            .get_sort_by_name(&name)
            .cloned()
            .ok_or_else(|| format!("unknown custom value sort {name}"))?;
        validate_nullary_family(graph.type_info(), &program.sorts[node.sort_id as usize])?;
        let extension = extension.ok_or("custom value provider unavailable")?;
        let (value, span) = (value.clone(), node.span);
        let call = extension.lower_custom_value(graph, &native_sort, &value, span, program)?;
        program.nodes[index].kind = Some(pb::node::Kind::Call(call));
    }
    Ok(())
}

// The native container constructors intern these ordered payloads.
// Validate contents first; the resulting calls are internal compatibility code,
// never a claim that the wire value payload was a symbolic authored Call.
fn lower_container_values(program: &mut pb::Program) -> Result<Vec<u32>, String> {
    let mut sites: Vec<_> = (0..program.sorts.len() as u32).collect();
    let mut replacements = vec![];
    for (index, node) in program.nodes.iter().enumerate() {
        if let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue { value: Some(value) })) =
            &node.kind
        {
            if matches!(
                value,
                pb::primitive_value::Value::BigInt(_)
                    | pb::primitive_value::Value::BigRat(_)
                    | pb::primitive_value::Value::Rational(_)
            ) {
                let expected = match value {
                    pb::primitive_value::Value::BigInt(_) => "BigInt",
                    pb::primitive_value::Value::BigRat(_) => "BigRat",
                    _ => "Rational",
                };
                if !matches!(program.sorts.get(node.sort_id as usize).and_then(|s| s.kind.as_ref()), Some(pb::sort::Kind::Application(f)) if f.name == expected && f.args.is_empty())
                {
                    return Err(format!("{expected} payload/sort mismatch"));
                }
                value::Scalar::decode(
                    Some(expected),
                    &pb::PrimitiveValue {
                        value: Some(value.clone()),
                    },
                )?;
                continue; // authored value data stays inert in the protobuf arena
            }
            let (name, arity, key, args) = match value {
                pb::primitive_value::Value::Maybe(maybe) => (
                    "Maybe",
                    1,
                    if maybe.value.is_some() {
                        "egglog.experimental.maybe.some"
                    } else {
                        "egglog.experimental.maybe.none"
                    },
                    maybe.value.into_iter().collect(),
                ),
                pb::primitive_value::Value::Vec(values) => {
                    ("Vec", 1, "egglog.core.vec.of", values.items.clone())
                }
                pb::primitive_value::Value::Set(values) => {
                    ("Set", 1, "egglog.core.set.of", values.items.clone())
                }
                pb::primitive_value::Value::Multiset(values) => (
                    "MultiSet",
                    1,
                    "egglog.core.multiset.of",
                    values.items.clone(),
                ),
                pb::primitive_value::Value::Pair(pair) => (
                    "Pair",
                    2,
                    "egglog.core.pair.make",
                    vec![
                        pair.first.ok_or("missing Pair first child")?,
                        pair.second.ok_or("missing Pair second child")?,
                    ],
                ),
                pb::primitive_value::Value::Map(map) => (
                    "Map",
                    2,
                    "egglog.core.map.of",
                    map.entries
                        .iter()
                        .map(|entry| {
                            Ok([
                                entry.key.ok_or("missing Map key child")?,
                                entry.value.ok_or("missing Map value child")?,
                            ])
                        })
                        .collect::<Result<Vec<_>, String>>()?
                        .into_iter()
                        .flatten()
                        .collect(),
                ),
                _ => continue,
            };
            let Some(pb::sort::Kind::Application(family)) = program
                .sorts
                .get(node.sort_id as usize)
                .and_then(|s| s.kind.as_ref())
            else {
                return Err(format!("{name} payload requires {name} sort"));
            };
            if family.name != name || family.args.len() != arity {
                return Err(format!("{name} payload/sort mismatch"));
            }
            let expected = family
                .args
                .iter()
                .map(|i| sort_name(&program.sorts, *i))
                .collect::<Result<Vec<_>, _>>()?;
            for (position, item) in args.iter().enumerate() {
                if node_sort(program, *item)? != expected[position % arity] {
                    return Err(format!("{name} payload element sort mismatch"));
                }
            }
            replacements.push((
                index,
                key,
                args,
                (name == "Map").then(|| family.args.clone()),
            ));
        }
    }
    for (index, key, mut args, map_parameters) in replacements {
        if let Some(parameters) = map_parameters {
            let mut sorts = program.sorts.clone();
            let pair_sort = u32::try_from(sorts.len()).map_err(|_| "too many sorts")?;
            sorts.push(pb::Sort {
                kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                    name: "Pair".into(),
                    args: parameters,
                })),
                ..Default::default()
            });
            let vector_sort = u32::try_from(sorts.len()).map_err(|_| "too many sorts")?;
            sorts.push(pb::Sort {
                kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                    name: "Vec".into(),
                    args: vec![pair_sort],
                })),
                ..Default::default()
            });
            let pair_sort = crate::builtin::import_sort(&sorts, pair_sort, &mut program.sorts)?;
            let vector_sort = crate::builtin::import_sort(&sorts, vector_sort, &mut program.sorts)?;
            sites.resize(program.sorts.len(), program.nodes[index].sort_id);
            let mut pairs = vec![];
            for fields in args.chunks_exact(2) {
                pairs.push(u32::try_from(program.nodes.len()).map_err(|_| "too many nodes")?);
                program.nodes.push(pb::Node {
                    sort_id: pair_sort,
                    kind: Some(pb::node::Kind::Call(pb::Call {
                        func: "egglog.core.pair.make".into(),
                        args: fields.to_vec(),
                    })),
                    span: program.nodes[index].span,
                });
            }
            let entries = u32::try_from(program.nodes.len()).map_err(|_| "too many nodes")?;
            program.nodes.push(pb::Node {
                sort_id: vector_sort,
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "egglog.core.vec.of".into(),
                    args: pairs,
                })),
                span: program.nodes[index].span,
            });
            args = vec![entries];
        }
        program.nodes[index].kind = Some(pb::node::Kind::Call(pb::Call {
            func: key.into(),
            args,
        }));
    }
    Ok(sites)
}

fn node_sort(program: &pb::Program, index: u32) -> Result<String, String> {
    let node = program
        .nodes
        .get(index as usize)
        .ok_or("node index out of bounds")?;
    sort_name(&program.sorts, node.sort_id)
}

fn native_span(
    program: &pb::Program,
    span: Option<&pb::Span>,
    native_spans: &NativeSpans,
) -> Result<ast::Span, String> {
    let Some(span) = span else {
        return Ok(span!());
    };
    let file = program
        .files
        .get(span.file as usize)
        .ok_or("span file out of bounds")?;
    if span.start > span.end {
        return Err("span start exceeds end".into());
    }
    if let Some(contents) = &file.contents {
        if !contents.is_char_boundary(span.start as usize)
            || !contents.is_char_boundary(span.end as usize)
        {
            return Err("span must lie within UTF-8 character boundaries".into());
        }
        // Each table belongs to one append-only file arena, never a session.
        let mut files = native_spans.0.borrow_mut();
        if files.len() < program.files.len() {
            files.resize_with(program.files.len(), || None);
        }
        let file = Arc::clone(files[span.file as usize].get_or_insert_with(|| {
            Arc::new(SrcFile {
                name: Some(file.name.clone()),
                contents: contents.clone(),
            })
        }));
        drop(files);
        return Ok(ast::Span::Egglog(Arc::new(EgglogSpan {
            file,
            i: span.start as usize,
            j: span.end as usize,
        })));
    }
    // No source contents means no safe native excerpt; the protobuf locator is
    // still preserved independently in the error response.
    Ok(span!())
}

fn signature(
    program: &pb::Program,
    inputs: &[pb::Arg],
    output: u32,
) -> Result<ast::Schema, String> {
    let input = inputs
        .iter()
        .map(|argument| sort_name(&program.sorts, argument.sort))
        .collect::<Result<_, _>>()?;
    Ok(ast::Schema {
        input,
        output: sort_name(&program.sorts, output)?,
    })
}

fn expression(
    program: &pb::Program,
    index: u32,
    visiting: &mut HashSet<u32>,
    native_spans: &NativeSpans,
) -> Result<Expr, String> {
    // Remaining tree-only contexts bound expansion here. Action/query graph
    // planners use this adapter only for fixed-size literal payloads.
    lower_expression(program, index, visiting, &mut 65_536, native_spans)
}

fn lower_expression(
    program: &pb::Program,
    index: u32,
    visiting: &mut HashSet<u32>,
    remaining: &mut usize,
    native_spans: &NativeSpans,
) -> Result<Expr, String> {
    *remaining = remaining
        .checked_sub(1)
        .ok_or("native expression expansion exceeds 65536 nodes")?;
    if visiting.len() >= 256 {
        return Err("expression depth exceeds this adapter's current limit of 256".into());
    }
    if !visiting.insert(index) {
        return Err("cyclic expression is unsupported in this slice".into());
    }
    let node = program
        .nodes
        .get(index as usize)
        .ok_or("node index out of bounds")?;
    let sort = node_sort(program, index)?;
    let span = native_span(program, node.span.as_ref(), native_spans)?;
    let result = match node.kind.as_ref().ok_or("missing node kind")? {
        pb::node::Kind::Var(name) if !name.is_empty() => Expr::Var(span, name.clone()),
        pb::node::Kind::Apply(apply) => {
            let call = native_apply(program, node, apply)?;
            Expr::Call(
                span,
                call.func,
                call.args
                    .iter()
                    .map(|argument| {
                        lower_expression(program, *argument, visiting, remaining, native_spans)
                    })
                    .collect::<Result<_, _>>()?,
            )
        }
        pb::node::Kind::Call(call) => Expr::Call(
            span,
            call.func.clone(),
            call.args
                .iter()
                .map(|argument| {
                    lower_expression(program, *argument, visiting, remaining, native_spans)
                })
                .collect::<Result<_, _>>()?,
        ),
        pb::node::Kind::GetCost(call) => Expr::Call(
            span,
            crate::set_cost::get_cost_table_name(&call.func),
            call.args
                .iter()
                .map(|argument| {
                    lower_expression(program, *argument, visiting, remaining, native_spans)
                })
                .collect::<Result<_, _>>()?,
        ),
        pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::PartialCall(call)),
        }) => {
            if !matches!(
                program.sorts[node.sort_id as usize].kind,
                Some(pb::sort::Kind::Func(_))
            ) {
                return Err("partial call requires a function sort".into());
            }
            *remaining = remaining
                .checked_sub(1)
                .ok_or("native expression expansion exceeds 65536 nodes")?;
            let mut args = vec![Expr::Lit(span.clone(), Literal::String(call.func.clone()))];
            for argument in &call.args {
                args.push(lower_expression(
                    program,
                    *argument,
                    visiting,
                    remaining,
                    native_spans,
                )?);
            }
            Expr::Call(
                span,
                egglog::sort::FunctionSort::constructor_alias(&sort),
                args,
            )
        }
        pb::node::Kind::PrimitiveValue(value) => Expr::Lit(
            span,
            value::Scalar::decode(Some(&sort), value)?.into_literal()?,
        ),
        _ => return Err("this node kind is unsupported in a value position".into()),
    };
    visiting.remove(&index);
    Ok(result)
}

fn facts(
    program: &pb::Program,
    indices: &[u32],
    native_spans: &NativeSpans,
    capture: Option<u32>,
    mut occupied: impl FnMut(&str) -> bool,
) -> Result<(Vec<Fact>, HashMap<u32, Expr>), String> {
    // Query references are logical binders, not evaluated action locals. A
    // first pass classifies value edges so a standalone relation predicate is
    // never bound as a value of its private native row sort. The second pass
    // emits each node once, with shallow edges, even across Union backedges.
    let roots: HashSet<_> = indices.iter().copied().collect();
    let mut pending: Vec<_> = indices.iter().rev().copied().collect();
    if let Some(index) = capture {
        pending.push(index);
    }
    let mut values: HashSet<_> = capture.into_iter().collect();
    let mut seen = HashSet::new();
    let mut order = Vec::new();
    let mut names = HashSet::new();
    while let Some(index) = pending.pop() {
        if !seen.insert(index) {
            continue;
        }
        let node = program
            .nodes
            .get(index as usize)
            .ok_or("fact index out of bounds")?;
        order.push(index);
        let children = match node.kind.as_ref().ok_or("missing node kind")? {
            pb::node::Kind::Var(name) if !name.is_empty() => {
                names.insert(native_name("var", name));
                continue;
            }
            pb::node::Kind::Call(call)
            | pb::node::Kind::GetCost(call)
            | pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::PartialCall(call)),
            }) => &call.args,
            pb::node::Kind::Union(union) => {
                if union.members.is_empty() {
                    return Err("empty query Union is invalid".into());
                }
                values.insert(index);
                &union.members
            }
            pb::node::Kind::PrimitiveValue(_) => continue,
            _ => return Err("unsupported query graph node".into()),
        };
        values.extend(children.iter().copied());
        pending.extend(children.iter().rev().copied());
    }
    let mut next = 0usize;
    let mut fresh = |span: ast::Span| {
        let name = loop {
            let name = format!("__egglog_proto_query_{next}");
            next += 1;
            if !names.contains(&name) && !occupied(&name) && !occupied(&format!("${name}")) {
                break name;
            }
        };
        Expr::Var(span, name)
    };
    let mut references = HashMap::new();
    for &index in &order {
        let node = &program.nodes[index as usize];
        let span = native_span(program, node.span.as_ref(), native_spans)?;
        if let Some(pb::node::Kind::Var(name)) = &node.kind {
            // Rename at this use, never in the arena: the same Var may be a
            // deferred merge's special `old`/`new` in another binder.
            references.insert(index, Expr::Var(span, native_name("var", name)));
        } else if values.contains(&index) {
            references.insert(index, fresh(span));
        }
    }
    let mut result = Vec::new();
    let mut pending: Vec<_> = order.iter().rev().map(|index| (*index, false)).collect();
    let mut seen = HashSet::new();
    while let Some((index, exit)) = pending.pop() {
        let node = &program.nodes[index as usize];
        if !exit {
            if !seen.insert(index) {
                continue;
            }
            pending.push((index, true));
            let children = match node.kind.as_ref().unwrap() {
                pb::node::Kind::Call(call)
                | pb::node::Kind::GetCost(call)
                | pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::PartialCall(call)),
                }) => &call.args,
                pb::node::Kind::Union(union) => &union.members,
                _ => continue,
            };
            pending.extend(children.iter().rev().map(|child| (*child, false)));
            continue;
        }
        let span = native_span(program, node.span.as_ref(), native_spans)?;
        let value = match node.kind.as_ref().unwrap() {
            pb::node::Kind::Apply(apply) => {
                let call = native_apply(program, node, apply)?;
                Expr::Call(
                    span.clone(),
                    call.func,
                    call.args
                        .iter()
                        .map(|argument| references[argument].clone())
                        .collect(),
                )
            }
            pb::node::Kind::Union(union) => {
                let value = references[&index].clone();
                for member in &union.members {
                    result.push(Fact::Eq(
                        span.clone(),
                        value.clone(),
                        references[member].clone(),
                    ));
                }
                continue;
            }
            pb::node::Kind::Var(_) => references[&index].clone(),
            pb::node::Kind::Call(call)
            | pb::node::Kind::GetCost(call)
            | pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::PartialCall(call)),
            }) => {
                let mut args: Vec<_> = call
                    .args
                    .iter()
                    .map(|child| references[child].clone())
                    .collect();
                let target = match &node.kind {
                    Some(pb::node::Kind::Call(_)) => call.func.clone(),
                    Some(pb::node::Kind::GetCost(_)) => {
                        crate::set_cost::get_cost_table_name(&call.func)
                    }
                    _ => {
                        if !matches!(
                            program.sorts[node.sort_id as usize].kind,
                            Some(pb::sort::Kind::Func(_))
                        ) {
                            return Err("partial call requires a function sort".into());
                        }
                        // Native FunctionCtor's target must remain syntactically
                        // literal; captured graph operands still use references.
                        args.insert(
                            0,
                            Expr::Lit(span.clone(), Literal::String(call.func.clone())),
                        );
                        egglog::sort::FunctionSort::constructor_alias(&node_sort(program, index)?)
                    }
                };
                Expr::Call(span.clone(), target, args)
            }
            pb::node::Kind::PrimitiveValue(_) => {
                // This adapter is fixed-size for a concrete payload, not a walk
                // of graph children. Consume it into shallow definitions so a
                // shared large String/exact value occurs only once in the AST.
                let literal = expression(program, index, &mut HashSet::new(), native_spans)?;
                if let Some(target) = references.get(&index) {
                    enum Leaf {
                        Enter(Expr, Option<Expr>),
                        Call(ast::Span, String, usize, Expr),
                    }
                    let mut pending = vec![Leaf::Enter(literal, Some(target.clone()))];
                    let mut operands = Vec::new();
                    while let Some(step) = pending.pop() {
                        match step {
                            Leaf::Enter(Expr::Call(span, name, args), target) => {
                                let target = target.unwrap_or_else(|| fresh(span.clone()));
                                pending.push(Leaf::Call(span, name, args.len(), target));
                                pending.extend(
                                    args.into_iter().rev().map(|arg| Leaf::Enter(arg, None)),
                                );
                            }
                            Leaf::Enter(value, target) => {
                                let target = target.unwrap_or_else(|| fresh(value.span().clone()));
                                result.push(Fact::Eq(value.span().clone(), value, target.clone()));
                                operands.push(target);
                            }
                            Leaf::Call(span, name, arity, target) => {
                                let args = operands.split_off(operands.len() - arity);
                                result.push(Fact::Eq(
                                    span.clone(),
                                    Expr::Call(span, name, args),
                                    target.clone(),
                                ));
                                operands.push(target);
                            }
                        }
                    }
                    continue;
                }
                literal
            }
        };
        if let Some(target) = references.get(&index)
            && !matches!(&node.kind, Some(pb::node::Kind::Var(_)))
        {
            result.push(Fact::Eq(span, value, target.clone()));
        } else if roots.contains(&index) {
            // A predicate root is required to match, but its output is not a
            // wire value. In particular, keep relation row sorts private.
            result.push(Fact::Fact(value));
        }
    }
    Ok((result, references))
}

// Unit marks the predicate-use surface, not a value of the native relation's
// hidden row sort. Check positions before reconciliation/publication or any
// effects. Every value edge is checked independently: memoizing a node after a
// legal standalone use must not authorize its later use as a value. This also
// leaves ordinary Union cycles to the existing identity-aware validator.
fn validate_relation_uses(program: &pb::Program, saved: &pb::Program) -> Result<(), String> {
    use pb::{node::Kind as N, primitive_value::Value as V};
    let relations: HashSet<_> = program
        .declarations
        .iter()
        .chain(&saved.declarations)
        .filter_map(|declaration| match &declaration.kind {
            Some(pb::declaration::Kind::Relation(relation)) => Some(relation.name.as_str()),
            _ => None,
        })
        .collect();
    if relations.is_empty() {
        return Ok(());
    }
    let value = |index: u32| -> Result<(), String> {
        let node = program
            .nodes
            .get(index as usize)
            .ok_or("relation use node out of bounds")?;
        if matches!(&node.kind, Some(N::Call(call)) if relations.contains(call.func.as_str())) {
            return Err("relation predicates cannot be used as values or captures".into());
        }
        Ok(())
    };
    for node in &program.nodes {
        match &node.kind {
            Some(N::Call(call)) => {
                if relations.contains(call.func.as_str())
                    && !matches!(
                        program.sorts.get(node.sort_id as usize).and_then(|sort| sort.kind.as_ref()),
                        Some(pb::sort::Kind::Application(family)) if family.name == "Unit" && family.args.is_empty()
                    )
                {
                    return Err("relation calls require the Unit predicate annotation".into());
                }
                for arg in &call.args {
                    value(*arg)?;
                }
            }
            Some(N::GetCost(call)) => {
                if relations.contains(call.func.as_str()) {
                    return Err("relation rows do not support constructor cost reads".into());
                }
                for arg in &call.args {
                    value(*arg)?;
                }
            }
            Some(N::Union(union)) => {
                for member in &union.members {
                    value(*member)?;
                }
            }
            Some(N::PrimitiveValue(primitive)) => match &primitive.value {
                Some(V::PartialCall(call)) => {
                    if relations.contains(call.func.as_str()) {
                        return Err("relation predicates cannot be partially applied".into());
                    }
                    for arg in &call.args {
                        value(*arg)?;
                    }
                }
                Some(V::Lambda(lambda)) => {
                    value(lambda.body)?;
                    for capture in &lambda.captures {
                        value(*capture)?;
                    }
                }
                Some(V::Vec(list) | V::Set(list) | V::Multiset(list)) => {
                    for item in &list.items {
                        value(*item)?;
                    }
                }
                Some(V::Map(map)) => {
                    for entry in &map.entries {
                        value(entry.key.ok_or("missing map key")?)?;
                        value(entry.value.ok_or("missing map value")?)?;
                    }
                }
                Some(V::Pair(pair)) => {
                    value(pair.first.ok_or("missing pair first")?)?;
                    value(pair.second.ok_or("missing pair second")?)?;
                }
                Some(V::Maybe(maybe)) => {
                    if let Some(item) = maybe.value {
                        value(item)?;
                    }
                }
                Some(V::Custom(custom)) => {
                    for arg in &custom.args {
                        value(*arg)?;
                    }
                }
                _ => (),
            },
            _ => (),
        }
    }
    let action = |action: &pb::Action| -> Result<(), String> {
        let target = match &action.kind {
            Some(pb::action::Kind::Set(set)) => {
                value(set.value.ok_or("missing set value")?)?;
                let call = set.target.as_ref().ok_or("missing set target")?;
                if relations.contains(call.func.as_str()) {
                    return Err("relation rows cannot be Set".into());
                }
                Some(call)
            }
            Some(pb::action::Kind::SetCost(set)) => {
                value(set.cost.ok_or("missing cost value")?)?;
                Some(set.target.as_ref().ok_or("missing cost target")?)
            }
            Some(pb::action::Kind::Subsume(call)) => {
                if relations.contains(call.func.as_str()) {
                    return Err("relation rows cannot be Subsumed".into());
                }
                Some(call)
            }
            Some(pb::action::Kind::Delete(call)) => Some(call),
            // Only the direct result is ignored. Its argument value edges have
            // already been checked, including any shared use of that node.
            Some(pb::action::Kind::Term(_)) => None,
            _ => None,
        };
        if let Some(call) = target {
            for arg in &call.args {
                value(*arg)?;
            }
        }
        Ok(())
    };
    for declaration in &program.declarations {
        match &declaration.kind {
            Some(pb::declaration::Kind::Function(function)) => {
                if let Some(merge) = function.merge {
                    value(merge)?;
                }
            }
            Some(pb::declaration::Kind::UserDefinedPrimitive(primitive)) => {
                if let Some(body) = primitive.body {
                    value(body)?;
                }
            }
            Some(pb::declaration::Kind::Constructor(constructor)) => {
                if let Some(cost) = constructor.cost {
                    value(cost)?;
                }
            }
            _ => (),
        }
    }
    for rule in graph::rules(program) {
        match &rule.kind {
            Some(pb::rule::Kind::Rule(rule)) => {
                for head in &rule.head {
                    action(head)?;
                }
            }
            Some(pb::rule::Kind::Rewrite(rewrite)) => {
                value(rewrite.lhs)?;
                value(rewrite.rhs)?;
            }
            Some(pb::rule::Kind::Birewrite(rewrite)) => {
                value(rewrite.lhs)?;
                value(rewrite.rhs)?;
            }
            _ => (),
        }
    }
    for command in command_tree(&program.commands) {
        match &command.kind {
            Some(pb::command::Kind::Action(head)) => action(head)?,
            Some(pb::command::Kind::Extract(extract)) => {
                for root in &extract.roots {
                    value(*root)?;
                }
            }
            // Query roots (including loop conditions) may be relation calls;
            // their nested edges were checked above. Unsupported command kinds
            // keep their existing fail-closed admission later in preparation.
            _ => (),
        }
    }
    Ok(())
}

// Validate the entire arena, including unused entries, without interpreting it.
// Removing Union outgoing edges must leave a DAG: every permitted cycle crosses
// an identity boundary. Value lowering still validates each actual use's context.
fn validate_node_graph(program: &pb::Program, native_spans: &NativeSpans) -> Result<(), String> {
    let mut edges = Vec::with_capacity(program.nodes.len());
    for (index, node) in program.nodes.iter().enumerate() {
        let sort = node_sort(program, index as u32)?;
        native_span(program, node.span.as_ref(), native_spans)?;
        let children = match &node.kind {
            Some(pb::node::Kind::Call(call) | pb::node::Kind::GetCost(call)) => call.args.clone(),
            Some(pb::node::Kind::Apply(apply)) => native_apply(program, node, apply)?.args,
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::PartialCall(call)),
            })) => {
                if !matches!(
                    program.sorts[node.sort_id as usize].kind,
                    Some(pb::sort::Kind::Func(_))
                ) {
                    return Err("partial call requires a function sort".into());
                }
                call.args.clone()
            }
            Some(pb::node::Kind::Union(union)) => {
                if union.members.is_empty()
                    && !matches!(
                        program.sorts[node.sort_id as usize].kind,
                        Some(pb::sort::Kind::Eq(_))
                    )
                {
                    return Err("empty Union requires an equality sort".into());
                }
                for member in &union.members {
                    if node_sort(program, *member)? != sort {
                        return Err("Union member sort mismatch".into());
                    }
                }
                vec![]
            }
            _ => {
                expression(program, index as u32, &mut HashSet::new(), native_spans)?;
                vec![]
            }
        };
        for child in &children {
            node_sort(program, *child)?;
        }
        edges.push(children);
    }
    let mut state = vec![0u8; edges.len()];
    for start in 0..edges.len() {
        let mut pending = vec![(start, false)];
        while let Some((index, exit)) = pending.pop() {
            if exit {
                state[index] = 2;
                continue;
            }
            match state[index] {
                2 => continue,
                1 => return Err("cyclic expression must cross a Union boundary".into()),
                _ => (),
            }
            state[index] = 1;
            pending.push((index, true));
            pending.extend(
                edges[index]
                    .iter()
                    .rev()
                    .map(|child| (*child as usize, false)),
            );
        }
    }
    Ok(())
}

// Each evaluated action owns an ordinary value memo. Union identity frames are
// classified separately and can outlive this one action.
fn classify_action_dags(program: &pb::Program) -> Result<HashMap<Vec<u32>, HashSet<u32>>, String> {
    let mut candidates = vec![];
    for (path, action) in action_sites(&program.commands) {
        candidates.push((path, action_roots(action)?));
    }
    classify_value_dags(program, candidates)
}

// Eligibility is independent of the operation; only evaluated values are local
// to an action or one ordered extraction root.
fn classify_value_dags<K: Eq + std::hash::Hash>(
    program: &pb::Program,
    sites: impl IntoIterator<Item = (K, Vec<u32>)>,
) -> Result<HashMap<K, HashSet<u32>>, String> {
    let mut selected = HashMap::new();
    for (path, roots) in sites {
        let root_union = if let [index] = roots.as_slice() {
            let node = program
                .nodes
                .get(*index as usize)
                .ok_or("action node out of bounds")?;
            matches!(&node.kind, Some(pb::node::Kind::Union(union)) if union.members.len() == 2)
                .then_some(*index)
        } else {
            None
        };
        // Set keys precede its value in the existing scoped action compiler.
        let mut pending = roots;
        let mut seen = HashSet::new();
        let mut eligible = true;
        while let Some(index) = pending.pop() {
            if !seen.insert(index) {
                continue;
            }
            let children = match program
                .nodes
                .get(index as usize)
                .ok_or("action node out of bounds")?
                .kind
                .as_ref()
                .unwrap()
            {
                pb::node::Kind::Call(call)
                | pb::node::Kind::GetCost(call)
                | pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::PartialCall(call)),
                }) => &call.args[..],
                pb::node::Kind::Apply(apply) => {
                    pending.extend(apply.function.iter().chain(&apply.args));
                    continue;
                }
                pb::node::Kind::Union(union) if root_union == Some(index) => &union.members[..],
                pb::node::Kind::Var(_) => &[],
                pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value:
                        Some(
                            pb::primitive_value::Value::I64(_)
                            | pb::primitive_value::Value::F64Bits(_)
                            | pb::primitive_value::Value::String(_)
                            | pb::primitive_value::Value::Bool(_)
                            | pb::primitive_value::Value::Unit(_)
                            | pb::primitive_value::Value::BigInt(_)
                            | pb::primitive_value::Value::BigRat(_)
                            | pb::primitive_value::Value::Rational(_),
                        ),
                }) => &[],
                _ => {
                    eligible = false;
                    break;
                }
            };
            pending.extend(children);
        }
        if eligible {
            selected.insert(path, seen);
        }
    }
    Ok(selected)
}

// The ordered evaluated roots of an action: Set's row-address arguments precede
// its value, and Delete/Subsume never evaluate the addressed table itself.
fn action_roots(action: &pb::Action) -> Result<Vec<u32>, String> {
    Ok(match action.kind.as_ref().ok_or("missing action kind")? {
        pb::action::Kind::Term(index) => vec![*index],
        pb::action::Kind::Set(set) => set
            .target
            .as_ref()
            .ok_or("missing set target")?
            .args
            .iter()
            .copied()
            .chain([set.value.ok_or("missing set value")?])
            .collect(),
        pb::action::Kind::Delete(call) | pb::action::Kind::Subsume(call) => call.args.clone(),
        pb::action::Kind::Panic(_) => vec![],
        pb::action::Kind::SetCost(set) => set
            .target
            .as_ref()
            .ok_or("missing cost target")?
            .args
            .iter()
            .copied()
            .chain([set.cost.ok_or("missing cost value")?])
            .collect(),
    })
}

// Preclassify the whole request, not just the current command. A binary first
// use must capture immediately if a later action reuses that same occurrence.
// Rule heads retain their independent boundary; Fail is transparent and loop
// bodies get a fresh evaluated-value frame on every iteration.
fn classify_union_actions(
    program: &pb::Program,
    constructor_targets: &HashSet<String>,
    constructor_costs: bool,
) -> Result<HashSet<Vec<u32>>, String> {
    let unions = |action: &pb::Action| -> Result<(HashSet<u32>, bool), String> {
        let mut pending = action_roots(action)?;
        let root = match action.kind {
            Some(pb::action::Kind::Term(index)) => Some(index),
            _ => None,
        };
        let mut seen = HashSet::new();
        let mut unions = HashSet::new();
        let mut root_cycle = false;
        while let Some(index) = pending.pop() {
            if !seen.insert(index) {
                root_cycle |= Some(index) == root;
                continue;
            }
            match program
                .nodes
                .get(index as usize)
                .ok_or("action node out of bounds")?
                .kind
                .as_ref()
            {
                Some(pb::node::Kind::Union(union)) => {
                    if !matches!(
                        program.sorts[program.nodes[index as usize].sort_id as usize].kind,
                        Some(pb::sort::Kind::Eq(_))
                    ) {
                        return Err("action Union requires an equality sort".into());
                    }
                    unions.insert(index);
                    pending.extend(&union.members);
                }
                Some(pb::node::Kind::Call(call) | pb::node::Kind::GetCost(call))
                | Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::PartialCall(call)),
                })) => pending.extend(&call.args),
                _ => (),
            }
        }
        Ok((unions, root_cycle))
    };
    let mut uses = HashMap::<u32, usize>::new();
    for command in command_tree(&program.commands) {
        if let Some(pb::command::Kind::Action(action)) = &command.kind {
            for union in unions(action)?.0 {
                *uses.entry(union).or_default() += 1;
            }
        }
    }
    let mut scoped = HashSet::new();
    for (path, action) in action_sites(&program.commands) {
        let (reached, root_cycle) = unions(action)?;
        let cost_action = matches!(action.kind, Some(pb::action::Kind::SetCost(_)))
            || constructor_costs
                && matches!(&action.kind, Some(pb::action::Kind::Delete(call)) if constructor_targets.contains(&call.func));
        if reached.is_empty() && !cost_action {
            continue;
        }
        let generalized = cost_action
            || root_cycle
            || reached.iter().any(|union| uses[union] > 1)
            || !matches!(&action.kind, Some(pb::action::Kind::Term(index))
                if reached.len() == 1 && matches!(&program.nodes[*index as usize].kind,
                    Some(pb::node::Kind::Union(union)) if union.members.len() == 2));
        if generalized {
            check_variables(program, &action_roots(action)?, &mut HashMap::new(), false)?;
            scoped.insert(path);
        }
    }
    Ok(scoped)
}

// Source rendering and rule heads still use the legacy binary-action lowering;
// they cannot borrow a direct request's captured native identity frame.
fn validate_legacy_union_scope<'a>(
    program: &pb::Program,
    actions: impl IntoIterator<Item = &'a pb::Action>,
) -> Result<(), String> {
    let mut seen = HashSet::new();
    for action in actions {
        if let Some(pb::action::Kind::Term(index)) = &action.kind {
            let node = program
                .nodes
                .get(*index as usize)
                .ok_or("action node out of bounds")?;
            if matches!(node.kind, Some(pb::node::Kind::Union(_))) && !seen.insert(*index) {
                return Err("repeated action Union occurrence requires identity retention, which is not supported yet".into());
            }
        }
    }
    Ok(())
}

fn validate_union_occurrences(program: &pb::Program) -> Result<(), String> {
    validate_legacy_union_scope(
        program,
        command_tree(&program.commands).filter_map(|command| match &command.kind {
            Some(pb::command::Kind::Action(action)) => Some(action),
            _ => None,
        }),
    )?;
    for rule in graph::rules(program) {
        if let Some(pb::rule::Kind::Rule(rule)) = &rule.kind {
            validate_legacy_union_scope(program, &rule.head)?;
        }
    }
    Ok(())
}

// Both byte execution and Source rendering use this first-demand local plan.
// The caller owns one memo per top-level action or ordered rule head.
fn action_dag_actions(
    program: &pb::Program,
    action: &pb::Action,
    mut occupied: impl FnMut(&str) -> bool,
    native_spans: &NativeSpans,
    memo: &mut HashMap<u32, Expr>,
    next: &mut usize,
) -> Result<(Vec<Action>, Vec<u32>), String> {
    enum Walk {
        Enter(u32),
        Call(u32, usize),
        CostTarget,
    }
    let union = match &action.kind {
        Some(pb::action::Kind::Term(index)) => match &program.nodes[*index as usize].kind {
            Some(pb::node::Kind::Union(union)) => {
                if !matches!(
                    program.sorts[program.nodes[*index as usize].sort_id as usize].kind,
                    Some(pb::sort::Kind::Eq(_))
                ) {
                    return Err("action Union requires an equality sort".into());
                }
                if let Some(value) = memo.get(index) {
                    return Ok((
                        vec![Action::Expr(
                            native_span(program, action.span.as_ref(), native_spans)?,
                            value.clone(),
                        )],
                        vec![],
                    ));
                }
                if union.members.len() != 2 {
                    return Err("rule/action Union currently requires exactly two members".into());
                }
                Some((*index, union.members.clone()))
            }
            _ => None,
        },
        _ => None,
    };
    let roots = match &union {
        Some((_, members)) => members.clone(),
        None => action_roots(action)?,
    };
    let mut pending: Vec<_> = roots.into_iter().rev().map(Walk::Enter).collect();
    let mut results = Vec::new();
    let mut actions = Vec::new();
    let mut evaluations = Vec::new();
    if let Some(pb::action::Kind::SetCost(set)) = &action.kind {
        pending = vec![
            Walk::Enter(set.cost.ok_or("missing cost value")?),
            Walk::CostTarget,
        ];
        pending.extend(
            set.target
                .as_ref()
                .ok_or("missing cost target")?
                .args
                .iter()
                .rev()
                .map(|index| Walk::Enter(*index)),
        );
    }
    let mut bind_value = |index: u32, value: Expr| -> Result<(String, Expr), String> {
        let span = native_span(
            program,
            program.nodes[index as usize].span.as_ref(),
            native_spans,
        )?;
        let name = loop {
            let candidate = format!("__egglog_proto_action_{next}");
            *next += 1;
            if !occupied(&candidate) && !occupied(&format!("${candidate}")) {
                break candidate;
            }
        };
        actions.push(Action::Let(span.clone(), name.clone(), value));
        evaluations.push(index);
        Ok((name.clone(), Expr::Var(span, name)))
    };
    while let Some(step) = pending.pop() {
        let (index, value) = match step {
            Walk::Enter(index) => {
                let node = &program.nodes[index as usize];
                if let Some(value) = memo.get(&index) {
                    results.push(value.clone());
                    continue;
                }
                match node.kind.as_ref().expect("validated node") {
                    pb::node::Kind::Apply(apply) => {
                        let call = native_apply(program, node, apply)?;
                        pending.push(Walk::Call(index, call.args.len()));
                        pending.extend(call.args.iter().rev().map(|child| Walk::Enter(*child)));
                        continue;
                    }
                    pb::node::Kind::Call(call)
                    | pb::node::Kind::GetCost(call)
                    | pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::PartialCall(call)),
                    }) => {
                        pending.push(Walk::Call(index, call.args.len()));
                        pending.extend(call.args.iter().rev().map(|child| Walk::Enter(*child)));
                        continue;
                    }
                    pb::node::Kind::Var(_)
                    | pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value:
                            Some(
                                pb::primitive_value::Value::I64(_)
                                | pb::primitive_value::Value::F64Bits(_)
                                | pb::primitive_value::Value::String(_)
                                | pb::primitive_value::Value::Bool(_)
                                | pb::primitive_value::Value::Unit(_)
                                | pb::primitive_value::Value::BigInt(_)
                                | pb::primitive_value::Value::BigRat(_)
                                | pb::primitive_value::Value::Rational(_),
                            ),
                    }) => {
                        let value = expression(program, index, &mut HashSet::new(), native_spans)?;
                        if matches!(value, Expr::Var(..)) {
                            memo.insert(index, value.clone());
                            results.push(value);
                            continue;
                        }
                        (index, value)
                    }
                    _ => {
                        return Err("unsupported action DAG node".into());
                    }
                }
            }
            Walk::Call(index, arity) => {
                let node = &program.nodes[index as usize];
                let mut args = results.split_off(results.len() - arity);
                let target = match node.kind.as_ref().unwrap() {
                    pb::node::Kind::Call(call) => call.func.clone(),
                    pb::node::Kind::Apply(_) => "unstable-app".into(),
                    pb::node::Kind::GetCost(call) => {
                        crate::set_cost::get_cost_table_name(&call.func)
                    }
                    pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::PartialCall(call)),
                    }) => {
                        args.insert(
                            0,
                            Expr::Lit(
                                native_span(program, node.span.as_ref(), native_spans)?,
                                Literal::String(call.func.clone()),
                            ),
                        );
                        egglog::sort::FunctionSort::constructor_alias(&node_sort(program, index)?)
                    }
                    _ => unreachable!(),
                };
                let span = native_span(program, node.span.as_ref(), native_spans)?;
                (index, Expr::Call(span, target, args))
            }
            Walk::CostTarget => {
                let Some(pb::action::Kind::SetCost(set)) = &action.kind else {
                    unreachable!()
                };
                let target = set.target.as_ref().unwrap();
                bind_value(
                    set.cost.unwrap(),
                    Expr::Call(
                        native_span(program, action.span.as_ref(), native_spans)?,
                        target.func.clone(),
                        results.clone(),
                    ),
                )?;
                continue;
            }
        };
        let (_, value) = bind_value(index, value)?;
        memo.insert(index, value.clone());
        results.push(value);
    }
    let span = native_span(program, action.span.as_ref(), native_spans)?;
    actions.push(match action.kind.as_ref().unwrap() {
        pb::action::Kind::Term(_) => {
            if let Some((index, _)) = union {
                let rhs = results.pop().unwrap();
                let lhs = results.pop().unwrap();
                memo.insert(index, lhs.clone());
                Action::Union(span, lhs, rhs)
            } else {
                Action::Expr(span, results.pop().unwrap())
            }
        }
        pb::action::Kind::Set(set) => {
            let value = results.pop().unwrap();
            Action::Set(
                span,
                set.target.as_ref().unwrap().func.clone(),
                results,
                value,
            )
        }
        pb::action::Kind::Delete(call) | pb::action::Kind::Subsume(call) => Action::Change(
            span,
            if matches!(action.kind, Some(pb::action::Kind::Delete(_))) {
                ast::Change::Delete
            } else {
                ast::Change::Subsume
            },
            call.func.clone(),
            results,
        ),
        pb::action::Kind::Panic(message) => Action::Panic(span, message.clone()),
        pb::action::Kind::SetCost(set) => {
            let cost = results.pop().unwrap();
            Action::Set(
                span,
                crate::set_cost::get_cost_table_name(&set.target.as_ref().unwrap().func),
                results,
                cost,
            )
        }
    });
    Ok((actions, evaluations))
}

// One root has the same flush/recovery boundary as native eval_expr. Its memo
// and captured value never outlive this evaluation, including aggregate Extract.
fn eval_extract_root(
    graph: &mut EGraph,
    program: &pb::Program,
    index: u32,
    dag: Option<&HashSet<u32>>,
    execute: bool,
    native_spans: &NativeSpans,
) -> Result<Option<(ArcSort, Value)>, egglog::Error> {
    let error = egglog::Error::BackendError;
    let sort_name = node_sort(program, index).map_err(error)?;
    let sort = graph
        .get_sort_by_name(&sort_name)
        .cloned()
        .ok_or_else(|| error(format!("unknown extraction root sort {sort_name}")))?;
    if dag.is_none() {
        let expr = expression(program, index, &mut HashSet::new(), native_spans).map_err(error)?;
        if execute {
            return graph.eval_expr(&expr).map(Some);
        }
        graph.typecheck_expr_with_bindings_and_output(&expr, &[], sort, egglog::Context::Full)?;
        return Ok(None);
    }
    let action = pb::Action {
        kind: Some(pb::action::Kind::Term(index)),
        span: program.nodes[index as usize].span,
    };
    let mut next = 0;
    let (mut actions, _) = action_dag_actions(
        program,
        &action,
        |name| {
            graph.type_info().is_global(name)
                || graph.get_sort_by_name(name).is_some()
                || graph.type_info().get_func_type(name).is_some()
                || graph.type_info().is_primitive(name)
        },
        native_spans,
        &mut HashMap::new(),
        &mut next,
    )
    .map_err(error)?;
    let Action::Expr(span, terminal) = actions.pop().expect("planned terminal") else {
        unreachable!("root plan has a Term terminal")
    };
    // Continue the planner's monotonic allocator; no retained-prefix scan.
    let name = loop {
        let candidate = format!("__egglog_proto_action_{next}");
        next += 1;
        if !graph.type_info().is_global(&candidate)
            && !graph.type_info().is_global(&format!("${candidate}"))
            && graph.get_sort_by_name(&candidate).is_none()
            && graph.type_info().get_func_type(&candidate).is_none()
            && !graph.type_info().is_primitive(&candidate)
        {
            break candidate;
        }
    };
    actions.push(Action::Let(span, name.clone(), terminal));
    let (result, mut captured) = graph.eval_scoped_actions(&[], execute, |builder| {
        for action in actions {
            builder.action(action)?;
        }
        let actual = builder.capture_local(&name)?;
        if actual.name() != sort.name() {
            return Err(error("extraction root sort mismatch".into()));
        }
        Ok(())
    });
    result?;
    Ok(execute.then(|| (sort, captured.pop().expect("executed root capture").1)))
}

// Only Union locations are retained across direct commands. Ordinary results
// share first-demand locals inside this action, in one native action boundary.
#[allow(clippy::too_many_arguments)]
fn eval_scoped_action(
    graph: &mut EGraph,
    program: &pb::Program,
    action: &pb::Action,
    values: &mut HashMap<u32, Value>,
    execute: bool,
    dag: Option<&HashSet<u32>>,
    observer: &mut dyn FnMut(ExecutionEvent<'_>),
    native_spans: &NativeSpans,
) -> Result<(), egglog::Error> {
    if dag.is_some() {
        let (actions, _) = action_dag_actions(
            program,
            action,
            |name| {
                graph.type_info().is_global(name)
                    || graph.get_sort_by_name(name).is_some()
                    || graph.type_info().get_func_type(name).is_some()
                    || graph.type_info().is_primitive(name)
            },
            native_spans,
            &mut HashMap::new(),
            &mut 0,
        )
        .map_err(egglog::Error::BackendError)?;
        let command = Command::ActionScope(
            native_span(program, action.span.as_ref(), native_spans)
                .map_err(egglog::Error::BackendError)?,
            ast::GenericActions(actions),
        );
        return if execute {
            graph
                .run_program_observed(vec![command], &mut |_, _, _| {}, &mut |_, event| {
                    observer(event)
                })
                .map(|_| ())
        } else {
            graph.validate_program(vec![command]).map(|_| ())
        };
    }
    enum Walk {
        Enter(u32),
        Call(u32, usize),
        Member(u32, usize),
        CostTarget,
    }
    let error = egglog::Error::BackendError;
    let roots = action_roots(action).map_err(error)?;
    let cost_table = match &action.kind {
        Some(pb::action::Kind::Delete(call)) => {
            let name = crate::set_cost::get_cost_table_name(&call.func);
            graph.get_function(&name).is_some().then_some(name)
        }
        _ => None,
    };
    let mut slots = HashMap::new();
    let mut materialized = HashSet::new();
    let mut memo = HashMap::<u32, Expr>::new();
    let mut inputs = Vec::new();
    let mut pending: Vec<_> = roots.iter().rev().copied().collect();
    let mut seen = HashSet::new();
    while let Some(index) = pending.pop() {
        if !seen.insert(index) {
            continue;
        }
        let children = match program.nodes[index as usize].kind.as_ref().unwrap() {
            pb::node::Kind::Union(union) => {
                if let Some(value) = values.get(&index) {
                    let name = format!("__egglog_proto_union_{index}");
                    inputs.push((
                        name.clone(),
                        node_sort(program, index).map_err(error)?,
                        *value,
                    ));
                    slots.insert(index, name);
                    materialized.insert(index);
                    continue;
                }
                &union.members
            }
            pb::node::Kind::Call(call)
            | pb::node::Kind::GetCost(call)
            | pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::PartialCall(call)),
            }) => &call.args,
            _ => continue,
        };
        pending.extend(children.iter().rev().copied());
    }
    let compile = |builder: &mut egglog::ScopedActionBuilder<'_>| {
        let mut pending = if let Some(pb::action::Kind::SetCost(set)) = &action.kind {
            let mut pending = vec![Walk::Enter(set.cost.unwrap()), Walk::CostTarget];
            pending.extend(
                set.target
                    .as_ref()
                    .unwrap()
                    .args
                    .iter()
                    .rev()
                    .map(|index| Walk::Enter(*index)),
            );
            pending
        } else {
            roots
                .iter()
                .rev()
                .map(|index| Walk::Enter(*index))
                .collect()
        };
        let mut results = Vec::<Expr>::new();
        let mut temporary = 0usize;
        let mut remaining = 65_536usize;
        while let Some(step) = pending.pop() {
            remaining = remaining
                .checked_sub(1)
                .ok_or_else(|| error("native action expansion exceeds 65536 steps".into()))?;
            match step {
                Walk::Enter(index) => {
                    let node = &program.nodes[index as usize];
                    let span =
                        native_span(program, node.span.as_ref(), native_spans).map_err(error)?;
                    if let Some(value) = memo.get(&index) {
                        results.push(value.clone());
                        continue;
                    }
                    match node.kind.as_ref().expect("validated node") {
                        pb::node::Kind::Union(union) => {
                            if !matches!(
                                program.sorts[node.sort_id as usize].kind,
                                Some(pb::sort::Kind::Eq(_))
                            ) {
                                return Err(error("action Union requires an equality sort".into()));
                            }
                            let first_use = match slots.entry(index) {
                                std::collections::hash_map::Entry::Vacant(entry) => {
                                    entry.insert(format!("__egglog_proto_union_{index}"));
                                    true
                                }
                                std::collections::hash_map::Entry::Occupied(_) => false,
                            };
                            if !first_use {
                                // A reached backedge needs a real value now. It
                                // is not an eager allocation for a pending slot.
                                if materialized.insert(index) {
                                    builder.fresh_eq_class(
                                        slots[&index].clone(),
                                        &node_sort(program, index).map_err(error)?,
                                        span.clone(),
                                    )?;
                                    builder.capture_eq_class(&slots[&index])?;
                                }
                                results.push(Expr::Var(span, slots[&index].clone()));
                            } else if let Some(first) = union.members.first() {
                                pending.push(Walk::Member(index, 0));
                                pending.push(Walk::Enter(*first));
                            } else {
                                builder.fresh_eq_class(
                                    slots[&index].clone(),
                                    &node_sort(program, index).map_err(error)?,
                                    span.clone(),
                                )?;
                                builder.capture_eq_class(&slots[&index])?;
                                materialized.insert(index);
                                results.push(Expr::Var(span, slots[&index].clone()));
                            }
                        }
                        pb::node::Kind::Call(call)
                        | pb::node::Kind::GetCost(call)
                        | pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                            value: Some(pb::primitive_value::Value::PartialCall(call)),
                        }) => {
                            pending.push(Walk::Call(index, call.args.len()));
                            pending.extend(call.args.iter().rev().map(|index| Walk::Enter(*index)));
                        }
                        _ => {
                            let value =
                                expression(program, index, &mut HashSet::new(), native_spans)
                                    .map_err(error)?;
                            if matches!(value, Expr::Var(..)) {
                                memo.insert(index, value.clone());
                                results.push(value);
                                continue;
                            }
                            let name = format!("__egglog_proto_action_{temporary}");
                            temporary += 1;
                            builder.action(Action::Let(span.clone(), name.clone(), value))?;
                            let value = Expr::Var(span, name);
                            memo.insert(index, value.clone());
                            results.push(value);
                        }
                    }
                }
                Walk::Call(index, arity) => {
                    let node = &program.nodes[index as usize];
                    let span =
                        native_span(program, node.span.as_ref(), native_spans).map_err(error)?;
                    let mut args = results.split_off(results.len() - arity);
                    let function = match node.kind.as_ref().unwrap() {
                        pb::node::Kind::Call(call) => call.func.clone(),
                        pb::node::Kind::GetCost(call) => {
                            crate::set_cost::get_cost_table_name(&call.func)
                        }
                        pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                            value: Some(pb::primitive_value::Value::PartialCall(call)),
                        }) => {
                            args.insert(
                                0,
                                Expr::Lit(span.clone(), Literal::String(call.func.clone())),
                            );
                            egglog::sort::FunctionSort::constructor_alias(
                                &node_sort(program, index).map_err(error)?,
                            )
                        }
                        _ => unreachable!(),
                    };
                    let name = format!("__egglog_proto_action_{temporary}");
                    temporary += 1;
                    builder.action(Action::Let(
                        span.clone(),
                        name.clone(),
                        Expr::Call(span.clone(), function, args),
                    ))?;
                    let value = Expr::Var(span, name);
                    memo.insert(index, value.clone());
                    results.push(value);
                }
                Walk::Member(index, position) => {
                    let node = &program.nodes[index as usize];
                    let pb::node::Kind::Union(union) = node.kind.as_ref().unwrap() else {
                        unreachable!()
                    };
                    let span =
                        native_span(program, node.span.as_ref(), native_spans).map_err(error)?;
                    let value = results.pop().unwrap();
                    if materialized.insert(index) {
                        builder.action(Action::Let(span.clone(), slots[&index].clone(), value))?;
                        builder.capture_eq_class(&slots[&index])?;
                    } else {
                        // In particular, an earlier backedge's class must be
                        // unioned with the first completed member, never replaced.
                        builder.action(Action::Union(
                            span.clone(),
                            Expr::Var(span.clone(), slots[&index].clone()),
                            value,
                        ))?;
                    }
                    if let Some(next) = union.members.get(position + 1) {
                        pending.push(Walk::Member(index, position + 1));
                        pending.push(Walk::Enter(*next));
                    } else {
                        results.push(Expr::Var(span, slots[&index].clone()));
                    }
                }
                Walk::CostTarget => {
                    let Some(pb::action::Kind::SetCost(set)) = &action.kind else {
                        unreachable!()
                    };
                    builder.action(Action::Expr(
                        native_span(program, action.span.as_ref(), native_spans).map_err(error)?,
                        Expr::Call(
                            native_span(program, action.span.as_ref(), native_spans)
                                .map_err(error)?,
                            set.target.as_ref().unwrap().func.clone(),
                            results.clone(),
                        ),
                    ))?;
                }
            }
        }
        let span = native_span(program, action.span.as_ref(), native_spans).map_err(error)?;
        let action = match action.kind.as_ref().unwrap() {
            pb::action::Kind::Term(_) => Action::Expr(span, results.pop().unwrap()),
            pb::action::Kind::Set(set) => {
                let value = results.pop().unwrap();
                Action::Set(
                    span,
                    set.target.as_ref().unwrap().func.clone(),
                    results,
                    value,
                )
            }
            pb::action::Kind::SetCost(set) => {
                let value = results.pop().unwrap();
                Action::Set(
                    span,
                    crate::set_cost::get_cost_table_name(&set.target.as_ref().unwrap().func),
                    results,
                    value,
                )
            }
            pb::action::Kind::Delete(call) if cost_table.is_some() => {
                builder.action(Action::Change(
                    span.clone(),
                    ast::Change::Delete,
                    call.func.clone(),
                    results.clone(),
                ))?;
                Action::Change(
                    span,
                    ast::Change::Delete,
                    cost_table.clone().unwrap(),
                    results,
                )
            }
            pb::action::Kind::Delete(call) | pb::action::Kind::Subsume(call) => Action::Change(
                span,
                if matches!(action.kind, Some(pb::action::Kind::Delete(_))) {
                    ast::Change::Delete
                } else {
                    ast::Change::Subsume
                },
                call.func.clone(),
                results,
            ),
            _ => unreachable!("only scoped action kinds use this compiler"),
        };
        builder.action(action)
    };
    let (result, captured) =
        graph.eval_scoped_actions_observed(&inputs, execute, compile, observer);
    if execute {
        let captured_indices: HashMap<_, _> = slots
            .into_iter()
            .map(|(index, name)| (name, index))
            .collect();
        for (name, value) in captured {
            values.insert(captured_indices[&name], value);
        }
    } else if result.is_ok() {
        // Type-only placeholders are never executed or inserted into inventory.
        for index in materialized {
            values.entry(index).or_insert(Value::new_const(0));
        }
    }
    result
}

fn lower_action(
    program: &pb::Program,
    action: &pb::Action,
    native_spans: &NativeSpans,
) -> Result<Vec<Action>, String> {
    let span = native_span(program, action.span.as_ref(), native_spans)?;
    let lowered = match action.kind.as_ref().ok_or("missing action kind")? {
        pb::action::Kind::Term(index) => {
            let node = program
                .nodes
                .get(*index as usize)
                .ok_or("action node out of bounds")?;
            if let Some(pb::node::Kind::Union(union)) = &node.kind {
                let [lhs, rhs] = union.members.as_slice() else {
                    return Err("action Union currently requires exactly two members".into());
                };
                if !matches!(
                    program
                        .sorts
                        .get(node.sort_id as usize)
                        .and_then(|sort| sort.kind.as_ref()),
                    Some(pb::sort::Kind::Eq(_))
                ) {
                    return Err("action Union requires an equality sort".into());
                }
                for member in [lhs, rhs] {
                    if node_sort(program, *member)? != node_sort(program, *index)? {
                        return Err("Union member sort mismatch".into());
                    }
                }
                Action::Union(
                    span,
                    expression(program, *lhs, &mut HashSet::new(), native_spans)?,
                    expression(program, *rhs, &mut HashSet::new(), native_spans)?,
                )
            } else {
                Action::Expr(
                    span,
                    expression(program, *index, &mut HashSet::new(), native_spans)?,
                )
            }
        }
        pb::action::Kind::Set(set) => {
            let target = set.target.as_ref().ok_or("missing set target")?;
            Action::Set(
                span,
                target.func.clone(),
                target
                    .args
                    .iter()
                    .map(|index| expression(program, *index, &mut HashSet::new(), native_spans))
                    .collect::<Result<_, _>>()?,
                expression(
                    program,
                    set.value.ok_or("missing set value")?,
                    &mut HashSet::new(),
                    native_spans,
                )?,
            )
        }
        pb::action::Kind::Delete(call) | pb::action::Kind::Subsume(call) => Action::Change(
            span,
            if matches!(action.kind, Some(pb::action::Kind::Delete(_))) {
                ast::Change::Delete
            } else {
                ast::Change::Subsume
            },
            call.func.clone(),
            call.args
                .iter()
                .map(|index| expression(program, *index, &mut HashSet::new(), native_spans))
                .collect::<Result<_, _>>()?,
        ),
        pb::action::Kind::Panic(message) => Action::Panic(span, message.clone()),
        _ => return Err("SetCost is not supported yet".into()),
    };
    Ok(vec![lowered])
}

// Native local bindings preserve the addressed key across deleting the row and
// its auxiliary annotation. This is the same ordinary action/compiler path;
// functions and relation predicates have no constructor cost to remove.
fn lower_rule_cost_deletes(
    mut command: Command,
    constructors: &HashSet<String>,
    mode: pb::ExecutionMode,
) -> Command {
    if mode == pb::ExecutionMode::Normal
        && let Command::Rule { rule } = &mut command
    {
        let mut head = Vec::new();
        for (index, action) in std::mem::take(&mut rule.head.0).into_iter().enumerate() {
            if let Action::Change(span, ast::Change::Delete, name, args) = &action
                && constructors.contains(name)
            {
                let mut key = Vec::with_capacity(args.len());
                for (argument, value) in args.iter().enumerate() {
                    let local = format!("__egglog_proto_delete_{index}_{argument}");
                    head.push(Action::Let(span.clone(), local.clone(), value.clone()));
                    key.push(Expr::Var(span.clone(), local));
                }
                head.push(Action::Change(
                    span.clone(),
                    ast::Change::Delete,
                    name.clone(),
                    key.clone(),
                ));
                head.push(Action::Change(
                    span.clone(),
                    ast::Change::Delete,
                    crate::set_cost::get_cost_table_name(name),
                    key,
                ));
            } else {
                head.push(action);
            }
        }
        rule.head.0 = head;
    }
    command
}

fn lower_rule(
    program: &pb::Program,
    rule: &pb::Rule,
    ruleset: &str,
    name: &str,
    native_spans: &NativeSpans,
    mut occupied: impl FnMut(&str) -> bool,
) -> Result<Vec<Command>, String> {
    if rule.name.as_ref().is_some_and(String::is_empty) {
        return Err("an explicit rule label must not be empty".into());
    }
    let eval_mode = match pb::RuleEvalMode::try_from(rule.eval_mode) {
        Ok(pb::RuleEvalMode::Seminaive) => ast::RuleEvalMode::Seminaive,
        Ok(pb::RuleEvalMode::Naive) => ast::RuleEvalMode::Naive,
        Ok(pb::RuleEvalMode::UnsafeSeminaive) => ast::RuleEvalMode::UnsafeSeminaive,
        _ => return Err(format!("invalid rule evaluation mode {}", rule.eval_mode)),
    };
    let span = native_span(program, rule.span.as_ref(), native_spans)?;
    match rule.kind.as_ref().ok_or("missing rule kind")? {
        kind @ (pb::rule::Kind::Rewrite(_) | pb::rule::Kind::Birewrite(_)) => {
            // Native rewrite commands have no option fields. Keep this
            // adapter limit explicit rather than silently losing wire options.
            if eval_mode != ast::RuleEvalMode::Seminaive || rule.no_decomp || rule.include_subsumed
            {
                return Err("nondefault rewrite options require native rule expansion, which is not supported yet".into());
            }
            let (lhs, rhs, conditions, subsume, bidirectional) = match kind {
                pb::rule::Kind::Rewrite(rewrite) => (
                    rewrite.lhs,
                    rewrite.rhs,
                    &rewrite.conditions,
                    rewrite.subsume,
                    false,
                ),
                pb::rule::Kind::Birewrite(rewrite) => {
                    (rewrite.lhs, rewrite.rhs, &rewrite.conditions, false, true)
                }
                _ => unreachable!(),
            };
            if node_sort(program, lhs)? != node_sort(program, rhs)? {
                return Err("rewrite output sort mismatch".into());
            }
            for (query, head) in [(lhs, rhs), (rhs, lhs)]
                .into_iter()
                .take(1 + usize::from(bidirectional))
            {
                let mut bindings = HashMap::new();
                check_variables(program, &[query], &mut bindings, true)?;
                check_variables(program, conditions, &mut bindings, true)?;
                check_variables(program, &[head], &mut bindings, false)?;
            }
            let mut commands = Vec::new();
            for (direction, query, rhs) in [("=>", lhs, rhs), ("<=", rhs, lhs)]
                .into_iter()
                .take(1 + usize::from(bidirectional))
            {
                let mut bindings = HashMap::new();
                check_variables(program, &[query], &mut bindings, true)?;
                check_variables(program, conditions, &mut bindings, true)?;
                let action = pb::Action {
                    kind: Some(pb::action::Kind::Term(rhs)),
                    span: rule.span,
                };
                let mut memo = HashMap::new();
                let (mut head, _) = action_dag_actions(
                    program,
                    &action,
                    |name| bindings.contains_key(name),
                    native_spans,
                    &mut memo,
                    &mut 0,
                )?;
                if matches!(head.last(), Some(Action::Expr(..))) {
                    head.pop();
                }
                let mut head = ast::GenericActions(head)
                    .map_symbols(&mut |h| h, &mut |v: String| native_name("var", &v))
                    .0;
                let value = memo
                    .remove(&rhs)
                    .ok_or("missing rewrite result")?
                    .map_symbols(&mut |h| h, &mut |v: String| native_name("var", &v));
                let mut query_roots = Vec::with_capacity(conditions.len() + 1);
                query_roots.push(query);
                query_roots.extend(conditions.iter().copied());
                let (body, references) = facts(
                    program,
                    &query_roots,
                    native_spans,
                    Some(query),
                    &mut occupied,
                )?;
                head.push(Action::Union(
                    span.clone(),
                    references[&query].clone(),
                    value,
                ));
                if subsume {
                    let Some(pb::node::Kind::Call(call)) = &program.nodes[query as usize].kind
                    else {
                        return Err("subsumed rewrite must have a function call on the lhs".into());
                    };
                    head.push(Action::Change(
                        span.clone(),
                        ast::Change::Subsume,
                        call.func.clone(),
                        call.args
                            .iter()
                            .map(|index| references[index].clone())
                            .collect(),
                    ));
                }
                let native = ast::Rule {
                    span: span.clone(),
                    head: ast::GenericActions(head),
                    body,
                    name: if bidirectional {
                        format!("{name}{direction}")
                    } else {
                        name.to_owned()
                    },
                    ruleset: ruleset.into(),
                    eval_mode,
                    no_decomp: false,
                    include_subsumed: false,
                };
                commands.push(Command::Rule { rule: native });
            }
            Ok(commands)
        }
        pb::rule::Kind::Rule(body) => {
            let mut bindings = HashMap::new();
            check_variables(program, &body.query, &mut bindings, true)?;
            let roots = body
                .head
                .iter()
                .map(action_roots)
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .flatten()
                .collect::<Vec<_>>();
            check_variables(program, &roots, &mut bindings, false)?;
            let mut head = Vec::new();
            let mut memo = HashMap::new();
            let mut next = 0;
            for action in &body.head {
                let (actions, _) = action_dag_actions(
                    program,
                    action,
                    |name| bindings.contains_key(name),
                    native_spans,
                    &mut memo,
                    &mut next,
                )?;
                head.extend(
                    ast::GenericActions(actions)
                        .map_symbols(&mut |h| h, &mut |v: String| native_name("var", &v))
                        .0,
                );
            }
            Ok(vec![Command::Rule {
                rule: ast::Rule {
                    span,
                    head: ast::GenericActions(head),
                    body: facts(program, &body.query, native_spans, None, &mut occupied)?.0,
                    name: name.into(),
                    ruleset: ruleset.into(),
                    eval_mode,
                    no_decomp: rule.no_decomp,
                    include_subsumed: rule.include_subsumed,
                },
            }])
        }
    }
}

// Check annotations in each binder: native type inference cannot see the
// annotations erased while lowering the wire arena.
fn check_variables(
    program: &pb::Program,
    roots: &[u32],
    bindings: &mut HashMap<String, String>,
    bind: bool,
) -> Result<(), String> {
    let mut pending = roots.to_vec();
    let mut seen = HashSet::new();
    while let Some(index) = pending.pop() {
        if !seen.insert(index) {
            continue;
        }
        let node = program
            .nodes
            .get(index as usize)
            .ok_or("node index out of bounds")?;
        match node.kind.as_ref().ok_or("missing node kind")? {
            pb::node::Kind::Var(name) => {
                let sort = node_sort(program, index)?;
                match bindings.get(name) {
                    Some(expected) if *expected == sort => (),
                    None if bind => {
                        bindings.insert(name.clone(), sort);
                    }
                    _ => return Err(format!("unbound or inconsistently typed variable {name}")),
                }
            }
            pb::node::Kind::Apply(apply) => {
                pending.extend(apply.function);
                pending.extend(&apply.args);
            }
            pb::node::Kind::Call(call) | pb::node::Kind::GetCost(call) => {
                pending.extend(&call.args)
            }
            pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::PartialCall(call)),
            }) => pending.extend(&call.args),
            pb::node::Kind::Union(union) => pending.extend(&union.members),
            pb::node::Kind::PrimitiveValue(_) => (),
        }
    }
    Ok(())
}

fn encode_sort(
    graph: &EGraph,
    names: &NativeNames,
    sort: &ArcSort,
    response: &mut pb::RunProgramOutput,
) -> Result<u32, egglog::Error> {
    let mut sorts = vec![];
    let index = graph
        .export_sort(sort, &mut sorts)
        .map_err(egglog::Error::ExtractError)?;
    for sort in &mut sorts {
        if let Some(pb::sort::Kind::Eq(name)) = &mut sort.kind
            && let Some(logical) = names.sorts.get(name)
        {
            *name = logical.clone();
        }
    }
    crate::builtin::import_sort(&sorts, index, &mut response.sorts)
        .map_err(egglog::Error::ExtractError)
}

#[allow(clippy::too_many_arguments)]
fn encode_term(
    session: &Session,
    terms: &TermDag,
    term: TermId,
    sort: &ArcSort,
    native_value: Value,
    children: &[u32],
    response: &mut pb::RunProgramOutput,
    encoded: &mut HashMap<pb::Node, u32>,
) -> Result<u32, egglog::Error> {
    let (graph, names) = (&session.graph, &session.names);
    let scalar = value::Scalar::reflect(graph, sort, native_value)
        .map(|value| value.encode())
        .transpose()
        .map_err(egglog::Error::ExtractError)?;
    let custom = session
        .extension
        .as_ref()
        .map(|extension| extension.encode_observed_custom_value(graph, sort, native_value))
        .transpose()
        .map_err(egglog::Error::ExtractError)?
        .flatten();
    let sort_id = encode_sort(graph, names, sort, response)?;
    let kind = if let Some(value) = custom {
        pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Custom(value)),
        })
    } else if let Some(scalar) = scalar {
        let Some(pb::sort::Kind::Application(family)) = &response.sorts[sort_id as usize].kind
        else {
            return Err(egglog::Error::ExtractError(
                "native scalar has a non-application sort".into(),
            ));
        };
        if !family.args.is_empty() {
            return Err(egglog::Error::ExtractError(
                "native scalar sort is not nullary".into(),
            ));
        }
        value::Scalar::decode(Some(&family.name), &scalar).map_err(egglog::Error::ExtractError)?;
        pb::node::Kind::PrimitiveValue(scalar)
    } else if sort.clone().as_arc_any().is::<egglog::sort::FunctionSort>() {
        let value = graph
            .value_to_container::<egglog::sort::FunctionContainer>(native_value)
            .ok_or_else(|| egglog::Error::ExtractError("missing native function value".into()))?;
        if children.len() != value.1.len() {
            return Err(egglog::Error::ExtractError(
                "function capture arity mismatch".into(),
            ));
        }
        drop(value);
        let target = graph
            .export_function_value_target(sort, native_value)
            .map_err(egglog::Error::ExtractError)?;
        pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::PartialCall(pb::Call {
                func: names.callables.get(&target).unwrap_or(&target).clone(),
                args: children.to_vec(),
            })),
        })
    } else if sort.is_container_sort() {
        pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(
                value::container_payload(
                    sort,
                    &response.sorts[sort_id as usize],
                    children,
                    &response.nodes,
                )
                .map_err(egglog::Error::ExtractError)?,
            ),
        })
    } else {
        match terms.get(term) {
            Term::App(name, _) if sort.is_eq_sort() => {
                graph.get_function(name).ok_or_else(|| {
                    egglog::Error::ExtractError(format!("unsupported extracted constructor {name}"))
                })?;
                pb::node::Kind::Call(pb::Call {
                    func: names.callables.get(name).unwrap_or(name).clone(),
                    args: children.to_vec(),
                })
            }
            _ => {
                return Err(egglog::Error::ExtractError(
                    "native value requires an explicit custom codec".into(),
                ));
            }
        }
    };
    let node = pb::Node {
        sort_id,
        kind: Some(kind),
        ..Default::default()
    };
    if let Some(index) = encoded.get(&node) {
        return Ok(*index);
    }
    let index = response.nodes.len() as u32;
    encoded.insert(node.clone(), index);
    response.nodes.push(node);
    Ok(index)
}

#[cfg(test)]
#[path = "../tests/common/protobuf.rs"]
pub(crate) mod fixtures;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::protobuf::fixtures::Observed;

    thread_local! {
        pub(super) static DECLARATION_ORDER_WORK: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    }

    #[test]
    fn declaration_order_matches_legacy_graphs_and_prefixes() {
        for edges in 0..1usize << 9 {
            for resupplied in 0..1usize << 3 {
                // Declaration zero is an initial non-function. Resupplied
                // computed declarations precede even earlier ready new ones.
                let installed: HashSet<_> = (1..=3)
                    .filter(|index| resupplied & (1 << (index - 1)) != 0)
                    .collect();
                let mut prefix = vec![0];
                prefix.extend((1..=3).filter(|index| installed.contains(index)));
                let pending: Vec<_> = (1..=3)
                    .filter(|index| !installed.contains(index))
                    .map(|index| {
                        let dependencies: HashSet<usize> = (1..=3)
                            .filter(|dependency| {
                                edges & (1 << ((index - 1) * 3 + dependency - 1)) != 0
                            })
                            .collect();
                        (index, dependencies)
                    })
                    .collect();
                let mut old_pending = pending.clone();
                let mut old_installed = installed.clone();
                let mut expected = prefix.clone();
                let valid = loop {
                    if old_pending.is_empty() {
                        break true;
                    }
                    let Some(position) = old_pending
                        .iter()
                        .position(|(_, dependencies)| dependencies.is_subset(&old_installed))
                    else {
                        break false;
                    };
                    let (index, _) = old_pending.remove(position);
                    old_installed.insert(index);
                    expected.push(index);
                };
                let result = extend_declaration_order(pending, installed, &mut prefix);
                assert_eq!(prefix, expected, "edges={edges}, resupplied={resupplied}");
                assert_eq!(result.is_ok(), valid);
                if !valid {
                    assert_eq!(
                        result.unwrap_err(),
                        "recursive program-defined primitives or function merges are not supported yet"
                    );
                }
            }
        }
        let mut order = vec![];
        extend_declaration_order(
            vec![
                (0, HashSet::from([1])),
                (1, HashSet::new()),
                (2, HashSet::new()),
            ],
            HashSet::new(),
            &mut order,
        )
        .unwrap();
        assert_eq!(order, [1, 0, 2], "newly ready earlier index wins");
    }

    #[test]
    fn declaration_order_work_scales_with_vertices_and_edges() {
        for chain in [false, true] {
            let mut measurements = vec![];
            for count in [32, 64, 128] {
                let pending = (0..count)
                    .map(|index| {
                        let dependencies = if chain && index + 1 < count {
                            HashSet::from([index + 1])
                        } else {
                            HashSet::new()
                        };
                        (index, dependencies)
                    })
                    .collect();
                DECLARATION_ORDER_WORK.set(0);
                let mut order = vec![];
                extend_declaration_order(pending, HashSet::new(), &mut order).unwrap();
                let expected: Vec<_> = if chain {
                    (0..count).rev().collect()
                } else {
                    (0..count).collect()
                };
                assert_eq!(order, expected);
                measurements.push((count, DECLARATION_ORDER_WORK.get()));
            }
            eprintln!("declaration ordering chain={chain}: {measurements:?}");
            assert!(measurements.iter().all(|(count, work)| *work <= 4 * count));
            assert!(
                measurements
                    .windows(2)
                    .all(|pair| pair[1].1 <= 2 * pair[0].1 + 2)
            );
        }
    }

    #[test]
    fn callable_name_projection_maps_all_action_targets_once() {
        let target = pb::Call {
            func: "logical".into(),
            args: vec![],
        };
        let actions: Vec<_> = [
            pb::action::Kind::Set(pb::Set {
                target: Some(target.clone()),
                value: Some(0),
            }),
            pb::action::Kind::SetCost(pb::SetCost {
                target: Some(target.clone()),
                cost: Some(0),
            }),
            pb::action::Kind::Delete(target.clone()),
            pb::action::Kind::Subsume(target),
            pb::action::Kind::Panic("logical".into()),
        ]
        .into_iter()
        .map(|kind| pb::Action {
            kind: Some(kind),
            ..Default::default()
        })
        .collect();
        let rule = pb::Rule {
            kind: Some(pb::rule::Kind::Rule(pb::RuleBody {
                head: actions.clone(),
                ..Default::default()
            })),
            ..Default::default()
        };
        let mut body: Vec<_> = actions
            .into_iter()
            .map(|action| pb::Command {
                kind: Some(pb::command::Kind::Action(action)),
                ..Default::default()
            })
            .collect();
        body.push(pb::Command {
            kind: Some(pb::command::Kind::Fail(Box::new(pb::Command {
                kind: Some(pb::command::Kind::Run(pb::Run {
                    rulesets: vec![pb::RulesetSelection {
                        kind: Some(pb::ruleset_selection::Kind::Ruleset(pb::Ruleset {
                            rules: vec![rule.clone()],
                        })),
                    }],
                    ..Default::default()
                })),
                ..Default::default()
            }))),
            ..Default::default()
        });
        let mut program = pb::Program {
            rulesets: vec![pb::RulesetBinding {
                name: "logical".into(),
                value: Some(pb::Ruleset { rules: vec![rule] }),
            }],
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Loop(pb::Loop {
                    body,
                    ..Default::default()
                })),
                ..Default::default()
            }],
            ..Default::default()
        };
        let mut projected = 0;
        map_callable_names(
            &mut program,
            |name| {
                assert_eq!(
                    name, "logical",
                    "each structural target projects exactly once"
                );
                *name = "native".into();
                projected += 1;
            },
            |_| panic!("no table-size selector"),
        );
        assert_eq!(projected, 12);
        assert_eq!(program.rulesets[0].name, "logical");
        for rule in graph::rules(&program) {
            let Some(pb::rule::Kind::Rule(body)) = &rule.kind else {
                panic!("rule body")
            };
            assert!(
                matches!(&body.head[4].kind, Some(pb::action::Kind::Panic(message)) if message == "logical")
            );
        }
        assert!(action_sites(&program.commands).any(|(_, action)| {
            matches!(&action.kind, Some(pb::action::Kind::Panic(message)) if message == "logical")
        }));
    }

    #[test]
    fn native_spans_share_files_and_preserve_validation_boundaries() {
        let mut program = pb::Program {
            files: [
                ("same.egg", Some("aλ")),
                ("same.egg", Some("other")),
                ("unused.egg", Some("unused")),
                ("omitted.egg", None),
                ("empty.egg", Some("")),
            ]
            .into_iter()
            .map(|(name, contents)| pb::SourceFile {
                name: name.into(),
                contents: contents.map(str::to_owned),
            })
            .collect(),
            ..Default::default()
        };
        let native_spans = NativeSpans::default();
        for (file, start, end) in [
            (99, 0, 0),
            (0, 2, 0),
            (0, 2, 3),
            (0, 0, 2),
            (0, 4, 4),
            (3, 2, 1),
            (4, 0, 1),
        ] {
            let span = pb::Span { file, start, end };
            assert!(native_span(&program, Some(&span), &native_spans).is_err());
        }
        assert!(native_spans.0.borrow().is_empty());
        let mut spans = vec![];
        for (file, start, end) in [
            (0, 0, 1),
            (0, 1, 3),
            (1, 0, 5),
            (0, 3, 3),
            (4, 0, 0),
            (3, 100, 101),
        ] {
            let span = pb::Span { file, start, end };
            spans.push(native_span(&program, Some(&span), &native_spans).unwrap());
        }
        let [
            ast::Span::Egglog(first),
            ast::Span::Egglog(second),
            ast::Span::Egglog(other),
            ..,
        ] = spans.as_slice()
        else {
            panic!("contents-backed spans")
        };
        assert!(Arc::ptr_eq(&first.file, &second.file));
        assert!(!Arc::ptr_eq(&first.file, &other.file));
        assert_eq!(
            spans[..5].iter().map(ast::Span::string).collect::<Vec<_>>(),
            ["a", "λ", "other", "", ""]
        );
        assert!(matches!(&spans[5], ast::Span::Rust(_)));
        assert!(matches!(
            native_span(&program, None, &native_spans).unwrap(),
            ast::Span::Rust(_)
        ));
        assert!(native_spans.0.borrow()[2].is_none());
        assert!(native_spans.0.borrow()[3].is_none());
        // Providers may append files without replacing the authored arena.
        program.files.push(pb::SourceFile {
            name: "helper.egg".into(),
            contents: Some("helper".into()),
        });
        let helper_span = pb::Span {
            file: 5,
            start: 0,
            end: 6,
        };
        assert_eq!(
            native_span(&program, Some(&helper_span), &native_spans)
                .unwrap()
                .string(),
            "helper"
        );
        assert!(Arc::ptr_eq(
            native_spans.0.borrow()[0].as_ref().unwrap(),
            &first.file
        ));
        drop(native_spans);
        drop(program);
        assert_eq!(spans[0].to_string(), "In 1:1-1 of same.egg: a");
    }

    #[test]
    fn native_spans_follow_preparation_into_action_lowering_not_later_requests() {
        let (engine, id) = host_default_engine();
        let mut program = inventory_fixture("(datatype E (N i64)) (N 1)");
        let prepared = engine.graphs[&id].prepare(&mut program).unwrap();
        let file = prepared.context.native_spans.0.borrow()[0].clone().unwrap();
        let declaration = prepared
            .installations
            .iter()
            .find_map(|installation| match &installation.command {
                Some(Command::Constructor {
                    span: ast::Span::Egglog(span),
                    ..
                }) => Some(span),
                _ => None,
            })
            .unwrap();
        assert!(Arc::ptr_eq(&file, &declaration.file));
        let Some(pb::command::Kind::Action(action)) = &program.commands[0].kind else {
            panic!("action fixture")
        };
        let actions = lower_action(&program, action, &prepared.context.native_spans).unwrap();
        let [Action::Expr(ast::Span::Egglog(span), expr)] = actions.as_slice() else {
            panic!("ordinary constructor action")
        };
        let ast::Span::Egglog(expression_span) = expr.span() else {
            panic!("expression span")
        };
        let action_file = prepared.context.native_spans.0.borrow()
            [action.span.unwrap().file as usize]
            .clone()
            .unwrap();
        assert!(Arc::ptr_eq(&action_file, &span.file));
        assert!(Arc::ptr_eq(&action_file, &expression_span.file));
        let mut later = pb::Program {
            files: vec![pb::SourceFile {
                name: "fixture.egg".into(),
                contents: Some("other".into()),
            }],
            ..Default::default()
        };
        let next = engine.graphs[&id].prepare(&mut later).unwrap();
        let origin = pb::Span {
            file: 0,
            start: 0,
            end: 5,
        };
        let ast::Span::Egglog(next_span) =
            native_span(&later, Some(&origin), &next.context.native_spans).unwrap()
        else {
            panic!("next request")
        };
        assert!(!Arc::ptr_eq(&file, &next_span.file));
        assert_eq!(next_span.file.contents, "other");
        drop(prepared);
        drop(program);
        assert_eq!(expr.span().string(), "(N 1)");
    }

    mod partial_call_staging {
        use super::*;
        use cost_model::{CostModelContract, CostModelRuntime, ModelSort, NativeCostModel};
        use std::sync::atomic::{AtomicUsize, Ordering};

        struct MetadataModel {
            calls: Arc<AtomicUsize>,
            annotation: &'static str,
            objective: &'static str,
            additive: bool,
        }

        impl NativeCostModel for MetadataModel {
            fn contract(&self) -> CostModelContract {
                self.calls.fetch_add(1, Ordering::SeqCst);
                let sort = |name: &str| ModelSort {
                    sorts: vec![pb::Sort {
                        kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                            name: name.into(),
                            args: vec![],
                        })),
                        ..Default::default()
                    }],
                    root: 0,
                };
                CostModelContract {
                    annotation: sort(self.annotation),
                    objective: sort(self.objective),
                    additive: self.additive,
                }
            }

            fn start(&self, _: &pb::Program) -> Result<Arc<dyn CostModelRuntime>, egglog::Error> {
                panic!("preparation must not start a cost model")
            }
        }

        // Author the factory directly in protobuf so the adapter regression
        // does not depend on Source's separate compiler context.
        fn table_factory_fixture(target: &str) -> pb::Program {
            let body = if target.starts_with("(constructor") {
                "(Target 7) (check (= (Target 7) (Target 7)))"
            } else {
                "(set (Target 7) (Item 9)) (check (= (Target 7) (Item 9)))"
            };
            let mut program = inventory_fixture(&format!(
                "(sort A) (constructor Item (i64) A) {target}
                 (sort Other) (constructor Marker () Other)
                 (sort F (UnstableFn (i64) A)) {body}"
            ));
            let function = program
                .sorts
                .iter()
                .position(|sort| matches!(sort.kind, Some(pb::sort::Kind::Func(_))))
                .unwrap() as u32;
            let Some(pb::sort::Kind::Func(signature)) = &program.sorts[function as usize].kind
            else {
                unreachable!()
            };
            let output = signature.result;
            let argument = program
                .nodes
                .iter()
                .find_map(|node| match &node.kind {
                    Some(pb::node::Kind::Call(call)) if call.func == "Target" => Some(call.args[0]),
                    _ => None,
                })
                .unwrap();
            let partial = program.nodes.len() as u32;
            program.nodes.extend([
                pb::Node {
                    sort_id: function,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::PartialCall(pb::Call {
                            func: "Target".into(),
                            args: vec![],
                        })),
                    })),
                    ..Default::default()
                },
                pb::Node {
                    sort_id: function,
                    kind: Some(pb::node::Kind::Call(pb::Call {
                        func: "factory".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
                pb::Node {
                    sort_id: output,
                    kind: Some(pb::node::Kind::Apply(pb::Apply {
                        function: Some(partial + 1),
                        args: vec![argument],
                    })),
                    ..Default::default()
                },
            ]);
            program.declarations.push(pb::Declaration {
                kind: Some(pb::declaration::Kind::UserDefinedPrimitive(
                    pb::UserDefinedPrimitive {
                        name: "factory".into(),
                        inputs: vec![],
                        output: function,
                        body: Some(partial),
                    },
                )),
                ..Default::default()
            });
            // Creating a constructor function value needs Write, so evaluate
            // the new factory in Full context rather than a Read-only Check.
            program.commands.last_mut().unwrap().kind =
                Some(pb::command::Kind::Extract(pb::Extract {
                    roots: vec![partial + 2],
                    variants: 1,
                    extractor: pb::Extractor::Tree.into(),
                    ..Default::default()
                }));
            program
        }

        #[test]
        fn table_factories_close_in_one_request_without_creating_rows() {
            for target in [
                "(constructor Target (i64) A)",
                "(function Target (i64) A :no-merge)",
                "(function Target (i64) A :merge new)",
            ] {
                for reversed in [false, true] {
                    let mut program = table_factory_fixture(target);
                    if reversed {
                        program.declarations.reverse();
                    }
                    let (mut engine, id) = host_default_engine();
                    let session = &engine.graphs[&id];
                    let definitions = session.definitions.clone();
                    let request = session.request;
                    let tuples = session.graph.num_tuples();
                    session.prepare(&mut program.clone()).unwrap();
                    assert_eq!(session.definitions, definitions);
                    assert_eq!(session.request, request);
                    assert_eq!(session.graph.num_tuples(), tuples);
                    assert!(
                        session
                            .graph
                            .get_function(&native_name("call", "Target"))
                            .is_none()
                    );
                    let mut setup = program.clone();
                    setup.commands.clear();
                    assert_eq!(run_host_default(&mut engine, id, setup).error, None);
                    assert_eq!(engine.graphs[&id].graph.num_tuples(), tuples);
                    if !target.starts_with("(constructor") {
                        // Creating a function value does not read its missing row.
                        let mut missing = program.clone();
                        missing.commands = vec![pb::Command {
                            kind: Some(pb::command::Kind::Action(pb::Action {
                                kind: Some(pb::action::Kind::Term(program.nodes.len() as u32 - 1)),
                                ..Default::default()
                            })),
                            ..Default::default()
                        }];
                        let response = run_host_default(&mut engine, id, missing);
                        assert_eq!(
                            response.error.unwrap().code,
                            i32::from(pb::ErrorCode::RuntimeFailure)
                        );
                        assert_eq!(engine.graphs[&id].graph.num_tuples(), tuples);
                    }
                    let text = source::Renderer::default().render(&program).unwrap();
                    let response = run_host_default(&mut engine, id, program);
                    assert_eq!(response.error, None);
                    let Some(pb::command_output::Kind::Extraction(extraction)) =
                        &response.output.outputs[0].kind
                    else {
                        panic!("applied factory result")
                    };
                    let term = extraction.roots[0].variants[0].term;
                    let Some(pb::node::Kind::Call(call)) =
                        &response.output.nodes[term as usize].kind
                    else {
                        panic!("table result")
                    };
                    assert_eq!(
                        call.func,
                        if target.starts_with("(constructor") {
                            "Target"
                        } else {
                            "Item"
                        }
                    );
                    assert_eq!(
                        engine.graphs[&id]
                            .graph
                            .get_size(&native_name("call", "Target")),
                        1
                    );
                    crate::new_experimental_egraph()
                        .parse_and_run_program(None, &text)
                        .unwrap();
                }
            }
        }

        #[test]
        fn nonzero_capture_and_merge_compilation_do_not_run_bodies_or_validators() {
            let bodies = Arc::new(AtomicUsize::new(0));
            let validators = Arc::new(AtomicUsize::new(0));
            let observed = bodies.clone();
            let checked = validators.clone();
            let (mut engine, id) = host_default_engine();
            let session = engine.graphs.get_mut(&id).unwrap();
            egglog::add_primitive_with_validator!(&mut session.graph,
            "counted-stage"[id = "test.counted.stage"] = {observed: Arc<AtomicUsize>}
            |left: i64, right: i64| -> i64 {{
                self.ctx.fetch_add(1, Ordering::SeqCst);
                left + right
            }}, move |_: &mut TermDag, args: &[TermId]| -> Option<TermId> {
                checked.fetch_add(1, Ordering::SeqCst);
                args.first().copied()
            });
            // This private fixture completes ambient initialization after Create.
            session.builtins = crate::builtin::configured_catalog(&session.graph).unwrap();
            let mut program = inventory_fixture(
                "(function Target (i64 i64) i64 :merge (+ old new))
                 (sort F (UnstableFn (i64) i64))
                 (primitive factory (i64) F (unstable-fn \"+\" (+ _0 1)))
                 (set (Target 2 3) 4) (set (Target 2 3) 5)
                 (check (= (unstable-app (factory 1) 3) 9))",
            );
            for node in &mut program.nodes {
                if let Some(pb::node::Kind::Call(call)) = &mut node.kind
                    && call.func == "egglog.core.i64.add"
                {
                    call.func = "test.counted.stage".into();
                }
                if let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::PartialCall(call)),
                })) = &mut node.kind
                {
                    call.func = "Target".into();
                }
            }
            let session = &engine.graphs[&id];
            let definitions = session.definitions.clone();
            let request = session.request;
            let tuples = session.graph.num_tuples();
            session.prepare(&mut program.clone()).unwrap();
            assert_eq!(bodies.load(Ordering::SeqCst), 0);
            assert_eq!(validators.load(Ordering::SeqCst), 0);
            assert_eq!(session.definitions, definitions);
            assert_eq!(session.request, request);
            assert_eq!(session.graph.num_tuples(), tuples);
            assert_eq!(run_host_default(&mut engine, id, program).error, None);
            assert!(bodies.load(Ordering::SeqCst) > 0);
            assert_eq!(validators.load(Ordering::SeqCst), 0);
        }

        #[test]
        fn malformed_factory_targets_reject_before_any_publication_or_effect() {
            let program = table_factory_fixture("(constructor Target (i64) A)");
            for invalid in ["unknown", "arity", "argument", "output"] {
                let mut program = program.clone();
                let capture = program.nodes.len() as u32;
                let scalar = program.sorts.iter().position(|sort| matches!(&sort.kind, Some(pb::sort::Kind::Application(family)) if family.name == "i64")).unwrap() as u32;
                program.nodes.push(pb::Node {
                    sort_id: scalar,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::I64(1)),
                    })),
                    ..Default::default()
                });
                let function_sort = program
                    .nodes
                    .iter()
                    .find_map(|node| {
                        matches!(
                            node.kind,
                            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                                value: Some(pb::primitive_value::Value::PartialCall(_)),
                            }))
                        )
                        .then_some(node.sort_id)
                    })
                    .unwrap();
                let other = program.sorts.iter().position(|sort| matches!(&sort.kind, Some(pb::sort::Kind::Eq(name)) if name == "Other")).unwrap() as u32;
                let Some(pb::sort::Kind::Func(signature)) =
                    &mut program.sorts[function_sort as usize].kind
                else {
                    unreachable!()
                };
                match invalid {
                    "argument" => signature.params[0] = other,
                    "output" => signature.result = other,
                    _ => (),
                }
                for node in &mut program.nodes {
                    if let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::PartialCall(call)),
                    })) = &mut node.kind
                    {
                        match invalid {
                            "unknown" => call.func = "missing-target".into(),
                            "arity" => {
                                call.args.push(capture);
                            }
                            _ => (),
                        }
                    }
                }
                let (mut engine, id) = host_default_engine();
                let definitions = engine.graphs[&id].definitions.clone();
                let request = engine.graphs[&id].request;
                let tuples = engine.graphs[&id].graph.num_tuples();
                let response = run_host_default(&mut engine, id, program);
                assert_eq!(
                    response.error.unwrap().code,
                    i32::from(pb::ErrorCode::InvalidProgram),
                    "{invalid}"
                );
                assert!(response.output.outputs.is_empty());

                assert_eq!(engine.graphs[&id].definitions, definitions);
                assert_eq!(engine.graphs[&id].request, request);
                assert_eq!(engine.graphs[&id].graph.num_tuples(), tuples);
                assert!(
                    engine.graphs[&id]
                        .graph
                        .get_function(&native_name("call", "Marker"))
                        .is_none()
                );
            }
        }

        #[test]
        fn model_metadata_uses_closed_context_without_starting_models() {
            for keep in [false, true] {
                for invalid in ["none", "unknown", "annotation", "objective", "greedy"] {
                    let (mut engine, id) = host_default_engine();
                    let calls = Arc::new(AtomicUsize::new(0));
                    let name = engine
                        .register_cost_model(
                            id,
                            Arc::new(MetadataModel {
                                calls: calls.clone(),
                                annotation: if invalid == "annotation" {
                                    "bool"
                                } else {
                                    "i64"
                                },
                                objective: if invalid == "objective" {
                                    "missing-objective"
                                } else {
                                    "i64"
                                },
                                additive: false,
                            }),
                        )
                        .unwrap();
                    let mut program = table_factory_fixture("(constructor Target (i64) A)");
                    let mut command = program.commands.pop().unwrap();
                    command.kind = Some(pb::command::Kind::Extract(pb::Extract {
                        roots: vec![program.nodes.len() as u32 - 1],
                        variants: 1,
                        extractor: pb::Extractor::Tree.into(),
                        ..Default::default()
                    }));
                    program.commands = vec![command];
                    let span = program.commands[0].span;
                    let model = if invalid == "unknown" {
                        "missing-model".into()
                    } else {
                        name
                    };
                    let extractor = if invalid == "greedy" {
                        pb::Extractor::GreedyDag
                    } else {
                        pb::Extractor::Tree
                    } as i32;
                    if keep {
                        program.commands[0].kind =
                            Some(pb::command::Kind::KeepBest(pb::KeepBest {
                                tables: vec!["Target".into()],
                                extractor,
                                cost_model: model,
                            }));
                    } else {
                        let Some(pb::command::Kind::Extract(extract)) =
                            &mut program.commands[0].kind
                        else {
                            unreachable!()
                        };
                        extract.cost_model = model;
                        extract.extractor = extractor;
                    }
                    let session = &engine.graphs[&id];
                    let definitions = session.definitions.clone();
                    let request = session.request;
                    match session.prepare(&mut program) {
                        Ok(_) => assert_eq!(invalid, "none"),
                        Err(error) => {
                            assert_ne!(invalid, "none", "{}", error.0.message);
                            assert_eq!(error.0.span, span);
                            let expected = match invalid {
                                "unknown" => "unknown cost model",
                                "annotation" => "stored annotation sort",
                                "objective" => "missing-objective",
                                "greedy" => "additive marginal cost model",
                                _ => unreachable!(),
                            };
                            assert!(error.0.message.contains(expected), "{}", error.0.message);
                        }
                    }
                    assert_eq!(
                        calls.load(Ordering::SeqCst),
                        usize::from(invalid != "unknown")
                    );
                    assert_eq!(session.definitions, definitions);
                    assert_eq!(session.request, request);
                    assert_eq!(session.graph.num_tuples(), 0);
                    assert!(
                        !session
                            .graph
                            .authoring_type_info()
                            .is_primitive(&native_name("call", "factory"))
                    );
                }
            }
            // Backend computed implementations publish their actual signatures;
            // metadata resolution does not need to export or execute their bodies.
            let (mut engine, id) = host_default_engine();
            let calls = Arc::new(AtomicUsize::new(0));
            let model = engine
                .register_cost_model(
                    id,
                    Arc::new(MetadataModel {
                        calls,
                        annotation: "i64",
                        objective: "i64",
                        additive: true,
                    }),
                )
                .unwrap();
            let mut staged = engine.graphs[&id].clone();
            let bodies = Arc::new(AtomicUsize::new(0));
            let observed = bodies.clone();
            egglog::add_primitive!(&mut staged.graph,
            "unprojectable-stage" = {observed: Arc<AtomicUsize>} |value: i64| -> i64 {{
                self.ctx.fetch_add(1, Ordering::SeqCst); value
            }});
            let commands = staged
                .graph
                .parse_program(
                    None,
                    "(primitive projection_missing (i64) i64 (unprojectable-stage _0))",
                )
                .unwrap();
            staged.graph = staged.graph.validate_program(commands).unwrap();
            let catalog = staged.graph.type_info().portable_builtin_catalog().unwrap();
            assert!(
                catalog
                    .definitions
                    .primitives
                    .iter()
                    .any(|primitive| { primitive.name == "projection_missing" })
            );
            assert!(
                staged
                    .resolve_cost_model(&model, pb::Extractor::Tree.into())
                    .is_ok()
            );
            assert_eq!(bodies.load(Ordering::SeqCst), 0);
            assert!(
                !engine.graphs[&id]
                    .graph
                    .authoring_type_info()
                    .is_primitive("projection_missing")
            );
        }

        #[test]
        fn recursive_model_controls_keep_admission_and_original_spans() {
            let (mut engine, id) = host_default_engine();
            let calls = Arc::new(AtomicUsize::new(0));
            let name = engine
                .register_cost_model(
                    id,
                    Arc::new(MetadataModel {
                        calls: calls.clone(),
                        annotation: "i64",
                        objective: "i64",
                        additive: true,
                    }),
                )
                .unwrap();
            for keep in [false, true] {
                for wrapper in ["fail", "zero", "repeat", "saturate"] {
                    let mut program = inventory_fixture(
                        "(sort A) (constructor Target () A) (Target) (extract (Target))",
                    );
                    let mut child = program.commands.pop().unwrap();
                    let span = child.span;
                    if keep {
                        child.kind = Some(pb::command::Kind::KeepBest(pb::KeepBest {
                            tables: vec!["Target".into()],
                            extractor: pb::Extractor::Tree.into(),
                            cost_model: name.clone(),
                        }));
                    } else {
                        let Some(pb::command::Kind::Extract(extract)) = &mut child.kind else {
                            unreachable!()
                        };
                        extract.cost_model = name.clone();
                    }
                    let kind = match wrapper {
                        "fail" => pb::command::Kind::Fail(Box::new(child)),
                        "zero" | "repeat" => pb::command::Kind::Loop(pb::Loop {
                            max_iterations: Some(u64::from(wrapper == "repeat")),
                            body: vec![child],
                            until: vec![],
                        }),
                        "saturate" => pb::command::Kind::Loop(pb::Loop {
                            body: vec![child],
                            max_iterations: Some(1),
                            until: vec![],
                        }),
                        _ => unreachable!(),
                    };
                    program.commands.push(pb::Command {
                        kind: Some(kind),
                        span,
                    });
                    let response = run_host_default(&mut engine, id, program);
                    let error = response.error.unwrap();
                    assert_eq!(error.code, i32::from(pb::ErrorCode::InvalidProgram));
                    assert!(error.message.contains(if wrapper == "fail" {
                        "observation wrappers are not implemented"
                    } else {
                        "mutation-progress witness"
                    }));
                    assert_eq!(calls.load(Ordering::SeqCst), 0);
                    assert!(response.output.outputs.is_empty());
                    assert_eq!(engine.graphs[&id].graph.num_tuples(), 0);
                    assert!(
                        engine.graphs[&id]
                            .graph
                            .get_function(&native_name("call", "Target"))
                            .is_none()
                    );
                }
            }
            let spans: Vec<_> = (0..4)
                .map(|start| {
                    Some(pb::Span {
                        file: 0,
                        start,
                        end: start + 1,
                    })
                })
                .collect();
            let commands = vec![pb::Command {
                span: spans[0],
                kind: Some(pb::command::Kind::Fail(Box::new(pb::Command {
                    span: spans[1],
                    kind: Some(pb::command::Kind::Loop(pb::Loop {
                        max_iterations: Some(0),
                        until: vec![],
                        body: vec![pb::Command {
                            span: spans[2],
                            kind: Some(pb::command::Kind::Loop(pb::Loop {
                                max_iterations: Some(1),
                                until: vec![],
                                body: vec![pb::Command {
                                    span: spans[3],
                                    kind: Some(pb::command::Kind::Extract(pb::Extract::default())),
                                }],
                            })),
                        }],
                    })),
                }))),
            }];
            assert_eq!(
                command_tree(&commands)
                    .map(|command| command.span)
                    .collect::<Vec<_>>(),
                spans
            );
        }
    }

    #[test]
    fn session_catalog_seed_survives_authored_primitives_and_empty_requests() {
        let (mut engine, id) = host_default_engine();
        assert!(!engine.graphs[&id].builtins.primitives.is_empty());
        let mut program = inventory_fixture(
            "(primitive successor (i64) i64 (+ _0 1)) (check (= (successor 3) 4))",
        );
        let commands = std::mem::take(&mut program.commands);
        assert_eq!(
            run_host_default(&mut engine, id, program.clone()).error,
            None
        );
        assert!(
            engine
                .graphs
                .get_mut(&id)
                .unwrap()
                .graph
                .type_info()
                .portable_builtin_catalog()
                .is_ok()
        );
        let definitions = engine.graphs[&id].definitions.clone();
        let empty = run_host_default(
            &mut engine,
            id,
            pb::Program {
                ..Default::default()
            },
        );
        assert_eq!(empty.error, None);
        assert!(empty.output.outputs.is_empty());
        assert_eq!(engine.graphs[&id].definitions, definitions);
        program.declarations.clear();
        program.commands = commands;
        assert_eq!(run_host_default(&mut engine, id, program).error, None);
    }

    #[derive(Default)]
    struct NativeCloneProbe(Arc<std::sync::atomic::AtomicUsize>);
    impl Clone for NativeCloneProbe {
        fn clone(&self) -> Self {
            self.0.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            Self(self.0.clone())
        }
    }

    #[test]
    fn preparation_compiles_cold_mixed_theory_in_one_context() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        let mut program = inventory_fixture(
            r#"
            (sort Items (Vec i64))
            (datatype E (Keep Items))
            (primitive constant () i64 (+ 10 20))
            (function merged () i64 :merge (constant))
            (primitive observe () i64 (merged))
            (ruleset r) (rule ((Keep xs)) ((Keep xs)) :ruleset r)
            (Keep (vec-empty)) (set (merged) 1) (set (merged) 2)
            (run r 1) (check (Keep (vec-empty))) (check (= (observe) 30))
        "#,
        );
        program.declarations.reverse();
        let (mut engine, id) = host_default_engine();
        let clones = Arc::new(AtomicUsize::new(0));
        *engine
            .graphs
            .get_mut(&id)
            .unwrap()
            .graph
            .extension_state_or_default::<NativeCloneProbe>() = NativeCloneProbe(clones.clone());
        let mut input = program.clone();
        let prepared = engine.graphs[&id].prepare(&mut input).unwrap();
        assert_eq!(clones.load(Ordering::SeqCst), 1);
        assert!(!prepared.installations.is_empty());
        assert!(!prepared.materialized.is_empty());
        assert!(engine.graphs[&id].definitions.declarations.is_empty());
        assert_eq!(engine.graphs[&id].graph.num_tuples(), 0);
        drop(prepared);
        for _ in 0..3 {
            clones.store(0, Ordering::SeqCst);
            let response = run_host_default(&mut engine, id, program.clone());
            assert_eq!(response.error, None);
            assert_eq!(clones.load(Ordering::SeqCst), 1);
        }
    }

    #[cfg(feature = "typed")]
    #[test]
    fn preparation_accepts_resupplied_typed_function_check_packets() {
        use crate::typed::{
            __private::{Callable, Expr},
            EGraph, EgglogValue,
            builtins::I64,
            eq, set,
        };
        use std::sync::atomic::{AtomicUsize, Ordering};

        // Use the same declaration/expression constructors as #[function];
        // packets below still come from the public register/check recording.
        let declaration = Callable::function(
            "single_preparation_slot",
            vec![],
            I64::sort_ref(),
            None::<fn(Expr, Expr) -> Expr>,
        );
        let slot = I64::from_expression(Expr::call(&declaration, vec![]));

        let mut writer = EGraph::with_recording(true).unwrap();
        writer.register(set(&slot, 7_i64)).unwrap();
        let setup = writer.history().unwrap();
        let mut reader = EGraph::with_recording(true).unwrap();
        assert!(!reader.check(eq(&slot, 7_i64)).unwrap());
        let check = reader.history().unwrap();
        assert_eq!(check.commands.len(), 1);
        assert!(matches!(
            check.commands[0].kind,
            Some(pb::command::Kind::Check(_))
        ));
        assert!(!setup.declarations.is_empty());
        assert!(!check.declarations.is_empty());

        let (mut engine, id) = host_default_engine();
        let clones = Arc::new(AtomicUsize::new(0));
        *engine
            .graphs
            .get_mut(&id)
            .unwrap()
            .graph
            .extension_state_or_default::<NativeCloneProbe>() = NativeCloneProbe(clones.clone());
        assert_eq!(run_host_default(&mut engine, id, setup).error, None);
        assert_eq!(clones.load(Ordering::SeqCst), 1);
        let tuples = engine.graphs[&id].graph.num_tuples();
        for _ in 0..3 {
            clones.store(0, Ordering::SeqCst);
            assert_eq!(run_host_default(&mut engine, id, check.clone()).error, None);
            assert_eq!(clones.load(Ordering::SeqCst), 1);
            assert_eq!(engine.graphs[&id].graph.num_tuples(), tuples);
        }
    }

    #[test]
    fn preparation_uses_one_compiler_for_cold_warm_and_resupplied_metadata() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        for mode in [
            pb::ExecutionMode::Normal,
            pb::ExecutionMode::TermEncoding,
            pb::ExecutionMode::Proofs,
            pb::ExecutionMode::ProofTesting,
        ] {
            let scalar = pb::Sort {
                kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                    name: "i64".into(),
                    args: vec![],
                })),
                ..Default::default()
            };
            let mut engine = Engine::default();
            let id = engine
                .create_request(pb::CreateEGraphRequest {
                    sorts: vec![scalar.clone()],
                    options: Some(pb::EGraphOptions {
                        cost_sort: Some(0),
                        execution_mode: mode.into(),
                        ..Default::default()
                    }),
                    ..Default::default()
                })
                .unwrap()
                .egraph_id;
            let clones = Arc::new(AtomicUsize::new(0));
            let session = engine.graphs.get_mut(&id).unwrap();
            // Install after mode selection so the original proof typechecking
            // graph has no probe: count only outer native graph clones.
            *session
                .graph
                .extension_state_or_default::<NativeCloneProbe>() =
                NativeCloneProbe(clones.clone());
            for kind in [
                pb::sort::Kind::Application(pb::SortApplication {
                    name: "Vec".into(),
                    args: vec![0],
                }),
                pb::sort::Kind::Func(pb::FuncSort {
                    params: vec![0],
                    result: 0,
                }),
            ] {
                let mut program = pb::Program {
                    sorts: vec![
                        scalar.clone(),
                        pb::Sort {
                            kind: Some(kind),
                            ..Default::default()
                        },
                    ],
                    ..Default::default()
                };
                clones.store(0, Ordering::SeqCst);
                let prepared = session.prepare(&mut program).unwrap();
                assert_eq!(
                    clones.load(Ordering::SeqCst),
                    1,
                    "new shape uses the single staging compiler: {mode:?}"
                );
                assert_eq!(prepared.materialized.len(), 1);
                assert!(!prepared.installations.is_empty());
                let name = sort_name(&program.sorts, 1).unwrap();
                assert!(session.graph.get_sort_by_name(&name).is_none());
                session
                    .install(prepared, &mut pb::RunProgramOutput::default())
                    .unwrap();
                assert!(session.graph.get_sort_by_name(&name).is_some());

                clones.store(0, Ordering::SeqCst);
                let prepared = session.prepare(&mut program).unwrap();
                assert!(prepared.installations.is_empty());
                assert_eq!(
                    clones.load(Ordering::SeqCst),
                    1,
                    "known shape reuses staging: {mode:?}"
                );
            }
            let mut declarations = inventory_fixture("(datatype E (N i64))");
            clones.store(0, Ordering::SeqCst);
            let prepared = session.prepare(&mut declarations).unwrap();
            assert_eq!(clones.load(Ordering::SeqCst), 1);
            session
                .install(prepared, &mut pb::RunProgramOutput::default())
                .unwrap();
            clones.store(0, Ordering::SeqCst);
            let prepared = session
                .prepare(&mut inventory_fixture("(datatype E (N i64))"))
                .unwrap();
            assert!(prepared.installations.is_empty());
            assert_eq!(
                clones.load(Ordering::SeqCst),
                1,
                "resupply uses the same staging path"
            );
            let tuples = session.graph.num_tuples();
            clones.store(0, Ordering::SeqCst);
            session.prepare(&mut pb::Program::default()).unwrap();
            assert_eq!(clones.load(Ordering::SeqCst), 1);
            assert_eq!(session.graph.num_tuples(), tuples);
            for bound in [0, 1] {
                let mut condition = inventory_fixture("(check (= 1 1))");
                let Some(pb::command::Kind::Check(check)) = condition.commands.pop().unwrap().kind
                else {
                    unreachable!()
                };
                condition.commands.push(pb::Command {
                    kind: Some(pb::command::Kind::Loop(pb::Loop {
                        until: check.facts,
                        max_iterations: Some(bound),
                        ..Default::default()
                    })),
                    ..Default::default()
                });
                clones.store(0, Ordering::SeqCst);
                session.prepare(&mut condition).unwrap();
                assert_eq!(
                    clones.load(Ordering::SeqCst),
                    1,
                    "internal conditions share the staging compiler: {mode:?}, bound {bound}"
                );
                assert_eq!(session.graph.num_tuples(), tuples);
            }

            let mut failure = inventory_fixture("(panic \"single-preparation\")");
            failure.files[0].name = "single-preparation.egg".into();
            let span = failure.commands[0].span;
            let response = run_host_default(&mut engine, id, failure);
            let error = response.error.unwrap();
            assert_eq!(error.code, i32::from(pb::ErrorCode::RuntimeFailure));
            assert_eq!(error.span, span);
            assert_eq!(error.location.unwrap().path, [0]);
            assert_eq!(
                response.files[span.unwrap().file as usize].name,
                "single-preparation.egg"
            );
            assert!(error.message.contains("single-preparation"));
        }
    }

    #[test]
    fn cached_builtin_environment_keeps_live_registry_errors_on_empty_requests() {
        let (mut engine, id) = host_default_engine();
        let graph = &mut engine.graphs.get_mut(&id).unwrap().graph;
        graph.add_pure_primitive(ForeignPrimitive("egglog.core.i64.add".into()), None);
        let expected = graph.type_info().builtin_catalog().err().unwrap();
        let definitions = engine.graphs[&id].definitions.clone();
        let response = run_host_default(&mut engine, id, pb::Program::default());
        assert_eq!(response.error.unwrap().message, expected);
        assert!(response.output.outputs.is_empty());
        assert_eq!(engine.graphs[&id].definitions, definitions);
    }

    #[test]
    fn session_catalog_seed_checks_dependent_primitives_across_scope_returns() {
        let (mut engine, id) = host_default_engine();
        let empty = pb::Program {
            ..Default::default()
        };
        let consistent = |engine: &mut Engine, id| {
            let session = engine.graphs.get_mut(&id).unwrap();
            assert!(session.graph.type_info().portable_builtin_catalog().is_ok());
            let definitions = session.definitions.clone();
            let response = run_host_default(engine, id, empty.clone());
            assert_eq!(response.error, None);
            assert!(response.output.outputs.is_empty());
            assert_eq!(engine.graphs[&id].definitions, definitions);
        };
        let base = "(primitive seed_a (i64) i64 (+ _0 1))
                    (primitive seed_b (i64) i64 (seed_a _0))";
        // Independent acknowledged installations retain the actual captured
        // callee owners, rather than assuming stored wire bodies prove this.
        for phase in source::Source::new(None, base).unwrap() {
            assert_eq!(
                run_host_default(&mut engine, id, phase.unwrap()).error,
                None
            );
            consistent(&mut engine, id);
        }
        let definitions = engine.graphs[&id].definitions.clone();
        let dependent = inventory_fixture(&format!(
            "{base} (primitive seed_c (i64) i64 (seed_b _0)) (check (= (seed_c 4) 5))"
        ));
        let incompatible = inventory_fixture("(primitive seed_b (i64) i64 (+ _0 2))");
        for _ in 0..2 {
            let bytes = engine
                .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
                .unwrap();
            let clone = pb::CloneEGraphResponse::decode(bytes.as_slice())
                .unwrap()
                .egraph_id;
            assert_eq!(
                run_host_default(&mut engine, clone, dependent.clone()).error,
                None
            );
            consistent(&mut engine, clone);
            let before = engine.graphs[&clone].definitions.clone();
            let request = engine.graphs[&clone].request;
            let response = run_host_default(&mut engine, clone, incompatible.clone());
            let error = response.error.unwrap();
            assert_eq!(error.code, i32::from(pb::ErrorCode::InvalidProgram));
            assert!(error.message.contains("conflicting declaration seed_b"));
            assert!(response.output.outputs.is_empty());
            assert_eq!(engine.graphs[&clone].request, request);
            assert_eq!(engine.graphs[&clone].definitions, before);
            consistent(&mut engine, clone);
            engine
                .destroy(&pb::DestroyEGraphRequest { egraph_id: clone }.encode_to_vec())
                .unwrap();
            assert_eq!(engine.graphs[&id].definitions, definitions);
            assert!(
                engine
                    .graphs
                    .get_mut(&id)
                    .unwrap()
                    .graph
                    .type_info()
                    .get_prims(&native_name("call", "seed_c"))
                    .is_none()
            );
            consistent(&mut engine, id);
        }
    }

    #[test]
    fn constructor_dag_scoped_compilation_is_inert_and_drops_partial_builders() {
        let native_spans = NativeSpans::default();
        let mut graph = crate::new_experimental_egraph();
        graph
            .parse_and_run_program(None, "(datatype A (Leaf) (Wrap A))")
            .unwrap();
        let functions = graph.get_function_names();
        let mut program = inventory_fixture("(datatype A (Leaf) (Wrap A)) (Leaf)");
        let Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Term(mut root)),
            ..
        })) = program.commands.pop().unwrap().kind
        else {
            panic!("fixture")
        };
        let sort_id = program.nodes[root as usize].sort_id;
        for _ in 0..1050 {
            program.nodes.push(pb::Node {
                sort_id,
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "Wrap".into(),
                    args: vec![root],
                })),
                ..Default::default()
            });
            root = program.nodes.len() as u32 - 1;
        }
        let action = pb::Action {
            kind: Some(pb::action::Kind::Term(root)),
            ..Default::default()
        };
        let mut values = HashMap::new();
        let closed = (0..=root).collect();
        eval_scoped_action(
            &mut graph,
            &program,
            &action,
            &mut values,
            false,
            Some(&closed),
            &mut |_| {},
            &native_spans,
        )
        .unwrap();
        assert_eq!(graph.num_tuples(), 0);
        assert!(graph.materialized_eq_classes().is_empty());
        assert!(values.is_empty());

        // Force a native compile error only after the shallow locals for the
        // complete deep child have been emitted. No nested native AST exists
        // on this partial-builder destruction path either.
        program.nodes.push(pb::Node {
            sort_id,
            kind: Some(pb::node::Kind::Call(pb::Call {
                func: "missing-after-locals".into(),
                args: vec![root],
            })),
            ..Default::default()
        });
        let invalid = pb::Action {
            kind: Some(pb::action::Kind::Term(root + 1)),
            ..Default::default()
        };
        assert!(
            eval_scoped_action(
                &mut graph,
                &program,
                &invalid,
                &mut values,
                false,
                Some(&closed),
                &mut |_| {},
                &native_spans,
            )
            .is_err()
        );
        assert_eq!(graph.num_tuples(), 0);
        assert!(graph.materialized_eq_classes().is_empty());
        program.nodes.pop();
        eval_scoped_action(
            &mut graph,
            &program,
            &action,
            &mut values,
            true,
            Some(&closed),
            &mut |_| {},
            &native_spans,
        )
        .unwrap();
        assert_eq!(graph.get_size("Wrap"), 1050);
        assert_eq!(graph.get_size("Leaf"), 1);
        assert_eq!(graph.materialized_eq_classes().len(), 1051);
        assert_eq!(graph.get_function_names(), functions);
        assert!(values.is_empty());
    }

    #[test]
    fn ordinary_action_dag_size_tracks_shared_representation_not_a_fixed_budget() {
        let mut program = inventory_fixture("(datatype A (Leaf) (Pair A A)) (Leaf)");
        let Some(pb::command::Kind::Action(action)) = &mut program.commands[0].kind else {
            panic!("Leaf action")
        };
        let Some(pb::action::Kind::Term(mut root)) = action.kind else {
            panic!("Leaf root")
        };
        assert_eq!(program.nodes.len(), 1);
        let sort_id = program.nodes[root as usize].sort_id;
        for _ in 0..22_000 {
            program.nodes.push(pb::Node {
                sort_id,
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "Pair".into(),
                    args: vec![root, root],
                })),
                ..Default::default()
            });
            root = program.nodes.len() as u32 - 1;
        }
        action.kind = Some(pb::action::Kind::Term(root));
        program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::TableSizes(pb::GetTableSizes {
                tables: vec!["Leaf".into(), "Pair".into()],
            })),
            ..Default::default()
        });

        // R=1, V=C=22,001, E=44,000: both former ordinary traversal
        // counters charged 66,002 steps to this compact, acyclic graph.
        let native_spans = NativeSpans::default();
        validate_node_graph(&program, &native_spans).unwrap();
        let closed = classify_action_dags(&program).unwrap();
        assert_eq!(closed[&vec![0]].len(), 22_001);
        let Some(pb::command::Kind::Action(action)) = &program.commands[0].kind else {
            unreachable!()
        };
        let mut memo = HashMap::new();
        let (actions, evaluated) = action_dag_actions(
            &program,
            action,
            |_| false,
            &native_spans,
            &mut memo,
            &mut 0,
        )
        .unwrap();
        assert_eq!(memo.len(), 22_001);
        assert!(evaluated.into_iter().eq(0..=root));
        assert_eq!(actions.len(), 22_002);
        for action in &actions[..22_001] {
            let Action::Let(_, _, Expr::Call(_, _, children)) = action else {
                panic!("one shallow local per call")
            };
            assert!(children.iter().all(|child| matches!(child, Expr::Var(..))));
        }
        assert!(matches!(
            actions.last(),
            Some(Action::Expr(_, Expr::Var(..)))
        ));

        let (mut engine, id) = host_default_engine();
        let response = run_host_default(&mut engine, id, program);
        assert_eq!(response.error, None);

        let Some(pb::command_output::Kind::Sizes(sizes)) = &response.output.outputs[0].kind else {
            panic!("observable tables, not unfolded extraction")
        };
        assert_eq!(
            sizes
                .sizes
                .iter()
                .map(|size| (size.table.as_str(), size.rows))
                .collect::<Vec<_>>(),
            [("Leaf", 1), ("Pair", 22_000)]
        );
    }

    #[test]
    fn inert_payload_dag_bindings_keep_first_demand_and_single_payload_ownership() {
        use pb::primitive_value::Value as V;
        let text = "shared payload".repeat(4096);
        let program = pb::Program {
            sorts: vec![
                pb::Sort {
                    kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                        name: "String".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                        name: "BigRat".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Eq("A".into())),
                    ..Default::default()
                },
            ],
            nodes: vec![
                pb::Node {
                    sort_id: 0,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(V::String(text.clone())),
                    })),
                    ..Default::default()
                },
                pb::Node {
                    sort_id: 1,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(V::BigRat(pb::BigRat {
                            numerator: "7".into(),
                            denominator: "2".into(),
                        })),
                    })),
                    ..Default::default()
                },
                pb::Node {
                    sort_id: 2,
                    kind: Some(pb::node::Kind::Call(pb::Call {
                        func: "Leaf".into(),
                        args: vec![1, 0, 1, 0],
                    })),
                    ..Default::default()
                },
            ],
            ..Default::default()
        };
        let action = pb::Action {
            kind: Some(pb::action::Kind::Term(2)),
            ..Default::default()
        };
        let (actions, evaluated) = action_dag_actions(
            &program,
            &action,
            |_| false,
            &NativeSpans::default(),
            &mut HashMap::new(),
            &mut 0,
        )
        .unwrap();
        assert_eq!(evaluated, [1, 1, 1, 1, 1, 0, 2]);
        assert_eq!(actions.len(), 8);
        let Action::Let(_, _, Expr::Lit(_, Literal::String(numerator))) = &actions[0] else {
            panic!("numerator payload is bound once before its builder")
        };
        assert_eq!(numerator, "7");
        let Action::Let(_, _, Expr::Lit(_, Literal::String(denominator))) = &actions[2] else {
            panic!("denominator follows the numerator builder")
        };
        assert_eq!(denominator, "2");
        let Action::Let(_, number, Expr::Call(_, target, _)) = &actions[4] else {
            panic!("one compound-number binding")
        };
        assert_eq!(target, "egglog.core.bigrat.make");
        let Action::Let(_, text_binding, Expr::Lit(_, Literal::String(actual))) = &actions[5]
        else {
            panic!("one shared string payload")
        };
        assert_eq!(actual, &text);
        let Action::Let(_, _, Expr::Call(_, target, arguments)) = &actions[6] else {
            panic!("constructor binding")
        };
        assert_eq!(target, "Leaf");
        assert!(matches!(&arguments[0], Expr::Var(_, name) if name == number));
        assert_eq!(arguments[0], arguments[2]);
        assert!(matches!(&arguments[1], Expr::Var(_, name) if name == text_binding));
        assert_eq!(arguments[1], arguments[3]);

        let (query, references) = facts(&program, &[2, 2], &NativeSpans::default(), None, |name| {
            name == "__egglog_proto_query_0"
        })
        .unwrap();
        assert_eq!(query.len(), 7);
        let mut payloads = Vec::new();
        for fact in &query {
            let expressions = match fact {
                Fact::Eq(_, lhs, rhs) => vec![lhs, rhs],
                Fact::Fact(value) => vec![value],
            };
            for expression in expressions {
                if let Expr::Lit(_, Literal::String(value)) = expression {
                    payloads.push(value.as_str());
                }
                if let Expr::Call(_, _, args) = expression {
                    assert!(args.iter().all(|arg| !matches!(arg, Expr::Call(..))));
                }
            }
        }
        assert_eq!(payloads.iter().filter(|value| **value == text).count(), 1);
        assert!(matches!(&references[&0], Expr::Var(_, name) if name != "__egglog_proto_query_0"));
        let Fact::Fact(Expr::Call(_, name, args)) = query.last().unwrap() else {
            panic!("root remains a predicate")
        };
        assert_eq!(name, "Leaf");
        assert_eq!(
            args,
            &[
                references[&1].clone(),
                references[&0].clone(),
                references[&1].clone(),
                references[&0].clone()
            ]
        );
    }

    #[test]
    fn query_graphs_have_linear_native_syntax_in_both_rewrite_directions() {
        let mut program = inventory_fixture("(datatype E (Leaf) (Pair E E))");
        let sort_id = program
            .sorts
            .iter()
            .position(|sort| matches!(&sort.kind, Some(pb::sort::Kind::Eq(name)) if name == "E"))
            .unwrap() as u32;
        let leaf = program.nodes.len() as u32;
        program.nodes.push(pb::Node {
            sort_id,
            kind: Some(pb::node::Kind::Call(pb::Call {
                func: "Leaf".into(),
                args: vec![],
            })),
            ..Default::default()
        });
        let mut root = leaf;
        for _ in 0..28 {
            let index = program.nodes.len() as u32;
            program.nodes.push(pb::Node {
                sort_id,
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "Pair".into(),
                    args: vec![root, root],
                })),
                ..Default::default()
            });
            root = index;
        }
        let spans = NativeSpans::default();
        let (query, _) = facts(&program, &[root, root], &spans, None, |_| false).unwrap();
        assert_eq!(query.len(), 29);
        for kind in [
            pb::rule::Kind::Rule(pb::RuleBody {
                query: vec![root],
                head: vec![],
            }),
            pb::rule::Kind::Rewrite(pb::Rewrite {
                lhs: root,
                rhs: leaf,
                conditions: vec![root],
                subsume: true,
            }),
            pb::rule::Kind::Birewrite(pb::BiRewrite {
                lhs: root,
                rhs: leaf,
                conditions: vec![root],
            }),
        ] {
            let commands = lower_rule(
                &program,
                &pb::Rule {
                    kind: Some(kind),
                    eval_mode: pb::RuleEvalMode::Seminaive.into(),
                    ..Default::default()
                },
                "r",
                "diamond",
                &spans,
                |_| false,
            )
            .unwrap();
            for command in commands {
                let Command::Rule { rule } = command else {
                    panic!("flat native rule")
                };
                assert_eq!(rule.body.len(), 29);
                let mut size = 0;
                for fact in rule.body {
                    let mut pending = match fact {
                        Fact::Fact(expr) => vec![expr],
                        Fact::Eq(_, lhs, rhs) => vec![lhs, rhs],
                    };
                    while let Some(expr) = pending.pop() {
                        size += 1;
                        if let Expr::Call(_, _, args) = expr {
                            assert!(args.iter().all(|arg| !matches!(arg, Expr::Call(..))));
                            pending.extend(args);
                        }
                    }
                }
                assert!(size <= 29 * 4);
            }
        }
    }

    fn closed_value_dag(terminal: &str) -> (pb::Program, u32) {
        let mut program = inventory_fixture(&format!(
            "(sort A) (sort As (Vec A))
             (constructor Leaf (As BigRat) A) (constructor Branch (As) A) {terminal}"
        ));
        let mut root = program.nodes.iter().position(|node|
            matches!(&node.kind, Some(pb::node::Kind::Call(call)) if call.func == "Leaf")
        ).unwrap() as u32;
        let sort_id = program.nodes[root as usize].sort_id;
        let vector = program.sorts.iter().position(|sort|
            matches!(&sort.kind, Some(pb::sort::Kind::Application(family)) if family.name == "Vec")
        ).unwrap() as u32;
        for _ in 0..16 {
            let children = program.nodes.len() as u32;
            program.nodes.push(pb::Node {
                sort_id: vector,
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "egglog.core.vec.of".into(),
                    args: vec![root, root],
                })),
                ..Default::default()
            });
            root = program.nodes.len() as u32;
            program.nodes.push(pb::Node {
                sort_id,
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "Branch".into(),
                    args: vec![children],
                })),
                ..Default::default()
            });
        }
        let Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Term(terminal)),
            ..
        })) = &program.commands[0].kind
        else {
            panic!("terminal")
        };
        let pb::node::Kind::Call(call) = program.nodes[*terminal as usize].kind.clone().unwrap()
        else {
            panic!("call")
        };
        let args = call
            .args
            .into_iter()
            .map(|arg| {
                if matches!(&program.nodes[arg as usize].kind,
                Some(pb::node::Kind::Call(call)) if call.func == "Leaf")
                {
                    root
                } else {
                    arg
                }
            })
            .collect();
        program.nodes[*terminal as usize].kind =
            Some(pb::node::Kind::Call(pb::Call { args, ..call }));
        (program, root)
    }

    #[test]
    fn action_and_rule_diamonds_share_lazy_locals_in_all_modes() {
        for in_rule in [false, true] {
            let mut program =
                inventory_fixture("(datatype E (Leaf) (Pair E E)) (relation Trigger ()) (Trigger)");
            let trigger = match &program.commands[0].kind {
                Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Term(index)),
                    ..
                })) => *index,
                _ => panic!("trigger"),
            };
            let sort_id = program
                .sorts
                .iter()
                .position(
                    |sort| matches!(&sort.kind, Some(pb::sort::Kind::Eq(name)) if name == "E"),
                )
                .unwrap() as u32;
            let mut root = program.nodes.len() as u32;
            program.nodes.push(pb::Node {
                sort_id,
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "Leaf".into(),
                    args: vec![],
                })),
                ..Default::default()
            });
            for _ in 0..28 {
                let parent = program.nodes.len() as u32;
                program.nodes.push(pb::Node {
                    sort_id,
                    kind: Some(pb::node::Kind::Call(pb::Call {
                        func: "Pair".into(),
                        args: vec![root, root],
                    })),
                    ..Default::default()
                });
                root = parent;
            }
            let action = pb::Action {
                kind: Some(pb::action::Kind::Term(root)),
                ..Default::default()
            };
            if in_rule {
                let rules = vec![pb::Rule {
                    name: Some("diamond".into()),
                    eval_mode: pb::RuleEvalMode::Seminaive.into(),
                    kind: Some(pb::rule::Kind::Rule(pb::RuleBody {
                        query: vec![trigger],
                        head: vec![action.clone(), action],
                    })),
                    ..Default::default()
                }];
                program.rulesets.push(pb::RulesetBinding {
                    name: "dag".into(),
                    value: Some(pb::Ruleset { rules }),
                });
                program.commands.push(pb::Command {
                    kind: Some(pb::command::Kind::Run(pb::Run {
                        rulesets: (vec!["dag".into()])
                            .into_iter()
                            .map(|name| pb::RulesetSelection {
                                kind: Some(pb::ruleset_selection::Kind::Name(name)),
                            })
                            .collect(),
                        ..Default::default()
                    })),
                    ..Default::default()
                });
                let lowered = lower_rule(
                    &program,
                    graph::rules(&program).next().unwrap(),
                    "dag",
                    "diamond",
                    &NativeSpans::default(),
                    |_| false,
                )
                .unwrap();
                let [Command::Rule { rule }] = lowered.as_slice() else {
                    panic!("one native rule")
                };
                assert_eq!(
                    rule.head
                        .0
                        .iter()
                        .filter(|action| matches!(action, Action::Let(..)))
                        .count(),
                    29
                );
                assert_eq!(rule.head.0.len(), 31); // duplicate root remains an ordered action
            } else {
                program.commands = vec![pb::Command {
                    kind: Some(pb::command::Kind::Action(action)),
                    ..Default::default()
                }];
            }
            let text = source::Renderer::default().render(&program).unwrap();
            assert!(
                text.matches("Pair").count() < 100,
                "no expanded presentation tree"
            );
            let phases = source::Source::new(None, &text)
                .unwrap()
                .collect::<Result<Vec<_>, _>>()
                .unwrap();
            for mode in [
                pb::ExecutionMode::Normal,
                pb::ExecutionMode::TermEncoding,
                pb::ExecutionMode::Proofs,
                pb::ExecutionMode::ProofTesting,
            ] {
                for replay in [false, true] {
                    let (mut engine, id) = host_default_engine();
                    let session = engine.graphs.get_mut(&id).unwrap();
                    let graph = std::mem::take(&mut session.graph);
                    session.graph = match mode {
                        pb::ExecutionMode::Normal => graph,
                        pb::ExecutionMode::TermEncoding => graph.with_term_encoding_enabled(),
                        pb::ExecutionMode::Proofs => graph.with_proofs_enabled(),
                        pb::ExecutionMode::ProofTesting => {
                            graph.with_proofs_enabled().with_proof_testing()
                        }
                    };
                    session.mode = mode;
                    for phase in if replay {
                        phases.clone()
                    } else {
                        vec![program.clone()]
                    } {
                        assert_eq!(
                            run_host_default(&mut engine, id, phase).error,
                            None,
                            "{in_rule}/{mode:?}/{replay}"
                        );
                    }
                    if matches!(
                        mode,
                        pb::ExecutionMode::Proofs | pb::ExecutionMode::ProofTesting
                    ) {
                        // Experimental text deliberately alpha-renames public
                        // declarations. Use this session's exported handles,
                        // not the original program's pre-render names.
                        let definitions = &engine.graphs[&id].definitions;
                        let pair = definitions
                            .declarations
                            .iter()
                            .find_map(|declaration| match &declaration.kind {
                                Some(pb::declaration::Kind::Constructor(constructor))
                                    if constructor.inputs.len() == 2
                                        && constructor
                                            .inputs
                                            .iter()
                                            .all(|arg| arg.sort == constructor.output) =>
                                {
                                    Some(constructor)
                                }
                                _ => None,
                            })
                            .unwrap();
                        let proof_sort = definitions.sorts[pair.output as usize].clone();
                        let pair_name = pair.name.clone();
                        // Direct construction has a Fiat justification; native
                        // ProveExists expects a rule justification. The shallow
                        // existential Prove query checks that same Pair witness
                        // without expanding its shared children into a query tree.
                        let proof_command = if in_rule {
                            pb::command::Kind::ProveExists(pb::ProveExists {
                                constructor: pair_name.clone(),
                            })
                        } else {
                            pb::command::Kind::Prove(pb::Prove { facts: vec![1] })
                        };
                        let response = run_host_default(
                            &mut engine,
                            id,
                            pb::Program {
                                sorts: vec![proof_sort],
                                nodes: vec![
                                    pb::Node {
                                        sort_id: 0,
                                        kind: Some(pb::node::Kind::Var("witness".into())),
                                        ..Default::default()
                                    },
                                    pb::Node {
                                        sort_id: 0,
                                        kind: Some(pb::node::Kind::Call(pb::Call {
                                            func: pair_name,
                                            args: vec![0, 0],
                                        })),
                                        ..Default::default()
                                    },
                                ],
                                commands: vec![pb::Command {
                                    kind: Some(proof_command),
                                    ..Default::default()
                                }],
                                ..Default::default()
                            },
                        );
                        assert_eq!(response.error, None, "{in_rule}/{mode:?}/{replay}");
                        let Some(pb::command_output::Kind::Proof(proof)) =
                            &response.output.outputs[0].kind
                        else {
                            panic!("proof output")
                        };
                        proof::validate(proof).unwrap();
                    }
                }
            }
        }
    }

    #[test]
    fn closed_value_fragments_preserve_read_barriers_and_source_replay() {
        // Native size reads exclude this action block's pending inserts.
        let (mut program, root) = closed_value_dag(
            "(constructor Demand (A i64 A i64) A)
             (Demand (Leaf (vec-empty) (bigrat (from-string \"7\") (from-string \"2\")))
                     (get-node-size!)
                     (Leaf (vec-empty) (bigrat (from-string \"7\") (from-string \"2\")))
                     (get-node-size!))
             (check (Demand a 0 b 0)
                    (Leaf (vec-empty) (bigrat (from-string \"7\") (from-string \"2\"))))",
        );
        let demand = program
            .nodes
            .iter_mut()
            .find_map(|node| match &mut node.kind {
                Some(pb::node::Kind::Call(call)) if call.func == "Demand" => Some(call),
                _ => None,
            })
            .unwrap();
        // Shared ordinary nodes retain their first demand inside one action.
        demand.args[3] = demand.args[1];
        let (mut engine, id) = host_default_engine();
        let mut execution = program.clone();
        let prepared = engine.graphs[&id].prepare(&mut execution).unwrap();
        let closed = &prepared.context.action_dags[&vec![0]];
        assert!(closed.contains(&root));
        let Some(pb::command::Kind::Action(action)) = &execution.commands[0].kind else {
            unreachable!()
        };
        let (_, evaluations) = action_dag_actions(
            &execution,
            action,
            |_| false,
            &prepared.context.native_spans,
            &mut HashMap::new(),
            &mut 0,
        )
        .unwrap();
        for (name, expected) in [
            ("Branch", 16),
            ("egglog.experimental.size.nodes", 1),
            ("Demand", 1),
        ] {
            let nodes: HashSet<_> = program
                .nodes
                .iter()
                .enumerate()
                .filter_map(|(index, node)| {
                    matches!(&node.kind, Some(pb::node::Kind::Call(call)) if call.func == name)
                        .then_some(index as u32)
                })
                .collect();
            assert_eq!(
                evaluations
                    .iter()
                    .filter(|index| nodes.contains(index))
                    .count(),
                expected
            );
        }
        assert!(evaluations.iter().all(|node| closed.contains(node)));
        assert_eq!(
            evaluations.iter().collect::<HashSet<_>>().len(),
            evaluations.len(),
            "shared nodes are demanded once, not unused same-named arena nodes"
        );
        assert_eq!(engine.graphs[&id].graph.num_tuples(), 0);
        assert_eq!(
            run_host_default(&mut engine, id, program.clone()).error,
            None
        );
        assert_eq!(
            engine.graphs[&id]
                .graph
                .get_size(&native_name("call", "Branch")),
            16
        );

        let text = source::Renderer::default().render(&program).unwrap();
        assert_eq!(text.matches("(action-scope ").count(), 1);
        let (mut replay, replay_id) = host_default_engine();
        for phase in source::Source::new(None, &text).unwrap() {
            assert_eq!(
                run_host_default(&mut replay, replay_id, phase.unwrap()).error,
                None
            );
        }
    }

    #[test]
    fn closed_value_fragments_keep_partial_failure_at_first_demand() {
        for first in [false, true] {
            let (signature, args) = if first {
                (
                    "BigRat A A",
                    "(bigrat (from-string \"bad\") (from-string \"2\"))
                  (Leaf (vec-empty) (bigrat (from-string \"7\") (from-string \"2\"))) (Late)",
                )
            } else {
                (
                    "A BigRat A",
                    "(Leaf (vec-empty) (bigrat (from-string \"7\") (from-string \"2\")))
                  (bigrat (from-string \"bad\") (from-string \"2\")) (Late)",
                )
            };
            let (program, _) = closed_value_dag(&format!(
                "(constructor Late () A) (constructor Demand ({signature}) A) (Demand {args})"
            ));
            let text = source::Renderer::default().render(&program).unwrap();
            let (mut engine, id) = host_default_engine();
            let response = run_host_default(&mut engine, id, program);
            let error = response.error.unwrap();
            assert_eq!(error.code, i32::from(pb::ErrorCode::RuntimeFailure));
            assert_eq!(error.location.unwrap().path, [0]);
            assert!(response.output.outputs.is_empty());
            let graph = &engine.graphs[&id].graph;
            assert_eq!(
                graph.get_size(&native_name("call", "Branch")),
                if first { 0 } else { 16 }
            );
            assert_eq!(graph.get_size(&native_name("call", "Late")), 0);
            assert_eq!(graph.get_size(&native_name("call", "Demand")), 0);
            let (mut replay, replay_id) = host_default_engine();
            let mut failed = false;
            for phase in source::Source::new(None, &text).unwrap() {
                let response = run_host_default(&mut replay, replay_id, phase.unwrap());
                if let Some(error) = response.error {
                    assert_eq!(error.code, i32::from(pb::ErrorCode::RuntimeFailure));
                    failed = true;
                    break;
                }
            }
            assert!(failed);
            assert_eq!(
                replay.graphs[&replay_id]
                    .graph
                    .materialized_eq_classes()
                    .len(),
                if first { 0 } else { 17 }
            );
        }
    }

    #[derive(Clone, Default)]
    struct RootCostModel(Arc<std::sync::atomic::AtomicUsize>);

    impl cost_model::NativeCostModel for RootCostModel {
        fn contract(&self) -> cost_model::CostModelContract {
            let sort = cost_model::ModelSort {
                sorts: vec![pb::Sort {
                    kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                        name: "i64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                }],
                root: 0,
            };
            cost_model::CostModelContract {
                annotation: sort.clone(),
                objective: sort,
                additive: true,
            }
        }
        fn start(
            &self,
            _: &pb::Program,
        ) -> Result<Arc<dyn cost_model::CostModelRuntime>, egglog::Error> {
            self.0.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            Ok(Arc::new(self.clone()))
        }
    }

    impl cost_model::CostModelRuntime for RootCostModel {
        fn run(
            &self,
            operation: Box<dyn FnOnce() -> Result<(), egglog::Error> + '_>,
        ) -> Result<(), egglog::Error> {
            operation()
        }
        fn cost(&self, _: u32, _: &[cost_model::Objective]) -> cost_model::Objective {
            Arc::new(0i64)
        }
        fn compare(
            &self,
            _: &cost_model::Objective,
            _: &cost_model::Objective,
        ) -> std::cmp::Ordering {
            std::cmp::Ordering::Equal
        }
        fn combine(
            &self,
            _: &cost_model::Objective,
            _: &cost_model::Objective,
        ) -> cost_model::Objective {
            Arc::new(0i64)
        }
        fn identity(&self) -> cost_model::Objective {
            Arc::new(0i64)
        }
        fn encode(
            &self,
            _: &cost_model::Objective,
        ) -> Result<Option<pb::PrimitiveValue>, egglog::Error> {
            Ok(Some(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::I64(0)),
            }))
        }
    }

    #[test]
    fn extraction_dag_roots_have_fresh_memos_and_ordered_native_boundaries() {
        for extractor in [pb::Extractor::Tree, pb::Extractor::GreedyDag] {
            for custom in [false, true] {
                let (mut program, _) = closed_value_dag(
                    "(primitive read_after (A) i64 (get-node-size!))
                     (read_after (Leaf (vec-empty) (bigrat (from-string \"7\") (from-string \"2\"))))"
                );
                let Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Term(root)),
                    ..
                })) = &program.commands[0].kind
                else {
                    panic!("root")
                };
                let root = *root;
                let (mut engine, id) = host_default_engine();
                let model = RootCostModel::default();
                let cost_model = if custom {
                    engine
                        .register_cost_model(id, Arc::new(model.clone()))
                        .unwrap()
                } else {
                    String::new()
                };
                // Exactly the same Call NodeId must execute twice. Its first
                // count sees pending rows; the next root sees committed rows.
                program.commands[0].kind = Some(pb::command::Kind::Extract(pb::Extract {
                    roots: vec![root, root],
                    variants: 1,
                    extractor: extractor.into(),
                    cost_model,
                }));
                engine.graphs[&id].prepare(&mut program.clone()).unwrap();
                assert_eq!(engine.graphs[&id].graph.num_tuples(), 0);
                assert_eq!(model.0.load(std::sync::atomic::Ordering::SeqCst), 0);
                let response = run_host_default(&mut engine, id, program);
                assert_eq!(response.error, None);
                let Some(pb::command_output::Kind::Extraction(result)) =
                    &response.output.outputs[0].kind
                else {
                    panic!("aggregate extraction")
                };
                assert_eq!(result.roots.len(), 2);
                for (root, expected) in result.roots.iter().zip([0, 17]) {
                    let [variant] = root.variants.as_slice() else {
                        panic!("one variant")
                    };
                    assert!(matches!(&response.output.nodes[variant.term as usize].kind,
                        Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                            value: Some(pb::primitive_value::Value::I64(value)),
                        })) if *value == expected));
                }
                assert_eq!(
                    engine.graphs[&id]
                        .graph
                        .get_size(&native_name("call", "Branch")),
                    16
                );
                assert_eq!(engine.graphs[&id].graph.materialized_eq_classes().len(), 17);
                assert_eq!(
                    model.0.load(std::sync::atomic::Ordering::SeqCst),
                    usize::from(custom)
                );
            }
        }
    }

    #[test]
    fn extraction_dag_partial_failure_keeps_prefix_and_stops_later_roots() {
        for custom in [false, true] {
            let (mut program, _) = closed_value_dag(
                "(constructor Later () A) (constructor Demand (A BigRat A) A)
                 (Demand (Leaf (vec-empty) (bigrat (from-string \"7\") (from-string \"2\")))
                    (bigrat (from-string \"bad\") (from-string \"2\")) (Later))",
            );
            let Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Term(root)),
                ..
            })) = &program.commands[0].kind
            else {
                panic!("root")
            };
            let root = *root;
            let later = program.nodes.iter().position(|node|
                matches!(&node.kind, Some(pb::node::Kind::Call(call)) if call.func == "Later")
            ).unwrap() as u32;
            let (mut engine, id) = host_default_engine();
            let model = RootCostModel::default();
            let cost_model = if custom {
                engine
                    .register_cost_model(id, Arc::new(model.clone()))
                    .unwrap()
            } else {
                String::new()
            };
            program.commands[0].kind = Some(pb::command::Kind::Extract(pb::Extract {
                roots: vec![root, later],
                variants: 1,
                extractor: pb::Extractor::Tree.into(),
                cost_model,
            }));
            engine.graphs[&id].prepare(&mut program.clone()).unwrap();
            assert_eq!(engine.graphs[&id].graph.num_tuples(), 0);
            let response = run_host_default(&mut engine, id, program);
            let error = response.error.unwrap();
            assert_eq!(error.code, i32::from(pb::ErrorCode::RuntimeFailure));
            assert_eq!(error.location.unwrap().path, [0]);
            assert!(response.output.outputs.is_empty());
            let graph = &engine.graphs[&id].graph;
            assert_eq!(graph.get_size(&native_name("call", "Branch")), 16);
            assert_eq!(graph.get_size(&native_name("call", "Later")), 0);
            assert_eq!(graph.get_size(&native_name("call", "Demand")), 0);
            assert_eq!(model.0.load(std::sync::atomic::Ordering::SeqCst), 0);
        }
    }

    #[test]
    fn creation_global_flags_preserve_native_defaults_and_no_rule_prove_admission() {
        for mode in [
            pb::ExecutionMode::Normal,
            pb::ExecutionMode::TermEncoding,
            pb::ExecutionMode::Proofs,
            pb::ExecutionMode::ProofTesting,
        ] {
            for seminaive in [None, Some(false), Some(true)] {
                for no_decomp in [false, true] {
                    let mut engine = Engine::default();
                    let request = pb::CreateEGraphRequest {
                        sorts: vec![pb::Sort {
                            kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                                name: "i64".into(),
                                args: vec![],
                            })),
                            ..Default::default()
                        }],
                        options: Some(pb::EGraphOptions {
                            cost_sort: Some(0),
                            execution_mode: mode.into(),
                            seminaive,
                        }),
                        no_decomp,
                        ..Default::default()
                    };
                    let id = pb::CreateEGraphResponse::decode(
                        engine.create(&request.encode_to_vec()).unwrap().as_slice(),
                    )
                    .unwrap()
                    .egraph_id;
                    let session = &engine.graphs[&id];
                    assert_eq!(session.graph.seminaive, seminaive.unwrap_or(true));
                    assert_eq!(session.graph.no_decomp, no_decomp);
                    assert_eq!(session.mode, mode);
                    if mode != pb::ExecutionMode::Normal {
                        continue;
                    }
                    let frozen = run_host_default(
                        &mut engine,
                        id,
                        pb::Program {
                            commands: vec![pb::Command {
                                kind: Some(pb::command::Kind::Freeze(pb::Freeze::default())),
                                ..Default::default()
                            }],
                            ..Default::default()
                        },
                    );
                    assert_eq!(frozen.error, None);
                    let Some(pb::command_output::Kind::Snapshot(snapshot)) =
                        &frozen.output.outputs[0].kind
                    else {
                        panic!("expected actual frozen options");
                    };
                    let options = snapshot.options.as_ref().unwrap();
                    assert_eq!(options.seminaive, Some(seminaive.unwrap_or(true)));
                    // Logical snapshots retain admission, not planner resources.
                    let restored_id = pb::CreateEGraphResponse::decode(
                        engine
                            .create(
                                &pb::CreateEGraphRequest {
                                    sorts: request.sorts.clone(),
                                    options: Some(pb::EGraphOptions {
                                        cost_sort: Some(0),
                                        ..*options
                                    }),
                                    ..Default::default()
                                }
                                .encode_to_vec(),
                            )
                            .unwrap()
                            .as_slice(),
                    )
                    .unwrap()
                    .egraph_id;
                    assert_eq!(
                        engine.graphs[&restored_id].graph.seminaive,
                        seminaive.unwrap_or(true)
                    );
                    assert!(!engine.graphs[&restored_id].graph.no_decomp);
                    let program = pb::Program {
                        sorts: request.sorts,
                        nodes: vec![
                            pb::Node {
                                kind: Some(pb::node::Kind::Call(pb::Call {
                                    func: "egglog.experimental.size.tables".into(),
                                    args: vec![],
                                })),
                                ..Default::default()
                            },
                            pb::Node {
                                kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                                    value: Some(pb::primitive_value::Value::I64(0)),
                                })),
                                ..Default::default()
                            },
                            pb::Node {
                                kind: Some(pb::node::Kind::Union(pb::Union {
                                    members: vec![0, 1],
                                })),
                                ..Default::default()
                            },
                        ],
                        commands: vec![pb::Command {
                            kind: Some(pb::command::Kind::Prove(pb::Prove { facts: vec![2] })),
                            ..Default::default()
                        }],
                        ..Default::default()
                    };
                    assert!(graph::rules(&program).next().is_none());
                    let prepared = engine.graphs[&id].prepare(&mut program.clone());
                    assert_eq!(prepared.is_ok(), seminaive == Some(false));
                    let response = run_host_default(&mut engine, id, program);
                    let error = response.error.unwrap();
                    if seminaive == Some(false) {
                        // Compile admission above is independent of this later
                        // normal-mode proof extraction failure, not proof success.
                        assert_eq!(error.code, pb::ErrorCode::RuntimeFailure as i32);
                        assert_eq!(error.location.unwrap().path, vec![0]);
                    } else {
                        assert_eq!(error.code, pb::ErrorCode::InvalidProgram as i32);
                        assert!(error.message.contains("egglog.experimental.size.tables"));
                        assert!(error.location.is_none());
                    }
                }
            }
        }
    }

    #[test]
    fn scalar_reflection_reads_actual_native_values_without_terms() {
        let graph = crate::new_experimental_egraph();
        let values = [
            (
                "BigInt",
                graph.base_to_value(egglog::sort::Z::new(123.into())),
                value::Scalar::BigInt(123.into()),
            ),
            (
                "BigRat",
                graph.base_to_value(egglog::sort::Q::new(num::BigRational::new(
                    1.into(),
                    3.into(),
                ))),
                value::Scalar::BigRat(num::BigRational::new(1.into(), 3.into())),
            ),
            (
                "Rational",
                graph.base_to_value(crate::rational::R::new(num::rational::Rational64::new(
                    2, 3,
                ))),
                value::Scalar::Rational(num::rational::Rational64::new(2, 3)),
            ),
        ];
        for (family, native, expected) in values {
            assert_eq!(
                value::Scalar::reflect(&graph, graph.get_sort_by_name(family).unwrap(), native),
                Some(expected)
            );
        }
    }

    static HOST_DEFAULT_BODY_CALLS: std::sync::atomic::AtomicUsize =
        std::sync::atomic::AtomicUsize::new(0);

    // These closure tests intentionally need a provider with no Python view.
    // Vec's real Python metadata is now frozen and cannot serve that fixture.
    fn host_default_engine() -> (Engine, u64) {
        let mut engine = Engine::default();
        let request = pb::CreateEGraphRequest {
            sorts: vec![pb::Sort {
                kind: Some(pb::sort::Kind::Application(pb::SortApplication {
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
        };
        let id = pb::CreateEGraphResponse::decode(
            engine.create(&request.encode_to_vec()).unwrap().as_slice(),
        )
        .unwrap()
        .egraph_id;
        let graph = &mut engine.graphs.get_mut(&id).unwrap().graph;
        egglog::add_primitive!(
            graph,
            "test-default-identity"[id = "test.default.identity"] = |value: i64| -> i64 {
                {
                    HOST_DEFAULT_BODY_CALLS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                    value
                }
            }
        );
        (engine, id)
    }

    fn run_host_default(engine: &mut Engine, egraph_id: u64, program: pb::Program) -> Observed {
        let bytes = engine
            .run(
                &pb::RunProgramRequest {
                    egraph_id,
                    program: Some(program),
                    diagnostics: false,
                }
                .encode_to_vec(),
            )
            .unwrap();
        Observed::from_frames(
            (bytes)
                .iter()
                .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()),
        )
    }

    fn run_diagnostic_matches(
        engine: &mut Engine,
        egraph_id: u64,
        program: pb::Program,
    ) -> (Observed, u64) {
        let response = Observed::from_frames(
            engine
                .run_request(pb::RunProgramRequest {
                    egraph_id,
                    program: Some(program),
                    diagnostics: true,
                })
                .unwrap(),
        );
        let matches = response
            .output
            .outputs
            .iter()
            .filter_map(|output| match &output.kind {
                Some(pb::command_output::Kind::Diagnostic(document)) => Some(document),
                _ => None,
            })
            .map(|document| {
                let value: serde_json::Value = serde_json::from_slice(&document.content).unwrap();
                value["num_matches_per_rule"]
                    .as_object()
                    .unwrap()
                    .values()
                    .map(|value| value.as_u64().unwrap())
                    .sum::<u64>()
            })
            .sum();
        (response, matches)
    }

    #[test]
    fn extracted_node_interning_preserves_exact_float_bits() {
        let mut response = pb::RunProgramOutput::default();
        let mut encoded = HashMap::new();
        // Separate native graphs avoid OrderedFloat's own NaN/zero equality;
        // this regression concerns actual scalar reflection and protobuf keys.
        for (bits, expected) in [
            (0, 0),
            (1u64 << 63, 1),
            (0x7ff8_0000_0000_0001, 2),
            (0x7ff8_0000_0000_0002, 3),
            (0x7ff8_0000_0000_0001, 2),
            (0, 0),
        ] {
            let (mut engine, id) = host_default_engine();
            let session = engine.graphs.get_mut(&id).unwrap();
            let sort = session.graph.get_sort_by_name("f64").unwrap();
            let mut terms = TermDag::default();
            let term = terms.lit(Literal::Float(f64::from_bits(bits).into()));
            let index = encode_term(
                session,
                &terms,
                term,
                sort,
                session
                    .graph
                    .base_to_value(egglog::sort::F::new(f64::from_bits(bits).into())),
                &[],
                &mut response,
                &mut encoded,
            )
            .unwrap();
            assert_eq!(index, expected);
            assert!(matches!(
                &response.nodes[index as usize].kind,
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::F64Bits(actual))
                })) if *actual == bits
            ));
        }
        assert_eq!(response.nodes.len(), 4);
    }

    #[test]
    fn container_codec_checks_native_family_child_sorts_and_arity_without_terms() {
        let (mut engine, id) = host_default_engine();
        let session = engine.graphs.get_mut(&id).unwrap();
        session.graph.parse_and_run_program(None, "(sort V (Vec i64)) (sort S (Set i64)) (sort T (MultiSet i64)) (sort M (Map i64 i64)) (sort P (Pair i64 i64)) (sort O (Maybe i64))").unwrap();
        let mut response = pb::RunProgramOutput::default();
        let scalar = encode_sort(
            &session.graph,
            &session.names,
            session.graph.get_sort_by_name("i64").unwrap(),
            &mut response,
        )
        .unwrap();
        response.nodes.push(pb::Node {
            sort_id: scalar,
            ..Default::default()
        });
        for (name, valid, invalid) in [
            ("V", vec![0, 1, 3], vec![]),
            ("S", vec![0, 1, 3], vec![]),
            ("T", vec![0, 1, 3], vec![]),
            ("M", vec![0, 2, 4], vec![1, 3]),
            ("P", vec![2], vec![0, 1, 3]),
            ("O", vec![0, 1], vec![2, 3]),
        ] {
            let sort = session.graph.get_sort_by_name(name).unwrap();
            let index = encode_sort(&session.graph, &session.names, sort, &mut response).unwrap();
            let wire = &response.sorts[index as usize];
            for count in valid {
                assert!(
                    value::container_payload(sort, wire, &vec![0; count], &response.nodes).is_ok(),
                    "{name}/{count}"
                );
            }
            for count in invalid {
                assert!(
                    value::container_payload(sort, wire, &vec![0; count], &response.nodes).is_err(),
                    "{name}/{count}"
                );
            }
            let wrong_nodes = vec![pb::Node {
                sort_id: index,
                ..Default::default()
            }];
            assert!(value::container_payload(sort, wire, &[0, 0], &wrong_nodes).is_err());
            let mut wrong_family = wire.clone();
            let Some(pb::sort::Kind::Application(family)) = &mut wrong_family.kind else {
                unreachable!()
            };
            family.name = "Foreign".into();
            assert!(value::container_payload(sort, &wrong_family, &[], &response.nodes).is_err());
        }
    }

    #[test]
    fn set_codec_preserves_authored_child_evaluation_order() {
        let mut program = pb::Program {
            sorts: vec![
                pb::Sort {
                    kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                        name: "i64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                        name: "Set".into(),
                        args: vec![0],
                    })),
                    ..Default::default()
                },
            ],
            nodes: vec![
                pb::Node {
                    sort_id: 0,
                    kind: Some(pb::node::Kind::Call(pb::Call {
                        func: "effectful_child".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
                pb::Node {
                    sort_id: 0,
                    kind: Some(pb::node::Kind::Call(pb::Call {
                        func: "another_child".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
                pb::Node {
                    sort_id: 1,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Set(pb::ValueList {
                            items: vec![0, 1, 0],
                        })),
                    })),
                    ..Default::default()
                },
            ],
            ..Default::default()
        };
        lower_container_values(&mut program).unwrap();
        assert_eq!(
            program.nodes[2].kind,
            Some(pb::node::Kind::Call(pb::Call {
                func: "egglog.core.set.of".into(),
                args: vec![0, 1, 0]
            }))
        );
    }

    #[test]
    fn creation_threads_match_native_policy_and_survive_clone() {
        for threads in [None, Some(0), Some(1), Some(2)] {
            let request = pb::CreateEGraphRequest {
                sorts: vec![pb::Sort {
                    kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                        name: "i64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                }],
                options: Some(pb::EGraphOptions {
                    cost_sort: Some(0),
                    ..Default::default()
                }),
                threads,
                ..Default::default()
            };
            let mut engine = Engine::default();
            assert!(engine.create(&[0xff]).is_err());
            // Invalid creation must fail before configuring a potentially large pool.
            let mut invalid = request.clone();
            invalid.options = None;
            invalid.threads = Some(u32::MAX);
            assert!(engine.create(&invalid.encode_to_vec()).is_err());
            assert_eq!(engine.next_id, 0);
            assert!(engine.graphs.is_empty());
            let bytes = engine.create(&request.encode_to_vec());
            if cfg!(target_family = "wasm") && threads.is_some_and(|n| n > 1) {
                assert!(bytes.is_err());
                continue;
            }
            let id = pb::CreateEGraphResponse::decode(bytes.unwrap().as_slice())
                .unwrap()
                .egraph_id;
            let mut native = crate::new_experimental_egraph();
            if let Some(threads) = threads {
                native.set_num_threads(usize::try_from(threads).unwrap());
            }
            assert_eq!(engine.graphs[&id].graph.num_threads(), native.num_threads());
            let cloned = engine
                .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
                .unwrap();
            let clone = pb::CloneEGraphResponse::decode(cloned.as_slice())
                .unwrap()
                .egraph_id;
            assert_eq!(
                engine.graphs[&clone].graph.num_threads(),
                native.num_threads()
            );
        }
    }

    #[derive(Clone)]
    struct ForeignPrimitive(String);

    #[test]
    fn unknown_creation_modes_do_not_allocate_handles() {
        let mut engine = Engine::default();
        for execution_mode in [99, -1] {
            let request = pb::CreateEGraphRequest {
                sorts: vec![pb::Sort {
                    kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                        name: "i64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                }],
                options: Some(pb::EGraphOptions {
                    cost_sort: Some(0),
                    execution_mode,
                    ..Default::default()
                }),
                ..Default::default()
            };
            let result = engine.create(&request.encode_to_vec());
            assert!(
                result.is_err(),
                "unsupported mode {execution_mode} must not silently use normal execution"
            );
            assert_eq!(engine.next_id, 0);
            assert!(engine.graphs.is_empty());
        }
    }

    impl egglog::Primitive for ForeignPrimitive {
        fn name(&self) -> &str {
            &self.0
        }
        fn get_type_constraints(
            &self,
            _: &ast::Span,
        ) -> Box<dyn egglog::constraint::TypeConstraint> {
            panic!("occupied provider must not be typechecked")
        }
    }

    impl egglog::PurePrim for ForeignPrimitive {
        fn apply<'a, 'db>(&self, _: egglog::PureState<'a, 'db>, _: &[Value]) -> Option<Value> {
            panic!("occupied provider must not execute")
        }
    }

    #[test]
    fn foreign_physical_symbols_are_rejected_without_reuse_or_mutation() {
        for namespace in ["sort", "call"] {
            for foreign_kind in ["sort", "function", "primitive"] {
                let name = native_name(namespace, "Public");
                let mut graph = crate::new_experimental_egraph();
                match foreign_kind {
                    "sort" => {
                        graph
                            .parse_and_run_program(None, &format!("(sort {name})"))
                            .unwrap();
                    }
                    "function" => {
                        graph
                            .parse_and_run_program(
                                None,
                                &format!("(function {name} () i64 :merge new) (set ({name}) 7)"),
                            )
                            .unwrap();
                    }
                    _ => graph.add_pure_primitive(ForeignPrimitive(name.clone()), None),
                }
                let session = Session {
                    graph,
                    extension: None,
                    mode: pb::ExecutionMode::Normal,
                    definitions: pb::Program::default(),
                    builtins: crate::builtin::configured_catalog(&crate::new_experimental_egraph())
                        .unwrap(),
                    names: NativeNames::default(),
                    request: 0,
                    registry: rules::Registry::default(),
                    sorts: HashSet::new(),
                    cost_models: HashMap::new(),
                };
                let mut program = pb::Program {
                    sorts: vec![pb::Sort {
                        kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                            name: "i64".into(),
                            args: vec![],
                        })),
                        ..Default::default()
                    }],
                    declarations: vec![pb::Declaration {
                        kind: Some(if namespace == "sort" {
                            pb::declaration::Kind::EqSort(pb::EqSort {
                                name: "Public".into(),
                            })
                        } else {
                            pb::declaration::Kind::Function(pb::Function {
                                name: "Public".into(),
                                output: 0,
                                ..Default::default()
                            })
                        }),
                        ..Default::default()
                    }],
                    ..Default::default()
                };
                let error = session.prepare(&mut program).err().unwrap();
                assert!(
                    error
                        .0
                        .message
                        .contains("native declaration namespace collision")
                );
                assert_eq!(session.definitions, pb::Program::default());
                if foreign_kind == "function" {
                    session
                        .graph
                        .clone()
                        .parse_and_run_program(None, &format!("(check (= ({name}) 7))"))
                        .unwrap();
                }
            }
        }
    }

    #[test]
    fn preparation_compiles_unused_rules_without_running_bodies_or_validators() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        for mode in [
            pb::ExecutionMode::Normal,
            pb::ExecutionMode::TermEncoding,
            pb::ExecutionMode::Proofs,
            pb::ExecutionMode::ProofTesting,
        ] {
            let calls = Arc::new(AtomicUsize::new(0));
            let validations = Arc::new(AtomicUsize::new(0));
            let observed = calls.clone();
            let validator_calls = validations.clone();
            let (mut engine, id) = host_default_engine();
            let session = engine.graphs.get_mut(&id).unwrap();
            egglog::add_primitive_with_validator!(&mut session.graph, "counted"[id = "test.counted"] = {observed: Arc<AtomicUsize>} |value: i64| -> i64 {{
                self.ctx.fetch_add(1, Ordering::SeqCst);
                value
            }}, move |_: &mut TermDag, args: &[TermId]| -> Option<TermId> {
                validator_calls.fetch_add(1, Ordering::SeqCst);
                args.first().copied()
            });
            let graph = std::mem::take(&mut session.graph);
            session.graph = match mode {
                pb::ExecutionMode::Normal => graph,
                pb::ExecutionMode::TermEncoding => graph.with_term_encoding_enabled(),
                pb::ExecutionMode::Proofs => graph.with_proofs_enabled(),
                pb::ExecutionMode::ProofTesting => graph.with_proofs_enabled().with_proof_testing(),
            };
            session.mode = mode;
            // This private fixture finishes ambient initialization after Create;
            // real extensions initialize before the seed is captured.
            session.builtins = crate::builtin::configured_catalog(&session.graph).unwrap();
            let mut program = pb::Program {
                sorts: vec![
                    pb::Sort {
                        kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                            name: "i64".into(),
                            args: vec![],
                        })),
                        ..Default::default()
                    },
                    pb::Sort {
                        kind: Some(pb::sort::Kind::Eq("Num".into())),
                        ..Default::default()
                    },
                ],
                declarations: vec![
                    pb::Declaration {
                        kind: Some(pb::declaration::Kind::EqSort(pb::EqSort {
                            name: "Num".into(),
                        })),
                        ..Default::default()
                    },
                    pb::Declaration {
                        kind: Some(pb::declaration::Kind::Constructor(pb::Constructor {
                            name: "N".into(),
                            inputs: vec![pb::Arg {
                                name: "x".into(),
                                sort: 0,
                            }],
                            output: 1,
                            ..Default::default()
                        })),
                        ..Default::default()
                    },
                ],
                nodes: vec![
                    pb::Node {
                        sort_id: 0,
                        kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                            value: Some(pb::primitive_value::Value::I64(1)),
                        })),
                        ..Default::default()
                    },
                    pb::Node {
                        sort_id: 0,
                        kind: Some(pb::node::Kind::Call(pb::Call {
                            func: "test.counted".into(),
                            args: vec![0],
                        })),
                        ..Default::default()
                    },
                    pb::Node {
                        sort_id: 1,
                        kind: Some(pb::node::Kind::Call(pb::Call {
                            func: "N".into(),
                            args: vec![1],
                        })),
                        ..Default::default()
                    },
                    pb::Node {
                        sort_id: 0,
                        kind: Some(pb::node::Kind::Var("x".into())),
                        ..Default::default()
                    },
                    pb::Node {
                        sort_id: 0,
                        kind: Some(pb::node::Kind::Call(pb::Call {
                            func: "test.counted".into(),
                            args: vec![3],
                        })),
                        ..Default::default()
                    },
                    pb::Node {
                        sort_id: 0,
                        kind: Some(pb::node::Kind::Union(pb::Union {
                            members: vec![4, 0],
                        })),
                        ..Default::default()
                    },
                    pb::Node {
                        sort_id: 1,
                        kind: Some(pb::node::Kind::Call(pb::Call {
                            func: "N".into(),
                            args: vec![3],
                        })),
                        ..Default::default()
                    },
                ],
                commands: vec![
                    pb::Command {
                        kind: Some(pb::command::Kind::Action(pb::Action {
                            kind: Some(pb::action::Kind::Term(2)),
                            ..Default::default()
                        })),
                        ..Default::default()
                    },
                    pb::Command {
                        kind: Some(pb::command::Kind::Prove(pb::Prove { facts: vec![2] })),
                        ..Default::default()
                    },
                ],
                ..Default::default()
            };
            let mut invalid = program.clone();
            invalid.commands.push(pb::Command {
                kind: Some(pb::command::Kind::Prove(pb::Prove { facts: vec![999] })),
                ..Default::default()
            });
            assert!(run_host_default(&mut engine, id, invalid).error.is_some());
            let mut ungrounded = program.clone();
            ungrounded.commands.push(pb::Command {
                kind: Some(pb::command::Kind::Loop(pb::Loop {
                    max_iterations: Some(0),
                    body: vec![pb::Command {
                        kind: Some(pb::command::Kind::Run(pb::Run {
                            rulesets: vec![pb::RulesetSelection {
                                kind: Some(pb::ruleset_selection::Kind::Ruleset(pb::Ruleset {
                                    rules: vec![pb::Rule {
                                        kind: Some(pb::rule::Kind::Rule(pb::RuleBody {
                                            query: vec![5],
                                            head: vec![pb::Action {
                                                kind: Some(pb::action::Kind::Term(6)),
                                                ..Default::default()
                                            }],
                                        })),
                                        eval_mode: pb::RuleEvalMode::Seminaive.into(),
                                        ..Default::default()
                                    }],
                                })),
                            }],
                            ..Default::default()
                        })),
                        ..Default::default()
                    }],
                    ..Default::default()
                })),
                ..Default::default()
            });
            let error = run_host_default(&mut engine, id, ungrounded).error.unwrap();
            assert!(error.message.contains("ungrounded"), "{}", error.message);
            engine.graphs[&id].prepare(&mut program.clone()).unwrap();
            assert_eq!(calls.load(Ordering::SeqCst), 0);
            assert_eq!(validations.load(Ordering::SeqCst), 0);
            if mode != pb::ExecutionMode::Normal {
                let mut unsupported = program.clone();
                let Some(pb::node::Kind::Call(call)) = &mut unsupported.nodes[1].kind else {
                    unreachable!()
                };
                call.func = "test.default.identity".into(); // registered, no proof validator
                let error = run_host_default(&mut engine, id, unsupported)
                    .error
                    .unwrap();
                assert!(error.message.contains("validator"), "{}", error.message);
            }
            if matches!(
                mode,
                pb::ExecutionMode::Normal | pb::ExecutionMode::TermEncoding
            ) {
                program.commands.truncate(1);
            }
            assert_eq!(run_host_default(&mut engine, id, program).error, None);
            assert!(calls.load(Ordering::SeqCst) > 0);
            if matches!(
                mode,
                pb::ExecutionMode::Proofs | pb::ExecutionMode::ProofTesting
            ) {
                assert!(validations.load(Ordering::SeqCst) > 0);
            }
        }
    }

    #[test]
    fn installation_sites_use_original_indices_and_resupply_executes_nothing() {
        let (mut engine, id) = host_default_engine();
        let session = engine.graphs.get_mut(&id).unwrap();
        session.graph = std::mem::take(&mut session.graph).with_proofs_enabled();
        session.mode = pb::ExecutionMode::Proofs;
        let mut program = source::Source::new(None, "(datatype Num (N i64))")
            .unwrap()
            .next()
            .unwrap()
            .unwrap();
        program
            .declarations
            .insert(0, program.declarations[0].clone());
        program.declarations.push(program.declarations[2].clone()); // compatible resupply
        let i64_sort = program
            .sorts
            .iter()
            .position(
                |s| matches!(&s.kind, Some(pb::sort::Kind::Application(f)) if f.name == "i64"),
            )
            .unwrap() as u32;
        program.sorts.push(pb::Sort {
            kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                name: "Vec".into(),
                args: vec![i64_sort],
            })),
            ..Default::default()
        });
        let prepared = session.prepare(&mut program.clone()).unwrap();
        assert_eq!(
            prepared
                .installations
                .iter()
                .map(|i| i.source_declaration)
                .collect::<Vec<_>>(),
            [Some(0), None, Some(2),]
        );
        let installed = run_host_default(&mut engine, id, program.clone());
        assert_eq!(installed.error, None);
        assert!(installed.output.outputs.is_empty());
        let cloned = engine
            .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
            .unwrap();
        let clone = pb::CloneEGraphResponse::decode(cloned.as_slice())
            .unwrap()
            .egraph_id;
        for id in [id, clone] {
            let response = run_host_default(&mut engine, id, program.clone());
            assert_eq!(response.error, None);
        }
    }

    // These inventory controls deliberately bind all definitions before their
    // combined command list; they do not model Source's submission boundaries.
    // Concatenation preserves each packet's node/Union occurrences, while the
    // producer's monotone sort/file arenas remain cumulative in this flat input.
    fn inventory_fixture(source: &str) -> pb::Program {
        let mut program = pb::Program::default();
        let phases = source::Source::new(None, source)
            .unwrap()
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        for phase in &phases {
            crate::builtin::definitions::reconcile_declarations(phase, &mut program).unwrap();
        }
        for phase in &phases {
            let files = program.files.len() as u32;
            graph::append(&mut program, phase, files).unwrap();
        }
        let mut seen = HashSet::new();
        program.rulesets.reverse();
        program
            .rulesets
            .retain(|binding| seen.insert(binding.name.clone()));
        program.rulesets.reverse();
        program
    }

    #[test]
    fn action_controls_union_frames_are_fresh_per_iteration() {
        let (mut engine, id) = host_default_engine();
        let mut program = inventory_fixture("(sort A)");
        let sort_id = program.sorts.len() as u32;
        program.sorts.push(pb::Sort {
            kind: Some(pb::sort::Kind::Eq("A".into())),
            ..Default::default()
        });
        program.nodes.push(pb::Node {
            sort_id,
            kind: Some(pb::node::Kind::Union(pb::Union { members: vec![] })),
            ..Default::default()
        });
        let action = pb::Command {
            kind: Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Term(0)),
                ..Default::default()
            })),
            ..Default::default()
        };
        program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Loop(pb::Loop {
                max_iterations: Some(3),
                until: vec![],
                body: vec![pb::Command {
                    kind: Some(pb::command::Kind::Loop(pb::Loop {
                        max_iterations: Some(2),
                        until: vec![],
                        body: vec![action.clone(), action],
                    })),
                    ..Default::default()
                }],
            })),
            ..Default::default()
        });
        let response = run_host_default(&mut engine, id, program);
        assert_eq!(response.error, None);
        assert!(
            matches!(&response.output.outputs[0].kind, Some(pb::command_output::Kind::Run(outcome)) if outcome.updated && !outcome.can_stop)
        );
        assert_eq!(
            engine.graphs[&id]
                .graph
                .materialized_eq_classes()
                .iter()
                .filter(|(name, _)| name.as_ref() == native_name("sort", "A"))
                .count(),
            6,
            "two uses retain one Union identity inside each body; six body executions mint six classes"
        );
    }

    // Native class inventory: execution enters only through encoded requests.
    #[test]
    fn byte_actions_preserve_orphan_class_inventory() {
        let (mut engine, id) = host_default_engine();
        let program = inventory_fixture(
            "(sort A) (sort B) (sort Unused)
             (constructor AItem (i64) A) (constructor BItem (i64) B)
             (AItem 11) (AItem 22) (BItem 11)
             (union (AItem 11) (AItem 22))
             (delete (AItem 11)) (delete (AItem 22)) (delete (BItem 11))",
        );
        let response = run_host_default(&mut engine, id, program);
        assert_eq!(response.error, None);
        let graph = &engine.graphs[&id].graph;
        assert_eq!(graph.num_tuples(), 0);
        for name in ["AItem", "BItem"] {
            assert_eq!(graph.get_size(&native_name("call", name)), 0);
        }
        let classes = graph.materialized_eq_classes();
        for (sort, expected) in [("A", 1), ("B", 1), ("Unused", 0)] {
            assert_eq!(
                classes
                    .iter()
                    .filter(|(name, _)| name.as_ref() == native_name("sort", sort))
                    .count(),
                expected,
                "{sort} class inventory after deleting every producer"
            );
        }
        assert_eq!(classes.len(), 2, "no synthetic or untyped class identities");
    }

    #[test]
    fn byte_class_inventory_clone_destroy_and_failure_prefix() {
        let (mut engine, id) = host_default_engine();
        let initial = inventory_fixture("(datatype A (AItem i64)) (AItem 1)");
        assert_eq!(run_host_default(&mut engine, id, initial).error, None);
        let prefix = engine.graphs[&id].graph.materialized_eq_classes();
        assert_eq!(prefix.len(), 1);
        let bytes = engine
            .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
            .unwrap();
        let child = pb::CloneEGraphResponse::decode(bytes.as_slice())
            .unwrap()
            .egraph_id;
        let response = run_host_default(
            &mut engine,
            child,
            inventory_fixture("(datatype A (AItem i64)) (AItem 2) (panic \"inventory-prefix\")"),
        );
        assert!(response.error.is_some());
        assert_eq!(
            engine.graphs[&child].graph.materialized_eq_classes().len(),
            2
        );
        assert_eq!(engine.graphs[&id].graph.materialized_eq_classes(), prefix);
        let response = engine
            .destroy(&pb::DestroyEGraphRequest { egraph_id: child }.encode_to_vec())
            .unwrap();
        pb::DestroyEGraphResponse::decode(response.as_slice()).unwrap();
        assert_eq!(engine.graphs[&id].graph.materialized_eq_classes(), prefix);
        assert_eq!(
            run_host_default(
                &mut engine,
                id,
                inventory_fixture("(datatype A (AItem i64)) (delete (AItem 1))")
            )
            .error,
            None
        );
        assert_eq!(engine.graphs[&id].graph.num_tuples(), 0);
        assert_eq!(engine.graphs[&id].graph.materialized_eq_classes(), prefix);
    }

    #[test]
    fn byte_union_empty_shared_singleton_has_no_carriers() {
        let (mut engine, id) = host_default_engine();
        let mut program =
            inventory_fixture("(datatype A (AItem i64)) (function keep () A :merge old) (AItem 1)");
        let Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Term(item)),
            ..
        })) = program.commands.last().unwrap().kind.as_ref()
        else {
            panic!("constructor fixture")
        };
        let item = *item;
        let sort_id = program.nodes[item as usize].sort_id;
        let empty = program.nodes.len() as u32;
        for members in [vec![], vec![item], vec![]] {
            program.nodes.push(pb::Node {
                sort_id,
                kind: Some(pb::node::Kind::Union(pb::Union { members })),
                ..Default::default()
            });
        }
        program.commands.clear();
        for index in [empty, empty, empty + 1, empty + 2] {
            program.commands.push(pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Term(index)),
                    ..Default::default()
                })),
                ..Default::default()
            });
        }
        program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Set(pb::Set {
                    target: Some(pb::Call {
                        func: "keep".into(),
                        args: vec![],
                    }),
                    value: Some(empty),
                })),
                ..Default::default()
            })),
            ..Default::default()
        });
        let response = run_host_default(&mut engine, id, program);
        assert_eq!(response.error, None);
        assert!(response.output.outputs.is_empty());
        let graph = &engine.graphs[&id].graph;
        assert_eq!(graph.materialized_eq_classes().len(), 3);
        assert_eq!(graph.get_size(&native_name("call", "AItem")), 1);
        assert_eq!(graph.get_size(&native_name("call", "keep")), 1);
        assert_eq!(graph.num_tuples(), 2, "no identity carrier rows");
    }

    #[test]
    fn byte_union_binary_member_failure_keeps_native_inventory() {
        for (lhs, rhs, expected_classes) in [
            ("(N (vec-get (vec-of 1) 2))", "(Seen)", 1),
            ("(Seen)", "(N (vec-get (vec-of 1) 2))", 2),
        ] {
            let source =
                format!("(sort V (Vec i64)) (datatype E (N i64) (Seen)) (N 9) (union {lhs} {rhs})");
            let mut native = crate::new_experimental_egraph();
            let error = native.parse_and_run_program(None, &source).unwrap_err();
            assert!(error.to_string().contains("call of primitive"));
            assert_eq!(native.materialized_eq_classes().len(), expected_classes);
            for reused in [false, true] {
                let (mut engine, id) = host_default_engine();
                let mut program = inventory_fixture(&source);
                let failure_index = program.commands.len() - 1;
                let span = program.commands[failure_index].span;
                let source_file = program.files[span.unwrap().file as usize].clone();
                if reused {
                    program
                        .commands
                        .push(program.commands[failure_index].clone());
                }
                let response = run_host_default(&mut engine, id, program);
                let error = response.error.unwrap();
                assert_eq!(error.code, i32::from(pb::ErrorCode::RuntimeFailure));
                assert_eq!(error.location.unwrap().path, [failure_index as u32]);
                let actual = error.span.unwrap();
                let expected = span.unwrap();
                assert_eq!((actual.start, actual.end), (expected.start, expected.end));
                assert_eq!(response.files[actual.file as usize], source_file);
                assert!(response.output.outputs.is_empty());
                let graph = &engine.graphs[&id].graph;
                assert_eq!(graph.materialized_eq_classes().len(), expected_classes);
                for table in ["N", "Seen"] {
                    assert_eq!(
                        graph.get_size(&native_name("call", table)),
                        native.get_size(table)
                    );
                }
            }
        }
    }

    #[test]
    fn byte_union_failure_keeps_run_reports_and_reusable_prefix() {
        let declarations = "(sort V (Vec i64)) (datatype E (N i64) (Seen) (Goal i64) (After)) (function keep () E :merge old)";
        let source = format!(
            "{declarations} (ruleset derive) (rule ((N x)) ((Goal x)) :ruleset derive :name \"make-goal\") (N 9) (run derive 1) (print-stats) (union (Seen) (N (vec-get (vec-of 1) 2))) (After)"
        );
        let mut native = crate::new_experimental_egraph();
        assert!(native.parse_and_run_program(None, &source).is_err());
        assert_eq!(native.materialized_eq_classes().len(), 3);
        assert_eq!(native.get_size("After"), 0);

        let (mut engine, id) = host_default_engine();
        let mut program = inventory_fixture(&source);
        let mut definitions = program.clone();
        definitions.commands.clear();
        assert_eq!(run_host_default(&mut engine, id, definitions).error, None);
        program.declarations.clear();
        program.rulesets.clear();
        program.rulesets.clear();
        let Some(pb::command::Kind::Run(run)) = &mut program.commands[1].kind else {
            panic!("fixture Run")
        };
        run.rulesets = (vec!["derive".into()])
            .into_iter()
            .map(|name| pb::RulesetSelection {
                kind: Some(pb::ruleset_selection::Kind::Name(name)),
            })
            .collect();
        let command_span = pb::Span {
            file: 0,
            start: 0,
            end: 1,
        };
        program.commands[3].span = Some(command_span);
        let Some(pb::command::Kind::Action(action)) = &program.commands[3].kind else {
            panic!("fixture Union")
        };
        let action_span = action.span.unwrap();
        let action_file = program.files[action_span.file as usize].clone();
        assert_ne!(action_span, command_span);
        // Force first-use retention; the duplicate and After marker must remain
        // unentered after the first Union's later member fails.
        program.commands.insert(4, program.commands[3].clone());
        let response = Observed::from_frames(
            (engine
                .run(
                    &pb::RunProgramRequest {
                        egraph_id: id,
                        program: Some(program),
                        diagnostics: true,
                    }
                    .encode_to_vec(),
                )
                .unwrap())
            .iter()
            .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()),
        );
        let error = response.error.as_ref().unwrap();
        assert_eq!(error.code, i32::from(pb::ErrorCode::RuntimeFailure));
        assert_eq!(error.location.as_ref().unwrap().path, [3]);
        assert!(error.location.as_ref().unwrap().iterations.is_empty());
        let span = error.span.unwrap();
        assert_eq!((span.start, span.end), (action_span.start, action_span.end));
        assert_eq!(response.files[span.file as usize], action_file);
        assert_eq!(response.output.outputs.len(), 3);
        for (output, path) in response.output.outputs.iter().zip([1, 1, 2]) {
            assert_eq!(output.location.as_ref().unwrap().path, [path]);
            assert!(output.location.as_ref().unwrap().iterations.is_empty());
        }
        let Some(pb::command_output::Kind::Run(outcome)) = &response.output.outputs[0].kind else {
            panic!("Run")
        };
        let Some(pb::command_output::Kind::Diagnostic(run_detail)) =
            &response.output.outputs[1].kind
        else {
            panic!("Run diagnostic")
        };
        let Some(pb::command_output::Kind::Diagnostic(stats)) = &response.output.outputs[2].kind
        else {
            panic!("Stats")
        };
        let native_report = native.get_overall_run_report();
        assert_eq!(
            (outcome.updated, outcome.can_stop),
            (native_report.updated, native_report.can_stop)
        );
        let run_detail: serde_json::Value = serde_json::from_slice(&run_detail.content).unwrap();
        assert!(run_detail.get("updated").is_none());
        assert_eq!(
            run_detail["num_matches_per_rule"]
                .as_object()
                .unwrap()
                .values()
                .map(|value| value.as_u64().unwrap())
                .sum::<u64>(),
            1
        );

        let graph = &engine.graphs[&id].graph;
        assert_eq!(
            graph.materialized_eq_classes().len(),
            native.materialized_eq_classes().len()
        );
        assert_eq!(graph.num_tuples(), native.num_tuples());
        for table in ["N", "Goal", "Seen", "After", "keep"] {
            assert_eq!(
                graph.get_size(&native_name("call", table)),
                native.get_size(table)
            );
        }

        // Reuse this exact handle immediately. A new generalized action creates
        // After, sets keep, and is followed by an ordinary byte Check.
        let mut retry = inventory_fixture(&format!(
            "{declarations} (print-stats) (set (keep) (After)) (check (= (keep) (After)))"
        ));
        retry.declarations.clear();
        let Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Set(set)),
            ..
        })) = &mut retry.commands[1].kind
        else {
            panic!("fixture Set")
        };
        let after = set.value.unwrap();
        set.value = Some(retry.nodes.len() as u32);
        retry.nodes.push(pb::Node {
            sort_id: retry.nodes[after as usize].sort_id,
            kind: Some(pb::node::Kind::Union(pb::Union {
                members: vec![after],
            })),
            ..Default::default()
        });
        let reused = Observed::from_frames(
            (engine
                .run(
                    &pb::RunProgramRequest {
                        egraph_id: id,
                        program: Some(retry),
                        diagnostics: true,
                    }
                    .encode_to_vec(),
                )
                .unwrap())
            .iter()
            .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()),
        );
        assert_eq!(reused.error, None);
        assert_eq!(reused.output.outputs.len(), 1);
        assert_eq!(
            reused.output.outputs[0].location.as_ref().unwrap().path,
            [0]
        );
        assert_eq!(
            reused.output.outputs[0].kind,
            Some(pb::command_output::Kind::Diagnostic(stats.clone())),
            "cumulative collected detail survives failure"
        );
        let graph = &engine.graphs[&id].graph;
        assert_eq!(graph.materialized_eq_classes().len(), 4);
        assert_eq!(graph.get_size(&native_name("call", "After")), 1);
        assert_eq!(graph.get_size(&native_name("call", "keep")), 1);
        assert_eq!(graph.num_tuples(), native.num_tuples() + 2);
    }

    #[test]
    fn byte_union_cycles_keep_backedge_identity_and_distinct_occurrences() {
        let (mut engine, id) = host_default_engine();
        let mut program = inventory_fixture("(datatype A (Atom i64) (Box A)) (Atom 7)");
        let Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Term(atom)),
            ..
        })) = &program.commands.last().unwrap().kind
        else {
            panic!("fixture")
        };
        let atom = *atom;
        let sort_id = program.nodes[atom as usize].sort_id;
        program.commands.clear();
        let start = program.nodes.len() as u32;
        // Two distinct self cycles; one mutual cycle whose backedge is reached
        // before its first member completes; one cycle anchored by an atom.
        let kinds = [
            pb::node::Kind::Union(pb::Union {
                members: vec![start + 1],
            }),
            pb::node::Kind::Call(pb::Call {
                func: "Box".into(),
                args: vec![start],
            }),
            pb::node::Kind::Union(pb::Union {
                members: vec![start + 3],
            }),
            pb::node::Kind::Call(pb::Call {
                func: "Box".into(),
                args: vec![start + 2],
            }),
            pb::node::Kind::Union(pb::Union {
                members: vec![start + 5],
            }),
            pb::node::Kind::Union(pb::Union {
                members: vec![start + 6],
            }),
            pb::node::Kind::Call(pb::Call {
                func: "Box".into(),
                args: vec![start + 4],
            }),
            pb::node::Kind::Union(pb::Union {
                members: vec![atom, start + 8],
            }),
            pb::node::Kind::Call(pb::Call {
                func: "Box".into(),
                args: vec![start + 7],
            }),
        ];
        program.nodes.extend(kinds.into_iter().map(|kind| pb::Node {
            sort_id,
            kind: Some(kind),
            ..Default::default()
        }));
        for index in [start, start + 2, start + 4, start + 7, start + 5, start] {
            program.commands.push(pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Term(index)),
                    ..Default::default()
                })),
                ..Default::default()
            });
        }
        program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Check(pb::Check {
                facts: vec![start, start + 2, start + 4, start + 7],
            })),
            ..Default::default()
        });
        let response = run_host_default(&mut engine, id, program);
        assert_eq!(response.error, None);
        assert!(response.output.outputs.is_empty());
        let graph = &engine.graphs[&id].graph;
        assert_eq!(graph.materialized_eq_classes().len(), 4);
        assert_eq!(graph.get_size(&native_name("call", "Box")), 4);
        assert_eq!(graph.num_tuples(), 5);
        let mut roots = HashSet::new();
        graph
            .constructor_enodes(&native_name("call", "Box"), |enode| {
                assert_eq!(
                    enode.children,
                    [enode.eclass],
                    "a backedge must remain in its own completed class"
                );
                roots.insert(enode.eclass);
            })
            .unwrap();
        assert_eq!(roots.len(), 4);
    }

    #[test]
    fn byte_union_structured_vector_preserves_cycle_and_empty_identity() {
        let (mut engine, id) = host_default_engine();
        let mut program =
            inventory_fixture("(sort A) (sort AV (Vec A)) (constructor Holder (AV) A)");
        let eq = program
            .sorts
            .iter()
            .position(|sort| sort.kind == Some(pb::sort::Kind::Eq("A".into())))
            .unwrap() as u32;
        let vector = program
            .sorts
            .iter()
            .position(|sort| {
                matches!(&sort.kind, Some(pb::sort::Kind::Application(family)) if family.name == "Vec")
            })
            .unwrap() as u32;
        assert!(program.nodes.is_empty());
        for (sort_id, kind) in [
            (eq, pb::node::Kind::Union(pb::Union { members: vec![1] })),
            (
                eq,
                pb::node::Kind::Call(pb::Call {
                    func: "Holder".into(),
                    args: vec![2],
                }),
            ),
            (
                vector,
                pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Vec(pb::ValueList {
                        items: vec![0],
                    })),
                }),
            ),
            (eq, pb::node::Kind::Union(pb::Union { members: vec![] })),
            (
                eq,
                pb::node::Kind::Call(pb::Call {
                    func: "Holder".into(),
                    args: vec![5],
                }),
            ),
            (
                vector,
                pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Vec(pb::ValueList {
                        items: vec![3],
                    })),
                }),
            ),
        ] {
            program.nodes.push(pb::Node {
                sort_id,
                kind: Some(kind),
                ..Default::default()
            });
        }
        for index in [0, 0, 4, 4, 3] {
            program.commands.push(pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Term(index)),
                    ..Default::default()
                })),
                ..Default::default()
            });
        }
        let response = run_host_default(&mut engine, id, program);
        assert_eq!(response.error, None);
        assert!(response.output.outputs.is_empty());
        let graph = &engine.graphs[&id].graph;
        assert_eq!(graph.materialized_eq_classes().len(), 3);
        assert_eq!(graph.num_tuples(), 2, "only the two authored Holder rows");
        let mut children = HashSet::new();
        let mut cyclic = 0;
        graph
            .constructor_enodes(&native_name("call", "Holder"), |enode| {
                let vector = graph
                    .value_to_container::<egglog::sort::VecContainer>(enode.children[0])
                    .unwrap();
                assert_eq!(vector.data.len(), 1);
                children.insert(vector.data[0]);
                cyclic += usize::from(vector.data[0] == enode.eclass);
            })
            .unwrap();
        assert_eq!(
            children.len(),
            2,
            "cycle and empty retain distinct identities"
        );
        assert_eq!(cyclic, 1, "the vector backedge is its Holder's class");
    }

    #[test]
    fn byte_union_first_binary_use_is_captured_across_run_and_deletion() {
        let (mut engine, id) = host_default_engine();
        let mut program = inventory_fixture(
            "(datatype A (Atom i64)) (function keep () A :merge old) (ruleset r) (union (Atom 1) (Atom 2)) (delete (Atom 1)) (delete (Atom 2)) (run r 1)",
        );
        let Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Term(union)),
            ..
        })) = program.commands.first().unwrap().kind.as_ref()
        else {
            panic!("fixture")
        };
        let union = *union;
        program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Set(pb::Set {
                    target: Some(pb::Call {
                        func: "keep".into(),
                        args: vec![],
                    }),
                    value: Some(union),
                })),
                ..Default::default()
            })),
            ..Default::default()
        });
        let response = run_host_default(&mut engine, id, program.clone());
        assert_eq!(response.error, None);
        assert_eq!(response.output.outputs.len(), 1);
        assert!(matches!(
            response.output.outputs[0].kind,
            Some(pb::command_output::Kind::Run(_))
        ));
        let graph = &engine.graphs[&id].graph;
        assert_eq!(
            graph.get_size(&native_name("call", "Atom")),
            0,
            "reusing a Union must not reevaluate deleted members"
        );
        assert_eq!(graph.get_size(&native_name("call", "keep")), 1);
        assert_eq!(graph.materialized_eq_classes().len(), 1);
        // A fresh request, even on a cloned egraph, gets a fresh occurrence frame.
        let bytes = engine
            .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
            .unwrap();
        let clone = pb::CloneEGraphResponse::decode(bytes.as_slice())
            .unwrap()
            .egraph_id;
        program.commands.truncate(1);
        for graph_id in [id, clone] {
            assert_eq!(
                run_host_default(&mut engine, graph_id, program.clone()).error,
                None
            );
            let graph = &engine.graphs[&graph_id].graph;
            assert_eq!(graph.get_size(&native_name("call", "Atom")), 2);
            assert_eq!(graph.materialized_eq_classes().len(), 2);
        }
    }

    #[test]
    fn byte_union_retains_members_but_ordinary_calls_reread_after_writes() {
        let (mut engine, id) = host_default_engine();
        let mut program = inventory_fixture(
            "(datatype A (Atom i64)) (function read () i64 :merge new) (function keep () A :merge old) (ruleset r) (set (read) 1) (Atom (read)) (set (read) 2) (run r 1)",
        );
        let Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Term(call)),
            ..
        })) = &program.commands[1].kind
        else {
            panic!("fixture")
        };
        let call = *call;
        let union = program.nodes.len() as u32;
        program.nodes.push(pb::Node {
            sort_id: program.nodes[call as usize].sort_id,
            kind: Some(pb::node::Kind::Union(pb::Union {
                members: vec![call],
            })),
            ..Default::default()
        });
        let original = program.commands[1].clone();
        let Some(pb::command::Kind::Action(action)) = &mut program.commands[1].kind else {
            unreachable!()
        };
        action.kind = Some(pb::action::Kind::Term(union));
        program.commands.push(original);
        program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Set(pb::Set {
                    target: Some(pb::Call {
                        func: "keep".into(),
                        args: vec![],
                    }),
                    value: Some(union),
                })),
                ..Default::default()
            })),
            ..Default::default()
        });
        let response = run_host_default(&mut engine, id, program);
        assert_eq!(response.error, None);
        assert_eq!(response.output.outputs.len(), 1);
        let graph = &mut engine.graphs.get_mut(&id).unwrap().graph;
        assert_eq!(graph.get_size(&native_name("call", "Atom")), 2);
        graph
            .run_program(vec![Command::Check(
                span!(),
                vec![Fact::Eq(
                    span!(),
                    Expr::Call(span!(), native_name("call", "keep"), vec![]),
                    Expr::Call(
                        span!(),
                        native_name("call", "Atom"),
                        vec![Expr::Lit(span!(), Literal::Int(1))],
                    ),
                )],
            )])
            .unwrap();
        assert_eq!(graph.materialized_eq_classes().len(), 2);
    }

    #[test]
    fn byte_union_control_contexts_and_invalid_unused_graphs_preserve_effect_boundaries() {
        for case in 0..11 {
            let (mut engine, id) = host_default_engine();
            let mut program = inventory_fixture("(datatype A (Atom i64) (Box A)) (Atom 1)");
            let Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Term(atom)),
                ..
            })) = &program.commands[0].kind
            else {
                panic!("fixture")
            };
            let sort_id = program.nodes[*atom as usize].sort_id;
            let union = program.nodes.len() as u32;
            program.nodes.push(pb::Node {
                sort_id,
                kind: Some(pb::node::Kind::Union(pb::Union::default())),
                ..Default::default()
            });
            let action = pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Term(union)),
                    ..Default::default()
                })),
                ..Default::default()
            };
            match case {
                0 => program.commands.push(pb::Command {
                    kind: Some(pb::command::Kind::Fail(Box::new(action))),
                    ..Default::default()
                }),
                1 => {
                    program.nodes[union as usize].kind = Some(pb::node::Kind::Call(pb::Call {
                        func: "Box".into(),
                        args: vec![union],
                    }));
                    // This invalid cycle is intentionally unused.
                }
                2 => program.commands.push(pb::Command {
                    kind: Some(pb::command::Kind::Check(pb::Check { facts: vec![union] })),
                    ..Default::default()
                }),
                3 => {
                    let scalar = program
                        .nodes
                        .iter()
                        .position(|node| {
                            matches!(node.kind, Some(pb::node::Kind::PrimitiveValue(_)))
                        })
                        .unwrap() as u32;
                    program.nodes[union as usize].kind = Some(pb::node::Kind::Union(pb::Union {
                        members: vec![scalar],
                    }));
                }
                4..=6 => {
                    let session = engine.graphs.get_mut(&id).unwrap();
                    session.mode = match case {
                        4 => pb::ExecutionMode::TermEncoding,
                        5 => pb::ExecutionMode::Proofs,
                        _ => pb::ExecutionMode::ProofTesting,
                    };
                    session.graph = match case {
                        4 => std::mem::take(&mut session.graph).with_term_encoding_enabled(),
                        5 => std::mem::take(&mut session.graph).with_proofs_enabled(),
                        _ => std::mem::take(&mut session.graph)
                            .with_proofs_enabled()
                            .with_proof_testing(),
                    };
                    program.commands.push(action);
                }
                7 => program.commands.push(pb::Command {
                    kind: Some(pb::command::Kind::Loop(pb::Loop {
                        max_iterations: Some(0),
                        body: vec![pb::Command {
                            kind: Some(pb::command::Kind::Run(pb::Run {
                                rulesets: vec![pb::RulesetSelection {
                                    kind: Some(pb::ruleset_selection::Kind::Ruleset(pb::Ruleset {
                                        rules: vec![pb::Rule {
                                            eval_mode: pb::RuleEvalMode::Seminaive.into(),
                                            kind: Some(pb::rule::Kind::Rule(pb::RuleBody {
                                                query: vec![],
                                                head: vec![pb::Action {
                                                    kind: Some(pb::action::Kind::Term(union)),
                                                    ..Default::default()
                                                }],
                                            })),
                                            ..Default::default()
                                        }],
                                    })),
                                }],
                                ..Default::default()
                            })),
                            ..Default::default()
                        }],
                        ..Default::default()
                    })),
                    ..Default::default()
                }),
                8 => program.declarations.push(pb::Declaration {
                    kind: Some(pb::declaration::Kind::UserDefinedPrimitive(
                        pb::UserDefinedPrimitive {
                            name: "deferred".into(),
                            inputs: vec![],
                            output: sort_id,
                            body: Some(union),
                        },
                    )),
                    ..Default::default()
                }),
                _ => program.commands.push(pb::Command {
                    kind: Some(pb::command::Kind::Loop(pb::Loop {
                        body: vec![action],
                        max_iterations: Some(u64::from(case == 9)),
                        until: vec![],
                    })),
                    ..Default::default()
                }),
            }
            let response = run_host_default(&mut engine, id, program);
            let graph = &engine.graphs[&id].graph;
            if matches!(case, 0 | 9 | 10) {
                if case == 0 {
                    assert_eq!(
                        response.error.unwrap().code,
                        i32::from(pb::ErrorCode::RuntimeFailure)
                    );
                    assert!(response.output.outputs.is_empty());
                } else {
                    assert_eq!(response.error, None);
                    assert!(
                        matches!(&response.output.outputs[0].kind, Some(pb::command_output::Kind::Run(outcome)) if outcome.updated == (case == 9))
                    );
                }
                assert_eq!(graph.get_size(&native_name("call", "Atom")), 1);
                assert_eq!(
                    graph.materialized_eq_classes().len(),
                    if case == 10 { 1 } else { 2 },
                    "case {case}: Fail retains its successful prefix; Repeat0 does not mint a Union identity"
                );
                continue;
            }
            assert_eq!(
                response.error.unwrap().code,
                i32::from(pb::ErrorCode::InvalidProgram),
                "case {case}"
            );
            assert!(response.output.outputs.is_empty());
            assert_eq!(graph.num_tuples(), 0, "case {case}");
            assert!(graph.materialized_eq_classes().is_empty(), "case {case}");
        }
    }

    #[test]
    fn byte_union_set_preserves_address_then_value_failure_prefix() {
        for (key, value, classes) in [
            ("(N (vec-get (vec-of 1) 2))", "(Seen)", 1),
            ("(Seen)", "(N (vec-get (vec-of 1) 2))", 2),
            ("(Seen)", "(N 10)", 3),
        ] {
            let source = format!(
                "(sort V (Vec i64)) (datatype A (N i64) (Seen)) (function store (A) A :merge old) (N 9) (set (store {key}) {value})"
            );
            let mut native = crate::new_experimental_egraph();
            let baseline = native.parse_and_run_program(None, &source);
            let (mut engine, id) = host_default_engine();
            let mut program = inventory_fixture(&source);
            let Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Set(set)),
                ..
            })) = &mut program.commands.last_mut().unwrap().kind
            else {
                panic!("fixture")
            };
            let original = set.value.unwrap();
            set.value = Some(program.nodes.len() as u32);
            program.nodes.push(pb::Node {
                sort_id: program.nodes[original as usize].sort_id,
                kind: Some(pb::node::Kind::Union(pb::Union {
                    members: vec![original],
                })),
                ..Default::default()
            });
            let response = run_host_default(&mut engine, id, program);
            assert_eq!(response.error.is_some(), baseline.is_err());
            if let Some(error) = response.error {
                assert_eq!(error.code, i32::from(pb::ErrorCode::RuntimeFailure));
            }
            assert!(response.output.outputs.is_empty());
            let graph = &engine.graphs[&id].graph;
            assert_eq!(graph.materialized_eq_classes().len(), classes);
            assert_eq!(
                graph.materialized_eq_classes().len(),
                native.materialized_eq_classes().len()
            );
            for table in ["N", "Seen", "store"] {
                assert_eq!(
                    graph.get_size(&native_name("call", table)),
                    native.get_size(table)
                );
            }
        }
    }

    #[test]
    fn byte_union_reuse_canonicalizes_before_post_run_lookup() {
        let (mut engine, id) = host_default_engine();
        let mut program = inventory_fixture(
            "(datatype A (Atom i64)) (function keep () A :merge old) (function read (A) i64 :no-merge) (ruleset r) (rule ((= x (keep))) ((union x (Atom 0))) :ruleset r) (Atom 0) (set (read (Atom 0)) 7) (run r 1)",
        );
        let run = program.commands.pop().unwrap();
        let sort_id = program
            .sorts
            .iter()
            .position(|sort| matches!(&sort.kind, Some(pb::sort::Kind::Eq(name)) if name == "A"))
            .unwrap() as u32;
        let integer = program.sorts.iter().position(|sort| matches!(&sort.kind, Some(pb::sort::Kind::Application(family)) if family.name == "i64")).unwrap() as u32;
        let union = program.nodes.len() as u32;
        program.nodes.push(pb::Node {
            sort_id,
            kind: Some(pb::node::Kind::Union(pb::Union::default())),
            ..Default::default()
        });
        program.nodes.push(pb::Node {
            sort_id: integer,
            kind: Some(pb::node::Kind::Call(pb::Call {
                func: "read".into(),
                args: vec![union],
            })),
            ..Default::default()
        });
        program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Set(pb::Set {
                    target: Some(pb::Call {
                        func: "keep".into(),
                        args: vec![],
                    }),
                    value: Some(union),
                })),
                ..Default::default()
            })),
            ..Default::default()
        });
        program.commands.push(run);
        program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Term(union + 1)),
                ..Default::default()
            })),
            ..Default::default()
        });
        let response = run_host_default(&mut engine, id, program);
        assert_eq!(response.error, None);
        assert_eq!(response.output.outputs.len(), 1);
        let graph = &engine.graphs[&id].graph;
        assert_eq!(graph.materialized_eq_classes().len(), 1);
        assert_eq!(graph.num_tuples(), 3);
        assert_eq!(graph.get_size(&native_name("call", "read")), 1);
    }

    #[test]
    fn additive_content_retries_share_global_cursors_and_first_diagnostics() {
        for mode in [
            pb::ExecutionMode::Normal,
            pb::ExecutionMode::TermEncoding,
            pb::ExecutionMode::Proofs,
            pb::ExecutionMode::ProofTesting,
        ] {
            let (mut engine, id) = host_default_engine();
            let session = engine.graphs.get_mut(&id).unwrap();
            session.graph = match mode {
                pb::ExecutionMode::Normal => std::mem::take(&mut session.graph),
                pb::ExecutionMode::TermEncoding => {
                    std::mem::take(&mut session.graph).with_term_encoding_enabled()
                }
                pb::ExecutionMode::Proofs => {
                    std::mem::take(&mut session.graph).with_proofs_enabled()
                }
                pb::ExecutionMode::ProofTesting => std::mem::take(&mut session.graph)
                    .with_proofs_enabled()
                    .with_proof_testing(),
            };
            session.mode = mode;
            let mut input = inventory_fixture(
                "(datatype E (N i64) (Goal i64)) (ruleset a) (rule ((N x)) ((Goal x)) :ruleset a :name \"first\") (N 1) (run a 1) (check (Goal 1))",
            );
            let (first, matches) = run_diagnostic_matches(&mut engine, id, input.clone());
            assert_eq!(first.error, None);
            assert!(matches > 0, "{mode:?} executes the initial rule");
            graph::rules_mut(&mut input)
                .into_iter()
                .next()
                .unwrap()
                .name = Some("later".into());
            graph::rules_mut(&mut input).into_iter().next().unwrap().doc =
                "metadata does not restart a rule".into();
            for node in &mut input.nodes {
                if let Some(pb::node::Kind::Var(name)) = &mut node.kind {
                    *name = "_0".into();
                }
            }
            let rule = graph::rules(&input).next().unwrap().clone();
            input.rulesets = vec![pb::RulesetBinding {
                name: "b".into(),
                value: Some(pb::Ruleset {
                    rules: vec![rule; 2],
                }),
            }];
            input.commands = vec![pb::Command {
                kind: Some(pb::command::Kind::Run(pb::Run {
                    rulesets: (vec!["a".into(), "missing".into(), "b".into(), "a".into()])
                        .into_iter()
                        .map(|name| pb::RulesetSelection {
                            kind: Some(pb::ruleset_selection::Kind::Name(name)),
                        })
                        .collect(),
                    ..Default::default()
                })),
                ..Default::default()
            }];
            let (retry, matches) = run_diagnostic_matches(&mut engine, id, input.clone());
            assert_eq!(retry.error, None);
            assert_eq!(matches, 0);
            let registry = &engine.graphs[&id].registry;
            assert_eq!(registry.rules.len(), 1);
            assert_eq!(registry.groups["a"], registry.groups["b"]);
            let stats = run_host_default(
                &mut engine,
                id,
                pb::Program {
                    commands: vec![pb::Command {
                        kind: Some(pb::command::Kind::Stats(pb::Unit {})),
                        ..Default::default()
                    }],
                    ..Default::default()
                },
            );
            assert_eq!(stats.error, None);
            let representative = graph::rules(
                &engine.graphs[&id].registry.rules[0]
                    .candidate
                    .record
                    .program,
            )
            .next()
            .unwrap();
            assert_eq!(representative.name.as_deref(), Some("first"));
            assert!(representative.doc.is_empty());

            graph::rules_mut(&mut input)
                .into_iter()
                .next()
                .unwrap()
                .no_decomp = true;
            input.commands.truncate(1);
            assert_eq!(run_host_default(&mut engine, id, input).error, None);
            assert_eq!(engine.graphs[&id].registry.rules.len(), 2);
            for groups in [vec![], vec!["unregistered".into()]] {
                let empty = run_host_default(
                    &mut engine,
                    id,
                    pb::Program {
                        commands: vec![pb::Command {
                            kind: Some(pb::command::Kind::Run(pb::Run {
                                rulesets: groups
                                    .into_iter()
                                    .map(|name| pb::RulesetSelection {
                                        kind: Some(pb::ruleset_selection::Kind::Name(name)),
                                    })
                                    .collect(),
                                ..Default::default()
                            })),
                            ..Default::default()
                        }],
                        ..Default::default()
                    },
                );
                assert_eq!(empty.error, None);
                assert!(
                    matches!(&empty.output.outputs[0].kind, Some(pb::command_output::Kind::Run(result)) if !result.updated && result.can_stop)
                );
            }
        }
    }

    #[test]
    fn additive_freeze_reconstructs_membership_and_shared_content_once() {
        let (mut engine, id) = host_default_engine();
        let mut input = inventory_fixture(
            "(datatype E (N i64) (Goal i64)) (ruleset a) (rule ((N x)) ((Goal x)) :ruleset a) (N 1)",
        );
        let rule = graph::rules(&input).next().unwrap().clone();
        input.rulesets.push(pb::RulesetBinding {
            name: "b".into(),
            value: Some(pb::Ruleset {
                rules: vec![rule.clone()],
            }),
        });
        input.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Freeze(pb::Freeze {})),
            ..Default::default()
        });
        let response = run_host_default(&mut engine, id, input);
        assert_eq!(response.error, None);
        let Some(pb::command_output::Kind::Snapshot(snapshot)) =
            &response.output.outputs.last().unwrap().kind
        else {
            panic!("snapshot")
        };
        let program = snapshot.program.as_ref().unwrap();
        assert_eq!(graph::rules(program).count(), 2);
        assert_eq!(
            program
                .rulesets
                .iter()
                .map(|binding| binding.name.as_str())
                .collect::<Vec<_>>(),
            ["a", "b"]
        );
        assert_eq!(program.rulesets[0].value, program.rulesets[1].value);
        let (mut restored, fresh) = host_default_engine();
        assert_eq!(
            run_host_default(&mut restored, fresh, program.clone()).error,
            None
        );
        let registry = &restored.graphs[&fresh].registry;
        assert_eq!(registry.rules.len(), 1);
        assert_eq!(registry.groups["a"], registry.groups["b"]);
    }

    #[test]
    fn additive_source_static_wrappers_preserve_content_across_packets() {
        let mut renderer = source::Renderer::default();
        let mut native = crate::new_experimental_egraph();
        let mut input = inventory_fixture(
            "(datatype E (N i64) (Goal i64)) (ruleset a) (rule ((N x)) ((Goal x)) :ruleset a) (N 1) (run a 1) (check (Goal 1))",
        );
        let check = input.commands.pop().unwrap();
        let rule = graph::rules(&input).next().unwrap().clone();
        input.commands = vec![pb::Command {
            kind: Some(pb::command::Kind::Loop(pb::Loop {
                max_iterations: Some(1),
                body: input.commands,
                ..Default::default()
            })),
            ..Default::default()
        }];
        input.commands.push(check);
        let initial = renderer.render(&input).unwrap();
        native.parse_and_run_program(None, &initial).unwrap();
        input.rulesets = vec![pb::RulesetBinding {
            name: "a".into(),
            value: Some(pb::Ruleset {
                rules: vec![rule.clone()],
            }),
        }];
        input.commands = vec![pb::Command {
            kind: Some(pb::command::Kind::Loop(pb::Loop {
                max_iterations: Some(1),
                body: vec![pb::Command {
                    kind: Some(pb::command::Kind::Run(pb::Run {
                        rulesets: (vec!["a".into()])
                            .into_iter()
                            .map(|name| pb::RulesetSelection {
                                kind: Some(pb::ruleset_selection::Kind::Name(name)),
                            })
                            .collect(),
                        ..Default::default()
                    })),
                    ..Default::default()
                }],
                ..Default::default()
            })),
            ..Default::default()
        }];
        let retry = renderer.render(&input).unwrap();
        assert!(!retry.contains("(rule "), "{retry}");
        native.parse_and_run_program(None, &retry).unwrap();
    }

    #[test]
    fn setup_failure_preserves_bindings_and_retains_native_installation_prefix() {
        // A native fault after registering one new rule and the next holder
        // isolates setup publication from resumable private installation state.
        let (mut engine, id) = host_default_engine();
        let old = pb::Rule {
            name: Some("old".into()),
            eval_mode: pb::RuleEvalMode::Seminaive.into(),
            kind: Some(pb::rule::Kind::Rule(pb::RuleBody::default())),
            ..Default::default()
        };
        let initial = pb::Program {
            rulesets: ["", "b"]
                .into_iter()
                .map(|name| pb::RulesetBinding {
                    name: name.into(),
                    value: Some(pb::Ruleset {
                        rules: vec![old.clone()],
                    }),
                })
                .collect(),
            ..Default::default()
        };
        assert_eq!(run_host_default(&mut engine, id, initial).error, None);
        let mut first = old.clone();
        first.name = Some("first".into());
        first.no_decomp = true;
        let mut second = old.clone();
        second.name = Some("second".into());
        second.eval_mode = pb::RuleEvalMode::Naive.into();
        let mut input = pb::Program {
            rulesets: vec![
                pb::RulesetBinding {
                    name: String::new(),
                    value: Some(pb::Ruleset {
                        rules: vec![old, first],
                    }),
                },
                pb::RulesetBinding {
                    name: "empty".into(),
                    value: Some(pb::Ruleset::default()),
                },
                pb::RulesetBinding {
                    name: "b".into(),
                    value: Some(pb::Ruleset {
                        rules: vec![second],
                    }),
                },
            ],
            ..Default::default()
        };
        let session = engine.graphs.get_mut(&id).unwrap();
        let mut prepared = session.prepare(&mut input.clone()).unwrap();
        prepared.context.candidates[2].commands.insert(
            1,
            Command::Action(Action::Panic(ast::Span::Panic, "registration fault".into())),
        );
        let mut response = pb::RunProgramOutput::default();
        assert!(session.install(prepared, &mut response).is_err());
        assert_eq!(session.registry.groups[""], [0]);
        assert_eq!(session.registry.groups["b"], [0]);
        assert!(!session.registry.groups.contains_key("empty"));
        assert_eq!(session.registry.rules.len(), 3);
        let first_name = session.registry.rules[1].candidate.name.clone();
        let second_holder = format!("{}_holder", session.registry.rules[2].candidate.name);
        session
            .graph
            .validate_program(vec![Command::RunSchedule(ast::Schedule::Run(
                ast::Span::Panic,
                ast::RunConfig {
                    ruleset: second_holder,
                    until: None,
                },
            ))])
            .unwrap();

        let run = pb::Command {
            kind: Some(pb::command::Kind::Run(pb::Run {
                rulesets: ["", "b"]
                    .into_iter()
                    .map(|name| pb::RulesetSelection {
                        kind: Some(pb::ruleset_selection::Kind::Name(name.into())),
                    })
                    .collect(),
                ..Default::default()
            })),
            ..Default::default()
        };
        let (before_retry, matches) = run_diagnostic_matches(
            &mut engine,
            id,
            pb::Program {
                commands: vec![run.clone()],
                ..Default::default()
            },
        );
        assert_eq!(before_retry.error, None);
        assert_eq!(
            matches, 1,
            "failed setup still selects only the old shared rule"
        );
        // Removing the injected fault lets resupply resume after the already
        // installed holder, while the completed first rule remains interned.
        engine.graphs.get_mut(&id).unwrap().registry.rules[2]
            .candidate
            .commands
            .remove(1);
        input.commands.push(run);
        let (retry, matches) = run_diagnostic_matches(&mut engine, id, input);
        assert_eq!(retry.error, None);
        assert_eq!(
            matches, 2,
            "retry selects the two new rules without replaying old content"
        );
        let registry = &engine.graphs[&id].registry;
        assert_eq!(registry.groups[""], [0, 1]);
        assert_eq!(registry.groups["b"], [2]);
        assert!(registry.groups["empty"].is_empty());
        assert_eq!(registry.rules.len(), 3);
        assert_eq!(registry.rules[1].candidate.name, first_name);
    }

    #[test]
    fn additive_rule_provenance_is_shared_and_imported_once_per_submission() {
        let (mut engine, id) = host_default_engine();
        let first = pb::Rule {
            name: Some("first".into()),
            eval_mode: pb::RuleEvalMode::Seminaive.into(),
            span: Some(pb::Span {
                file: 0,
                start: 0,
                end: 1,
            }),
            kind: Some(pb::rule::Kind::Rule(pb::RuleBody {
                query: vec![],
                head: vec![pb::Action {
                    kind: Some(pb::action::Kind::Term(0)),
                    ..Default::default()
                }],
            })),
            ..Default::default()
        };
        let mut second = first.clone();
        second.name = Some("second".into());
        second.no_decomp = true;
        let input = pb::Program {
            rulesets: vec![pb::RulesetBinding {
                name: "g".into(),
                value: Some(pb::Ruleset {
                    rules: vec![first, second],
                }),
            }],

            sorts: vec![pb::Sort {
                kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                    name: "i64".into(),
                    args: vec![],
                })),
                ..Default::default()
            }],
            nodes: vec![pb::Node {
                kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::I64(7)),
                })),
                ..Default::default()
            }],
            files: vec![pb::SourceFile {
                name: "shared.egg".into(),
                contents: Some("x".repeat(100_000)),
            }],
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Run(pb::Run {
                    rulesets: (vec!["g".into()])
                        .into_iter()
                        .map(|name| pb::RulesetSelection {
                            kind: Some(pb::ruleset_selection::Kind::Name(name)),
                        })
                        .collect(),
                    ..Default::default()
                })),
                ..Default::default()
            }],
            ..Default::default()
        };
        let response = run_host_default(&mut engine, id, input);
        assert_eq!(response.error, None);
        let rules = &engine.graphs[&id].registry.rules;
        assert!(Arc::ptr_eq(
            &rules[0].candidate.record.files,
            &rules[1].candidate.record.files
        ));
        assert!(
            rules
                .iter()
                .all(|rule| rule.candidate.record.program.files.is_empty())
        );
        let frozen = run_host_default(
            &mut engine,
            id,
            pb::Program {
                commands: vec![pb::Command {
                    kind: Some(pb::command::Kind::Freeze(pb::Freeze {})),
                    ..Default::default()
                }],
                ..Default::default()
            },
        );
        let Some(pb::command_output::Kind::Snapshot(snapshot)) = &frozen.output.outputs[0].kind
        else {
            panic!("snapshot")
        };
        let program = snapshot.program.as_ref().unwrap();
        assert_eq!(graph::rules(program).count(), 2);
        assert_eq!(
            program.files.len(),
            1,
            "all rules reuse their owned submission provenance"
        );
        for rule in graph::rules(program) {
            let file = &program.files[rule.span.unwrap().file as usize];
            assert_eq!(file.name, "shared.egg");
            assert_eq!(file.contents.as_ref().unwrap().len(), 100_000);
        }
    }

    #[test]
    fn setup_bindings_support_repeated_source_runs() {
        for max_iterations in [Some(2), None] {
            let mut input = inventory_fixture(
                "(datatype E (N i64) (Goal i64)) (ruleset g) (rule ((N x)) ((Goal x)) :ruleset g) (N 1) (run g 1) (check (Goal 1))",
            );
            let check = input.commands.pop().unwrap();
            let run = input.commands.pop().unwrap();
            input.commands.push(pb::Command {
                kind: Some(pb::command::Kind::Loop(pb::Loop {
                    max_iterations,
                    body: vec![run],
                    ..Default::default()
                })),
                ..Default::default()
            });
            input.commands.push(check);
            let text = source::Renderer::default().render(&input).unwrap();
            let mut native = crate::new_experimental_egraph();
            native.parse_and_run_program(None, &text).unwrap();
        }
    }

    #[test]
    fn additive_source_preserves_action_dag_sites_after_registration_projection() {
        let (mut input, _) = closed_value_dag(
            "(constructor Use (A A) A) (Use (Leaf (vec-empty) (bigrat (from-string \"7\") (from-string \"2\"))) (Leaf (vec-empty) (bigrat (from-string \"7\") (from-string \"2\"))))",
        );
        input.rulesets.insert(
            0,
            pb::RulesetBinding {
                name: "empty".into(),
                value: Some(pb::Ruleset { rules: vec![] }),
            },
        );
        let text = source::Renderer::default().render(&input).unwrap();
        assert!(text.contains("(action-scope"), "{text}");
        let mut native = crate::new_experimental_egraph();
        native.parse_and_run_program(None, &text).unwrap();
        assert_eq!(native.materialized_eq_classes().len(), 18);
    }

    #[test]
    fn additive_core_source_checks_exact_current_and_retained_selector_names() {
        let selector = native_name("source_ruleset", "__protobuf_source_selection_1_0");
        let conflict = pb::Program {
            sorts: vec![pb::Sort {
                kind: Some(pb::sort::Kind::Eq(selector.clone())),
                ..Default::default()
            }],
            declarations: vec![pb::Declaration {
                kind: Some(pb::declaration::Kind::EqSort(pb::EqSort { name: selector })),
                ..Default::default()
            }],
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Run(pb::Run {
                    rulesets: (vec!["unknown".into()])
                        .into_iter()
                        .map(|name| pb::RulesetSelection {
                            kind: Some(pb::ruleset_selection::Kind::Name(name)),
                        })
                        .collect(),
                    ..Default::default()
                })),
                ..Default::default()
            }],
            ..Default::default()
        };
        assert!(
            source::Renderer::core()
                .render(&conflict)
                .unwrap_err()
                .to_string()
                .contains("private source ruleset")
        );
        let mut renderer = source::Renderer::core();
        let run = pb::Program {
            commands: conflict.commands.clone(),
            ..Default::default()
        };
        renderer.render(&run).unwrap();
        assert!(
            renderer
                .render(&conflict)
                .unwrap_err()
                .to_string()
                .contains("private source ruleset")
        );
        renderer.render(&run).unwrap();
    }
    #[test]
    fn ruleset_replacements_literals_empty_names_and_omission_keep_rule_cursors() {
        let (mut engine, id) = host_default_engine();
        let definitions = "(datatype E (N i64) (Goal i64) (Other i64))";
        let first = inventory_fixture(&format!(
            "{definitions} (ruleset g) (rule ((N x)) ((Goal x)) :ruleset g) (N 1) (run g 1) (check (Goal 1))"
        ));
        let first_rule = first.rulesets[0].value.as_ref().unwrap().rules[0].clone();
        let (response, matches) = run_diagnostic_matches(&mut engine, id, first.clone());
        assert_eq!(response.error, None);
        assert_eq!(matches, 1);
        let second = inventory_fixture(&format!(
            "{definitions} (ruleset g) (rule ((N x)) ((Other x)) :ruleset g) (N 2) (run g 1) (check (Other 2)) (fail (check (Goal 2)))"
        ));
        assert_eq!(run_host_default(&mut engine, id, second).error, None);
        assert_eq!(engine.graphs[&id].registry.groups["g"], [1]);
        // Omission retains g, and the empty name is a regular independent binding.
        let mut omitted = first.clone();
        omitted.rulesets = vec![pb::RulesetBinding {
            name: String::new(),
            value: Some(pb::Ruleset {
                rules: vec![first_rule.clone()],
            }),
        }];
        omitted.commands = vec![pb::Command {
            kind: Some(pb::command::Kind::Run(pb::Run {
                rulesets: vec![
                    pb::RulesetSelection {
                        kind: Some(pb::ruleset_selection::Kind::Name("g".into())),
                    },
                    pb::RulesetSelection {
                        kind: Some(pb::ruleset_selection::Kind::Ruleset(pb::Ruleset {
                            rules: vec![first_rule.clone(), first_rule],
                        })),
                    },
                    pb::RulesetSelection {
                        kind: Some(pb::ruleset_selection::Kind::Name(String::new())),
                    },
                    pb::RulesetSelection {
                        kind: Some(pb::ruleset_selection::Kind::Name("missing".into())),
                    },
                ],
                ..Default::default()
            })),
            ..Default::default()
        }];
        let (response, matches) = run_diagnostic_matches(&mut engine, id, omitted);
        assert_eq!(response.error, None);
        assert_eq!(
            matches, 1,
            "readded content catches up once without replaying old matches"
        );
        assert_eq!(engine.graphs[&id].registry.rules.len(), 2);
        assert_eq!(engine.graphs[&id].registry.groups["g"], [1]);
        let mut empty = pb::Program {
            rulesets: vec![pb::RulesetBinding {
                name: "g".into(),
                value: Some(pb::Ruleset::default()),
            }],
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Run(pb::Run {
                    rulesets: vec![pb::RulesetSelection {
                        kind: Some(pb::ruleset_selection::Kind::Name("g".into())),
                    }],
                    ..Default::default()
                })),
                ..Default::default()
            }],
            ..Default::default()
        };
        empty.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Freeze(pb::Freeze {})),
            ..Default::default()
        });
        let child = engine
            .clone_request(pb::CloneEGraphRequest { egraph_id: id })
            .unwrap()
            .egraph_id;
        let (response, matches) = run_diagnostic_matches(&mut engine, child, empty);
        assert_eq!(response.error, None);
        assert_eq!(matches, 0);
        let snapshot = response
            .output
            .outputs
            .iter()
            .find_map(|output| {
                if let Some(pb::command_output::Kind::Snapshot(snapshot)) = &output.kind {
                    snapshot.program.as_ref()
                } else {
                    None
                }
            })
            .unwrap();
        assert!(
            snapshot
                .rulesets
                .iter()
                .find(|binding| binding.name == "g")
                .unwrap()
                .value
                .as_ref()
                .unwrap()
                .rules
                .is_empty()
        );
        assert_eq!(
            snapshot.rulesets.len(),
            2,
            "Freeze exports current names, including empty bindings"
        );
        assert!(engine.graphs[&child].registry.groups["g"].is_empty());
        assert_eq!(engine.graphs[&id].registry.groups["g"], [1]);
        let (response, matches) = run_diagnostic_matches(&mut engine, child, first);
        assert_eq!(response.error, None);
        assert_eq!(
            matches, 0,
            "replacement and clone preserve the content cursor"
        );
    }

    #[test]
    fn invalid_ruleset_setup_and_unentered_literal_reject_before_effects() {
        let (mut engine, id) = host_default_engine();
        for invalid in 0..3 {
            let mut program = pb::Program::default();
            match invalid {
                0 => program.rulesets.push(pb::RulesetBinding {
                    name: "g".into(),
                    value: None,
                }),
                1 => {
                    program.rulesets = vec![
                        pb::RulesetBinding {
                            name: "g".into(),
                            value: Some(pb::Ruleset::default())
                        };
                        2
                    ]
                }
                2 => program.commands.push(pb::Command {
                    kind: Some(pb::command::Kind::Loop(pb::Loop {
                        max_iterations: Some(0),
                        body: vec![pb::Command {
                            kind: Some(pb::command::Kind::Run(pb::Run {
                                rulesets: vec![pb::RulesetSelection::default()],
                                ..Default::default()
                            })),
                            ..Default::default()
                        }],
                        ..Default::default()
                    })),
                    ..Default::default()
                }),
                _ => unreachable!(),
            }
            program.commands.insert(
                0,
                pb::Command {
                    kind: Some(pb::command::Kind::Action(pb::Action {
                        kind: Some(pb::action::Kind::Panic("must not execute".into())),
                        ..Default::default()
                    })),
                    ..Default::default()
                },
            );
            let response = run_host_default(&mut engine, id, program);
            assert_eq!(
                response.error.unwrap().code,
                i32::from(pb::ErrorCode::InvalidProgram)
            );
            assert_eq!(engine.graphs[&id].request, 0);
        }
    }
}
