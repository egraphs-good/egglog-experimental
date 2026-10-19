//! In-process compatibility adapter for encoded protobuf requests.
//!
//! This executable slice supports concrete equality/scalar/Vec/Pair/Map/Maybe sorts,
//! constructors, functions, Unit-annotated relation predicates, ordered actions,
//! shared immutable rulesets, checks, requested proofs, table sizes and logical
//! table rows in all four modes. Extraction remains ordinary-mode only.
//! Unsupported forms fail explicitly before installation.
//! Explicit native extensions may additionally supply inert host-value codecs.
//! In particular, profiling must currently be requested: the
//! native engine cannot yet disable its optional timing collection.
//!
//! Decoded protobuf messages supply all authored semantics. Native ASTs exist
//! during validation and execution; the native engine retains its compiled
//! state, with derived indexes for names and diagnostics. No source or previously
//! supplied AST is accepted by this boundary.

use crate::builtin::{PortableEGraph, PortablePrimitive, PortableTypeInfo};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt;
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
use num::{BigInt, Integer, One, Zero};
use prost::Message;

pub mod cost_model;
mod freeze;
mod proof;
mod report;
pub mod source;

// Native input paths paired with the actual wire command and its relative
// list path. This is request-local correspondence, not another control tree.
type ScheduleSites<'a> = HashMap<Vec<usize>, (&'a pb::Command, Vec<u32>)>;
type ExecutionFailureSite = (pb::CommandLocation, Option<pb::Span>);

#[derive(Default)]
struct ScheduleMeasurements {
    requested: HashMap<Vec<u32>, LeafSummary>,
    maintenance: HashMap<Option<Vec<u32>>, LeafSummary>,
    selected: Vec<pb::RulesetRef>,
    failure: Option<ExecutionFailureSite>,
    changed: bool,
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
                Some(
                    pb::command::Kind::Repeat(pb::Repeat { body, .. })
                    | pb::command::Kind::Saturate(pb::Saturate { body, .. }),
                ) => {
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
            Some(pb::command::Kind::Repeat(body)) => pending.extend(body.body.iter().rev()),
            Some(pb::command::Kind::Saturate(body)) => pending.extend(body.body.iter().rev()),
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
    extension: Option<Arc<dyn NativeExtension>>,
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

    /// Return None for other native value types; reject malformed reconstruction
    /// of a recognized type. Neither branch may execute or materialize payloads.
    fn encode_custom_value(
        &self,
        native_sort: &ArcSort,
        terms: &TermDag,
        term: TermId,
    ) -> Result<Option<pb::CustomValue>, String>;

    /// Inspect a recognized native value without invoking arbitrary native
    /// reconstruction. Used by owned callback observations and Freeze.
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
    // Authored definitions and presentation/default closures, never execution ASTs.
    definitions: pb::Program,
    names: NativeNames,
    request: u64,
    // Direct clone source and its mutation/namespace stamp, not an ancestry log.
    clone_parent: Option<(u64, u64)>,
    // Derived native handles, aligned with the canonical occurrence arenas.
    rulesets: Vec<String>,
    rules: Vec<String>,
    // Successfully registered closed container aliases, including encoded modes
    // where physical TypeInfo is not the authoring type environment.
    sorts: HashSet<String>,
    cost_models: HashMap<String, Arc<dyn cost_model::NativeCostModel>>,
}

struct Installation {
    command: Option<Command>,
    site: pb::maintenance_site::Target,
    span: Option<pb::Span>,
    declaration: Option<usize>,
    ruleset: Option<usize>,
}

struct Prepared {
    definitions: pb::Program,
    request: u64,
    installations: Vec<Installation>,
    materialized: Vec<Command>,
    // Canonical declaration indices whose native installation is still pending.
    pending_declarations: HashSet<usize>,
    rulesets: Vec<String>,
    rules: Vec<String>,
    published: HashSet<usize>,
    // Request-local correspondence, captured only after complete preparation.
    submitted_names: HashMap<String, usize>,
    context: RequestOccurrences,
}

#[derive(Default)]
struct NativeSpans(RefCell<Vec<Option<Arc<SrcFile>>>>);

#[derive(Default)]
struct RequestOccurrences {
    rulesets: Vec<String>,
    names: HashMap<String, String>,
    origins: HashMap<String, (pb::RuleAttribution, pb::NativeRuleDirection)>,
    response_rules: HashMap<pb::RuleAttribution, u32>,
    files: Vec<pb::SourceFile>,
    // Indexed by the execution arena, not the response's merged source files.
    native_spans: NativeSpans,
    include_run_reports: bool,
    scoped_actions: HashSet<Vec<u32>>,
    constructor_dags: HashMap<Vec<u32>, HashSet<u32>>,
    extraction_dags: HashMap<u32, HashSet<u32>>,
    union_values: HashMap<u32, Value>,
}

struct LeafSummary {
    invocations: u64,
    nanos: [Option<u64>; 3],
    rules: HashMap<String, (u64, Option<u64>)>,
}

impl Default for LeafSummary {
    fn default() -> Self {
        Self {
            invocations: 0,
            nanos: [Some(0); 3],
            rules: HashMap::new(),
        }
    }
}

impl LeafSummary {
    fn finish(
        &mut self,
        result: Result<&egglog_reports::RunReport, &egglog::Error>,
        authored_rules: bool,
    ) {
        let Ok(report) = result else {
            self.nanos = [None; 3];
            // An earlier successful iteration is not a complete site total.
            // Admitted loop bodies cannot catch this failure and resume here.
            self.rules.clear();
            return;
        };
        for (total, measured) in self.nanos.iter_mut().zip([
            &report.search_and_apply_time_per_ruleset,
            &report.merge_time_per_ruleset,
            &report.rebuild_time_per_ruleset,
        ]) {
            *total = total.and_then(|old| {
                let elapsed = measured.values().map(|d| d.as_nanos()).sum::<u128>();
                old.checked_add(u64::try_from(elapsed).ok()?)
            });
        }
        if authored_rules {
            for (name, matches) in &report.num_matches_per_rule {
                let (count, nanos) = self.rules.entry(name.to_string()).or_insert((0, Some(0)));
                *count += *matches as u64;
                *nanos = nanos.and_then(|old| {
                    old.checked_add(
                        report
                            .search_and_apply_time_per_rule
                            .get(name)?
                            .as_nanos()
                            .try_into()
                            .ok()?,
                    )
                });
            }
        }
    }
}

fn execution_error(
    error: egglog::Error,
    names: &NativeNames,
    files: &[pb::SourceFile],
    span: Option<pb::Span>,
    location: Option<pb::CommandLocation>,
    panic: bool,
) -> pb::Error {
    // Native Fail reports its wrapper's span, whereas a helper may retain an
    // inner authored origin. Only map sources already owned by this response;
    // generated helper text is not a fabricated user source location.
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
            let file = files.iter().position(|file| {
                origin.file.name.as_deref() == Some(file.name.as_str())
                    && file.contents.as_ref() == Some(&origin.file.contents)
            })?;
            Some(pb::Span {
                file: u32::try_from(file).ok()?,
                start: u32::try_from(origin.i).ok()?,
                end: u32::try_from(origin.j).ok()?,
            })
        })
        .or(span);
    let code = match &error {
        egglog::Error::CheckError(..) => pb::ErrorCode::CheckFailed,
        egglog::Error::ExtractError(..) => pb::ErrorCode::ExtractionFailed,
        egglog::Error::Panic { .. } => pb::ErrorCode::Panic,
        egglog::Error::NoSuchRuleset(..)
        | egglog::Error::TypeError(egglog::TypeError::UnboundFunction(..)) => {
            pb::ErrorCode::UnknownName
        }
        egglog::Error::ProofError { .. } => pb::ErrorCode::ProofFailed,
        _ if panic => pb::ErrorCode::Panic,
        _ => pb::ErrorCode::EvaluationFailed,
    };
    let proof_failure = if let egglog::Error::ProofError { error, .. } = &error {
        use egglog::proof::ProveExistsError as E;
        let (reason, constructor) = match error {
            E::RequiresConstructor => (pb::ProofFailureReason::RequiresConstructor, None),
            E::PrimitivesUnsupported => (pb::ProofFailureReason::PrimitivesUnsupported, None),
            E::QueryDidNotMatch { constructor } => (
                pb::ProofFailureReason::QueryDidNotMatch,
                Some(
                    names
                        .callables
                        .get(constructor)
                        .unwrap_or(constructor)
                        .clone(),
                ),
            ),
            E::ProofsNotEnabled => (pb::ProofFailureReason::ProofsNotEnabled, None),
        };
        Some(pb::ProofFailure {
            reason: reason.into(),
            constructor,
        })
    } else {
        None
    };
    pb::Error {
        code: code.into(),
        message: error.to_string(),
        span,
        location,
        proof_failure,
        ..Default::default()
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

    /// Decodes a creation request and returns an encoded handle.
    pub fn create(&mut self, bytes: &[u8]) -> Result<Vec<u8>, TransportError> {
        let request = pb::CreateEGraphRequest::decode(bytes)?;
        let mode =
            pb::ExecutionMode::try_from(request.options.as_ref().map_or(0, |o| o.execution_mode))
                .map_err(|_| TransportError("unknown execution mode".into()))?;
        let seminaive = request
            .options
            .as_ref()
            .and_then(|options| options.seminaive)
            .unwrap_or(true);
        let no_decomp = request.no_decomp;
        if !request.declarations.is_empty() {
            return Err(TransportError(
                "creation declarations are not supported yet".into(),
            ));
        }
        let cost = request
            .options
            .and_then(|options| options.cost_sort)
            .and_then(|index| request.sorts.get(index as usize));
        if !matches!(cost.and_then(|sort| sort.kind.as_ref()), Some(pb::sort::Kind::Family(family)) if family.name == "i64" && family.args.is_empty())
        {
            return Err(TransportError(
                "this adapter currently requires the i64 cost sort".into(),
            ));
        }
        let program = pb::Program {
            ir_version: 1,
            sorts: request.sorts,
            files: request.files,
            ..Default::default()
        };
        let native_spans = NativeSpans::default();
        let mut graph = crate::new_experimental_egraph();
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
        let catalog = graph
            .type_info()
            .portable_builtin_catalog()
            .map_err(TransportError)?
            .definitions;
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
                definitions: catalog,
                names: NativeNames::default(),
                request: 0,
                clone_parent: None,
                rulesets: Vec::new(),
                rules: Vec::new(),
                sorts: HashSet::new(),
                cost_models: HashMap::new(),
            },
        );
        Ok(pb::CreateEGraphResponse {
            egraph_id: self.next_id,
        }
        .encode_to_vec())
    }

    /// Decodes a clone request, retaining native execution state and independent mutations.
    pub fn clone_egraph(&mut self, bytes: &[u8]) -> Result<Vec<u8>, TransportError> {
        let request = pb::CloneEGraphRequest::decode(bytes)?;
        let mut graph = self
            .graphs
            .get(&request.egraph_id)
            .ok_or_else(|| TransportError("unknown egraph_id".into()))?
            .clone();
        graph.clone_parent = Some((request.egraph_id, graph.request));
        self.next_id = self
            .next_id
            .checked_add(1)
            .ok_or_else(|| TransportError("handle space exhausted".into()))?;
        self.graphs.insert(self.next_id, graph);
        Ok(pb::CloneEGraphResponse {
            egraph_id: self.next_id,
        }
        .encode_to_vec())
    }

    /// Decodes a destruction request and invalidates the addressed handle.
    pub fn destroy(&mut self, bytes: &[u8]) -> Result<Vec<u8>, TransportError> {
        let request = pb::DestroyEGraphRequest::decode(bytes)?;
        self.graphs
            .remove(&request.egraph_id)
            .ok_or_else(|| TransportError("unknown egraph_id".into()))?;
        Ok(pb::DestroyEGraphResponse {}.encode_to_vec())
    }

    /// Restore a directly saved scope, retaining active native pop state only.
    /// Invalid/stale pairs leave both handles untouched; saved survives success.
    pub fn return_to(&mut self, bytes: &[u8]) -> Result<Vec<u8>, TransportError> {
        let request = pb::ReturnToEGraphRequest::decode(bytes)?;
        if request.active_id == request.saved_id {
            return Err(TransportError(
                "active and saved handles must differ".into(),
            ));
        }
        let active = self
            .graphs
            .get(&request.active_id)
            .ok_or_else(|| TransportError("unknown active_id".into()))?;
        let saved = self
            .graphs
            .get(&request.saved_id)
            .ok_or_else(|| TransportError("unknown saved_id".into()))?;
        if active.clone_parent != Some((request.saved_id, saved.request))
            || active.request < saved.request
        {
            return Err(TransportError("unrelated or stale scope return".into()));
        }
        // Pair validation is complete. Move graphs; no recompilation, report
        // summation, provider execution, or replacement canonical ownership.
        let mut active = self.graphs.remove(&request.active_id).unwrap();
        let mut saved = self.graphs.remove(&request.saved_id).unwrap();
        active.graph.restore_from(saved.graph);
        saved.graph = active.graph;
        saved.request = active.request;
        self.graphs.insert(request.saved_id, saved);
        Ok(pb::ReturnToEGraphResponse {}.encode_to_vec())
    }

    /// Queries or updates native resources without cloning logical/execution
    /// state. Allocation failures retain the native thread-pool failure boundary.
    pub fn configure_resources(&mut self, bytes: &[u8]) -> Result<Vec<u8>, TransportError> {
        let request = pb::ConfigureEGraphResourcesRequest::decode(bytes)?;
        let operation = request
            .operation
            .ok_or_else(|| TransportError("missing or unknown resource operation".into()))?;
        let session = self
            .graphs
            .get_mut(&request.egraph_id)
            .ok_or_else(|| TransportError("unknown egraph_id".into()))?;
        match operation {
            pb::configure_e_graph_resources_request::Operation::Query(_) => (),
            pb::configure_e_graph_resources_request::Operation::Threads(threads) => {
                if cfg!(target_family = "wasm") && threads > 1 {
                    return Err(TransportError(
                        "native wasm execution supports at most one thread".into(),
                    ));
                }
                let threads = usize::try_from(threads)
                    .map_err(|_| TransportError("thread count exceeds native usize".into()))?;
                let stamp = session
                    .request
                    .checked_add(1)
                    .ok_or_else(|| TransportError("request identity space exhausted".into()))?;
                session.graph.set_num_threads(threads);
                session.request = stamp;
            }
            pb::configure_e_graph_resources_request::Operation::ReportLevel(level) => {
                let level = match pb::ReportLevel::try_from(level) {
                    Ok(pb::ReportLevel::TimeOnly) => egglog_reports::ReportLevel::TimeOnly,
                    Ok(pb::ReportLevel::WithPlan) => egglog_reports::ReportLevel::WithPlan,
                    Ok(pb::ReportLevel::StageInfo) => egglog_reports::ReportLevel::StageInfo,
                    _ => return Err(TransportError("unknown report level".into())),
                };
                let stamp = session
                    .request
                    .checked_add(1)
                    .ok_or_else(|| TransportError("request identity space exhausted".into()))?;
                session.graph.set_report_level(level);
                session.request = stamp;
            }
            pb::configure_e_graph_resources_request::Operation::NoDecomp(enabled) => {
                let stamp = session
                    .request
                    .checked_add(1)
                    .ok_or_else(|| TransportError("request identity space exhausted".into()))?;
                session.graph.no_decomp = enabled;
                session.request = stamp;
            }
        }
        Ok(pb::ConfigureEGraphResourcesResponse {
            threads: u64::try_from(session.graph.num_threads())
                .map_err(|_| TransportError("native thread count exceeds uint64".into()))?,
            no_decomp: session.graph.no_decomp,
        }
        .encode_to_vec())
    }

    /// Executes only the decoded program and returns encoded results and prefix errors.
    pub fn run(&mut self, bytes: &[u8]) -> Result<Vec<u8>, TransportError> {
        let request = pb::RunProgramRequest::decode(bytes)?;
        let session = self
            .graphs
            .get_mut(&request.egraph_id)
            .ok_or_else(|| TransportError("unknown egraph_id".into()))?;
        let mut response = pb::RunProgramResponse {
            ruleset_publication: Some(pb::RulesetPublication::default()),
            profile: request.profile.then(|| pb::ProfileSummary {
                complete: false,
                ..Default::default()
            }),
            ..Default::default()
        };
        let Some(mut program) = request.program else {
            response.error = Some(pb::Error {
                code: pb::ErrorCode::InvalidProgram.into(),
                message: "missing program".into(),
                ..Default::default()
            });
            return Ok(response.encode_to_vec());
        };
        response.files = program.files.clone();
        let prepared = if request.profile {
            session.prepare(&mut program)
        } else {
            Err("profile=false is unsupported until native collection can be disabled".into())
        };
        let prepared = match prepared {
            Ok(prepared) => prepared,
            Err(error) => {
                response.error = Some(*error.0);
                return Ok(response.encode_to_vec());
            }
        };
        let mut context = match session.install(prepared, &mut response) {
            Ok(context) => context,
            Err(error) => {
                response.error = Some(*error);
                return Ok(response.encode_to_vec());
            }
        };
        context.include_run_reports = request.include_run_reports;
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
            );
            if let Err(error) = result {
                let panic = matches!(
                    &command.kind,
                    Some(pb::command::Kind::Action(pb::Action {
                        kind: Some(pb::action::Kind::Panic(_)),
                        ..
                    }))
                );
                let (location, span) = failure_site.unwrap_or_else(|| {
                    (
                        location,
                        match &command.kind {
                            Some(pb::command::Kind::Action(action)) => action.span.or(command.span),
                            _ => command.span,
                        },
                    )
                });
                let origin = match &error {
                    egglog::Error::Panic {
                        rule: Some(rule), ..
                    } => context.origins.get(rule).map(|(origin, _)| origin.clone()),
                    _ => None,
                };
                let mut error = execution_error(
                    error,
                    &session.names,
                    &response.files,
                    span,
                    Some(location),
                    panic,
                );
                if let Some(origin) = origin {
                    let index =
                        *context
                            .response_rules
                            .entry(origin.clone())
                            .or_insert_with(|| {
                                response.rules.push(origin);
                                (response.rules.len() - 1) as u32
                            });
                    error.rule = Some(index);
                }
                response.error = Some(error);
                break;
            }
        }
        response.profile.as_mut().unwrap().complete = response.error.is_none();
        Ok(response.encode_to_vec())
    }
}

impl Session {
    fn install(
        &mut self,
        prepared: Prepared,
        response: &mut pb::RunProgramResponse,
    ) -> Result<RequestOccurrences, Box<pb::Error>> {
        let Prepared {
            definitions,
            request,
            installations,
            mut pending_declarations,
            rulesets,
            rules,
            mut published,
            submitted_names,
            mut context,
            ..
        } = prepared;
        self.request = request;
        response.files = context.files.clone();
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
                    installation.site,
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
                if let Some(index) = installation.ruleset {
                    published.insert(index);
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
        // Confirm the submitted presentations against completed bindings before
        // retain_rulesets compacts their canonical occurrence indices.
        let mut names: Vec<_> = submitted_names
            .into_iter()
            .filter_map(|(name, index)| published.contains(&index).then_some(name))
            .collect();
        names.sort_unstable();
        response.ruleset_publication = Some(pb::RulesetPublication { names });
        // Retain only completed registrations and their canonical closures.
        // The compiler clone and its IDs are discarded.
        self.definitions = definitions;
        self.definitions.declarations = std::mem::take(&mut self.definitions.declarations)
            .into_iter()
            .enumerate()
            .filter_map(|(index, d)| (!pending_declarations.contains(&index)).then_some(d))
            .collect();
        let (retained_sets, retained_rules) = crate::builtin::definitions::retain_rulesets(
            &mut self.definitions,
            &published.into_iter().collect::<Vec<_>>(),
        )
        .expect("validated canonical occurrence closure");
        self.rulesets = retained_sets
            .into_iter()
            .map(|i| rulesets[i].clone())
            .collect();
        self.rules = retained_rules
            .into_iter()
            .map(|i| rules[i].clone())
            .collect();
        self.names = project_names(&mut pb::Program::default(), &self.definitions);
        match failure {
            Some((error, span)) => Err(Box::new(execution_error(
                error,
                &self.names,
                &response.files,
                span,
                None,
                false,
            ))),
            None => Ok(context),
        }
    }

    // Authoring resolution selects annotated calls; the native compile-only
    // boundary then registers and compiles the entire request on a disposable
    // clone. Neither clone's runtime state or backend IDs are ever adopted.
    fn prepare(&self, program: &mut pb::Program) -> Result<Prepared, PreparationError> {
        if program.ir_version != 1 {
            return Err(format!("unsupported IR version {}", program.ir_version).into());
        }
        let native_spans = NativeSpans::default();
        validate_relation_uses(program, &self.definitions)?;
        for rule in &program.rules {
            if let Some(pb::rule_decl::Kind::Rule(rule)) = &rule.kind {
                validate_legacy_union_scope(program, &rule.head)?;
            }
        }
        let mut staged = self.clone();
        staged.request = staged
            .request
            .checked_add(1)
            .ok_or("request identity space exhausted")?;
        // These live guards also apply to empty requests. A native named
        // Primitive can be executable while retaining a projection error.
        let native = staged.graph.type_info().builtin_catalog()?;
        if staged.definitions.ir_version == 0 {
            staged.definitions = staged
                .graph
                .type_info()
                .portable_builtin_catalog()?
                .definitions;
        } else {
            for name in native.undescribed_primitives {
                if let Some(primitives) = staged.graph.type_info().get_prims(&name) {
                    for primitive in primitives {
                        let any: &dyn std::any::Any = primitive.primitive.as_ref();
                        if let Some(defined) =
                            any.downcast_ref::<crate::primitive::DefinedPrimitive>()
                        {
                            defined.definition.as_ref().map_err(Clone::clone)?;
                        }
                    }
                }
            }
        }
        let mut next_declaration = staged.definitions.declarations.len();
        let added =
            crate::builtin::definitions::reconcile_declarations(program, &mut staged.definitions)?;
        let occurrences =
            crate::builtin::definitions::reconcile_rulesets(program, &mut staged.definitions)?;
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
        staged.names = project_names(program, &staged.definitions);
        let mut authored = staged.definitions.clone();
        project_names(&mut authored, &staged.definitions);
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
                Some(pb::declaration::Kind::Primitive(p)) => {
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
                Some(pb::declaration::Kind::Primitive(p)) => &p.name,
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
                    .resolve_command_before_proofs(command.clone())
                    .map_err(|error| error.to_string())?;
                pending_declarations.insert(declaration_indices[index].unwrap());
                installations.push(Installation {
                    command: Some(command),
                    site: pb::maintenance_site::Target::Declaration(index as u32),
                    span: declaration.span,
                    declaration: declaration_indices[index],
                    ruleset: None,
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
                site: pb::maintenance_site::Target::Sort(site),
                span: program.sorts[site as usize].span,
                declaration: None,
                ruleset: None,
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
        validate_host_declarations(program, &mut staged.graph)?;
        let NodeGraphMetrics {
            depths,
            expansions,
            order,
        } = validate_node_graph(program, &native_spans)?;
        let constructor_dags = if self.mode == pb::ExecutionMode::Normal {
            classify_constructor_dags(
                program,
                &constructor_targets,
                &depths,
                &expansions,
                &order,
                &staged.graph,
            )?
        } else {
            HashMap::new()
        };
        let extraction_dags = if self.mode == pb::ExecutionMode::Normal {
            let roots = command_tree(&program.commands)
                .filter_map(|command| match &command.kind {
                    Some(pb::command::Kind::Extract(extract)) => Some(extract.roots.as_slice()),
                    _ => None,
                })
                .flatten()
                .filter(|root| {
                    depths
                        .get(**root as usize)
                        .is_none_or(|depth| *depth <= 256)
                })
                .map(|root| (*root, vec![*root]));
            classify_closed_dags(
                program,
                &constructor_targets,
                &depths,
                &expansions,
                &order,
                &staged.graph,
                roots,
            )?
        } else {
            HashMap::new()
        };
        let mut scoped_actions = classify_union_actions(
            program,
            &constructor_targets,
            self.mode == pb::ExecutionMode::Normal,
            &depths,
            &native_spans,
        )?;
        if !scoped_actions.is_empty() && self.mode != pb::ExecutionMode::Normal {
            return Err("scoped actions require normal execution mode".into());
        }
        scoped_actions.extend(constructor_dags.keys().cloned());
        lower_builtin_calls(program, &staged.graph, &signatures)?;
        for index in declaration_order(program, &mut staged.graph)? {
            let declaration = &program.declarations[index];
            if !added[index] {
                continue;
            }
            if matches!(
                declaration.kind,
                Some(
                    pb::declaration::Kind::HostPrimitive(_)
                        | pb::declaration::Kind::HostSortFamily(_)
                )
            ) {
                continue; // Already checked against the native catalog above.
            }
            let span = native_span(program, declaration.span.as_ref(), &native_spans)?;
            let command = match declaration.kind.as_ref().ok_or("missing declaration kind")? {
                pb::declaration::Kind::EqSort(_) => continue,
                pb::declaration::Kind::Constructor(constructor) => {
                    if constructor.name.is_empty() { return Err("constructor name must not be empty".into()); }
                    let output = program.sorts.get(constructor.output as usize).ok_or("constructor output sort out of bounds")?;
                    if !matches!(output.kind, Some(pb::sort::Kind::Eq(_))) {
                        return Err("constructor output must be an equality sort".into());
                    }
                    let cost = constructor.cost.map(|index| -> Result<u64, String> {
                        let node = program.nodes.get(index as usize).ok_or("cost index out of bounds")?;
                        match &node.kind {
                            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue { value: Some(pb::primitive_value::Value::I64(cost)) })) if *cost >= 0 && node_sort(program, index)? == "i64" => Ok(*cost as u64),
                            _ => Err("constructor costs currently require a nonnegative inert i64".into()),
                        }
                    }).transpose()?;
                    Command::Constructor { span, name: constructor.name.clone(), table_name: Some(ast::TableName::Public(staged.names.callables[&constructor.name].clone())), schema: signature(program, &constructor.inputs, constructor.output)?, cost, unextractable: constructor.unextractable, hidden: declaration.hidden, let_binding: false, term_constructor: None }
                }
                pb::declaration::Kind::Function(function) => {
                    if function.name.is_empty() { return Err("function name must not be empty".into()); }
                    let schema = signature(program, &function.inputs, function.output)?;
                    if let Some(index) = function.merge {
                        if node_sort(program, index)? != schema.output {
                            return Err("merge output sort mismatch".into());
                        }
                        let mut bindings = HashMap::from([("old".into(), schema.output.clone()), ("new".into(), schema.output.clone())]);
                        check_variables(program, &[index], &mut bindings, false)?;
                        // Native function validation resolves this deferred body
                        // in Context::Write: builtin calls retain their actual
                        // capabilities, and callable backends are installed first.
                    }
                    Command::Function { span, name: function.name.clone(), table_name: Some(ast::TableName::Public(staged.names.callables[&function.name].clone())), schema, merge: function.merge.map(|index| expression(program, index, &mut HashSet::new(), &native_spans)).transpose()?, hidden: declaration.hidden, let_binding: false, term_constructor: None, unextractable: true }
                },
                pb::declaration::Kind::Primitive(primitive) => primitive_command(program, primitive, span, &native_spans)?,
                pb::declaration::Kind::Relation(relation) => Command::Relation {
                    span,
                    name: relation.name.clone(),
                    table_name: Some(ast::TableName::Public(staged.names.callables[&relation.name].clone())),
                    inputs: relation.inputs.iter().map(|arg| sort_name(&program.sorts, arg.sort)).collect::<Result<_, _>>()?,
                },
                _ => return Err("only equality-sort, constructor, function, relation, and primitive declarations execute in this slice".into()),
            };
            // Computed bodies close in the final compile-only pass, after
            // preceding table declarations have actual disposable backends.
            if !matches!(command, Command::Function { .. } | Command::UserDefined(..)) {
                staged
                    .graph
                    .resolve_command_before_proofs(command.clone())
                    .map_err(|error| error.to_string())?;
            }
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
                    .resolve_command_before_proofs(cost_table.clone())
                    .map_err(|error| error.to_string())?;
                installations.push(Installation {
                    command: Some(cost_table),
                    site: pb::maintenance_site::Target::Declaration(index as u32),
                    span: declaration.span,
                    declaration: None,
                    ruleset: None,
                });
            }
            pending_declarations.insert(declaration_indices[index].unwrap());
            installations.push(Installation {
                command: Some(command),
                site: pb::maintenance_site::Target::Declaration(index as u32),
                span: declaration.span,
                declaration: declaration_indices[index],
                ruleset: None,
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
            .chain(program.rules.iter().flat_map(|rule| match &rule.kind {
                Some(pb::rule_decl::Kind::Rule(body)) => body.head.as_slice(),
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
                    code: pb::ErrorCode::UnknownName.into(),
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
        for rule in &program.rules {
            if let Some(pb::rule_decl::Kind::Rewrite(rewrite)) = &rule.kind
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
        let mut rulesets = self.rulesets.clone();
        rulesets.resize(staged.definitions.rulesets.len(), String::new());
        let mut rules = self.rules.clone();
        rules.resize(staged.definitions.rules.len(), String::new());
        let named: HashMap<_, _> = staged
            .definitions
            .rulesets
            .iter()
            .enumerate()
            .filter_map(|(i, s)| s.name.as_ref().map(|name| (name.clone(), i)))
            .collect();
        let published: HashSet<_> = self
            .definitions
            .rulesets
            .iter()
            .enumerate()
            .filter_map(|(i, s)| s.name.as_ref().map(|_| i))
            .collect();
        let mut roots: Vec<_> = program
            .rulesets
            .iter()
            .enumerate()
            .filter_map(|(i, s)| s.name.as_ref().map(|_| occurrences.rulesets[i]))
            .collect();
        for command in command_tree(&program.commands) {
            if let Some(pb::command::Kind::Run(run)) = &command.kind {
                match run
                    .ruleset
                    .as_ref()
                    .and_then(|r| r.kind.as_ref())
                    .ok_or("missing ruleset reference")?
                {
                    pb::ruleset_ref::Kind::Index(i) => roots.push(
                        *occurrences
                            .rulesets
                            .get(*i as usize)
                            .ok_or("ruleset index out of bounds")?,
                    ),
                    pb::ruleset_ref::Kind::Name(name) => {
                        roots.push(*named.get(name).ok_or_else(|| {
                            PreparationError(Box::new(pb::Error {
                                code: pb::ErrorCode::UnknownName.into(),
                                message: format!("unknown ruleset {name}"),
                                span: command.span,
                                ..Default::default()
                            }))
                        })?)
                    }
                }
            }
        }
        let mut visited = HashSet::new();
        let mut order = Vec::new();
        for root in roots {
            let mut pending = vec![(root, false)];
            while let Some((index, leaving)) = pending.pop() {
                if leaving {
                    order.push(index);
                    continue;
                }
                if !visited.insert(index) {
                    continue;
                }
                pending.push((index, true));
                if let Some(pb::ruleset::Kind::Combined(c)) =
                    &staged.definitions.rulesets[index].kind
                {
                    pending.extend(c.rulesets.iter().rev().map(|r| {
                        let Some(pb::ruleset_ref::Kind::Index(i)) = r.kind else {
                            unreachable!("canonical reference")
                        };
                        (i as usize, false)
                    }));
                }
            }
        }
        let mut used = HashSet::new();
        for index in order {
            if !rulesets[index].is_empty() {
                if staged.definitions.rulesets[index].name.is_some() && !published.contains(&index)
                {
                    let local = occurrences
                        .rulesets
                        .iter()
                        .position(|i| *i == index)
                        .expect("new binding has a submitted presentation");
                    installations.push(Installation {
                        command: None,
                        site: pb::maintenance_site::Target::Ruleset(local as u32),
                        span: program.rulesets[local].span,
                        declaration: None,
                        ruleset: Some(index),
                    });
                }
                continue;
            }
            let local = occurrences
                .rulesets
                .iter()
                .position(|i| *i == index)
                .expect("new occurrence has a submitted presentation");
            let site = pb::maintenance_site::Target::Ruleset(local as u32);
            let span = program.rulesets[local].span;
            let selection = ruleset_selection(
                &staged.definitions,
                [(index, pb::ruleset_ref::Kind::Index(local as u32))],
            );
            let mut holders = Vec::new();
            for (rule_index, _) in selection {
                if rules[rule_index].is_empty() {
                    let local_rule = occurrences
                        .rules
                        .iter()
                        .position(|i| *i == rule_index)
                        .expect("new rule has a submitted presentation");
                    used.insert(local_rule);
                    let name = format!("__protobuf_{}_rule_{local_rule}", staged.request);
                    let holder = format!("{name}_holder");
                    installations.push(Installation {
                        command: Some(Command::AddRuleset(
                            native_span(program, span.as_ref(), &native_spans)?,
                            holder.clone(),
                        )),
                        site: site.clone(),
                        span,
                        declaration: None,
                        ruleset: None,
                    });
                    let rule = &program.rules[local_rule];
                    installations.push(Installation {
                        command: Some(lower_rule_cost_deletes(
                            lower_rule(program, rule, &holder, &name, &native_spans)?,
                            &constructor_targets,
                            self.mode,
                        )),
                        site: site.clone(),
                        span: rule.span.or(span),
                        declaration: None,
                        ruleset: None,
                    });
                    rules[rule_index] = name;
                }
                holders.push(format!("{}_holder", rules[rule_index]));
            }
            let name = format!("__protobuf_{}_{}", staged.request, local);
            installations.push(Installation {
                command: Some(Command::UnstableCombinedRuleset(
                    native_span(program, span.as_ref(), &native_spans)?,
                    name.clone(),
                    holders,
                )),
                site,
                span,
                declaration: None,
                ruleset: staged.definitions.rulesets[index]
                    .name
                    .as_ref()
                    .map(|_| index),
            });
            rulesets[index] = name;
        }
        let mut context = RequestOccurrences {
            native_spans,
            scoped_actions,
            constructor_dags,
            extraction_dags,
            rulesets: occurrences
                .rulesets
                .iter()
                .map(|i| rulesets[*i].clone())
                .collect(),
            names: named
                .iter()
                .map(|(name, index)| (name.clone(), rulesets[*index].clone()))
                .collect(),
            files: program.files.clone(),
            ..Default::default()
        };
        let mut routes: Vec<_> = named
            .iter()
            .map(|(name, index)| (*index, pb::ruleset_ref::Kind::Name(name.clone())))
            .collect();
        routes.sort_by_key(|(index, _)| *index);
        routes.extend(
            occurrences
                .rulesets
                .iter()
                .enumerate()
                .map(|(local, index)| (*index, pb::ruleset_ref::Kind::Index(local as u32))),
        );
        for (rule, mut origin) in ruleset_selection(
            &staged.definitions,
            routes
                .into_iter()
                .filter(|(index, _)| !rulesets[*index].is_empty()),
        ) {
            if let Some(span) = &mut origin.span {
                let file = &staged.definitions.files[span.file as usize];
                span.file = match context.files.iter().position(|old| old == file) {
                    Some(index) => index as u32,
                    None => {
                        context.files.push(file.clone());
                        (context.files.len() - 1) as u32
                    }
                };
            }
            let directions: &[(_, _)] = if matches!(
                staged.definitions.rules[rule].kind,
                Some(pb::rule_decl::Kind::Birewrite(_))
            ) {
                &[
                    ("=>", pb::NativeRuleDirection::Forward),
                    ("<=", pb::NativeRuleDirection::Reverse),
                ]
            } else {
                &[("", pb::NativeRuleDirection::Single)]
            };
            for (suffix, direction) in directions {
                context
                    .origins
                    .entry(format!("{}{suffix}", rules[rule]))
                    .or_insert((origin.clone(), *direction));
            }
        }
        let mut validation: Vec<_> = installations
            .iter()
            .filter_map(|i| i.command.clone())
            .collect();
        for (index, rule) in program.rules.iter().enumerate() {
            if !used.contains(&index) && occurrences.rules[index] >= self.rules.len() {
                validation.push(lower_rule_cost_deletes(
                    lower_rule(
                        program,
                        rule,
                        "",
                        &format!("__protobuf_{}_unused_{index}", staged.request),
                        &context.native_spans,
                    )?,
                    &constructor_targets,
                    self.mode,
                ));
            }
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
        let mut compiler = self
            .graph
            .validate_program(validation)
            .map_err(|error| error.to_string())?;
        for (span, facts) in conditions {
            compiler
                .validate_condition(span, facts)
                .map_err(|error| error.to_string())?;
        }
        let mut values = HashMap::new();
        for (path, action) in action_sites(&program.commands) {
            if context.scoped_actions.contains(&path) {
                eval_scoped_action(
                    &mut compiler,
                    program,
                    action,
                    &mut values,
                    false,
                    context.constructor_dags.get(&path),
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
                            &mut compiler,
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
        // Model metadata must see the same fully compiled context, including
        // authored Primitive projections. This graph never enters Prepared.
        staged.graph = compiler;
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
            .filter_map(|(declaration, added)| {
                (added
                    || matches!(
                        declaration.kind,
                        Some(
                            pb::declaration::Kind::HostPrimitive(_)
                                | pb::declaration::Kind::HostSortFamily(_)
                        )
                    ))
                .then_some(declaration)
            })
            .collect();
        Ok(Prepared {
            definitions: staged.definitions,
            request: staged.request,
            installations,
            materialized,
            pending_declarations,
            rulesets,
            rules,
            published,
            submitted_names: program
                .rulesets
                .iter()
                .zip(occurrences.rulesets)
                .filter_map(|(ruleset, index)| {
                    ruleset.name.as_ref().map(|name| (name.clone(), index))
                })
                .collect(),
            context,
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
                    | pb::command::Kind::PrintSize(_)
            )
        ) {
            return lower_native_observation(program, command, context, sites);
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
                            | pb::command::Kind::Repeat(_)
                            | pb::command::Kind::Saturate(_)
                            | pb::command::Kind::Stats(_)
                            | pb::command::Kind::PrintSize(_)
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
            pb::command::Kind::Prove(prove) => {
                Command::Prove(span, facts(program, &prove.facts, &context.native_spans)?)
            }
            pb::command::Kind::ProveExists(prove) => {
                let name = self
                    .names
                    .callables
                    .get(&prove.constructor)
                    .ok_or_else(|| {
                        PreparationError(Box::new(pb::Error {
                            code: pb::ErrorCode::UnknownName.into(),
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
                            code: pb::ErrorCode::UnknownName.into(),
                            message: format!("unknown table {table}"),
                            span: command.span,
                            ..Default::default()
                        })));
                    }
                }
                return Ok(vec![]);
            }
            pb::command::Kind::PrintFunction(print) => {
                if print.table.is_empty() {
                    return Err("table name must not be empty".into());
                }
                let logical = self.names.callables.get(&print.table).ok_or_else(|| {
                    PreparationError(Box::new(pb::Error {
                        code: pb::ErrorCode::UnknownName.into(),
                        message: format!("unknown table {}", print.table),
                        span: command.span,
                        ..Default::default()
                    }))
                })?;
                stored_table_signature(&self.definitions, logical)?;
                return Ok(vec![]);
            }
            pb::command::Kind::Freeze(_) => return Ok(vec![]),
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
        &self,
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
                        code: pb::ErrorCode::UnknownName.into(),
                        message: format!("unknown scheduler {}", run.scheduler),
                        span: command.span,
                        ..Default::default()
                    })));
                }
                self.lower_command(program, command, context, &mut HashMap::new())
            }
            pb::command::Kind::Repeat(_) | pb::command::Kind::Saturate(_) => {
                let (body, until) = match &command.kind {
                    Some(pb::command::Kind::Repeat(repeat)) => {
                        repeat.times.ok_or("missing Repeat count")?;
                        (&repeat.body, &repeat.until)
                    }
                    Some(pb::command::Kind::Saturate(saturate)) => {
                        if saturate.max_iterations == Some(0) {
                            return Err("Saturate bound must be positive".into());
                        }
                        (&saturate.body, &saturate.until)
                    }
                    _ => unreachable!(),
                };
                let mut commands = vec![];
                if !until.is_empty() {
                    conditions.push((span, facts(program, until, &context.native_spans)?));
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
                                    | pb::command::Kind::PrintSize(_)
                            )
                        ) =>
            {
                self.validate_control(
                    program, child, context, schedulers, in_loop, conditions, path,
                )
            }
            pb::command::Kind::Action(_) if context.scoped_actions.contains(path) => Ok(vec![]),
            pb::command::Kind::Action(_) => {
                self.lower_command(program, command, context, &mut HashMap::new())
            }
            pb::command::Kind::Check(_)
            | pb::command::Kind::Stats(_)
            | pb::command::Kind::PrintSize(_)
                if !in_loop || self.mode == pb::ExecutionMode::Normal =>
            {
                self.lower_command(program, command, context, &mut HashMap::new())
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
            pb::command::Kind::Run(run) => {
                let native = match run
                    .ruleset
                    .as_ref()
                    .and_then(|r| r.kind.as_ref())
                    .ok_or("missing ruleset reference")?
                {
                    pb::ruleset_ref::Kind::Name(name) => {
                        context.names.get(name).ok_or_else(|| {
                            PreparationError(Box::new(pb::Error {
                                code: pb::ErrorCode::UnknownName.into(),
                                message: format!("unknown ruleset {name}"),
                                span: command.span,
                                ..Default::default()
                            }))
                        })?
                    }
                    pb::ruleset_ref::Kind::Index(index) => context
                        .rulesets
                        .get(*index as usize)
                        .ok_or("ruleset index out of bounds")?,
                };
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

    fn execute(
        &mut self,
        program: &pb::Program,
        command: &pb::Command,
        context: &mut RequestOccurrences,
        location: &pb::CommandLocation,
        response: &mut pb::RunProgramResponse,
        failure_site: &mut Option<ExecutionFailureSite>,
    ) -> Result<(), egglog::Error> {
        let output = match command.kind.as_ref().unwrap() {
            pb::command::Kind::Fail(child) if context.scoped_actions.contains(&location.path) => {
                let result =
                    self.execute(program, child, context, location, response, failure_site);
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
                    measurements: &measurements,
                    outcome: None,
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
                measurements.publish(
                    pb::maintenance_site::Target::Command(pb::StaticCommandPath {
                        path: location.path.clone(),
                    }),
                    context,
                    response,
                );
                result?;
                None
            }
            pb::command::Kind::Freeze(_) => {
                Some(pb::command_output::Kind::Snapshot(freeze::export(self)?))
            }
            pb::command::Kind::Action(action)
                if context.scoped_actions.contains(&location.path) =>
            {
                eval_scoped_action(
                    &mut self.graph,
                    program,
                    action,
                    &mut context.union_values,
                    true,
                    context.constructor_dags.get(&location.path),
                    &mut |_| {},
                    &context.native_spans,
                )?;
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
            pb::command::Kind::PrintFunction(print) => {
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
                    let mut exported = pb::RunProgramResponse::default();
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
                let mut output = pb::PrintedFunction {
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
                Some(pb::command_output::Kind::PrintedFunction(output))
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
                    pb::maintenance_site::Target::Command(pb::StaticCommandPath {
                        path: location.path.clone(),
                    }),
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
                run_report: None,
            });
        }
        Ok(())
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
        site: pb::maintenance_site::Target,
        requested: Option<RequestedObservation<'_>>,
        context: &mut RequestOccurrences,
        response: &mut pb::RunProgramResponse,
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
            Some(pb::command::Kind::PrintSize(print)) => Some(print),
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
                    if context.include_run_reports {
                        match report::export(
                            &report,
                            &measurements.borrow().selected,
                            context,
                            response,
                        ) {
                            Ok(detail) => run_report = Some(detail),
                            Err(error) => {
                                export_error = Some(egglog::Error::BackendError(error));
                                return;
                            }
                        }
                    }
                    pb::command_output::Kind::Run(pb::RunOutcome {
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
                egglog::CommandOutput::OverallStatistics(report) => {
                    match report::export(&report, &[], context, response) {
                        Ok(detail) => pb::command_output::Kind::Statistics(detail),
                        Err(error) => {
                            export_error = Some(egglog::Error::BackendError(error));
                            return;
                        }
                    }
                }
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
                run_report,
            });
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
        if captured.is_none() {
            owned_measurements
                .into_inner()
                .publish(site, context, response);
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
        mode: pb::ExecutionMode,
        location: Option<&pb::CommandLocation>,
        sites: &ScheduleSites<'_>,
    ) {
        match event {
            ExecutionEvent::ActionsFinished { changed, .. } => self.changed |= changed,
            ExecutionEvent::RunFinished {
                result: Ok(report), ..
            } => self.changed |= report.updated,
            _ => (),
        }
        match event {
            ExecutionEvent::CommandCompleted {
                origin: ExecutionOrigin::Requested,
                ..
            } => self.failure = None,
            ExecutionEvent::RunStarted { origin, schedule }
            | ExecutionEvent::RunFinished {
                origin, schedule, ..
            } => {
                let mapped = schedule.and_then(|schedule| {
                    let (command, path) = sites.get(schedule.path)?;
                    let mut nested = location.expect("schedule has command site").clone();
                    nested.path.extend(path);
                    nested
                        .iterations
                        .extend(schedule.iterations.iter().map(|i| *i as u64));
                    Some((*command, nested))
                });
                let authored = origin == ExecutionOrigin::Requested;
                if matches!(event, ExecutionEvent::RunStarted { .. })
                    && let Some((
                        pb::Command {
                            kind: Some(pb::command::Kind::Run(run)),
                            ..
                        },
                        _,
                    )) = &mapped
                {
                    let selected = run.ruleset.as_ref().expect("validated Run");
                    if !self.selected.contains(selected) {
                        self.selected.push(selected.clone());
                    }
                }
                if matches!(event, ExecutionEvent::RunFinished { result: Err(_), .. })
                    && self.failure.is_none()
                {
                    self.failure = mapped
                        .as_ref()
                        .map(|(command, location)| (location.clone(), command.span));
                }
                let path = mapped
                    .as_ref()
                    .map(|(_, location)| location.path.clone())
                    .or_else(|| location.map(|location| location.path.clone()));
                let summary = if authored {
                    self.requested
                        .entry(path.expect("authored Run has command site"))
                        .or_default()
                } else {
                    self.maintenance.entry(path).or_default()
                };
                match event {
                    ExecutionEvent::RunStarted { .. } => summary.invocations += 1,
                    ExecutionEvent::RunFinished { result, .. } => {
                        summary.finish(result, authored && mode == pb::ExecutionMode::Normal)
                    }
                    _ => unreachable!(),
                }
            }
            _ => (),
        }
    }

    fn publish(
        self,
        site: pb::maintenance_site::Target,
        context: &mut RequestOccurrences,
        response: &mut pb::RunProgramResponse,
    ) {
        let measurements = self;
        let profile = response.profile.as_mut().expect("summary requested");
        let mut requested: Vec<_> = measurements.requested.into_iter().collect();
        requested.sort_unstable_by(|a, b| a.0.cmp(&b.0));
        for (path, requested) in requested {
            let mut rules: Vec<pb::RuleSummary> = vec![];
            let mut positions = HashMap::new();
            let mut measured: Vec<_> = requested.rules.into_iter().collect();
            measured.sort_unstable_by(|a, b| a.0.cmp(&b.0));
            for (name, (matches, nanos)) in measured {
                if let Some((origin, _)) = context.origins.get(&name) {
                    let index =
                        *context
                            .response_rules
                            .entry(origin.clone())
                            .or_insert_with(|| {
                                response.rules.push(origin.clone());
                                (response.rules.len() - 1) as u32
                            });
                    let position = *positions.entry(index).or_insert_with(|| {
                        rules.push(pb::RuleSummary {
                            rule: Some(index),
                            matches: Some(0),
                            search_and_apply_nanos: Some(0),
                        });
                        rules.len() - 1
                    });
                    let rule = &mut rules[position];
                    rule.matches = rule.matches.and_then(|old| old.checked_add(matches));
                    rule.search_and_apply_nanos = rule
                        .search_and_apply_nanos
                        .and_then(|old| old.checked_add(nanos?));
                }
            }
            profile.runs.push(pb::RunSummary {
                command_path: path,
                invocations: requested.invocations,
                rules,
                search_and_apply_nanos: requested.nanos[0],
                merge_nanos: requested.nanos[1],
                rebuild_nanos: requested.nanos[2],
            });
        }
        let mut maintenance: Vec<_> = measurements.maintenance.into_iter().collect();
        maintenance.sort_unstable_by(|a, b| a.0.cmp(&b.0));
        for (path, maintenance) in maintenance {
            let site = Some(pb::MaintenanceSite {
                target: Some(path.map_or_else(
                    || site.clone(),
                    |path| pb::maintenance_site::Target::Command(pb::StaticCommandPath { path }),
                )),
            });
            if let Some(existing) = profile.maintenance.iter_mut().find(|m| m.site == site) {
                existing.invocations += maintenance.invocations;
                for (total, next) in [
                    &mut existing.search_and_apply_nanos,
                    &mut existing.merge_nanos,
                    &mut existing.rebuild_nanos,
                ]
                .into_iter()
                .zip(maintenance.nanos)
                {
                    *total = total.and_then(|old| old.checked_add(next?));
                }
            } else {
                profile.maintenance.push(pb::MaintenanceSummary {
                    site,
                    invocations: maintenance.invocations,
                    search_and_apply_nanos: maintenance.nanos[0],
                    merge_nanos: maintenance.nanos[1],
                    rebuild_nanos: maintenance.nanos[2],
                });
            }
        }
    }
}

fn control_command(command: &pb::Command) -> bool {
    match &command.kind {
        Some(
            pb::command::Kind::Run(_)
            | pb::command::Kind::Repeat(_)
            | pb::command::Kind::Saturate(_),
        ) => true,
        Some(pb::command::Kind::Fail(child)) => control_command(child),
        _ => false,
    }
}

fn lower_native_observation<'a>(
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
                facts(program, &check.facts, &context.native_spans)?,
            )]
        }
        pb::command::Kind::Stats(_) => vec![Command::PrintOverallStatistics(span, None)],
        pb::command::Kind::PrintSize(print) => {
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
    let Some(pb::scheduler::Kind::BackOff(options)) = bind
        .scheduler
        .as_ref()
        .and_then(|scheduler| scheduler.kind.as_ref())
    else {
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

struct WireSchedule<'a> {
    executor: NativeExecutor<'a>,
    program: &'a pb::Program,
    context: &'a mut RequestOccurrences,
    response: &'a mut pb::RunProgramResponse,
    root: &'a pb::CommandLocation,
    measurements: &'a RefCell<ScheduleMeasurements>,
    bindings: Vec<(String, SchedulerBinding)>,
    outcome: &'a mut Option<pb::LoopOutcome>,
    suppressed: bool,
    partial: &'a mut ControlReport,
}

struct WireEnvelope<'a> {
    mode: pb::ExecutionMode,
    names: &'a NativeNames,
    program: &'a pb::Program,
    context: &'a mut RequestOccurrences,
    response: &'a mut pb::RunProgramResponse,
    root: &'a pb::CommandLocation,
    measurements: &'a RefCell<ScheduleMeasurements>,
    outcome: Option<pb::LoopOutcome>,
    export_error: Option<egglog::Error>,
    suppressed: bool,
    anchor: &'a pb::Command,
    bindings: Vec<(String, SchedulerBinding)>,
    partial: ControlReport,
}

impl WireEnvelope<'_> {
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
            measurements: self.measurements,
            bindings: self.bindings.clone(),
            outcome: &mut self.outcome,
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
        let kind = if let Some(outcome) = self.outcome.take() {
            pb::command_output::Kind::Loop(outcome)
        } else {
            pb::command_output::Kind::Run(pb::RunOutcome {
                updated: report.updated,
                can_stop: report.can_stop,
            })
        };
        self.export_error = self.output(kind, report).err();
    }

    fn output(
        &mut self,
        kind: pb::command_output::Kind,
        report: &egglog_reports::RunReport,
    ) -> Result<(), egglog::Error> {
        let run_report = self
            .context
            .include_run_reports
            .then(|| {
                report::export(
                    report,
                    &self.measurements.borrow().selected,
                    self.context,
                    self.response,
                )
            })
            .transpose()
            .map_err(egglog::Error::BackendError)?;
        self.response.outputs.push(pb::CommandOutput {
            kind: Some(kind),
            location: Some(self.root.clone()),
            run_report,
        });
        Ok(())
    }
}

impl WireSchedule<'_> {
    fn location(&self, path: &[usize], iterations: &[u64]) -> pb::CommandLocation {
        let mut location = self.root.clone();
        location.path.extend(path.iter().map(|index| *index as u32));
        location.iterations.extend(iterations);
        location
    }
}

impl ControlContext for WireSchedule<'_> {
    type Node = pb::Command;
    type Error = egglog::Error;
    type Scope = (usize, HashMap<u32, Value>);

    fn view<'a>(&self, node: &'a pb::Command) -> Result<Control<'a, pb::Command>, egglog::Error> {
        Ok(match node.kind.as_ref().expect("validated command") {
            pb::command::Kind::Repeat(repeat) => {
                Control::Repeat(&repeat.body, repeat.times.unwrap())
            }
            pb::command::Kind::Saturate(saturate) => {
                Control::Saturate(&saturate.body, saturate.max_iterations)
            }
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
                measurements: self.measurements,
                outcome: None,
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
                self.context.constructor_dags.get(&location.path),
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
            lower_native_observation(self.program, node, self.context, &mut sites)
                .expect("validated leaf")
        };
        let mut report = None;
        let (result, _, _) = self.executor.run_observed(
            commands,
            pb::maintenance_site::Target::Command(pb::StaticCommandPath {
                path: location.path.clone(),
            }),
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
            Some(pb::command::Kind::Repeat(repeat)) => &repeat.until,
            Some(pb::command::Kind::Saturate(saturate)) => &saturate.until,
            _ => unreachable!(),
        };
        if until.is_empty() {
            return Ok(false);
        }
        let location = self.location(path, iterations);
        let result = self.executor.graph.check_condition_observed(
            native_span(self.program, node.span.as_ref(), &self.context.native_spans)
                .expect("validated span"),
            facts(self.program, until, &self.context.native_spans).expect("validated until"),
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
        path: &[usize],
        _: &[u64],
        report: &ControlReport,
        count: u64,
        stop: ControlStop,
    ) -> Result<(), egglog::Error> {
        if path.is_empty() {
            let termination = match stop {
                ControlStop::Count => pb::TerminationReason::CountReached,
                ControlStop::Bound => pb::TerminationReason::IterationLimit,
                ControlStop::Saturated => pb::TerminationReason::Saturated,
                ControlStop::Until => pb::TerminationReason::UntilMatched,
                ControlStop::SchedulerLimit => pb::TerminationReason::SchedulerLimit,
            };
            *self.outcome = Some(pb::LoopOutcome {
                updated: report.report.updated,
                iterations: count,
                termination: Some(termination.into()),
            });
        }
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
fn project_names(program: &mut pb::Program, definitions: &pb::Program) -> NativeNames {
    let mut names = NativeNames::default();
    let mut host_keys = HashSet::new();
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
            Some(pb::declaration::Kind::Primitive(p)) => {
                names
                    .callables
                    .insert(native_name("call", &p.name), p.name.clone());
            }
            Some(pb::declaration::Kind::HostPrimitive(p)) => {
                host_keys.insert(p.name.as_str());
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
            Some(pb::declaration::Kind::Primitive(p)) => project_call(&mut p.name),
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
    let mut commands: Vec<_> = program.commands.iter_mut().collect();
    let mut actions = vec![];
    while let Some(command) = commands.pop() {
        match &mut command.kind {
            Some(pb::command::Kind::Fail(child)) => commands.push(child.as_mut()),
            Some(pb::command::Kind::Repeat(body)) => commands.extend(body.body.iter_mut()),
            Some(pb::command::Kind::Saturate(body)) => commands.extend(body.body.iter_mut()),
            Some(pb::command::Kind::Action(action)) => actions.push(action),
            Some(pb::command::Kind::PrintSize(print)) => {
                for table in &mut print.tables {
                    project_size(table);
                }
            }
            Some(pb::command::Kind::PrintFunction(print)) => project_call(&mut print.table),
            Some(pb::command::Kind::KeepBest(keep)) => {
                for table in &mut keep.tables {
                    project_call(table);
                }
            }
            Some(pb::command::Kind::ProveExists(prove)) => project_call(&mut prove.constructor),
            _ => (),
        }
    }
    for action in
        actions
            .into_iter()
            .chain(program.rules.iter_mut().flat_map(|r| match &mut r.kind {
                Some(pb::rule_decl::Kind::Rule(r)) => r.head.as_mut_slice(),
                _ => &mut [],
            }))
    {
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
        Some(pb::sort::Kind::Family(family))
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
        Some(pb::sort::Kind::Family(family))
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
        Some(pb::sort::Kind::Family(family))
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
    let Some(pb::sort::Kind::Family(family)) = &sort.kind else {
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
                Some(pb::declaration::Kind::Function(_) | pb::declaration::Kind::Primitive(_))
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
            Some(pb::declaration::Kind::Primitive(p)) => Some((p.name.as_str(), i)),
            _ => None,
        })
        .collect();
    let mut pending = vec![];
    let mut installed = HashSet::new();
    for (i, d) in program.declarations.iter().enumerate() {
        let (name, body, primitive) = match &d.kind {
            Some(pb::declaration::Kind::Function(f)) => (f.name.as_str(), f.merge, false),
            Some(pb::declaration::Kind::Primitive(p)) => (
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
    while !pending.is_empty() {
        let Some(position) = pending
            .iter()
            .position(|(_, dependencies)| dependencies.is_subset(&installed))
        else {
            return Err(
                "recursive program-defined primitives or function merges are not supported yet"
                    .into(),
            );
        };
        let (index, _) = pending.remove(position);
        installed.insert(index);
        order.push(index);
    }
    Ok(order)
}

fn primitive_command(
    program: &pb::Program,
    primitive: &pb::Primitive,
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
            Some(pb::sort::Kind::Family(family)) if !family.args.is_empty() => {
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
            .resolve_command_before_proofs(command.clone())
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
            if function.is_none() && signatures.contains_key(&call.func) {
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
                if !matches!(program.sorts.get(node.sort_id as usize).and_then(|s| s.kind.as_ref()), Some(pb::sort::Kind::Family(f)) if f.name == expected && f.args.is_empty())
                {
                    return Err(format!("{expected} payload/sort mismatch"));
                }
                validate_exact_number(value)?;
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
            let Some(pb::sort::Kind::Family(family)) = program
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
                kind: Some(pb::sort::Kind::Family(pb::HostSort {
                    name: "Pair".into(),
                    args: parameters,
                })),
                ..Default::default()
            });
            let vector_sort = u32::try_from(sorts.len()).map_err(|_| "too many sorts")?;
            sorts.push(pb::Sort {
                kind: Some(pb::sort::Kind::Family(pb::HostSort {
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

fn validate_host_declarations(program: &pb::Program, graph: &mut EGraph) -> Result<(), String> {
    // Presentation/defaults were reconciled against the full staged context.
    // Provider checks must not revalidate saved code in a pruned namespace.
    for declaration in &program.declarations {
        match &declaration.kind {
            Some(pb::declaration::Kind::HostPrimitive(primitive)) => {
                graph
                    .type_info()
                    .check_portable_builtin_signature(program, primitive)?;
            }
            Some(pb::declaration::Kind::HostSortFamily(family)) => {
                if matches!(
                    family.name.as_str(),
                    "Vec" | "Set" | "MultiSet" | "Pair" | "Map" | "Maybe"
                ) {
                    let arity =
                        if matches!(family.name.as_str(), "Vec" | "Set" | "MultiSet" | "Maybe") {
                            1
                        } else {
                            2
                        };
                    if family.arity != arity || declaration.bindings.is_some() {
                        return Err(format!(
                            "unsupported or incompatible {} family descriptor",
                            family.name
                        ));
                    }
                    continue;
                }
                let sort = graph
                    .get_sort_by_name(&family.name)
                    .ok_or_else(|| format!("unknown host sort family {}", family.name))?;
                if family.arity != 0
                    || declaration.bindings.is_some()
                    || sort.is_eq_sort()
                    || sort.is_container_sort()
                {
                    return Err(format!(
                        "unsupported or incompatible host sort family {}",
                        family.name
                    ));
                }
            }
            _ => (),
        }
    }
    Ok(())
}

fn expression(
    program: &pb::Program,
    index: u32,
    visiting: &mut HashSet<u32>,
    native_spans: &NativeSpans,
) -> Result<Expr, String> {
    // The compatibility AST is a tree. Bound expansion of a compact shared DAG
    // before it can allocate exponentially; a later native-IR path can lift this.
    lower_expression(program, index, visiting, &mut 65_536, native_spans)
}

// These checks never normalize malformed wire data. Native constructors remain
// separate symbolic operations with their original partial/panic behavior.
fn canonical_decimal(text: &str) -> Result<BigInt, String> {
    let value: BigInt = text.parse().map_err(|_| "invalid decimal integer")?;
    if value.to_string() != text {
        return Err("noncanonical decimal integer".into());
    }
    Ok(value)
}

fn validate_exact_number(value: &pb::primitive_value::Value) -> Result<(), String> {
    use pb::primitive_value::Value as V;
    match value {
        V::BigInt(text) => {
            canonical_decimal(text)?;
        }
        V::BigRat(ratio) => {
            let numerator = canonical_decimal(&ratio.numerator)?;
            let denominator = canonical_decimal(&ratio.denominator)?;
            if denominator <= BigInt::zero() || numerator.gcd(&denominator) != BigInt::one() {
                return Err("BigRat value must be reduced with a positive denominator".into());
            }
        }
        V::Rational(ratio) => {
            if ratio.denominator <= 0
                || ratio
                    .numerator
                    .unsigned_abs()
                    .gcd(&(ratio.denominator as u64))
                    != 1
            {
                return Err("Rational value must be reduced with a positive denominator".into());
            }
        }
        _ => return Err("expected an exact numeric value".into()),
    }
    Ok(())
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
        pb::node::Kind::PrimitiveValue(pb::PrimitiveValue { value: Some(value) })
            if matches!(
                value,
                pb::primitive_value::Value::BigInt(_)
                    | pb::primitive_value::Value::BigRat(_)
                    | pb::primitive_value::Value::Rational(_)
            ) =>
        {
            validate_exact_number(value)?;
            let (name, arguments, extra_nodes) = match value {
                pb::primitive_value::Value::BigInt(text) if sort == "BigInt" => (
                    "egglog.core.bigint.from_string",
                    vec![Expr::Lit(span.clone(), Literal::String(text.clone()))],
                    1,
                ),
                pb::primitive_value::Value::Rational(ratio) if sort == "Rational" => (
                    "egglog.experimental.rational.make",
                    vec![
                        Expr::Lit(span.clone(), Literal::Int(ratio.numerator)),
                        Expr::Lit(span.clone(), Literal::Int(ratio.denominator)),
                    ],
                    2,
                ),
                pb::primitive_value::Value::BigRat(ratio) if sort == "BigRat" => (
                    "egglog.core.bigrat.make",
                    [&ratio.numerator, &ratio.denominator]
                        .into_iter()
                        .map(|text| {
                            Expr::Call(
                                span.clone(),
                                "egglog.core.bigint.from_string".into(),
                                vec![Expr::Lit(span.clone(), Literal::String(text.clone()))],
                            )
                        })
                        .collect(),
                    4,
                ),
                _ => return Err("exact numeric payload/sort mismatch".into()),
            };
            *remaining = remaining
                .checked_sub(extra_nodes)
                .ok_or("native expression expansion exceeds 65536 nodes")?;
            Expr::Call(span, name.into(), arguments)
        }
        pb::node::Kind::PrimitiveValue(value) => {
            let literal = match value.value.as_ref() {
                Some(pb::primitive_value::Value::I64(value)) if sort == "i64" => {
                    Literal::Int(*value)
                }
                Some(pb::primitive_value::Value::F64Bits(value)) if sort == "f64" => {
                    Literal::Float(f64::from_bits(*value).into())
                }
                Some(pb::primitive_value::Value::String(value)) if sort == "String" => {
                    Literal::String(value.clone())
                }
                Some(pb::primitive_value::Value::Bool(value)) if sort == "bool" => {
                    Literal::Bool(*value)
                }
                Some(pb::primitive_value::Value::Unit(_)) if sort == "Unit" => Literal::Unit,
                _ => return Err("unsupported value or scalar payload/sort mismatch".into()),
            };
            Expr::Lit(span, literal)
        }
        _ => return Err("this node kind is unsupported in a value position".into()),
    };
    visiting.remove(&index);
    Ok(result)
}

fn facts(
    program: &pb::Program,
    indices: &[u32],
    native_spans: &NativeSpans,
) -> Result<Vec<Fact>, String> {
    let mut result = vec![];
    for index in indices {
        let node = program
            .nodes
            .get(*index as usize)
            .ok_or("fact index out of bounds")?;
        if let Some(pb::node::Kind::Union(union)) = &node.kind {
            if union.members.len() < 2 {
                return Err("empty/single-member query Unions are not supported yet".into());
            }
            let first = *union.members.first().ok_or("empty equality fact")?;
            for other in union.members.iter().skip(1) {
                result.push(Fact::Eq(
                    native_span(program, node.span.as_ref(), native_spans)?,
                    expression(program, first, &mut HashSet::new(), native_spans)?,
                    expression(program, *other, &mut HashSet::new(), native_spans)?,
                ));
            }
        } else {
            result.push(Fact::Fact(expression(
                program,
                *index,
                &mut HashSet::new(),
                native_spans,
            )?));
        }
    }
    // Facts introduce query binders. Rename at this use, not in the arena:
    // the same Var node may also be the special `old`/`new` of a merge.
    Ok(result
        .into_iter()
        .map(|fact| {
            fact.map_symbols(&mut |head| head, &mut |leaf: String| {
                native_name("var", &leaf)
            })
        })
        .collect())
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
                        Some(pb::sort::Kind::Family(family)) if family.name == "Unit" && family.args.is_empty()
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
            Some(pb::declaration::Kind::Primitive(primitive)) => {
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
        if let Some(python) = declaration
            .bindings
            .as_ref()
            .and_then(|bindings| bindings.python.as_ref())
        {
            for view in &python.views {
                for parameter in &view.params {
                    if let Some(default) = parameter.default_expr {
                        value(default)?;
                    }
                }
            }
        }
    }
    for rule in &program.rules {
        match &rule.kind {
            Some(pb::rule_decl::Kind::Rule(rule)) => {
                for head in &rule.head {
                    action(head)?;
                }
            }
            Some(pb::rule_decl::Kind::Rewrite(rewrite)) => {
                value(rewrite.lhs)?;
                value(rewrite.rhs)?;
            }
            Some(pb::rule_decl::Kind::Birewrite(rewrite)) => {
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
struct NodeGraphMetrics {
    depths: Vec<usize>,
    expansions: Vec<usize>,
    order: Vec<usize>,
}

fn validate_node_graph(
    program: &pb::Program,
    native_spans: &NativeSpans,
) -> Result<NodeGraphMetrics, String> {
    let mut edges = Vec::with_capacity(program.nodes.len());
    for (index, node) in program.nodes.iter().enumerate() {
        let sort = node_sort(program, index as u32)?;
        native_span(program, node.span.as_ref(), native_spans)?;
        let children = match &node.kind {
            Some(pb::node::Kind::Call(call) | pb::node::Kind::GetCost(call)) => call.args.clone(),
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
    let mut depths = vec![0usize; edges.len()];
    let mut expansions = vec![0usize; edges.len()];
    let mut order = Vec::with_capacity(edges.len());
    for start in 0..edges.len() {
        let mut pending = vec![(start, false)];
        while let Some((index, exit)) = pending.pop() {
            if exit {
                depths[index] = 1 + edges[index]
                    .iter()
                    .map(|child| depths[*child as usize])
                    .max()
                    .unwrap_or(0);
                // Structural validation is independent of the tree adapter.
                // Saturating expansion sizes select the action DAG path without
                // constructing (or overflowing the size of) an expanded tree.
                expansions[index] = edges[index].iter().fold(1usize, |size, child| {
                    size.saturating_add(expansions[*child as usize]).min(65_537)
                });
                state[index] = 2;
                order.push(index);
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
    Ok(NodeGraphMetrics {
        depths,
        expansions,
        order,
    })
}

// Only transitively closed constructors/scalars and fixed native value builders
// may be shared. Other Calls are ordered barriers, never memoized ancestors.
fn classify_constructor_dags(
    program: &pb::Program,
    constructors: &HashSet<String>,
    depths: &[usize],
    expansions: &[usize],
    order: &[usize],
    graph: &EGraph,
) -> Result<HashMap<Vec<u32>, HashSet<u32>>, String> {
    let mut candidates = vec![];
    for (path, action) in action_sites(&program.commands) {
        if !matches!(
            action.kind,
            Some(pb::action::Kind::Term(_) | pb::action::Kind::Set(_))
        ) {
            continue;
        }
        candidates.push((path, action_roots(action)?));
    }
    classify_closed_dags(
        program,
        constructors,
        depths,
        expansions,
        order,
        graph,
        candidates,
    )
}

// Eligibility is independent of the operation; only evaluated values are local
// to an action or one ordered extraction root.
fn classify_closed_dags<K: Eq + std::hash::Hash>(
    program: &pb::Program,
    constructors: &HashSet<String>,
    depths: &[usize],
    expansions: &[usize],
    order: &[usize],
    graph: &EGraph,
    sites: impl IntoIterator<Item = (K, Vec<u32>)>,
) -> Result<HashMap<K, HashSet<u32>>, String> {
    let mut candidates = vec![];
    for (path, roots) in sites {
        let mut needs_scoping = false;
        for root in &roots {
            let depth = depths
                .get(*root as usize)
                .ok_or("action node out of bounds")?;
            needs_scoping |= *depth > 256 || expansions[*root as usize] > 65_536;
        }
        if needs_scoping {
            candidates.push((path, roots));
        }
    }
    if candidates.is_empty() {
        return Ok(HashMap::new());
    }
    let mut closed = HashSet::new();
    for &index in order {
        let eligible = match program.nodes[index].kind.as_ref().unwrap() {
            pb::node::Kind::Call(call) => {
                let value_builder = if matches!(
                    call.func.as_str(),
                    "egglog.core.vec.of"
                        | "egglog.core.vec.empty"
                        | "egglog.core.bigint.from_string"
                        | "egglog.core.bigrat.make"
                        | "egglog.experimental.rational.make"
                ) {
                    let types = graph.authoring_type_info();
                    let sorts = call
                        .args
                        .iter()
                        .copied()
                        .chain([index as u32])
                        .map(|node| {
                            let name = node_sort(program, node)?;
                            types
                                .get_sort_by_name(&name)
                                .cloned()
                                .ok_or_else(|| format!("unknown value-builder sort {name}"))
                        })
                        .collect::<Result<Vec<_>, String>>()?;
                    types
                        .resolve_builtin(&call.func, &sorts)?
                        .is_valid_in_context(egglog::Context::Pure)
                } else {
                    false
                };
                (constructors.contains(&call.func) || value_builder)
                    && call.args.iter().all(|child| closed.contains(child))
            }
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
            }) => true,
            _ => false,
        };
        if eligible {
            closed.insert(index as u32);
        }
    }
    let mut selected = HashMap::new();
    for (path, roots) in candidates {
        if roots
            .iter()
            .any(|root| !closed.contains(root) && depths[*root as usize] > 256)
        {
            continue;
        }
        // Set keys precede its value in the existing scoped action compiler.
        let mut pending = roots;
        let mut seen = HashSet::new();
        // Bound compact nodes/edges first; the planner also counts rereads.
        let mut remaining = 65_536usize
            .checked_sub(pending.len())
            .ok_or("constructor action DAG exceeds 65536 nodes and edges")?;
        let mut eligible = true;
        while let Some(index) = pending.pop() {
            if !seen.insert(index) {
                continue;
            }
            let children = match program.nodes[index as usize].kind.as_ref().unwrap() {
                pb::node::Kind::Call(call) => &call.args[..],
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
            remaining = remaining
                .checked_sub(1 + children.len())
                .ok_or("constructor action DAG exceeds 65536 nodes and edges")?;
            pending.extend(children);
        }
        if eligible
            && seen.iter().any(|index| {
                closed.contains(index)
                    && matches!(
                        program.nodes[*index as usize].kind,
                        Some(pb::node::Kind::Call(_))
                    )
            })
        {
            selected.insert(path, closed.intersection(&seen).copied().collect());
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
    depths: &[usize],
    native_spans: &NativeSpans,
) -> Result<HashSet<Vec<u32>>, String> {
    let unions = |action: &pb::Action| -> Result<(HashSet<u32>, usize), String> {
        let mut pending = action_roots(action)?;
        let mut seen = HashSet::new();
        let mut unions = HashSet::new();
        let mut depth = 0;
        while let Some(index) = pending.pop() {
            if !seen.insert(index) {
                continue;
            }
            depth = depth.max(
                *depths
                    .get(index as usize)
                    .ok_or("action node out of bounds")?,
            );
            match program
                .nodes
                .get(index as usize)
                .ok_or("action node out of bounds")?
                .kind
                .as_ref()
            {
                Some(pb::node::Kind::Union(union)) => {
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
        Ok((unions, depth))
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
        let (reached, depth) = unions(action)?;
        let cost_action = matches!(action.kind, Some(pb::action::Kind::SetCost(_)))
            || constructor_costs
                && matches!(&action.kind, Some(pb::action::Kind::Delete(call)) if constructor_targets.contains(&call.func));
        if reached.is_empty() && !cost_action {
            continue;
        }
        // Moving the arena-wide tree limit must not broaden the existing
        // Union/cost path's admission beyond this constructor-only slice.
        if depth > 256 {
            return Err("expression depth exceeds this adapter's current limit of 256".into());
        }
        let generalized = cost_action
            || reached.iter().any(|union| uses[union] > 1)
            || lower_action(program, action, native_spans).is_err();
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
    for rule in &program.rules {
        if let Some(pb::rule_decl::Kind::Rule(rule)) = &rule.kind {
            validate_legacy_union_scope(program, &rule.head)?;
        }
    }
    Ok(())
}

// Both byte execution and Source rendering use this first-demand local plan.
// Nonclosed Calls are evaluated afresh and end the fragment memo's lifetime.
fn constructor_dag_actions(
    program: &pb::Program,
    action: &pb::Action,
    mut occupied: impl FnMut(&str) -> bool,
    native_spans: &NativeSpans,
    closed: &HashSet<u32>,
) -> Result<(Vec<Action>, Vec<u32>), String> {
    enum Walk {
        Enter(u32),
        Call(u32, usize),
    }
    let mut pending: Vec<_> = action_roots(action)?
        .into_iter()
        .rev()
        .map(Walk::Enter)
        .collect();
    let mut results = Vec::new();
    let mut actions = Vec::new();
    let mut evaluations = Vec::new();
    let mut memo = HashMap::<u32, String>::new();
    let mut next = 0usize;
    let mut remaining = 65_536usize;
    let mut bind_value = |index: u32, value: Expr| -> Result<(String, Expr), String> {
        let span = native_span(
            program,
            program.nodes[index as usize].span.as_ref(),
            native_spans,
        )?;
        let name = loop {
            let candidate = format!("__egglog_proto_action_{next}");
            next += 1;
            if !occupied(&candidate) && !occupied(&format!("${candidate}")) {
                break candidate;
            }
        };
        actions.push(Action::Let(span.clone(), name.clone(), value));
        evaluations.push(index);
        Ok((name.clone(), Expr::Var(span, name)))
    };
    while let Some(step) = pending.pop() {
        remaining = remaining
            .checked_sub(1)
            .ok_or("native action expansion exceeds 65536 steps")?;
        let (index, value) = match step {
            Walk::Enter(index) => {
                let node = &program.nodes[index as usize];
                let span = native_span(program, node.span.as_ref(), native_spans)?;
                if let Some(name) = memo.get(&index) {
                    results.push(Expr::Var(span, name.clone()));
                    continue;
                }
                match node.kind.as_ref().expect("validated node") {
                    pb::node::Kind::Call(call) => {
                        pending.push(Walk::Call(index, call.args.len()));
                        pending.extend(call.args.iter().rev().map(|child| Walk::Enter(*child)));
                        continue;
                    }
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
                    }) => {
                        let value = expression(program, index, &mut HashSet::new(), native_spans)?;
                        // Exact-number leaves have a fixed native construction:
                        // literals, or BigRat's two one-argument BigInt builders.
                        // Bind those components too so Source scope replay sees
                        // the same first-demand locals, without nested payloads.
                        let value = match value {
                            Expr::Call(span, target, arguments) => {
                                let mut bound = Vec::with_capacity(arguments.len());
                                for argument in arguments {
                                    let argument = match argument {
                                        Expr::Call(span, target, literals) => {
                                            let mut args = Vec::with_capacity(literals.len());
                                            for literal in literals {
                                                remaining = remaining.checked_sub(1).ok_or(
                                                    "native action expansion exceeds 65536 steps",
                                                )?;
                                                args.push(bind_value(index, literal)?.1);
                                            }
                                            Expr::Call(span, target, args)
                                        }
                                        literal => literal,
                                    };
                                    remaining = remaining
                                        .checked_sub(1)
                                        .ok_or("native action expansion exceeds 65536 steps")?;
                                    bound.push(bind_value(index, argument)?.1);
                                }
                                Expr::Call(span, target, bound)
                            }
                            literal => literal,
                        };
                        (index, value)
                    }
                    _ => {
                        return Err(
                            "constructor action scope requires closed constructor syntax".into(),
                        );
                    }
                }
            }
            Walk::Call(index, arity) => {
                let node = &program.nodes[index as usize];
                let pb::node::Kind::Call(call) = node.kind.as_ref().unwrap() else {
                    unreachable!()
                };
                let args = results.split_off(results.len() - arity);
                let span = native_span(program, node.span.as_ref(), native_spans)?;
                (index, Expr::Call(span, call.func.clone(), args))
            }
        };
        // Bind inert payloads at first demand too: shared String/compound-number
        // leaves must not be copied once per incoming edge. Existing nonclosed
        // Calls still end this memo's lifetime, so no reads cross a barrier.
        let (name, value) = bind_value(index, value)?;
        if closed.contains(&index) {
            memo.insert(index, name);
        } else {
            memo.clear();
        }
        results.push(value);
    }
    let span = native_span(program, action.span.as_ref(), native_spans)?;
    actions.push(match action.kind.as_ref().unwrap() {
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
        _ => return Err("constructor action scope requires Term or Set".into()),
    });
    Ok((actions, evaluations))
}

// One root has the same flush/recovery boundary as native eval_expr. Its memo
// and captured value never outlive this evaluation, including aggregate Extract.
fn eval_extract_root(
    graph: &mut EGraph,
    program: &pb::Program,
    index: u32,
    closed: Option<&HashSet<u32>>,
    execute: bool,
    native_spans: &NativeSpans,
) -> Result<Option<(ArcSort, Value)>, egglog::Error> {
    let error = egglog::Error::BackendError;
    let sort_name = node_sort(program, index).map_err(error)?;
    let sort = graph
        .get_sort_by_name(&sort_name)
        .cloned()
        .ok_or_else(|| error(format!("unknown extraction root sort {sort_name}")))?;
    let Some(closed) = closed else {
        let expr = expression(program, index, &mut HashSet::new(), native_spans).map_err(error)?;
        if execute {
            return graph.eval_expr(&expr).map(Some);
        }
        graph.typecheck_expr_with_bindings_and_output(&expr, &[], sort, egglog::Context::Full)?;
        return Ok(None);
    };
    let action = pb::Action {
        kind: Some(pb::action::Kind::Term(index)),
        span: program.nodes[index as usize].span,
    };
    let (mut actions, _) = constructor_dag_actions(
        program,
        &action,
        |name| graph.type_info().is_global(name),
        native_spans,
        closed,
    )
    .map_err(error)?;
    let Action::Expr(span, terminal) = actions.pop().expect("planned terminal") else {
        unreachable!("root plan has a Term terminal")
    };
    // Avoid both globals and the planner's local bindings.
    let mut next = actions.len();
    let name = loop {
        let candidate = format!("__egglog_proto_action_{next}");
        next += 1;
        if !graph.type_info().is_global(&candidate)
            && !graph.type_info().is_global(&format!("${candidate}"))
            && !actions
                .iter()
                .any(|action| matches!(action, Action::Let(_, name, _) if name == &candidate))
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

// Only Union locations are retained across direct commands. An admitted closed
// constructor DAG shares local results within this action only; other Calls
// are lowered anew on every demand. All effects retain one native rule boundary.
#[allow(clippy::too_many_arguments)]
fn eval_scoped_action(
    graph: &mut EGraph,
    program: &pb::Program,
    action: &pb::Action,
    values: &mut HashMap<u32, Value>,
    execute: bool,
    closed: Option<&HashSet<u32>>,
    observer: &mut dyn FnMut(ExecutionEvent<'_>),
    native_spans: &NativeSpans,
) -> Result<(), egglog::Error> {
    if let Some(closed) = closed {
        let (actions, _) = constructor_dag_actions(
            program,
            action,
            |name| graph.type_info().is_global(name),
            native_spans,
            closed,
        )
        .map_err(egglog::Error::BackendError)?;
        let (result, _) = graph.eval_scoped_actions_observed(
            &[],
            execute,
            |builder| {
                for action in actions {
                    builder.action(action)?;
                }
                Ok(())
            },
            observer,
        );
        return result;
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
    let mut slots: HashMap<_, _> = values
        .keys()
        .map(|index| (*index, format!("__egglog_proto_union_{index}")))
        .collect();
    let mut materialized: HashSet<_> = values.keys().copied().collect();
    let mut inputs = values
        .iter()
        .map(|(index, value)| Ok((slots[index].clone(), node_sort(program, *index)?, *value)))
        .collect::<Result<Vec<_>, String>>()
        .map_err(error)?;
    inputs.sort_by(|a, b| a.0.cmp(&b.0));
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
                            if matches!(value, Expr::Lit(..)) {
                                // Native syntax-sensitive primitives (notably
                                // function targets) require genuine literals.
                                // Inert literals have no evaluation to reorder.
                                results.push(value);
                                continue;
                            }
                            let name = format!("__egglog_proto_action_{temporary}");
                            temporary += 1;
                            builder.action(Action::Let(span.clone(), name.clone(), value))?;
                            results.push(Expr::Var(span, name));
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
                    results.push(Expr::Var(span, name));
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

// The logical graph remains unchanged. Native selection and response routes
// share this ordered traversal, deduplicating by rule occurrence, not label.
fn ruleset_selection(
    definitions: &pb::Program,
    roots: impl IntoIterator<Item = (usize, pb::ruleset_ref::Kind)>,
) -> Vec<(usize, pb::RuleAttribution)> {
    let mut seen_sets = HashSet::new();
    let mut seen_rules = HashSet::new();
    let mut result = Vec::new();
    for (root, reference) in roots {
        let mut pending = vec![(root, Vec::new())];
        while let Some((index, children)) = pending.pop() {
            if !seen_sets.insert(index) {
                continue;
            }
            match definitions.rulesets[index]
                .kind
                .as_ref()
                .expect("validated ruleset")
            {
                pb::ruleset::Kind::Rules(list) => {
                    for (ordinal, &rule) in list.rules.iter().enumerate() {
                        if !seen_rules.insert(rule) {
                            continue;
                        }
                        let authored = &definitions.rules[rule as usize];
                        result.push((
                            rule as usize,
                            pb::RuleAttribution {
                                root: Some(pb::RulesetRef {
                                    kind: Some(reference.clone()),
                                }),
                                children: children.clone(),
                                rule: ordinal as u32,
                                name: authored.name.clone(),
                                span: authored.span,
                            },
                        ));
                    }
                }
                pb::ruleset::Kind::Combined(combined) => {
                    for (position, child) in combined.rulesets.iter().enumerate().rev() {
                        let Some(pb::ruleset_ref::Kind::Index(child)) = child.kind else {
                            unreachable!("canonical reference")
                        };
                        let mut path = children.clone();
                        path.push(position as u32);
                        pending.push((child as usize, path));
                    }
                }
            }
        }
    }
    result
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
    rule: &pb::RuleDecl,
    ruleset: &str,
    name: &str,
    native_spans: &NativeSpans,
) -> Result<Command, String> {
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
        kind @ (pb::rule_decl::Kind::Rewrite(_) | pb::rule_decl::Kind::Birewrite(_)) => {
            // Native rewrite commands have no option fields. Keep this
            // adapter limit explicit rather than silently losing wire options.
            if eval_mode != ast::RuleEvalMode::Seminaive || rule.no_decomp || rule.include_subsumed
            {
                return Err("nondefault rewrite options require native rule expansion, which is not supported yet".into());
            }
            let (lhs, rhs, conditions, subsume, bidirectional) = match kind {
                pb::rule_decl::Kind::Rewrite(rewrite) => (
                    rewrite.lhs,
                    rewrite.rhs,
                    &rewrite.conditions,
                    rewrite.subsume,
                    false,
                ),
                pb::rule_decl::Kind::Birewrite(rewrite) => {
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
            let rewrite = ast::Rewrite {
                span,
                lhs: expression(program, lhs, &mut HashSet::new(), native_spans)?
                    .map_symbols(&mut |h| h, &mut |v: String| native_name("var", &v)),
                rhs: expression(program, rhs, &mut HashSet::new(), native_spans)?
                    .map_symbols(&mut |h| h, &mut |v: String| native_name("var", &v)),
                conditions: facts(program, conditions, native_spans)?,
                name: name.into(),
            };
            Ok(if bidirectional {
                Command::BiRewrite(ruleset.into(), rewrite)
            } else {
                Command::Rewrite(ruleset.into(), rewrite, subsume)
            })
        }
        pb::rule_decl::Kind::Rule(body) => {
            let mut bindings = HashMap::new();
            check_variables(program, &body.query, &mut bindings, true)?;
            let mut head = Vec::new();
            for (index, action) in body.head.iter().enumerate() {
                check_variables(program, &action_roots(action)?, &mut bindings, false)?;
                if let Some(pb::action::Kind::SetCost(set)) = &action.kind {
                    let span = native_span(program, action.span.as_ref(), native_spans)?;
                    let target = set.target.as_ref().ok_or("missing cost target")?;
                    let mut key = Vec::with_capacity(target.args.len());
                    for (argument, value) in target.args.iter().enumerate() {
                        // Authored variables are projected before these native
                        // temporaries are introduced, so even adversarial wire
                        // names cannot capture the retained row arguments.
                        let local = format!("__egglog_proto_cost_{index}_{argument}");
                        head.push(Action::Let(
                            span.clone(),
                            local.clone(),
                            expression(program, *value, &mut HashSet::new(), native_spans)?
                                .map_symbols(&mut |h| h, &mut |v: String| native_name("var", &v)),
                        ));
                        key.push(Expr::Var(span.clone(), local));
                    }
                    // Native actions retain this order: capture each argument
                    // once, materialize the constructor, then evaluate/write C.
                    // A failing cost leaves the completed target prefix intact.
                    head.push(Action::Expr(
                        span.clone(),
                        Expr::Call(span.clone(), target.func.clone(), key.clone()),
                    ));
                    head.push(Action::Set(
                        span,
                        crate::set_cost::get_cost_table_name(&target.func),
                        key,
                        expression(
                            program,
                            set.cost.ok_or("missing cost value")?,
                            &mut HashSet::new(),
                            native_spans,
                        )?
                        .map_symbols(&mut |h| h, &mut |v: String| native_name("var", &v)),
                    ));
                } else {
                    head.extend(
                        ast::GenericActions(lower_action(program, action, native_spans)?)
                            .map_symbols(&mut |h| h, &mut |v: String| native_name("var", &v))
                            .0,
                    );
                }
            }
            Ok(Command::Rule {
                rule: ast::Rule {
                    span,
                    head: ast::GenericActions(head),
                    body: facts(program, &body.query, native_spans)?,
                    name: name.into(),
                    ruleset: ruleset.into(),
                    eval_mode,
                    no_decomp: rule.no_decomp,
                    include_subsumed: rule.include_subsumed,
                },
            })
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
    response: &mut pb::RunProgramResponse,
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
    response: &mut pb::RunProgramResponse,
    encoded: &mut HashMap<pb::Node, u32>,
) -> Result<u32, egglog::Error> {
    let (graph, names) = (&session.graph, &session.names);
    let exact_value =
        encode_exact_number(terms, term, sort).map_err(egglog::Error::ExtractError)?;
    let custom = session
        .extension
        .as_ref()
        .map(|extension| extension.encode_custom_value(sort, terms, term))
        .transpose()
        .map_err(egglog::Error::ExtractError)?
        .flatten();
    let kind = match terms.get(term) {
        _ if custom.is_some() => pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: custom.map(pb::primitive_value::Value::Custom),
        }),
        _ if exact_value.is_some() => {
            pb::node::Kind::PrimitiveValue(pb::PrimitiveValue { value: exact_value })
        }
        _ if sort.clone().as_arc_any().is::<egglog::sort::FunctionSort>() => {
            let value = graph
                .value_to_container::<egglog::sort::FunctionContainer>(native_value)
                .ok_or_else(|| {
                    egglog::Error::ExtractError("missing native function value".into())
                })?;
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
        }
        Term::Lit(literal) => pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(match literal {
                Literal::Int(value) => pb::primitive_value::Value::I64(*value),
                Literal::Float(value) => pb::primitive_value::Value::F64Bits(value.0.to_bits()),
                Literal::String(value) => pb::primitive_value::Value::String(value.clone()),
                Literal::Bool(value) => pb::primitive_value::Value::Bool(*value),
                Literal::Unit => pb::primitive_value::Value::Unit(pb::Unit {}),
            }),
        }),
        Term::App(name, native_children) if name == "multiset-of" && sort.is_container_sort() => {
            let sort_id = encode_sort(graph, names, sort, response)?;
            if sort.value_type() != Some(std::any::TypeId::of::<egglog::sort::MultiSetContainer>())
                || !matches!(&response.sorts[sort_id as usize].kind, Some(pb::sort::Kind::Family(family)) if family.name == "MultiSet" && family.args.len() == 1)
                || native_children.len() != children.len()
                || sort.inner_sorts().len() != 1
            {
                return Err(egglog::Error::ExtractError(
                    "MultiSet term/sort/arity mismatch".into(),
                ));
            }
            let Some(pb::sort::Kind::Family(family)) = &response.sorts[sort_id as usize].kind
            else {
                unreachable!("validated MultiSet family")
            };
            if children.iter().any(|child| {
                response
                    .nodes
                    .get(*child as usize)
                    .is_none_or(|node| node.sort_id != family.args[0])
            }) {
                return Err(egglog::Error::ExtractError(
                    "MultiSet child sort mismatch".into(),
                ));
            }
            pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Multiset(pb::ValueList {
                    items: children.to_vec(),
                })),
            })
        }
        Term::App(name, _)
            if matches!(name.as_str(), "vec-of" | "vec-empty" | "set-of")
                && sort.is_container_sort() =>
        {
            let expected = if name == "set-of" { "Set" } else { "Vec" };
            let sort_id = encode_sort(graph, names, sort, response)?;
            let inner = sort.inner_sorts();
            if !matches!(&response.sorts[sort_id as usize].kind, Some(pb::sort::Kind::Family(family)) if family.name == expected && family.args.len() == 1)
                || inner.len() != 1
            {
                return Err(egglog::Error::ExtractError(format!(
                    "{expected} term/sort mismatch"
                )));
            }
            pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(if expected == "Set" {
                    pb::primitive_value::Value::Set(pb::ValueList {
                        items: children.to_vec(),
                    })
                } else {
                    pb::primitive_value::Value::Vec(pb::ValueList {
                        items: children.to_vec(),
                    })
                }),
            })
        }
        Term::App(name, native_children)
            if matches!(name.as_str(), "maybe-none" | "maybe-some") && sort.is_container_sort() =>
        {
            let sort_id = encode_sort(graph, names, sort, response)?;
            if sort.value_type() != Some(std::any::TypeId::of::<crate::maybe::MaybeContainer>())
                || !matches!(&response.sorts[sort_id as usize].kind, Some(pb::sort::Kind::Family(family)) if family.name == "Maybe" && family.args.len() == 1)
                || children.len() != usize::from(name == "maybe-some")
                || native_children.len() != children.len()
                || sort.inner_sorts().len() != 1
            {
                return Err(egglog::Error::ExtractError(
                    "Maybe term/sort/arity mismatch".into(),
                ));
            }
            pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Maybe(pb::MaybeValue {
                    value: children.first().copied(),
                })),
            })
        }
        Term::App(name, _) if name == "pair" && sort.is_container_sort() => {
            let sort_id = encode_sort(graph, names, sort, response)?;
            let inner = sort.inner_sorts();
            if !matches!(&response.sorts[sort_id as usize].kind, Some(pb::sort::Kind::Family(family)) if family.name == "Pair" && family.args.len() == 2)
                || children.len() != 2
                || inner.len() != 2
            {
                return Err(egglog::Error::ExtractError(
                    "Pair term/sort/arity mismatch".into(),
                ));
            }
            pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Pair(pb::PairValue {
                    first: Some(children[0]),
                    second: Some(children[1]),
                })),
            })
        }
        Term::App(name, _) if name == "map-of" && sort.is_container_sort() => {
            let sort_id = encode_sort(graph, names, sort, response)?;
            let inner = sort.inner_sorts();
            if !matches!(&response.sorts[sort_id as usize].kind, Some(pb::sort::Kind::Family(family)) if family.name == "Map" && family.args.len() == 2)
                || !children.len().is_multiple_of(2)
                || inner.len() != 2
            {
                return Err(egglog::Error::ExtractError(
                    "Map term/sort/arity mismatch".into(),
                ));
            }
            let entries = children
                .chunks_exact(2)
                .map(|fields| pb::MapEntry {
                    key: Some(fields[0]),
                    value: Some(fields[1]),
                })
                .collect();
            pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Map(pb::MapValue { entries })),
            })
        }
        Term::App(name, _) => {
            graph.get_function(name).ok_or_else(|| {
                egglog::Error::ExtractError(format!("unsupported extracted host value {name}"))
            })?;
            pb::node::Kind::Call(pb::Call {
                func: names.callables.get(name).unwrap_or(name).clone(),
                args: children.to_vec(),
            })
        }
        Term::Var(_) => {
            return Err(egglog::Error::ExtractError(
                "extracted variable is not closed data".into(),
            ));
        }
    };
    let sort_id = encode_sort(graph, names, sort, response)?;
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

// Native reconstruction is trusted only with its actual runtime value type and
// exact term shape. A nominal constructor with the same printed head is not a
// numeric value. No native primitive is executed to inspect these terms.
fn encode_exact_number(
    terms: &TermDag,
    term: TermId,
    sort: &ArcSort,
) -> Result<Option<pb::primitive_value::Value>, String> {
    fn bigint_text(terms: &TermDag, term: TermId) -> Result<String, String> {
        let Term::App(name, children) = terms.get(term) else {
            return Err("BigInt reconstruction is not an application".into());
        };
        if name != "from-string" || children.len() != 1 {
            return Err("invalid BigInt reconstruction shape".into());
        }
        let Term::Lit(Literal::String(text)) = terms.get(children[0]) else {
            return Err("BigInt reconstruction requires a string literal".into());
        };
        Ok(text.clone())
    }
    use pb::primitive_value::Value as V;
    let actual = sort.value_type();
    let value = if actual == Some(std::any::TypeId::of::<egglog::sort::Z>()) {
        V::BigInt(bigint_text(terms, term)?)
    } else if actual == Some(std::any::TypeId::of::<egglog::sort::Q>()) {
        let Term::App(name, children) = terms.get(term) else {
            return Err("BigRat reconstruction is not an application".into());
        };
        if name != "bigrat" || children.len() != 2 {
            return Err("invalid BigRat reconstruction shape".into());
        }
        V::BigRat(pb::BigRat {
            numerator: bigint_text(terms, children[0])?,
            denominator: bigint_text(terms, children[1])?,
        })
    } else if actual == Some(std::any::TypeId::of::<crate::rational::R>()) {
        let Term::App(name, children) = terms.get(term) else {
            return Err("Rational reconstruction is not an application".into());
        };
        if name != "rational" || children.len() != 2 {
            return Err("invalid Rational reconstruction shape".into());
        }
        let (Term::Lit(Literal::Int(numerator)), Term::Lit(Literal::Int(denominator))) =
            (terms.get(children[0]), terms.get(children[1]))
        else {
            return Err("Rational reconstruction requires i64 literals".into());
        };
        V::Rational(pb::Rational {
            numerator: *numerator,
            denominator: *denominator,
        })
    } else {
        return Ok(None);
    };
    validate_exact_number(&value)?;
    Ok(Some(value))
}

#[cfg(test)]
mod tests {
    use super::*;

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
        assert!(Arc::ptr_eq(&file, &span.file));
        assert!(Arc::ptr_eq(&file, &expression_span.file));
        let mut later = pb::Program {
            ir_version: 1,
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
                        kind: Some(pb::sort::Kind::Family(pb::HostSort {
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
                    kind: Some(pb::node::Kind::Call(pb::Call {
                        func: "egglog.core.fn.apply".into(),
                        args: vec![partial + 1, argument],
                    })),
                    ..Default::default()
                },
            ]);
            program.declarations.push(pb::Declaration {
                kind: Some(pb::declaration::Kind::Primitive(pb::Primitive {
                    name: "factory".into(),
                    inputs: vec![],
                    output: function,
                    body: Some(partial),
                })),
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
                            i32::from(pb::ErrorCode::EvaluationFailed)
                        );
                        assert_eq!(engine.graphs[&id].graph.num_tuples(), tuples);
                    }
                    let text = source::Renderer::default().render(&program).unwrap();
                    let response = run_host_default(&mut engine, id, program);
                    assert_eq!(response.error, None);
                    let Some(pb::command_output::Kind::Extraction(extraction)) =
                        &response.outputs[0].kind
                    else {
                        panic!("applied factory result")
                    };
                    let term = extraction.roots[0].variants[0].term;
                    let Some(pb::node::Kind::Call(call)) = &response.nodes[term as usize].kind
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
            session.definitions = session
                .graph
                .type_info()
                .portable_builtin_catalog()
                .unwrap()
                .definitions;
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
                let scalar = program.sorts.iter().position(|sort| matches!(&sort.kind, Some(pb::sort::Kind::Family(family)) if family.name == "i64")).unwrap() as u32;
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
                assert!(response.outputs.is_empty());
                assert!(response.ruleset_publication.unwrap().names.is_empty());
                assert!(response.profile.unwrap().maintenance.is_empty());
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
            // A genuine native projection Err may be retained despite successful
            // compilation. Full metadata resolution must still reject it on a
            // disposable compiler, not silently inspect only the live seed.
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
            let expected = staged
                .graph
                .type_info()
                .portable_builtin_catalog()
                .err()
                .unwrap();
            assert_eq!(
                staged
                    .resolve_cost_model(&model, pb::Extractor::Tree.into())
                    .err()
                    .unwrap()
                    .0
                    .message,
                expected
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
                        "zero" | "repeat" => pb::command::Kind::Repeat(pb::Repeat {
                            times: Some(u64::from(wrapper == "repeat")),
                            body: vec![child],
                            until: vec![],
                        }),
                        "saturate" => pb::command::Kind::Saturate(pb::Saturate {
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
                    assert!(response.outputs.is_empty());
                    assert!(response.ruleset_publication.unwrap().names.is_empty());
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
                    kind: Some(pb::command::Kind::Repeat(pb::Repeat {
                        times: Some(0),
                        until: vec![],
                        body: vec![pb::Command {
                            span: spans[2],
                            kind: Some(pb::command::Kind::Saturate(pb::Saturate {
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
        assert_eq!(engine.graphs[&id].definitions.ir_version, 1);
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
                ir_version: 1,
                ..Default::default()
            },
        );
        assert_eq!(empty.error, None);
        assert!(empty.outputs.is_empty());
        assert_eq!(engine.graphs[&id].definitions, definitions);
        program.declarations.clear();
        program.commands = commands;
        assert_eq!(run_host_default(&mut engine, id, program).error, None);
    }

    #[test]
    fn session_catalog_seed_keeps_live_errors_on_sort_free_requests() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        static BODIES: AtomicUsize = AtomicUsize::new(0);

        for corrupt in ["registry", "projection"] {
            let (mut engine, id) = host_default_engine();
            let initial = run_host_default(
                &mut engine,
                id,
                pb::Program {
                    ir_version: 1,
                    ..Default::default()
                },
            );
            assert_eq!(initial.error, None);
            assert_eq!(engine.graphs[&id].definitions.ir_version, 1);
            let graph = &mut engine.graphs.get_mut(&id).unwrap().graph;
            if corrupt == "registry" {
                graph.add_pure_primitive(ForeignPrimitive("egglog.core.i64.add".into()), None);
            } else {
                // Executable native bodies can retain a portable projection
                // error. No body is evaluated by registration or preparation.
                egglog::add_primitive!(
                    graph,
                    "unprojectable-body" = |value: i64| -> i64 {
                        {
                            BODIES.fetch_add(1, Ordering::SeqCst);
                            value
                        }
                    }
                );
                graph
                    .parse_and_run_program(
                        None,
                        "(primitive projection_missing (i64) i64 (unprojectable-body _0))",
                    )
                    .unwrap();
            }
            let expected = graph.type_info().portable_builtin_catalog().err().unwrap();
            let tuples = graph.num_tuples();
            let definitions = engine.graphs[&id].definitions.clone();
            let request = engine.graphs[&id].request;
            let response = run_host_default(
                &mut engine,
                id,
                pb::Program {
                    ir_version: 1,
                    ..Default::default()
                },
            );
            assert_eq!(response.error.unwrap().message, expected, "{corrupt}");
            assert!(response.outputs.is_empty());
            assert!(response.ruleset_publication.unwrap().names.is_empty());
            let profile = response.profile.unwrap();
            assert!(!profile.complete);
            assert!(profile.maintenance.is_empty());
            assert_eq!(engine.graphs[&id].request, request);
            assert_eq!(engine.graphs[&id].definitions, definitions);
            assert_eq!(engine.graphs[&id].graph.num_tuples(), tuples);
            assert_eq!(BODIES.load(Ordering::SeqCst), 0);
        }
    }

    #[test]
    fn session_catalog_seed_checks_dependent_primitives_across_scope_returns() {
        let (mut engine, id) = host_default_engine();
        let empty = pb::Program {
            ir_version: 1,
            ..Default::default()
        };
        let consistent = |engine: &mut Engine, id| {
            let session = engine.graphs.get_mut(&id).unwrap();
            assert!(session.graph.type_info().portable_builtin_catalog().is_ok());
            let definitions = session.definitions.clone();
            let response = run_host_default(engine, id, empty.clone());
            assert_eq!(response.error, None);
            assert!(response.outputs.is_empty());
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
            assert!(response.outputs.is_empty());
            assert!(response.ruleset_publication.unwrap().names.is_empty());
            assert_eq!(engine.graphs[&clone].request, request);
            assert_eq!(engine.graphs[&clone].definitions, before);
            consistent(&mut engine, clone);
            engine
                .return_to(
                    &pb::ReturnToEGraphRequest {
                        active_id: clone,
                        saved_id: id,
                    }
                    .encode_to_vec(),
                )
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
    fn inert_payload_dag_bindings_keep_first_demand_and_single_payload_ownership() {
        use pb::primitive_value::Value as V;
        let text = "shared payload".repeat(4096);
        let program = pb::Program {
            ir_version: 1,
            sorts: vec![
                pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "String".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
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
        let (actions, evaluated) = constructor_dag_actions(
            &program,
            &action,
            |_| false,
            &NativeSpans::default(),
            &[0, 1, 2].into_iter().collect(),
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
        let Action::Let(_, string, Expr::Lit(_, Literal::String(actual))) = &actions[5] else {
            panic!("one string binding")
        };
        assert_eq!(actual, &text);
        let Action::Let(_, _, Expr::Call(_, target, arguments)) = &actions[6] else {
            panic!("constructor binding")
        };
        assert_eq!(target, "Leaf");
        let variables: Vec<_> = arguments
            .iter()
            .map(|argument| {
                let Expr::Var(_, name) = argument else {
                    panic!("shared payloads use only local references")
                };
                name
            })
            .collect();
        assert_eq!(variables, [number, string, number, string]);
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
            matches!(&sort.kind, Some(pb::sort::Kind::Family(family)) if family.name == "Vec")
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
        // The same ordinary Call node is demanded twice, separated by a fresh
        // demand of the closed fragment. Neither the read nor its parent is CSE.
        demand.args[3] = demand.args[1];
        let (mut engine, id) = host_default_engine();
        let mut execution = program.clone();
        let prepared = engine.graphs[&id].prepare(&mut execution).unwrap();
        let closed = &prepared.context.constructor_dags[&vec![0]];
        assert!(closed.contains(&root));
        let Some(pb::command::Kind::Action(action)) = &execution.commands[0].kind else {
            unreachable!()
        };
        let (_, evaluations) = constructor_dag_actions(
            &execution,
            action,
            |_| false,
            &prepared.context.native_spans,
            closed,
        )
        .unwrap();
        for (name, expected) in [
            ("Branch", 32),
            ("egglog.experimental.size.nodes", 2),
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
            if name != "Branch" {
                assert!(nodes.is_disjoint(closed));
            }
        }
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
        // The generated mixed scope is invertible, not a public license to
        // retain reads or move them before their first demand.
        let parsed = crate::new_experimental_egraph()
            .parse_program(None, &text)
            .unwrap();
        for cache_read in [false, true] {
            let mut commands = parsed.clone();
            let actions = commands
                .iter_mut()
                .find_map(|command| match command {
                    Command::ActionScope(_, actions) => Some(&mut actions.0),
                    _ => None,
                })
                .unwrap();
            let demand = actions.len() - 2;
            let Action::Let(_, _, Expr::Call(_, _, args)) = &mut actions[demand] else {
                panic!("flat terminal call")
            };
            let (Expr::Var(_, first), Expr::Var(_, second)) = (&args[1], &args[3]) else {
                panic!("read aliases")
            };
            let (first, second) = (first.clone(), second.clone());
            if cache_read {
                args[3] = args[1].clone();
            }
            let index = actions.iter().position(|action|
                matches!(action, Action::Let(_, name, _) if name == if cache_read { &second } else { &first })
            ).unwrap();
            let read = actions.remove(index);
            if !cache_read {
                actions.insert(0, read);
            }
            let changed = commands
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("\n");
            let error = source::Source::new(None, &changed)
                .unwrap()
                .collect::<Result<Vec<_>, _>>()
                .unwrap_err();
            assert!(error.to_string().contains("scope"), "{error}");
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
            assert_eq!(error.code, i32::from(pb::ErrorCode::EvaluationFailed));
            assert_eq!(error.location.unwrap().path, [0]);
            assert!(response.outputs.is_empty());
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
                    assert_eq!(error.code, i32::from(pb::ErrorCode::EvaluationFailed));
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
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
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
                let Some(pb::command_output::Kind::Extraction(result)) = &response.outputs[0].kind
                else {
                    panic!("aggregate extraction")
                };
                assert_eq!(result.roots.len(), 2);
                for (root, expected) in result.roots.iter().zip([0, 17]) {
                    let [variant] = root.variants.as_slice() else {
                        panic!("one variant")
                    };
                    assert!(matches!(&response.nodes[variant.term as usize].kind,
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
            assert_eq!(error.code, i32::from(pb::ErrorCode::EvaluationFailed));
            assert_eq!(error.location.unwrap().path, [0]);
            assert!(response.outputs.is_empty());
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
                            kind: Some(pb::sort::Kind::Family(pb::HostSort {
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
                            ir_version: 1,
                            commands: vec![pb::Command {
                                kind: Some(pb::command::Kind::Freeze(pb::Freeze::default())),
                                ..Default::default()
                            }],
                            ..Default::default()
                        },
                    );
                    assert_eq!(frozen.error, None);
                    let Some(pb::command_output::Kind::Snapshot(snapshot)) =
                        &frozen.outputs[0].kind
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
                        ir_version: 1,
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
                    assert!(program.rules.is_empty());
                    let prepared = engine.graphs[&id].prepare(&mut program.clone());
                    assert_eq!(prepared.is_ok(), seminaive == Some(false));
                    let response = run_host_default(&mut engine, id, program);
                    let error = response.error.unwrap();
                    if seminaive == Some(false) {
                        // Compile admission above is independent of this later
                        // normal-mode proof extraction failure, not proof success.
                        assert_eq!(error.code, pb::ErrorCode::ProofFailed as i32);
                        assert_eq!(error.location.unwrap().path, vec![0]);
                        assert_eq!(
                            error.proof_failure.unwrap().reason,
                            pb::ProofFailureReason::ProofsNotEnabled as i32
                        );
                    } else {
                        assert_eq!(error.code, pb::ErrorCode::InvalidProgram as i32);
                        assert!(error.message.contains("egglog.experimental.size.tables"));
                        assert!(error.location.is_none());
                        assert!(error.proof_failure.is_none());
                        assert!(response.profile.unwrap().maintenance.is_empty());
                    }
                }
            }
        }
    }

    #[test]
    fn no_decomp_resources_use_live_state_and_scope_stamps() {
        use pb::configure_e_graph_resources_request::Operation;
        use std::sync::atomic::{AtomicUsize, Ordering};
        #[derive(Default)]
        struct CloneWitness(Arc<AtomicUsize>);
        impl Clone for CloneWitness {
            fn clone(&self) -> Self {
                self.0.fetch_add(1, Ordering::SeqCst);
                Self(self.0.clone())
            }
        }
        let (mut engine, id) = host_default_engine();
        let clones = engine
            .graphs
            .get_mut(&id)
            .unwrap()
            .graph
            .extension_state_or_default::<CloneWitness>()
            .0
            .clone();
        let symbols = engine.graphs[&id].graph.parser.symbol_gen.clone();
        let threads = engine.graphs[&id].graph.num_threads();
        let mut stamp = engine.graphs[&id].request;
        for operation in [
            Operation::Query(pb::Unit {}),
            Operation::NoDecomp(true),
            Operation::NoDecomp(true),
            Operation::Query(pb::Unit {}),
            Operation::NoDecomp(false),
        ] {
            let response = pb::ConfigureEGraphResourcesResponse::decode(
                engine
                    .configure_resources(
                        &pb::ConfigureEGraphResourcesRequest {
                            egraph_id: id,
                            operation: Some(operation),
                        }
                        .encode_to_vec(),
                    )
                    .unwrap()
                    .as_slice(),
            )
            .unwrap();
            if let Operation::NoDecomp(enabled) = operation {
                stamp += 1;
                assert_eq!(response.no_decomp, enabled);
            }
            assert_eq!(response.no_decomp, engine.graphs[&id].graph.no_decomp);
            assert_eq!(engine.graphs[&id].request, stamp);
            assert!(engine.graphs[&id].graph.seminaive);
            assert_eq!(engine.graphs[&id].graph.num_threads(), threads);
            assert_eq!(engine.graphs[&id].graph.parser.symbol_gen, symbols);
            assert_eq!(clones.load(Ordering::SeqCst), 0);
        }
        let mut unknown = pb::ConfigureEGraphResourcesRequest {
            egraph_id: id,
            operation: None,
        }
        .encode_to_vec();
        unknown.extend([0x30, 0x01]); // Unknown operation field6, never a query.
        for bytes in [
            vec![0xff],
            unknown,
            pb::ConfigureEGraphResourcesRequest {
                egraph_id: id,
                operation: None,
            }
            .encode_to_vec(),
            pb::ConfigureEGraphResourcesRequest {
                egraph_id: u64::MAX,
                operation: Some(Operation::NoDecomp(true)),
            }
            .encode_to_vec(),
        ] {
            assert!(engine.configure_resources(&bytes).is_err());
            assert!(!engine.graphs[&id].graph.no_decomp);
            assert_eq!(engine.graphs[&id].request, stamp);
            assert_eq!(clones.load(Ordering::SeqCst), 0);
        }
        for mutate_saved in [false, true] {
            let active = pb::CloneEGraphResponse::decode(
                engine
                    .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
                    .unwrap()
                    .as_slice(),
            )
            .unwrap()
            .egraph_id;
            let target = if mutate_saved { id } else { active };
            engine
                .configure_resources(
                    &pb::ConfigureEGraphResourcesRequest {
                        egraph_id: target,
                        // Saved false->false still makes the saved pair stale.
                        operation: Some(Operation::NoDecomp(!mutate_saved)),
                    }
                    .encode_to_vec(),
                )
                .unwrap();
            assert_eq!(engine.graphs[&active].graph.no_decomp, !mutate_saved);
            let before = engine.graphs[&id].request;
            engine
                .configure_resources(
                    &pb::ConfigureEGraphResourcesRequest {
                        egraph_id: id,
                        operation: Some(Operation::Query(pb::Unit {})),
                    }
                    .encode_to_vec(),
                )
                .unwrap();
            assert_eq!(engine.graphs[&id].request, before);
            let returned = engine.return_to(
                &pb::ReturnToEGraphRequest {
                    active_id: active,
                    saved_id: id,
                }
                .encode_to_vec(),
            );
            assert_eq!(returned.is_err(), mutate_saved);
            assert!(!engine.graphs[&id].graph.no_decomp);
            assert_eq!(engine.graphs.contains_key(&active), mutate_saved);
            if mutate_saved {
                engine
                    .destroy(&pb::DestroyEGraphRequest { egraph_id: active }.encode_to_vec())
                    .unwrap();
            }
        }
        engine.graphs.get_mut(&id).unwrap().request = u64::MAX;
        for enabled in [false, true] {
            assert!(
                engine
                    .configure_resources(
                        &pb::ConfigureEGraphResourcesRequest {
                            egraph_id: id,
                            operation: Some(Operation::NoDecomp(enabled)),
                        }
                        .encode_to_vec(),
                    )
                    .is_err()
            );
            assert!(!engine.graphs[&id].graph.no_decomp);
            assert_eq!(engine.graphs[&id].request, u64::MAX);
        }
        let response = pb::ConfigureEGraphResourcesResponse::decode(
            engine
                .configure_resources(
                    &pb::ConfigureEGraphResourcesRequest {
                        egraph_id: id,
                        operation: Some(Operation::Query(pb::Unit {})),
                    }
                    .encode_to_vec(),
                )
                .unwrap()
                .as_slice(),
        )
        .unwrap();
        assert!(!response.no_decomp);
    }

    #[test]
    fn scope_return_resource_stamps_and_overflow_are_pre_mutation() {
        use pb::configure_e_graph_resources_request::Operation;
        let mut engine = Engine::default();
        let id = pb::CreateEGraphResponse::decode(
            engine
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
                        threads: Some(1),
                        ..Default::default()
                    }
                    .encode_to_vec(),
                )
                .unwrap()
                .as_slice(),
        )
        .unwrap()
        .egraph_id;
        for operation in [
            Operation::Threads(1),
            Operation::ReportLevel(pb::ReportLevel::TimeOnly.into()),
        ] {
            let active = pb::CloneEGraphResponse::decode(
                engine
                    .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
                    .unwrap()
                    .as_slice(),
            )
            .unwrap()
            .egraph_id;
            let stamp = engine.graphs[&id].request;
            engine
                .configure_resources(
                    &pb::ConfigureEGraphResourcesRequest {
                        egraph_id: id,
                        operation: Some(Operation::Query(pb::Unit {})),
                    }
                    .encode_to_vec(),
                )
                .unwrap();
            for level in [0, 99, -1] {
                assert!(
                    engine
                        .configure_resources(
                            &pb::ConfigureEGraphResourcesRequest {
                                egraph_id: id,
                                operation: Some(Operation::ReportLevel(level))
                            }
                            .encode_to_vec()
                        )
                        .is_err()
                );
            }
            assert_eq!(engine.graphs[&id].request, stamp);
            engine
                .return_to(
                    &pb::ReturnToEGraphRequest {
                        active_id: active,
                        saved_id: id,
                    }
                    .encode_to_vec(),
                )
                .unwrap();
            let active = pb::CloneEGraphResponse::decode(
                engine
                    .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
                    .unwrap()
                    .as_slice(),
            )
            .unwrap()
            .egraph_id;
            // Successful equal-value setters still invalidate the saved pairing.
            engine
                .configure_resources(
                    &pb::ConfigureEGraphResourcesRequest {
                        egraph_id: id,
                        operation: Some(operation),
                    }
                    .encode_to_vec(),
                )
                .unwrap();
            assert_eq!(engine.graphs[&id].request, stamp + 1);
            assert!(
                engine
                    .return_to(
                        &pb::ReturnToEGraphRequest {
                            active_id: active,
                            saved_id: id
                        }
                        .encode_to_vec()
                    )
                    .is_err()
            );
            assert!(engine.graphs.contains_key(&active));
            assert_eq!(engine.graphs[&active].clone_parent, Some((id, stamp)));
        }
        for mutate_active in [true, false] {
            let active = pb::CloneEGraphResponse::decode(
                engine
                    .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
                    .unwrap()
                    .as_slice(),
            )
            .unwrap()
            .egraph_id;
            let stamp = engine.graphs[&id].request;
            let target = if mutate_active { active } else { id };
            let response = pb::RunProgramResponse::decode(
                engine
                    .run(
                        &pb::RunProgramRequest {
                            egraph_id: target,
                            program: Some(pb::Program {
                                ir_version: 1,
                                commands: vec![pb::Command {
                                    kind: Some(pb::command::Kind::Action(pb::Action {
                                        kind: Some(pb::action::Kind::Panic(
                                            "committed scope failure".into(),
                                        )),
                                        ..Default::default()
                                    })),
                                    ..Default::default()
                                }],
                                ..Default::default()
                            }),
                            profile: true,
                            include_run_reports: false,
                        }
                        .encode_to_vec(),
                    )
                    .unwrap()
                    .as_slice(),
            )
            .unwrap();
            assert_eq!(
                response.error.unwrap().code,
                i32::from(pb::ErrorCode::Panic)
            );
            assert_eq!(engine.graphs[&target].request, stamp + 1);
            let returned = engine.return_to(
                &pb::ReturnToEGraphRequest {
                    active_id: active,
                    saved_id: id,
                }
                .encode_to_vec(),
            );
            assert_eq!(returned.is_ok(), mutate_active);
            assert_eq!(engine.graphs[&id].request, stamp + 1);
            assert_eq!(engine.graphs.contains_key(&active), !mutate_active);
        }
        engine.graphs.get_mut(&id).unwrap().request = u64::MAX;
        let symbols = engine.graphs[&id].graph.parser.symbol_gen.clone();
        let handles = engine.graphs.len();
        for operation in [
            Operation::Threads(0),
            Operation::ReportLevel(pb::ReportLevel::WithPlan.into()),
        ] {
            let error = engine
                .configure_resources(
                    &pb::ConfigureEGraphResourcesRequest {
                        egraph_id: id,
                        operation: Some(operation),
                    }
                    .encode_to_vec(),
                )
                .unwrap_err();
            assert!(error.0.contains("identity space exhausted"));
            assert_eq!(engine.graphs[&id].request, u64::MAX);
            assert_eq!(engine.graphs[&id].graph.num_threads(), 1);
            assert_eq!(engine.graphs[&id].graph.parser.symbol_gen, symbols);
        }
        let invalid = engine
            .configure_resources(
                &pb::ConfigureEGraphResourcesRequest {
                    egraph_id: id,
                    operation: Some(Operation::ReportLevel(99)),
                }
                .encode_to_vec(),
            )
            .unwrap_err();
        assert!(invalid.0.contains("unknown report level"));
        engine
            .configure_resources(
                &pb::ConfigureEGraphResourcesRequest {
                    egraph_id: id,
                    operation: Some(Operation::Query(pb::Unit {})),
                }
                .encode_to_vec(),
            )
            .unwrap();
        let response = pb::RunProgramResponse::decode(
            engine
                .run(
                    &pb::RunProgramRequest {
                        egraph_id: id,
                        program: Some(pb::Program {
                            ir_version: 1,
                            ..Default::default()
                        }),
                        profile: true,
                        include_run_reports: false,
                    }
                    .encode_to_vec(),
                )
                .unwrap()
                .as_slice(),
        )
        .unwrap();
        assert!(
            response
                .error
                .unwrap()
                .message
                .contains("identity space exhausted")
        );
        assert_eq!(engine.graphs[&id].request, u64::MAX);
        assert_eq!(engine.graphs.len(), handles);
        // The rejected WithPlan setter must not change native collection level.
        let mut probe = engine.graphs[&id].graph.clone();
        let output = probe
            .parse_and_run_program(
                None,
                "(datatype M (N i64)) (rule ((N x)) ((N 2))) (N 1) (run 1)",
            )
            .unwrap();
        let egglog::CommandOutput::RunSchedule(report) = output.last().unwrap() else {
            panic!("missing native run report")
        };
        let reports: Vec<_> = report
            .iterations
            .iter()
            .flat_map(|i| i.rule_set_report.rule_reports.values())
            .flatten()
            .collect();
        assert!(!reports.is_empty());
        assert!(reports.iter().all(|rule| rule.plan.is_none()));
    }

    #[test]
    fn exact_number_reconstruction_requires_runtime_type_and_canonical_shape() {
        let mut graph = crate::new_experimental_egraph();
        graph.parse_and_run_program(None, "(sort Nominal)").unwrap();
        let mut terms = TermDag::default();
        let one = terms.lit(Literal::Int(1));
        let two = terms.lit(Literal::Int(2));
        let text = terms.lit(Literal::String("1".into()));
        let integer = terms.app("from-string".into(), vec![text]);
        let rational = terms.app("rational".into(), vec![one, two]);
        let bigrat = terms.app("bigrat".into(), vec![integer, integer]);
        for (name, term) in [
            ("BigInt", integer),
            ("BigRat", bigrat),
            ("Rational", rational),
        ] {
            let sort = graph.get_sort_by_name(name).unwrap();
            assert!(encode_exact_number(&terms, term, sort).unwrap().is_some());
            for foreign in ["Nominal", "i64", "String"] {
                assert_eq!(
                    encode_exact_number(&terms, term, graph.get_sort_by_name(foreign).unwrap())
                        .unwrap(),
                    None
                );
            }
            for bad in [
                one,
                text,
                terms.app("wrong-head".into(), vec![one, two]),
                terms.app(name.to_lowercase(), vec![]),
            ] {
                assert!(encode_exact_number(&terms, bad, sort).is_err());
            }
        }
        let rational_sort = graph.get_sort_by_name("Rational").unwrap();
        for children in [vec![one], vec![text, two], vec![two, two]] {
            let malformed = terms.app("rational".into(), children);
            assert!(encode_exact_number(&terms, malformed, rational_sort).is_err());
        }
        let noncanonical = terms.lit(Literal::String("01".into()));
        let malformed = terms.app("from-string".into(), vec![noncanonical]);
        assert!(
            encode_exact_number(&terms, malformed, graph.get_sort_by_name("BigInt").unwrap())
                .is_err()
        );
        let malformed = terms.app("bigrat".into(), vec![one, integer]);
        assert!(
            encode_exact_number(&terms, malformed, graph.get_sort_by_name("BigRat").unwrap())
                .is_err()
        );
    }

    static HOST_DEFAULT_BODY_CALLS: std::sync::atomic::AtomicUsize =
        std::sync::atomic::AtomicUsize::new(0);

    // These closure tests intentionally need a provider with no Python view.
    // Vec's real Python metadata is now frozen and cannot serve that fixture.
    fn host_default_engine() -> (Engine, u64) {
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

    fn run_host_default(
        engine: &mut Engine,
        egraph_id: u64,
        program: pb::Program,
    ) -> pb::RunProgramResponse {
        let bytes = engine
            .run(
                &pb::RunProgramRequest {
                    egraph_id,
                    program: Some(program),
                    profile: true,
                    include_run_reports: false,
                }
                .encode_to_vec(),
            )
            .unwrap();
        pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()
    }

    fn host_default_program(default_node: u32) -> pb::Program {
        let (mut fixture, id) = host_default_engine();
        let mut p = fixture
            .graphs
            .get_mut(&id)
            .unwrap()
            .graph
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions;
        let i64_sort = p.sorts.iter().position(|s| matches!(&s.kind, Some(pb::sort::Kind::Family(f)) if f.name == "i64" && f.args.is_empty())).unwrap() as u32;
        p.nodes = vec![
            pb::Node {
                sort_id: i64_sort,
                kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::I64(i64::MAX)),
                })),
                ..Default::default()
            },
            pb::Node {
                sort_id: i64_sort,
                kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::I64(1)),
                })),
                ..Default::default()
            },
            pb::Node {
                sort_id: i64_sort,
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "egglog.core.i64.add".into(),
                    args: vec![0, 1],
                })),
                ..Default::default()
            },
            pb::Node {
                sort_id: i64_sort,
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "current".into(),
                    args: vec![],
                })),
                ..Default::default()
            },
        ];
        p.declarations.push(pb::Declaration {
            kind: Some(pb::declaration::Kind::Function(pb::Function {
                name: "current".into(),
                inputs: vec![],
                output: i64_sort,
                merge: None,
            })),
            ..Default::default()
        });
        let get = p.declarations.iter_mut().find(|d| matches!(&d.kind, Some(pb::declaration::Kind::HostPrimitive(h)) if h.name == "test.default.identity")).unwrap();
        get.bindings.as_mut().unwrap().python = Some(pb::PythonBindings {
            views: vec![pb::PythonCallable {
                kind: pb::PythonCallKind::Function.into(),
                path: vec!["test".into(), "identity".into()],
                params: vec![pb::PythonParameter {
                    core_input: Some(0),
                    name: "value".into(),
                    default_expr: Some(default_node),
                }],
                ..Default::default()
            }],
        });
        p
    }

    #[test]
    fn host_binding_default_keeps_builtin_callee_context_without_evaluation() {
        let (mut engine, id) = host_default_engine();
        // MAX + 1 would fail if evaluated. It remains a valid closed template.
        assert_eq!(
            run_host_default(&mut engine, id, host_default_program(2)).error,
            None
        );
        assert_eq!(
            run_host_default(&mut engine, id, host_default_program(2)).error,
            None
        );
        assert!(
            run_host_default(&mut engine, id, host_default_program(1))
                .error
                .is_some()
        );
        assert_eq!(
            HOST_DEFAULT_BODY_CALLS.load(std::sync::atomic::Ordering::SeqCst),
            0
        );
    }

    #[test]
    fn host_binding_default_keeps_user_callee_context_without_evaluation() {
        let (mut engine, id) = host_default_engine();
        assert_eq!(
            run_host_default(&mut engine, id, host_default_program(3)).error,
            None
        );
        let mut resend = host_default_program(3);
        resend
            .declarations
            .retain(|d| !matches!(d.kind, Some(pb::declaration::Kind::Function(_))));
        assert_eq!(
            run_host_default(&mut engine, id, resend).error,
            None,
            "default can refer to an ambient installed table"
        );
        assert!(
            run_host_default(&mut engine, id, host_default_program(1))
                .error
                .is_some()
        );
        assert_eq!(
            HOST_DEFAULT_BODY_CALLS.load(std::sync::atomic::Ordering::SeqCst),
            0
        );
    }

    #[test]
    fn map_default_saved_closure_never_accumulates_execution_helpers() {
        let program = pb::Program {
            ir_version: 1,
            sorts: vec![
                pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "i64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "Map".into(),
                        args: vec![0, 0],
                    })),
                    ..Default::default()
                },
            ],
            nodes: vec![
                pb::Node {
                    sort_id: 0,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::I64(7)),
                    })),
                    ..Default::default()
                },
                pb::Node {
                    sort_id: 1,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Map(pb::MapValue {
                            entries: vec![
                                pb::MapEntry {
                                    key: Some(0),
                                    value: Some(0)
                                };
                                2
                            ],
                        })),
                    })),
                    ..Default::default()
                },
            ],
            declarations: vec![pb::Declaration {
                kind: Some(pb::declaration::Kind::Function(pb::Function {
                    name: "take_map".into(),
                    inputs: vec![pb::Arg {
                        name: "map".into(),
                        sort: 1,
                    }],
                    output: 0,
                    merge: None,
                })),
                bindings: Some(pb::CallableBindings {
                    python: Some(pb::PythonBindings {
                        views: vec![pb::PythonCallable {
                            kind: pb::PythonCallKind::Function.into(),
                            path: vec!["test".into(), "take_map".into()],
                            params: vec![pb::PythonParameter {
                                core_input: Some(0),
                                name: "map".into(),
                                default_expr: Some(1),
                            }],
                            ..Default::default()
                        }],
                    }),
                    ..Default::default()
                }),
                ..Default::default()
            }],
            ..Default::default()
        };
        let mut engine = Engine::default();
        let id = pb::CreateEGraphResponse::decode(
            engine
                .create(
                    &pb::CreateEGraphRequest {
                        sorts: vec![program.sorts[0].clone()],
                        options: Some(pb::EGraphOptions {
                            cost_sort: Some(0),
                            ..Default::default()
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
        let mut saved = None;
        for _ in 0..4 {
            let request = pb::RunProgramRequest {
                egraph_id: id,
                program: Some(program.clone()),
                profile: true,
                include_run_reports: false,
            };
            let response = pb::RunProgramResponse::decode(
                engine.run(&request.encode_to_vec()).unwrap().as_slice(),
            )
            .unwrap();
            assert_eq!(response.error, None);
            let definitions = &engine.graphs[&id].definitions;
            if let Some(previous) = &saved {
                assert_eq!(
                    definitions, previous,
                    "resupply must not grow the saved closure"
                );
            }
            assert_eq!(definitions.nodes.len(), 2);
            assert!(
                definitions
                    .nodes
                    .iter()
                    .all(|n| matches!(n.kind, Some(pb::node::Kind::PrimitiveValue(_))))
            );
            let map = definitions
                .nodes
                .iter()
                .find_map(|n| match &n.kind {
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Map(map)),
                    })) => Some(map),
                    _ => None,
                })
                .unwrap();
            assert_eq!(map.entries.len(), 2);
            assert_eq!(map.entries[0], map.entries[1]);
            assert_eq!(map.entries[0].key, map.entries[0].value);
            saved = Some(definitions.clone());
        }
    }

    #[test]
    fn extracted_node_interning_preserves_exact_float_bits() {
        let (mut engine, id) = host_default_engine();
        let session = engine.graphs.get_mut(&id).unwrap();
        let sort = session.graph.get_sort_by_name("f64").unwrap();
        let mut response = pb::RunProgramResponse::default();
        let mut encoded = HashMap::new();
        // Separate native term arenas avoid OrderedFloat's own NaN/zero equality;
        // this regression concerns only the emitted protobuf node key.
        for (bits, expected) in [
            (0, 0),
            (1u64 << 63, 1),
            (0x7ff8_0000_0000_0001, 2),
            (0x7ff8_0000_0000_0002, 3),
            (0x7ff8_0000_0000_0001, 2),
            (0, 0),
        ] {
            let mut terms = TermDag::default();
            let term = terms.lit(Literal::Float(f64::from_bits(bits).into()));
            let index = encode_term(
                session,
                &terms,
                term,
                sort,
                session.graph.base_to_value(0i64),
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
    fn map_encoder_rejects_odd_native_terms_and_wrong_container_provenance() {
        let (mut engine, id) = host_default_engine();
        let session = engine.graphs.get_mut(&id).unwrap();
        session
            .graph
            .parse_and_run_program(None, "(sort M (Map i64 i64)) (sort V (Vec i64))")
            .unwrap();
        let mut terms = TermDag::default();
        let child = terms.lit(Literal::Int(7));
        let odd = terms.app("map-of".into(), vec![child]);
        let even = terms.app("map-of".into(), vec![child, child]);
        for (term, sort) in [(odd, "M"), (even, "V")] {
            let mut response = pb::RunProgramResponse::default();
            let children = match terms.get(term) {
                Term::App(_, children) => vec![0; children.len()],
                _ => unreachable!(),
            };
            let result = encode_term(
                session,
                &terms,
                term,
                session.graph.get_sort_by_name(sort).unwrap(),
                session.graph.base_to_value(0i64),
                &children,
                &mut response,
                &mut HashMap::new(),
            );
            assert!(matches!(result, Err(egglog::Error::ExtractError(_))));
            assert!(response.nodes.is_empty());
        }
    }

    #[test]
    fn maybe_encoder_checks_exact_native_provenance_and_optional_arity() {
        let (mut engine, id) = host_default_engine();
        let session = engine.graphs.get_mut(&id).unwrap();
        session
            .graph
            .parse_and_run_program(None, "(sort M (Maybe i64)) (sort V (Vec i64))")
            .unwrap();
        let mut terms = TermDag::default();
        let child = terms.lit(Literal::Int(7));
        for (name, sort, children) in [
            ("maybe-none", "M", vec![child]),
            ("maybe-some", "M", vec![]),
            ("maybe-some", "M", vec![child, child]),
            ("maybe-none", "V", vec![]),
            ("maybe-some", "V", vec![child]),
            ("vec-of", "M", vec![child]),
        ] {
            let term = terms.app(name.into(), children);
            for observed_count in 0..=2 {
                let mut response = pb::RunProgramResponse::default();
                assert!(
                    encode_term(
                        session,
                        &terms,
                        term,
                        session.graph.get_sort_by_name(sort).unwrap(),
                        session.graph.base_to_value(0i64),
                        &vec![0; observed_count],
                        &mut response,
                        &mut HashMap::new(),
                    )
                    .is_err(),
                    "{name}/{sort}, observed {observed_count}"
                );
                assert!(response.nodes.is_empty());
            }
        }
    }

    #[test]
    fn set_codec_preserves_authored_children_and_checks_native_provenance() {
        let mut program = pb::Program {
            sorts: vec![
                pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "i64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
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
        let (mut engine, id) = host_default_engine();
        let session = engine.graphs.get_mut(&id).unwrap();
        session
            .graph
            .parse_and_run_program(None, "(sort S (Set i64)) (sort V (Vec i64))")
            .unwrap();
        let mut terms = TermDag::default();
        let child = terms.lit(Literal::Int(7));
        for (name, sort) in [("set-of", "V"), ("vec-of", "S")] {
            let term = terms.app(name.into(), vec![child]);
            let mut response = pb::RunProgramResponse::default();
            assert!(
                encode_term(
                    session,
                    &terms,
                    term,
                    session.graph.get_sort_by_name(sort).unwrap(),
                    session.graph.base_to_value(0i64),
                    &[0],
                    &mut response,
                    &mut HashMap::new(),
                )
                .is_err()
            );
            assert!(response.nodes.is_empty());
        }
    }

    #[test]
    fn creation_threads_match_native_policy_and_survive_clone() {
        for threads in [None, Some(0), Some(1), Some(2)] {
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
    fn resource_queries_and_updates_use_live_native_state_without_cloning() {
        use pb::configure_e_graph_resources_request::Operation;
        use std::sync::atomic::{AtomicUsize, Ordering};
        #[derive(Default)]
        struct CloneWitness(Arc<AtomicUsize>);
        impl Clone for CloneWitness {
            fn clone(&self) -> Self {
                self.0.fetch_add(1, Ordering::SeqCst);
                Self(self.0.clone())
            }
        }
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
                ..Default::default()
            }),
            ..Default::default()
        };
        let created = engine.create(&request.encode_to_vec()).unwrap();
        let id = pb::CreateEGraphResponse::decode(created.as_slice())
            .unwrap()
            .egraph_id;
        let clones = engine
            .graphs
            .get_mut(&id)
            .unwrap()
            .graph
            .extension_state_or_default::<CloneWitness>()
            .0
            .clone();
        let mut native = crate::new_experimental_egraph();
        for operation in [
            Operation::Query(pb::Unit {}),
            Operation::Threads(0),
            Operation::Threads(1),
            Operation::Threads(2),
            Operation::Query(pb::Unit {}),
        ] {
            let request = pb::ConfigureEGraphResourcesRequest {
                egraph_id: id,
                operation: Some(operation),
            };
            let result = engine.configure_resources(&request.encode_to_vec());
            if cfg!(target_family = "wasm") && matches!(operation, Operation::Threads(n) if n > 1) {
                assert!(result.is_err());
            } else {
                if let Operation::Threads(n) = operation {
                    native.set_num_threads(usize::try_from(n).unwrap());
                }
                let response =
                    pb::ConfigureEGraphResourcesResponse::decode(result.unwrap().as_slice())
                        .unwrap();
                assert_eq!(
                    response.threads,
                    u64::try_from(native.num_threads()).unwrap()
                );
                assert_eq!(engine.graphs[&id].graph.num_threads(), native.num_threads());
            }
            assert_eq!(
                clones.load(Ordering::SeqCst),
                0,
                "resource access must not clone native state/cursors"
            );
        }
        let previous = engine.graphs[&id].graph.num_threads();
        let mut unknown = pb::ConfigureEGraphResourcesRequest {
            egraph_id: id,
            operation: None,
        }
        .encode_to_vec();
        unknown.extend([0x22, 0x00]); // Unknown operation field4, not a query.
        for bytes in [
            vec![0xff],
            unknown,
            pb::ConfigureEGraphResourcesRequest {
                egraph_id: id,
                operation: None,
            }
            .encode_to_vec(),
            pb::ConfigureEGraphResourcesRequest {
                egraph_id: u64::MAX,
                operation: Some(Operation::Threads(1)),
            }
            .encode_to_vec(),
        ] {
            assert!(engine.configure_resources(&bytes).is_err());
            assert_eq!(engine.graphs[&id].graph.num_threads(), previous);
            assert_eq!(clones.load(Ordering::SeqCst), 0);
        }
        engine
            .destroy(&pb::DestroyEGraphRequest { egraph_id: id }.encode_to_vec())
            .unwrap();
        assert!(
            engine
                .configure_resources(
                    &pb::ConfigureEGraphResourcesRequest {
                        egraph_id: id,
                        operation: Some(Operation::Query(pb::Unit {}))
                    }
                    .encode_to_vec()
                )
                .is_err()
        );
    }

    #[test]
    fn unknown_creation_modes_do_not_allocate_handles() {
        let mut engine = Engine::default();
        for execution_mode in [99, -1] {
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
                    names: NativeNames::default(),
                    request: 0,
                    clone_parent: None,
                    rulesets: Vec::new(),
                    rules: Vec::new(),
                    sorts: HashSet::new(),
                    cost_models: HashMap::new(),
                };
                let mut program = pb::Program {
                    ir_version: 1,
                    sorts: vec![pb::Sort {
                        kind: Some(pb::sort::Kind::Family(pb::HostSort {
                            name: "i64".into(),
                            args: vec![],
                        })),
                        ..Default::default()
                    }],
                    declarations: vec![pb::Declaration {
                        kind: Some(if namespace == "sort" {
                            pb::declaration::Kind::EqSort(pb::EqSort {
                                name: "Public".into(),
                                ..Default::default()
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
    fn attribution_forest_preserves_first_routes_files_directions_and_request_locality() {
        let (mut engine, id) = host_default_engine();
        let mut program = inventory_fixture("(datatype E (A) (B)) (birewrite (A) (B))");
        program.commands.clear();
        program.rules[0].name = Some("both".into());
        for file in ["one.egg", "two.egg"] {
            program.files.push(pb::SourceFile {
                name: file.into(),
                contents: Some("x".into()),
            });
        }
        for file in [1, 2, 1] {
            program.rules.push(pb::RuleDecl {
                name: Some("same label".into()),
                span: Some(pb::Span {
                    file,
                    start: 0,
                    end: 1,
                }),
                eval_mode: pb::RuleEvalMode::Seminaive.into(),
                kind: Some(pb::rule_decl::Kind::Rule(pb::Rule::default())),
                ..Default::default()
            });
        }
        // A=[L,R], L=[D], R=[D,E], B=[E,F]; only A/B/empty are named.
        program.rulesets = [
            (Some("A"), true, vec![1, 2]),
            (None, true, vec![3]),
            (None, true, vec![3, 4]),
            (None, false, vec![1, 0]),
            (None, false, vec![0, 2]),
            (Some("B"), true, vec![4, 7]),
            (Some("empty"), false, vec![]),
            (None, false, vec![3]),
        ]
        .into_iter()
        .map(|(name, combined, entries)| pb::Ruleset {
            name: name.map(str::to_owned),
            kind: Some(if combined {
                pb::ruleset::Kind::Combined(pb::CombinedRuleset {
                    rulesets: entries
                        .into_iter()
                        .map(|index| pb::RulesetRef {
                            kind: Some(pb::ruleset_ref::Kind::Index(index)),
                        })
                        .collect(),
                })
            } else {
                pb::ruleset::Kind::Rules(pb::RuleList { rules: entries })
            }),
            ..Default::default()
        })
        .collect();
        program.rulesets.push(program.rulesets[0].clone());
        let routes: Vec<_> = [(0, "A"), (5, "B"), (6, "empty")]
            .into_iter()
            .map(|(index, name)| (index, pb::ruleset_ref::Kind::Name(name.into())))
            .chain(
                (0..program.rulesets.len())
                    .map(|index| (index, pb::ruleset_ref::Kind::Index(index as u32))),
            )
            .collect();
        let mut singleton_firsts = HashMap::new();
        for route in &routes {
            for (rule, origin) in ruleset_selection(&program, [route.clone()]) {
                singleton_firsts.entry(rule).or_insert(origin);
            }
        }
        let forest = ruleset_selection(&program, routes);
        assert_eq!(
            forest.iter().map(|(rule, _)| *rule).collect::<Vec<_>>(),
            [1, 0, 2, 3]
        );
        assert_eq!(
            forest.into_iter().collect::<HashMap<_, _>>(),
            singleton_firsts
        );
        let prepared = engine.graphs[&id].prepare(&mut program.clone()).unwrap();
        let mut expected = HashMap::new();
        for (rule, root, children, ordinal) in [
            (1, "A", vec![0, 0], 0),
            (0, "A", vec![0, 0], 1),
            (2, "A", vec![1, 1], 1),
            (3, "B", vec![1], 0),
        ] {
            let origin = pb::RuleAttribution {
                root: Some(pb::RulesetRef {
                    kind: Some(pb::ruleset_ref::Kind::Name(root.into())),
                }),
                children,
                rule: ordinal,
                name: program.rules[rule].name.clone(),
                span: program.rules[rule].span,
            };
            let directions: &[(_, _)] = if rule == 0 {
                &[
                    ("=>", pb::NativeRuleDirection::Forward),
                    ("<=", pb::NativeRuleDirection::Reverse),
                ]
            } else {
                &[("", pb::NativeRuleDirection::Single)]
            };
            for (suffix, direction) in directions {
                expected.insert(
                    format!("{}{suffix}", prepared.rules[rule]),
                    (origin.clone(), *direction),
                );
            }
        }
        assert_eq!(prepared.context.origins, expected);
        assert_eq!(prepared.context.files, program.files);
        // Every installation still needs its entire independent selector.
        let selectors: HashMap<_, _> = prepared
            .installations
            .iter()
            .filter_map(|installation| match &installation.command {
                Some(Command::UnstableCombinedRuleset(_, name, children)) => {
                    Some((name.clone(), children.clone()))
                }
                _ => None,
            })
            .collect();
        assert_eq!(
            selectors[&prepared.rulesets[0]],
            [1, 0, 2].map(|rule| format!("{}_holder", prepared.rules[rule]))
        );
        assert_eq!(
            selectors[&prepared.rulesets[5]],
            [0, 2, 3].map(|rule| format!("{}_holder", prepared.rules[rule]))
        );
        assert_eq!(
            run_host_default(&mut engine, id, program.clone()).error,
            None
        );

        let current = pb::SourceFile {
            name: "current.egg".into(),
            contents: Some("current".into()),
        };
        let prepared = engine.graphs[&id]
            .prepare(&mut pb::Program {
                ir_version: 1,
                files: vec![current.clone()],
                ..Default::default()
            })
            .unwrap();
        assert!(prepared.installations.is_empty());
        for (origin, _) in expected.values_mut() {
            if let Some(span) = &mut origin.span {
                span.file = match span.file {
                    0 => 2,
                    1 => 1,
                    2 => 3,
                    _ => unreachable!(),
                };
            }
        }
        assert_eq!(prepared.context.origins, expected);
        assert_eq!(
            prepared.context.files,
            [
                current,
                program.files[1].clone(),
                program.files[0].clone(),
                program.files[2].clone()
            ]
        );
    }

    #[test]
    fn attribution_forest_keeps_deep_shared_traversal_iterative() {
        let mut program = pb::Program {
            rules: vec![pb::RuleDecl::default()],
            rulesets: vec![pb::Ruleset {
                kind: Some(pb::ruleset::Kind::Rules(pb::RuleList { rules: vec![0] })),
                ..Default::default()
            }],
            ..Default::default()
        };
        for child in 0..1024 {
            program.rulesets.push(pb::Ruleset {
                kind: Some(pb::ruleset::Kind::Combined(pb::CombinedRuleset {
                    rulesets: vec![
                        pb::RulesetRef {
                            kind: Some(pb::ruleset_ref::Kind::Index(child))
                        };
                        2
                    ],
                })),
                ..Default::default()
            });
        }
        let selection = ruleset_selection(
            &program,
            (0..=1024)
                .rev()
                .map(|root| (root, pb::ruleset_ref::Kind::Index(root as u32))),
        );
        let [(rule, origin)] = selection.as_slice() else {
            panic!("{selection:?}")
        };
        assert_eq!(*rule, 0);
        assert_eq!(
            origin.root.as_ref().unwrap().kind,
            Some(pb::ruleset_ref::Kind::Index(1024))
        );
        assert_eq!(origin.children, vec![0; 1024]);
    }

    #[test]
    fn attribution_routes_skip_uninstalled_occurrences() {
        let (engine, id) = host_default_engine();
        let program = pb::Program {
            ir_version: 1,
            rules: vec![pb::RuleDecl {
                name: Some("shared".into()),
                kind: Some(pb::rule_decl::Kind::Rule(pb::Rule::default())),
                eval_mode: pb::RuleEvalMode::Seminaive.into(),
                ..Default::default()
            }],
            rulesets: (0..2)
                .map(|_| pb::Ruleset {
                    kind: Some(pb::ruleset::Kind::Rules(pb::RuleList { rules: vec![0] })),
                    ..Default::default()
                })
                .collect(),
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Run(pb::Run {
                    ruleset: Some(pb::RulesetRef {
                        kind: Some(pb::ruleset_ref::Kind::Index(1)),
                    }),
                    ..Default::default()
                })),
                ..Default::default()
            }],
            ..Default::default()
        };
        let prepared = engine.graphs[&id].prepare(&mut program.clone()).unwrap();
        assert!(prepared.rulesets[0].is_empty());
        assert!(!prepared.rulesets[1].is_empty());
        let (origin, direction) = &prepared.context.origins[&prepared.rules[0]];
        assert_eq!(
            origin.root.as_ref().unwrap().kind,
            Some(pb::ruleset_ref::Kind::Index(1))
        );
        assert!(origin.children.is_empty());
        assert_eq!(origin.rule, 0);
        assert_eq!(*direction, pb::NativeRuleDirection::Single);
    }

    #[test]
    fn shared_selectors_keep_exact_native_handles_and_first_inclusion_order() {
        let (mut engine, id) = host_default_engine();
        let mut program = pb::Program {
            ir_version: 1,
            rules: (0..2)
                .map(|_| pb::RuleDecl {
                    name: Some("equal label".into()),
                    eval_mode: pb::RuleEvalMode::Seminaive.into(),
                    kind: Some(pb::rule_decl::Kind::Rule(pb::Rule::default())),
                    ..Default::default()
                })
                .collect(),
            rulesets: vec![
                pb::Ruleset {
                    kind: Some(pb::ruleset::Kind::Rules(pb::RuleList { rules: vec![0, 0] })),
                    ..Default::default()
                },
                pb::Ruleset {
                    kind: Some(pb::ruleset::Kind::Rules(pb::RuleList { rules: vec![1] })),
                    ..Default::default()
                },
                pb::Ruleset {
                    name: Some("parent".into()),
                    kind: Some(pb::ruleset::Kind::Combined(pb::CombinedRuleset {
                        rulesets: [1, 0, 1, 0]
                            .into_iter()
                            .map(|i| pb::RulesetRef {
                                kind: Some(pb::ruleset_ref::Kind::Index(i)),
                            })
                            .collect(),
                    })),
                    ..Default::default()
                },
            ],
            commands: [2, 0, 1]
                .into_iter()
                .map(|i| pb::Command {
                    kind: Some(pb::command::Kind::Run(pb::Run {
                        ruleset: Some(pb::RulesetRef {
                            kind: Some(pb::ruleset_ref::Kind::Index(i)),
                        }),
                        ..Default::default()
                    })),
                    ..Default::default()
                })
                .collect(),
            ..Default::default()
        };
        let prepared = engine.graphs[&id].prepare(&mut program.clone()).unwrap();
        let native_rules = prepared.rules.clone();
        let native_sets = prepared.rulesets.clone();
        assert_ne!(native_rules[0], native_rules[1]);
        let selectors: HashMap<_, _> = prepared
            .installations
            .iter()
            .filter_map(|i| match &i.command {
                Some(Command::UnstableCombinedRuleset(_, name, children)) => {
                    Some((name.clone(), children.clone()))
                }
                _ => None,
            })
            .collect();
        assert_eq!(
            selectors[&native_sets[0]],
            [format!("{}_holder", native_rules[0])]
        );
        assert_eq!(
            selectors[&native_sets[1]],
            [format!("{}_holder", native_rules[1])]
        );
        assert_eq!(
            selectors[&native_sets[2]],
            [
                format!("{}_holder", native_rules[1]),
                format!("{}_holder", native_rules[0])
            ]
        );
        let first = run_host_default(&mut engine, id, program.clone());
        assert_eq!(first.error, None);
        assert_eq!(
            first
                .profile
                .unwrap()
                .runs
                .iter()
                .map(|r| r.rules.iter().map(|r| r.matches.unwrap()).sum::<u64>())
                .collect::<Vec<_>>(),
            [2, 0, 0]
        );
        assert_eq!(engine.graphs[&id].rules, native_rules);
        assert_eq!(engine.graphs[&id].rulesets, native_sets);
        assert!(
            engine.graphs[&id]
                .prepare(&mut program.clone())
                .unwrap()
                .installations
                .is_empty()
        );
        let before = engine.graphs[&id].definitions.clone();
        let serial = engine.graphs[&id].request;
        let mut conflict = program.clone();
        conflict.rules[0].no_decomp = true;
        conflict.declarations.push(pb::Declaration {
            kind: Some(pb::declaration::Kind::EqSort(pb::EqSort {
                name: "must-not-register".into(),
                ..Default::default()
            })),
            ..Default::default()
        });
        conflict.rulesets.push(pb::Ruleset {
            name: Some("must-not-publish".into()),
            kind: Some(pb::ruleset::Kind::Rules(pb::RuleList::default())),
            ..Default::default()
        });
        let rejected = run_host_default(&mut engine, id, conflict);
        assert!(rejected.error.is_some());
        assert!(rejected.outputs.is_empty());
        assert!(rejected.profile.unwrap().maintenance.is_empty());
        let session = &engine.graphs[&id];
        assert_eq!(session.definitions, before);
        assert_eq!(session.request, serial);
        assert_eq!(session.rules, native_rules);
        assert_eq!(session.rulesets, native_sets);
        assert!(
            session
                .graph
                .get_sort_by_name("must-not-register")
                .is_none()
        );
        // A new leaf around the locally matched shared rule gets a selector,
        // not another rule registration or cursor.
        program.rulesets.push(pb::Ruleset {
            name: Some("fresh-leaf".into()),
            kind: Some(pb::ruleset::Kind::Rules(pb::RuleList { rules: vec![0] })),
            ..Default::default()
        });
        program.commands[0] = pb::Command {
            kind: Some(pb::command::Kind::Run(pb::Run {
                ruleset: Some(pb::RulesetRef {
                    kind: Some(pb::ruleset_ref::Kind::Index(3)),
                }),
                ..Default::default()
            })),
            ..Default::default()
        };
        let prepared = engine.graphs[&id].prepare(&mut program.clone()).unwrap();
        assert_eq!(prepared.installations.len(), 1);
        assert!(
            matches!(&prepared.installations[0].command, Some(Command::UnstableCombinedRuleset(_, _, children)) if children == &[format!("{}_holder", native_rules[0])])
        );
        let response = run_host_default(&mut engine, id, program);
        assert_eq!(response.error, None);
        assert!(
            response
                .profile
                .unwrap()
                .runs
                .iter()
                .all(|r| r.rules.iter().all(|r| r.matches == Some(0)))
        );
        assert_eq!(engine.graphs[&id].rules, native_rules);
        assert_eq!(
            &engine.graphs[&id].rulesets[..native_sets.len()],
            native_sets
        );
    }

    #[test]
    fn native_fault_between_installation_steps_retains_only_completed_roots() {
        // Deliberate in-module fault injection into a genuinely prepared plan:
        // real native panic execution, not a public-request reachability claim.
        // The encoded trailing-maintenance-failure tests cover that boundary.
        for after_first_root in [false, true] {
            let (mut engine, id) = host_default_engine();
            let program = pb::Program {
                ir_version: 1,
                rules: vec![pb::RuleDecl {
                    eval_mode: pb::RuleEvalMode::Seminaive.into(),
                    kind: Some(pb::rule_decl::Kind::Rule(pb::Rule::default())),
                    ..Default::default()
                }],
                rulesets: ["first", "second"]
                    .into_iter()
                    .map(|name| pb::Ruleset {
                        name: Some(name.into()),
                        kind: Some(pb::ruleset::Kind::Rules(pb::RuleList { rules: vec![0] })),
                        ..Default::default()
                    })
                    .collect(),
                commands: (0..2)
                    .map(|i| pb::Command {
                        kind: Some(pb::command::Kind::Run(pb::Run {
                            ruleset: Some(pb::RulesetRef {
                                kind: Some(pb::ruleset_ref::Kind::Index(i)),
                            }),
                            ..Default::default()
                        })),
                        ..Default::default()
                    })
                    .collect(),
                ..Default::default()
            };
            let session = engine.graphs.get_mut(&id).unwrap();
            let mut prepared = session.prepare(&mut program.clone()).unwrap();
            let old_rule = prepared.rules[0].clone();
            let old_first = prepared.rulesets[0].clone();
            let boundary = prepared
                .installations
                .iter()
                .position(|i| i.ruleset == Some(usize::from(after_first_root)))
                .unwrap();
            let commands = session
                .graph
                .parse_program(None, "(panic \"installation fault\")")
                .unwrap();
            prepared.installations.splice(
                boundary..boundary,
                commands.into_iter().map(|command| Installation {
                    command: Some(command),
                    site: pb::maintenance_site::Target::Ruleset(0),
                    span: None,
                    declaration: None,
                    ruleset: None,
                }),
            );
            let mut response = pb::RunProgramResponse {
                profile: Some(pb::ProfileSummary::default()),
                ..Default::default()
            };
            assert!(session.install(prepared, &mut response).is_err());
            assert_eq!(
                response.ruleset_publication.unwrap().names,
                if after_first_root {
                    vec!["first"]
                } else {
                    vec![]
                }
            );
            assert!(response.outputs.is_empty());
            assert_eq!(
                session.definitions.rulesets.len(),
                usize::from(after_first_root)
            );
            assert_eq!(
                session.definitions.rules.len(),
                usize::from(after_first_root)
            );
            assert!(
                !session
                    .definitions
                    .rulesets
                    .iter()
                    .any(|s| s.name.as_deref() == Some("second"))
            );
            // The orphan native singleton survives, while only a completed
            // published root authorizes retaining its canonical occurrence.
            let orphan = session
                .graph
                .parse_program(None, &format!("(run {old_rule}_holder 1)"))
                .unwrap();
            session.graph.validate_program(orphan).unwrap();
            if after_first_root {
                assert_eq!(session.rules, [old_rule.clone()]);
                assert_eq!(session.rulesets, [old_first.clone()]);
                let consume = run_host_default(
                    &mut engine,
                    id,
                    pb::Program {
                        ir_version: 1,
                        commands: vec![pb::Command {
                            kind: Some(pb::command::Kind::Run(pb::Run {
                                ruleset: Some(pb::RulesetRef {
                                    kind: Some(pb::ruleset_ref::Kind::Name("first".into())),
                                }),
                                ..Default::default()
                            })),
                            ..Default::default()
                        }],
                        ..Default::default()
                    },
                );
                assert_eq!(consume.error, None);
                assert!(consume.ruleset_publication.unwrap().names.is_empty());
                assert_eq!(consume.profile.unwrap().runs[0].rules[0].matches, Some(1));
            }
            let retry = run_host_default(&mut engine, id, program);
            assert_eq!(retry.error, None);
            assert_eq!(
                retry.ruleset_publication.unwrap().names,
                ["first", "second"]
            );
            assert_eq!(
                retry
                    .profile
                    .unwrap()
                    .runs
                    .iter()
                    .map(|r| r.rules.iter().map(|r| r.matches.unwrap()).sum::<u64>())
                    .collect::<Vec<_>>(),
                [u64::from(!after_first_root), 0]
            );
            let session = &engine.graphs[&id];
            assert_eq!(session.rules[0] == old_rule, after_first_root);
            assert_eq!(session.rulesets[0] == old_first, after_first_root);
            assert_eq!(session.definitions.rules.len(), 1);
            assert_eq!(session.definitions.rulesets.len(), 2);
        }
    }

    #[test]
    fn failed_candidate_closure_is_not_a_transparent_later_dependency() {
        // Diagnostic for frontend retry policy, using an injected native
        // installation failure. This does not prove that this failure point is
        // reachable through the ordinary public typed API without injection.
        let (mut engine, id) = host_default_engine();
        let candidate = pb::Program {
            ir_version: 1,
            sorts: vec![pb::Sort {
                kind: Some(pb::sort::Kind::Eq("Item".into())),
                ..Default::default()
            }],
            declarations: vec![
                pb::Declaration {
                    kind: Some(pb::declaration::Kind::EqSort(pb::EqSort {
                        name: "Item".into(),
                        ..Default::default()
                    })),
                    ..Default::default()
                },
                pb::Declaration {
                    kind: Some(pb::declaration::Kind::Constructor(pb::Constructor {
                        name: "D".into(),
                        output: 0,
                        ..Default::default()
                    })),
                    ..Default::default()
                },
            ],
            nodes: vec![pb::Node {
                sort_id: 0,
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "D".into(),
                    args: vec![],
                })),
                ..Default::default()
            }],
            rules: vec![
                pb::RuleDecl {
                    eval_mode: pb::RuleEvalMode::Seminaive.into(),
                    kind: Some(pb::rule_decl::Kind::Rule(pb::Rule::default())),
                    ..Default::default()
                },
                pb::RuleDecl {
                    eval_mode: pb::RuleEvalMode::Seminaive.into(),
                    kind: Some(pb::rule_decl::Kind::Rule(pb::Rule {
                        query: vec![],
                        head: vec![pb::Action {
                            kind: Some(pb::action::Kind::Term(0)),
                            ..Default::default()
                        }],
                    })),
                    ..Default::default()
                },
            ],
            rulesets: vec![pb::Ruleset {
                name: Some("A".into()),
                kind: Some(pb::ruleset::Kind::Rules(pb::RuleList { rules: vec![0, 1] })),
                ..Default::default()
            }],
            ..Default::default()
        };
        let session = engine.graphs.get_mut(&id).unwrap();
        let mut prepared = session.prepare(&mut candidate.clone()).unwrap();
        let before_d = prepared
            .installations
            .iter()
            .position(|i| i.site == pb::maintenance_site::Target::Declaration(1))
            .unwrap();
        let panic = session
            .graph
            .parse_program(None, "(panic \"before D\")")
            .unwrap()
            .remove(0);
        prepared.installations.insert(
            before_d,
            Installation {
                command: Some(panic),
                site: pb::maintenance_site::Target::Declaration(1),
                span: None,
                declaration: None,
                ruleset: None,
            },
        );
        let mut response = pb::RunProgramResponse {
            profile: Some(pb::ProfileSummary::default()),
            ..Default::default()
        };
        assert!(session.install(prepared, &mut response).is_err());
        assert!(response.ruleset_publication.unwrap().names.is_empty());
        assert!(session.definitions.rulesets.is_empty());
        assert!(session.definitions.rules.is_empty());
        assert!(!session.definitions.declarations.iter().any(
            |d| matches!(&d.kind, Some(pb::declaration::Kind::Constructor(c)) if c.name == "D")
        ));

        let mut recovery = candidate.clone();
        recovery.rules.clear();
        recovery.rulesets.clear();
        recovery.nodes.clear();
        let Some(pb::declaration::Kind::Constructor(d)) = &mut recovery.declarations[1].kind else {
            unreachable!()
        };
        d.inputs.push(pb::Arg {
            sort: 0,
            ..Default::default()
        });
        assert_eq!(run_host_default(&mut engine, id, recovery).error, None);

        let standalone = pb::Program {
            ir_version: 1,
            rules: vec![candidate.rules[0].clone()], // r does not depend on D
            rulesets: vec![pb::Ruleset {
                name: Some("B".into()),
                kind: Some(pb::ruleset::Kind::Rules(pb::RuleList { rules: vec![0] })),
                ..Default::default()
            }],
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Run(pb::Run {
                    ruleset: Some(pb::RulesetRef {
                        kind: Some(pb::ruleset_ref::Kind::Name("B".into())),
                    }),
                    ..Default::default()
                })),
                ..Default::default()
            }],
            ..Default::default()
        };
        let valid = run_host_default(&mut engine, id, standalone.clone());
        assert_eq!(valid.error, None);
        assert_eq!(valid.ruleset_publication.unwrap().names, ["B"]);
        assert_eq!(valid.profile.unwrap().runs[0].rules[0].matches, Some(1));
        let before = engine.graphs[&id].definitions.clone();
        let mut full_retry = candidate;
        full_retry.rulesets.extend(standalone.rulesets.clone());
        full_retry.commands = standalone.commands.clone();
        let conflict = run_host_default(&mut engine, id, full_retry);
        assert!(conflict.ruleset_publication.unwrap().names.is_empty());
        assert!(
            conflict
                .error
                .unwrap()
                .message
                .contains("conflicting declaration D")
        );
        assert!(conflict.outputs.is_empty());
        assert!(conflict.profile.unwrap().maintenance.is_empty());
        assert_eq!(engine.graphs[&id].definitions, before);
        let valid = run_host_default(&mut engine, id, standalone);
        assert_eq!(valid.error, None);
        assert_eq!(valid.ruleset_publication.unwrap().names, ["B"]);
        assert_eq!(
            valid.profile.unwrap().runs[0]
                .rules
                .iter()
                .map(|r| r.matches.unwrap())
                .sum::<u64>(),
            0
        );
    }

    #[test]
    fn publication_receipt_tracks_first_name_completion_before_compaction() {
        // Inject before/after the metadata-only step, without asserting that
        // either fault is reachable through an ordinary public request.
        for complete_name in [false, true] {
            let (mut engine, id) = host_default_engine();
            let mut program = pb::Program {
                ir_version: 1,
                rulesets: vec![
                    pb::Ruleset {
                        kind: Some(pb::ruleset::Kind::Rules(pb::RuleList::default())),
                        ..Default::default()
                    },
                    pb::Ruleset {
                        name: Some("parent".into()),
                        kind: Some(pb::ruleset::Kind::Combined(pb::CombinedRuleset {
                            rulesets: vec![pb::RulesetRef {
                                kind: Some(pb::ruleset_ref::Kind::Index(0)),
                            }],
                        })),
                        ..Default::default()
                    },
                ],
                ..Default::default()
            };
            let initial = run_host_default(&mut engine, id, program.clone());
            assert_eq!(initial.error, None);
            assert_eq!(initial.ruleset_publication.unwrap().names, ["parent"]);
            let session = engine.graphs.get_mut(&id).unwrap();
            let native_sets = session.rulesets.clone();
            assert_eq!(native_sets.len(), 2);
            assert!(session.rules.is_empty());

            // A relocated empty child has no shared rule to witness identity.
            // The unused anonymous entry must disappear during compaction.
            program.rulesets.insert(0, program.rulesets[0].clone());
            program.rulesets[1].name = Some(String::new());
            let Some(pb::ruleset::Kind::Combined(parent)) = &mut program.rulesets[2].kind else {
                unreachable!()
            };
            parent.rulesets[0].kind = Some(pb::ruleset_ref::Kind::Index(1));
            program.rulesets.push(pb::Ruleset {
                name: Some("failed".into()),
                kind: Some(pb::ruleset::Kind::Rules(pb::RuleList::default())),
                ..Default::default()
            });
            let mut prepared = session.prepare(&mut program.clone()).unwrap();
            assert_eq!(prepared.installations.len(), 2);
            assert!(prepared.installations[0].command.is_none());
            let boundary = usize::from(complete_name);
            let command = session
                .graph
                .parse_program(None, "(panic \"installation fault\")")
                .unwrap()
                .remove(0);
            prepared.installations.insert(
                boundary,
                Installation {
                    command: Some(command),
                    site: pb::maintenance_site::Target::Ruleset(3),
                    span: None,
                    declaration: None,
                    ruleset: None,
                },
            );
            let mut response = pb::RunProgramResponse {
                profile: Some(pb::ProfileSummary::default()),
                ..Default::default()
            };
            assert!(session.install(prepared, &mut response).is_err());
            assert_eq!(
                response.ruleset_publication.unwrap().names,
                if complete_name {
                    vec!["", "parent"]
                } else {
                    vec!["parent"]
                }
            );
            assert_eq!(session.rulesets, native_sets);
            assert!(session.rules.is_empty());
            assert_eq!(session.definitions.rulesets.len(), 2);
            assert_eq!(
                session.definitions.rulesets[0].name.as_deref(),
                complete_name.then_some("")
            );
            assert_eq!(
                session.definitions.rulesets[1].name.as_deref(),
                Some("parent")
            );
            let retry = run_host_default(&mut engine, id, program);
            assert_eq!(retry.error, None);
            assert_eq!(
                retry.ruleset_publication.unwrap().names,
                ["", "failed", "parent"]
            );
            let session = &engine.graphs[&id];
            assert_eq!(&session.rulesets[..2], native_sets);
            assert_eq!(session.rulesets.len(), 3);
            assert!(session.rules.is_empty());
        }
    }

    #[test]
    fn first_name_enrichment_waits_for_its_installation_step() {
        let (mut engine, id) = host_default_engine();
        let session = engine.graphs.get_mut(&id).unwrap();
        session.graph = std::mem::take(&mut session.graph).with_proofs_enabled();
        session.mode = pb::ExecutionMode::Proofs;
        let commands = session.graph.parse_program(None, "(sort Foreign)").unwrap();
        let mut helpers = Vec::new();
        session
            .graph
            .run_program_observed(commands, &mut |_, _, _| {}, &mut |_, event| {
                if let ExecutionEvent::CommandCompleted {
                    origin: ExecutionOrigin::Internal,
                    command: ast::ResolvedNCommand::AddRuleset(_, name),
                } = event
                {
                    helpers.push(name.clone());
                }
            })
            .unwrap();
        let mut definitions = pb::Program {
            ir_version: 1,
            rulesets: vec![
                pb::Ruleset {
                    kind: Some(pb::ruleset::Kind::Rules(pb::RuleList::default())),
                    ..Default::default()
                },
                pb::Ruleset {
                    name: Some("parent".into()),
                    kind: Some(pb::ruleset::Kind::Combined(pb::CombinedRuleset {
                        rulesets: vec![pb::RulesetRef {
                            kind: Some(pb::ruleset_ref::Kind::Index(0)),
                        }],
                    })),
                    ..Default::default()
                },
            ],
            ..Default::default()
        };
        let initial = run_host_default(&mut engine, id, definitions.clone());
        assert_eq!(initial.error, None);
        assert_eq!(initial.ruleset_publication.unwrap().names, ["parent"]);
        let before = engine.graphs[&id].rulesets.clone();
        let session = engine.graphs.get_mut(&id).unwrap();
        let mut poison = session
            .graph
            .parse_program(None, "(rule () ((panic \"maintenance failed\")))")
            .unwrap();
        let Command::Rule { rule } = &mut poison[0] else {
            unreachable!()
        };
        rule.ruleset = helpers.last().unwrap().clone();
        session.graph.run_program(poison).unwrap();
        definitions.rulesets[0].name = Some("child".into());
        let Some(pb::ruleset::Kind::Combined(c)) = &mut definitions.rulesets[1].kind else {
            unreachable!()
        };
        c.rulesets[0].kind = Some(pb::ruleset_ref::Kind::Index(1));
        definitions.rulesets.insert(
            0,
            pb::Ruleset {
                name: Some("first".into()),
                kind: Some(pb::ruleset::Kind::Rules(pb::RuleList::default())),
                ..Default::default()
            },
        );
        let failed = run_host_default(&mut engine, id, definitions.clone());
        assert_eq!(
            failed.ruleset_publication.unwrap().names,
            ["first", "parent"]
        );
        assert_eq!(failed.error.unwrap().code, i32::from(pb::ErrorCode::Panic));
        let session = &engine.graphs[&id];
        assert!(
            session
                .definitions
                .rulesets
                .iter()
                .any(|s| s.name.as_deref() == Some("first"))
        );
        assert!(
            !session
                .definitions
                .rulesets
                .iter()
                .any(|s| s.name.as_deref() == Some("child"))
        );
        assert_eq!(&session.rulesets[..before.len()], before);
        // The failing seminaive helper has consumed its empty-query match.
        // Retry keeps the completed root and assigns the child without native work.
        let retried = run_host_default(&mut engine, id, definitions);
        assert_eq!(retried.error, None);
        assert_eq!(
            retried.ruleset_publication.unwrap().names,
            ["child", "first", "parent"]
        );
        assert!(retried.profile.unwrap().maintenance.is_empty());
        assert!(
            engine.graphs[&id]
                .definitions
                .rulesets
                .iter()
                .any(|s| s.name.as_deref() == Some("child"))
        );
    }

    #[test]
    fn definition_registration_and_requested_proof_survive_trailing_maintenance_failure() {
        let (mut engine, id) = host_default_engine();
        let session = engine.graphs.get_mut(&id).unwrap();
        session.graph = std::mem::take(&mut session.graph).with_proofs_enabled();
        session.mode = pb::ExecutionMode::Proofs;
        // Discover native identity through the observed registration event, not
        // a naming convention, before injecting the test-only failing helper.
        let commands = session.graph.parse_program(None, "(sort Foreign)").unwrap();
        let mut helpers = vec![];
        session
            .graph
            .run_program_observed(commands, &mut |_, _, _| {}, &mut |_, event| {
                if let ExecutionEvent::CommandCompleted {
                    origin: ExecutionOrigin::Internal,
                    command: ast::ResolvedNCommand::AddRuleset(_, name),
                } = event
                {
                    helpers.push(name.clone());
                }
            })
            .unwrap();
        assert_eq!(helpers.len(), 6);
        let mut phases = source::Source::new(None, "(datatype Num (N i64) (Goal i64)) (ruleset r) (rule ((N x)) ((Goal x)) :ruleset r) (N 1) (run r 1) (prove-exists Goal)").unwrap().peekable();
        let proof_program = loop {
            let program = phases.next().unwrap().unwrap();
            if phases.peek().is_none() {
                break program;
            }
            assert_eq!(run_host_default(&mut engine, id, program).error, None);
        };
        let session = engine.graphs.get_mut(&id).unwrap();
        let mut poison = session
            .graph
            .parse_program(None, "(rule () ((panic \"maintenance failed\")))")
            .unwrap();
        let Command::Rule { rule } = &mut poison[0] else {
            unreachable!()
        };
        rule.ruleset = helpers.last().unwrap().clone();
        session.graph.run_program(poison).unwrap();
        let baseline = session.clone();

        let mut definitions = pb::Program {
            ir_version: 1,
            files: vec![pb::SourceFile {
                name: "install.egg".into(),
                contents: Some("first second".into()),
            }],
            rulesets: vec![
                pb::Ruleset {
                    name: Some("first".into()),
                    span: Some(pb::Span {
                        file: 0,
                        start: 0,
                        end: 5,
                    }),
                    kind: Some(pb::ruleset::Kind::Rules(pb::RuleList::default())),
                    ..Default::default()
                },
                pb::Ruleset {
                    name: Some("second".into()),
                    span: Some(pb::Span {
                        file: 0,
                        start: 6,
                        end: 12,
                    }),
                    kind: Some(pb::ruleset::Kind::Rules(pb::RuleList::default())),
                    ..Default::default()
                },
            ],
            ..Default::default()
        };
        definitions.commands.push(pb::Command {
            kind: Some(pb::command::Kind::ProveExists(pb::ProveExists {
                constructor: "unknown".into(),
            })),
            ..Default::default()
        });
        let invalid = run_host_default(&mut engine, id, definitions.clone());
        assert!(invalid.ruleset_publication.unwrap().names.is_empty());
        assert_eq!(
            invalid.error.unwrap().code,
            i32::from(pb::ErrorCode::UnknownName)
        );
        assert!(invalid.profile.unwrap().maintenance.is_empty());
        assert!(
            !engine.graphs[&id]
                .definitions
                .rulesets
                .iter()
                .any(|s| s.name.as_deref() == Some("first"))
        );
        definitions.commands.clear();
        let failed = run_host_default(&mut engine, id, definitions.clone());
        assert_eq!(failed.ruleset_publication.unwrap().names, ["first"]);
        let error = failed.error.unwrap();
        assert_eq!(error.code, i32::from(pb::ErrorCode::Panic));
        assert_eq!(error.location, None);
        assert_eq!(error.span, definitions.rulesets[0].span);
        assert!(failed.outputs.is_empty());
        let profile = failed.profile.unwrap();
        assert!(!profile.complete && profile.runs.is_empty());
        assert_eq!(profile.maintenance.len(), 1);
        let maintenance = &profile.maintenance[0];
        assert_eq!(
            maintenance.site.as_ref().unwrap().target,
            Some(pb::maintenance_site::Target::Ruleset(0))
        );
        assert!(maintenance.invocations > 1); // includes successes before failure
        assert_eq!(
            (
                maintenance.search_and_apply_nanos,
                maintenance.merge_nanos,
                maintenance.rebuild_nanos
            ),
            (None, None, None)
        );
        let session = engine.graphs.get_mut(&id).unwrap();
        let first = session
            .definitions
            .rulesets
            .iter()
            .position(|s| s.name.as_deref() == Some("first"))
            .unwrap();
        assert!(
            !session
                .definitions
                .rulesets
                .iter()
                .any(|s| s.name.as_deref() == Some("second"))
        );
        let native_first = session.rulesets[first].clone();
        let commands = session
            .graph
            .parse_program(None, &format!("(run {native_first} 1)"))
            .unwrap();
        session.graph.validate_program(commands).unwrap();
        definitions.rulesets.remove(0);
        let prepared = session.prepare(&mut definitions).unwrap();
        assert_eq!(prepared.installations.len(), 1); // second was never recorded

        engine.graphs.insert(id, baseline.clone());
        let mut program = proof_program.clone();
        // Add a distinct native action after the proof, via the actual producer.
        let mut suffix =
            source::Source::new(None, "(datatype Num (N i64) (Goal i64)) (N 2)").unwrap();
        suffix.next().unwrap().unwrap();
        let suffix = suffix.next().unwrap().unwrap();
        let original_nodes = program.nodes.len() as u32;
        program
            .nodes
            .extend(suffix.nodes.iter().cloned().map(|mut node| {
                if let Some(pb::node::Kind::Call(call)) = &mut node.kind {
                    for index in &mut call.args {
                        *index += original_nodes;
                    }
                }
                node
            }));
        let mut action = suffix.commands[0].clone();
        let Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Term(index)),
            ..
        })) = &mut action.kind
        else {
            unreachable!()
        };
        *index += original_nodes;
        program.commands.push(action);
        let response = run_host_default(&mut engine, id, program);
        assert_eq!(
            response
                .error
                .as_ref()
                .unwrap()
                .location
                .as_ref()
                .unwrap()
                .path,
            [0]
        );
        assert_eq!(response.outputs.len(), 1);
        let Some(pb::command_output::Kind::Proof(proof)) = &response.outputs[0].kind else {
            panic!("completed anchor")
        };
        proof::validate(proof).unwrap();
        assert_eq!(response.profile.as_ref().unwrap().maintenance.len(), 1);
        assert_eq!(
            response.profile.as_ref().unwrap().maintenance[0].search_and_apply_nanos,
            None
        );
        let Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Term(index)),
            ..
        })) = suffix.commands[0].kind
        else {
            unreachable!()
        };
        let mut check = suffix;
        check.commands = vec![pb::Command {
            kind: Some(pb::command::Kind::Check(pb::Check { facts: vec![index] })),
            ..Default::default()
        }];
        check.declarations.clear();
        assert_eq!(
            run_host_default(&mut engine, id, check).error.unwrap().code,
            i32::from(pb::ErrorCode::CheckFailed)
        );
        // Injected lifecycle controls: no public access to private maintenance
        // rules is implied. A zero loop completes before trailing maintenance;
        // a caught inline-helper error must not leak its nested locator into
        // that later failure or into an outer ExpectFail.
        let mut loop_baseline = baseline.clone();
        let mut repeated_poison = loop_baseline
            .graph
            .parse_program(None, "(rule () ((panic \"maintenance failed\")) :naive)")
            .unwrap();
        let Command::Rule { rule } = &mut repeated_poison[0] else {
            unreachable!()
        };
        rule.ruleset = helpers.last().unwrap().clone();
        loop_baseline.graph.run_program(repeated_poison).unwrap();
        for case in [
            "loop-completed",
            "loop-caught",
            "loop-uncaught",
            "loop-double-fail",
        ] {
            engine.graphs.insert(id, loop_baseline.clone());
            let mut command = pb::Command {
                kind: Some(pb::command::Kind::Repeat(pb::Repeat {
                    times: Some(if case == "loop-completed" { 0 } else { 1 }),
                    body: vec![pb::Command {
                        kind: Some(pb::command::Kind::Run(pb::Run {
                            ruleset: Some(pb::RulesetRef {
                                kind: Some(pb::ruleset_ref::Kind::Name("r".into())),
                            }),
                            ..Default::default()
                        })),
                        ..Default::default()
                    }],
                    ..Default::default()
                })),
                ..Default::default()
            };
            for _ in 0..match case {
                "loop-caught" => 1,
                "loop-double-fail" => 2,
                _ => 0,
            } {
                command = pb::Command {
                    kind: Some(pb::command::Kind::Fail(Box::new(command))),
                    ..Default::default()
                };
            }
            let response = run_host_default(
                &mut engine,
                id,
                pb::Program {
                    ir_version: 1,
                    commands: vec![command],
                    ..Default::default()
                },
            );
            let error = response
                .error
                .as_ref()
                .unwrap_or_else(|| panic!("{case}: {response:?}"));
            let location = error.location.as_ref().unwrap();
            if case == "loop-uncaught" {
                assert_eq!(location.path, [0, 0]);
                assert_eq!(location.iterations, [0]);
            } else {
                assert_eq!(location.path, [0]);
                assert!(location.iterations.is_empty());
            }
            assert_eq!(
                error.message.contains("maintenance failed"),
                case != "loop-double-fail"
            );
            assert_eq!(
                response.outputs.len(),
                usize::from(case == "loop-completed")
            );
            if case == "loop-completed" {
                let Some(pb::command_output::Kind::Loop(outcome)) = &response.outputs[0].kind
                else {
                    panic!("completed loop output was lost")
                };
                assert_eq!(outcome.iterations, 0);
                assert_eq!(
                    outcome.termination,
                    Some(pb::TerminationReason::CountReached.into())
                );
            }
        }
        // This is an injected lifecycle witness, not public access to private
        // maintenance rules. Native Fail must keep the anchor/helper boundary.
        for case in ["caught-anchor", "successful-anchor", "prerequisite"] {
            engine.graphs.insert(id, baseline.clone());
            let mut program = proof_program.clone();
            let integer = program.sorts.iter().position(|sort| matches!(
                &sort.kind, Some(pb::sort::Kind::Family(f)) if f.name == "i64" && f.args.is_empty()
            )).unwrap() as u32;
            let first = program.nodes.len() as u32;
            for value in [0, 1] {
                program.nodes.push(pb::Node {
                    sort_id: integer,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::I64(value)),
                    })),
                    ..Default::default()
                });
            }
            program.nodes.push(pb::Node {
                sort_id: integer,
                kind: Some(pb::node::Kind::Union(pb::Union {
                    members: vec![first, first + 1],
                })),
                ..Default::default()
            });
            let child = pb::Command {
                kind: Some(if case == "prerequisite" {
                    pb::command::Kind::Prove(pb::Prove { facts: vec![] })
                } else {
                    pb::command::Kind::Check(pb::Check {
                        facts: if case == "caught-anchor" {
                            vec![first + 2]
                        } else {
                            vec![]
                        },
                    })
                }),
                ..Default::default()
            };
            program.commands = vec![pb::Command {
                kind: Some(pb::command::Kind::Fail(Box::new(child))),
                ..Default::default()
            }];
            let response = run_host_default(&mut engine, id, program);
            let error = response.error.unwrap();
            assert_eq!(
                error.code,
                i32::from(if case == "successful-anchor" {
                    pb::ErrorCode::EvaluationFailed
                } else {
                    pb::ErrorCode::Panic
                })
            );
            assert_eq!(error.location.as_ref().unwrap().path, [0]);
            assert!(response.outputs.is_empty());
            assert_eq!(
                error.message.contains("maintenance failed"),
                case != "successful-anchor",
                "{case}: {error:?}"
            );
            assert_eq!(
                error.message.contains("Command should have failed"),
                case == "successful-anchor",
                "{case}: {error:?}"
            );
        }
        engine
            .destroy(&pb::DestroyEGraphRequest { egraph_id: id }.encode_to_vec())
            .unwrap();
        proof::validate(proof).unwrap();
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
            session.definitions = session
                .graph
                .type_info()
                .portable_builtin_catalog()
                .unwrap()
                .definitions;
            let mut program = pb::Program {
                ir_version: 1,
                sorts: vec![
                    pb::Sort {
                        kind: Some(pb::sort::Kind::Family(pb::HostSort {
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
                            ..Default::default()
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
            ungrounded.rules.push(pb::RuleDecl {
                kind: Some(pb::rule_decl::Kind::Rule(pb::Rule {
                    query: vec![5],
                    head: vec![pb::Action {
                        kind: Some(pb::action::Kind::Term(6)),
                        ..Default::default()
                    }],
                })),
                eval_mode: pb::RuleEvalMode::Seminaive.into(),
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
    fn source_render_and_wire_export_agree_under_exact_authored_rule_mapping() {
        let (mut engine, id) = host_default_engine();
        let session = engine.graphs.get_mut(&id).unwrap();
        session.graph = std::mem::take(&mut session.graph).with_proofs_enabled();
        session.mode = pb::ExecutionMode::Proofs;
        let mut native = crate::new_experimental_egraph().with_proofs_enabled();
        let mut renderer = source::Renderer::default();
        let mut names = HashMap::new();
        let mut callable_names = HashMap::new();
        let mut emitted_names = HashSet::new();
        let mut compared = 0;
        let mut mapped_heads = 0;
        for (request, phase) in source::Source::new(None, "(datatype Num (N i64) (Goal i64)) (ruleset r) (rule ((N x)) ((Goal x)) :ruleset r :name \"derive\") (N 1) (run r 1) (prove-exists Goal)").unwrap().enumerate() {
            let program = phase.unwrap();
            for ruleset in &program.rulesets {
                let Some(pb::ruleset::Kind::Rules(rules)) = &ruleset.kind else { unreachable!() };
                for index in &rules.rules {
                    names.insert(format!("__protobuf_{}_rule_{index}", request + 1), program.rules[*index as usize].name.clone().unwrap());
                }
            }
            let text = renderer.render(&program).unwrap();
            let commands = native.parse_program(None, &text).unwrap();
            let constructors: Vec<_> = program.declarations.iter().filter_map(|declaration| {
                match &declaration.kind {
                    Some(pb::declaration::Kind::Constructor(constructor)) => Some(constructor),
                    _ => None,
                }
            }).collect();
            let emitted: Vec<_> = commands.iter().filter_map(|command| {
                match command {
                    Command::Constructor { name, schema, .. } => Some((name, schema)),
                    _ => None,
                }
            }).collect();
            assert_eq!(constructors.len(), emitted.len());
            for (constructor, (name, schema)) in constructors.into_iter().zip(emitted) {
                assert_eq!(constructor.inputs.len(), schema.input.len());
                assert!(emitted_names.insert(name.clone()));
                assert!(callable_names.insert(native_name("call", &constructor.name), name.clone()).is_none());
            }
            let mut native_proof = None;
            native.run_program_observed(commands, &mut |_, origin, output| {
                if origin == ExecutionOrigin::Requested && let egglog::CommandOutput::ProveExists { proof_store, proof_id } = output {
                    native_proof = Some(proof::export(&proof_store, proof_id).unwrap());
                }
            }, &mut |_, _| {}).unwrap();
            let response = run_host_default(&mut engine, id, program);
            assert_eq!(response.error, None);
            if let Some(native_proof) = native_proof {
                let Some(pb::command_output::Kind::Proof(mut wire)) = response.outputs.into_iter().next().unwrap().kind else { unreachable!() };
                for term in &mut wire.terms {
                    if let Some(pb::proof_term::Kind::App(app)) = &mut term.kind
                        && let Some(name) = callable_names.get(&app.head)
                    {
                        app.head = name.clone();
                        mapped_heads += 1;
                    }
                }
                for step in &mut wire.proofs {
                    if let Some(pb::proof_step::Justification::Rule(rule)) = &mut step.justification {
                        rule.name = names.get(&rule.name).expect("exact published occurrence").clone();
                    }
                }
                assert_eq!(wire, native_proof); // every term, edge, literal and shared local ID
                compared += 1;
            }
        }
        assert!(compared > 0);
        assert!(mapped_heads > 0);
    }

    #[test]
    fn leaf_summary_preserves_measured_zero_and_unavailable_totals_independently() {
        let mut report = egglog_reports::RunReport::default();
        let mut authored = LeafSummary::default();
        let mut maintenance = LeafSummary::default();
        authored.invocations += 1;
        authored.finish(Ok(&report), true);
        assert_eq!(authored.nanos, [Some(0); 3]);
        report
            .search_and_apply_time_per_ruleset
            .insert("r".into(), std::time::Duration::from_nanos(7));
        report
            .merge_time_per_ruleset
            .insert("r".into(), std::time::Duration::from_nanos(11));
        report
            .rebuild_time_per_ruleset
            .insert("r".into(), std::time::Duration::from_nanos(13));
        for _ in 0..2 {
            maintenance.invocations += 1;
            maintenance.finish(Ok(&report), false);
        }
        assert_eq!(maintenance.nanos, [Some(14), Some(22), Some(26)]);
        maintenance.invocations += 1;
        maintenance.finish(
            Err(&egglog::Error::BackendError("failed leaf".into())),
            false,
        );
        maintenance.invocations += 1;
        maintenance.finish(Ok(&report), false);
        assert_eq!(maintenance.invocations, 4);
        assert_eq!(maintenance.nanos, [None; 3]);
        assert_eq!(authored.nanos, [Some(0); 3]);
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
        program.declarations.insert(
            0,
            pb::Declaration {
                kind: Some(pb::declaration::Kind::HostSortFamily(pb::HostSortFamily {
                    name: "i64".into(),
                    ..Default::default()
                })),
                ..Default::default()
            },
        );
        program.declarations.push(program.declarations[2].clone()); // compatible resupply
        let i64_sort = program
            .sorts
            .iter()
            .position(|s| matches!(&s.kind, Some(pb::sort::Kind::Family(f)) if f.name == "i64"))
            .unwrap() as u32;
        let vector = program.sorts.len() as u32;
        program.sorts.push(pb::Sort {
            kind: Some(pb::sort::Kind::Family(pb::HostSort {
                name: "Vec".into(),
                args: vec![i64_sort],
            })),
            ..Default::default()
        });
        program.rulesets.push(pb::Ruleset {
            name: Some("r".into()),
            kind: Some(pb::ruleset::Kind::Rules(pb::RuleList::default())),
            ..Default::default()
        });
        let prepared = session.prepare(&mut program.clone()).unwrap();
        assert_eq!(
            prepared
                .installations
                .iter()
                .map(|i| i.site.clone())
                .collect::<Vec<_>>(),
            [
                pb::maintenance_site::Target::Declaration(1),
                pb::maintenance_site::Target::Sort(vector),
                pb::maintenance_site::Target::Declaration(2),
                pb::maintenance_site::Target::Ruleset(0),
            ]
        );
        let installed = run_host_default(&mut engine, id, program.clone());
        assert_eq!(installed.error, None);
        assert!(installed.outputs.is_empty());
        let maintenance = installed.profile.unwrap().maintenance;
        assert_eq!(maintenance.len(), 1); // native Sort/Function registration has no run leaf
        assert_eq!(
            maintenance[0].site.as_ref().unwrap().target,
            Some(pb::maintenance_site::Target::Ruleset(0))
        );
        program.rulesets.clear();
        let cloned = engine
            .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
            .unwrap();
        let clone = pb::CloneEGraphResponse::decode(cloned.as_slice())
            .unwrap()
            .egraph_id;
        for id in [id, clone] {
            let response = run_host_default(&mut engine, id, program.clone());
            assert_eq!(response.error, None);
            assert!(response.profile.unwrap().maintenance.is_empty());
        }
    }

    // Compose compile-only Source phases into one request without rebasing their
    // cumulative node/sort arenas or changing command batching.
    fn inventory_fixture(source: &str) -> pb::Program {
        let mut declarations = vec![];
        let mut commands = vec![];
        let mut rulesets = vec![];
        let mut program = pb::Program::default();
        for phase in source::Source::new(Some("fixture.egg".into()), source).unwrap() {
            program = phase.unwrap();
            declarations.append(&mut program.declarations);
            commands.append(&mut program.commands);
            rulesets.append(&mut program.rulesets);
        }
        program.declarations = declarations;
        program.commands = commands;
        program.rulesets = rulesets;
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
            kind: Some(pb::command::Kind::Repeat(pb::Repeat {
                times: Some(3),
                until: vec![],
                body: vec![pb::Command {
                    kind: Some(pb::command::Kind::Repeat(pb::Repeat {
                        times: Some(2),
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
            matches!(&response.outputs[0].kind, Some(pb::command_output::Kind::Loop(outcome)) if outcome.iterations == 3 && outcome.updated)
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
    fn byte_class_inventory_clone_return_and_failure_prefix() {
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
            .return_to(
                &pb::ReturnToEGraphRequest {
                    active_id: child,
                    saved_id: id,
                }
                .encode_to_vec(),
            )
            .unwrap();
        pb::ReturnToEGraphResponse::decode(response.as_slice()).unwrap();
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
        assert!(response.outputs.is_empty());
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
                if reused {
                    program
                        .commands
                        .push(program.commands[failure_index].clone());
                }
                let response = run_host_default(&mut engine, id, program);
                let error = response.error.unwrap();
                assert_eq!(error.code, i32::from(pb::ErrorCode::EvaluationFailed));
                assert_eq!(error.location.unwrap().path, [failure_index as u32]);
                assert_eq!(error.span, span);
                assert!(response.outputs.is_empty());
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
        program.rules.clear();
        program.rulesets.clear();
        let Some(pb::command::Kind::Run(run)) = &mut program.commands[1].kind else {
            panic!("fixture Run")
        };
        run.ruleset = Some(pb::RulesetRef {
            kind: Some(pb::ruleset_ref::Kind::Name("derive".into())),
        });
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
        assert_ne!(action_span, command_span);
        // Force first-use retention; the duplicate and After marker must remain
        // unentered after the first Union's later member fails.
        program.commands.insert(4, program.commands[3].clone());
        let response = pb::RunProgramResponse::decode(
            engine
                .run(
                    &pb::RunProgramRequest {
                        egraph_id: id,
                        program: Some(program),
                        profile: true,
                        include_run_reports: true,
                    }
                    .encode_to_vec(),
                )
                .unwrap()
                .as_slice(),
        )
        .unwrap();
        let error = response.error.as_ref().unwrap();
        assert_eq!(error.code, i32::from(pb::ErrorCode::EvaluationFailed));
        assert_eq!(error.location.as_ref().unwrap().path, [3]);
        assert!(error.location.as_ref().unwrap().iterations.is_empty());
        assert_eq!(error.span, Some(action_span));
        assert_eq!(response.outputs.len(), 2);
        for (output, path) in response.outputs.iter().zip([1, 2]) {
            assert_eq!(output.location.as_ref().unwrap().path, [path]);
            assert!(output.location.as_ref().unwrap().iterations.is_empty());
        }
        let Some(pb::command_output::Kind::Run(outcome)) = &response.outputs[0].kind else {
            panic!("completed Run output")
        };
        let run_report = response.outputs[0].run_report.as_ref().unwrap();
        let Some(pb::command_output::Kind::Statistics(stats)) = &response.outputs[1].kind else {
            panic!("completed Stats output")
        };
        assert!(response.outputs[1].run_report.is_none());
        let native_report = native.get_overall_run_report();
        assert_eq!(
            (outcome.updated, outcome.can_stop),
            (native_report.updated, native_report.can_stop)
        );
        assert_eq!(
            (run_report.updated, run_report.can_stop),
            (outcome.updated, outcome.can_stop)
        );
        assert_eq!(run_report.iterations.len(), native_report.iterations.len());
        assert_eq!(
            native_report.num_matches_per_rule.values().sum::<usize>(),
            1
        );
        assert_eq!(run_report.num_matches_per_rule.len(), 1);
        assert_eq!(run_report.num_matches_per_rule[0].value, 1);
        assert_eq!(run_report.num_matches_per_rule[0].rule, Some(0));
        assert_eq!(
            run_report.num_matches_per_rule[0].direction,
            Some(pb::NativeRuleDirection::Single.into())
        );
        assert_eq!(stats.num_matches_per_rule, run_report.num_matches_per_rule);
        assert_eq!(response.rules.len(), 1);
        let origin = &response.rules[0];
        assert_eq!(origin.name.as_deref(), Some("make-goal"));
        assert_eq!(
            origin.root.as_ref().unwrap().kind,
            Some(pb::ruleset_ref::Kind::Name("derive".into()))
        );
        let profile = response.profile.as_ref().unwrap();
        assert!(!profile.complete);
        assert_eq!(profile.runs.len(), 1);
        assert!(profile.maintenance.is_empty(), "actions add no maintenance");
        let summary = &profile.runs[0];
        assert_eq!(summary.command_path, [1]);
        assert_eq!(summary.invocations, 1);
        assert!(summary.search_and_apply_nanos.is_some());
        assert!(summary.merge_nanos.is_some());
        assert!(summary.rebuild_nanos.is_some());
        assert_eq!(summary.rules.len(), 1);
        assert_eq!(summary.rules[0].rule, Some(0));
        assert_eq!(summary.rules[0].matches, Some(1));
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
        let reused = pb::RunProgramResponse::decode(
            engine
                .run(
                    &pb::RunProgramRequest {
                        egraph_id: id,
                        program: Some(retry),
                        profile: true,
                        include_run_reports: true,
                    }
                    .encode_to_vec(),
                )
                .unwrap()
                .as_slice(),
        )
        .unwrap();
        assert_eq!(reused.error, None);
        assert_eq!(reused.outputs.len(), 1);
        assert_eq!(reused.outputs[0].location.as_ref().unwrap().path, [0]);
        assert_eq!(
            reused.outputs[0].kind,
            Some(pb::command_output::Kind::Statistics(stats.clone())),
            "the exact cumulative report, including every timing, survives failure"
        );
        assert_eq!(reused.rules.len(), 1);
        let retained = &reused.rules[0];
        assert_eq!(retained.root, origin.root);
        assert_eq!(retained.children, origin.children);
        assert_eq!(retained.rule, origin.rule);
        assert_eq!(retained.name, origin.name);
        let (before, after) = (origin.span.unwrap(), retained.span.unwrap());
        assert_eq!((before.start, before.end), (after.start, after.end));
        assert_eq!(
            response.files[before.file as usize],
            reused.files[after.file as usize]
        );
        let profile = reused.profile.unwrap();
        assert!(profile.complete && profile.runs.is_empty());
        assert!(
            profile.maintenance.iter().all(|entry| {
                matches!(
                    &entry.site.as_ref().unwrap().target,
                    Some(pb::maintenance_site::Target::Command(path)) if path.path == [2]
                )
            }),
            "only the ordinary Check may contribute query maintenance"
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
        let response = run_host_default(&mut engine, id, program);
        assert_eq!(response.error, None);
        assert!(response.outputs.is_empty());
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
                matches!(&sort.kind, Some(pb::sort::Kind::Family(family)) if family.name == "Vec")
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
        assert!(response.outputs.is_empty());
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
        assert_eq!(response.outputs.len(), 1);
        assert!(matches!(
            response.outputs[0].kind,
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
        assert_eq!(response.outputs.len(), 1);
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
                7 => program.rules.push(pb::RuleDecl {
                    eval_mode: pb::RuleEvalMode::Seminaive.into(),
                    kind: Some(pb::rule_decl::Kind::Rule(pb::Rule {
                        query: vec![],
                        head: vec![pb::Action {
                            kind: Some(pb::action::Kind::Term(union)),
                            ..Default::default()
                        }],
                    })),
                    ..Default::default()
                }),
                8 => program.declarations.push(pb::Declaration {
                    kind: Some(pb::declaration::Kind::Primitive(pb::Primitive {
                        name: "deferred".into(),
                        inputs: vec![],
                        output: sort_id,
                        body: Some(union),
                    })),
                    ..Default::default()
                }),
                _ => program.commands.push(pb::Command {
                    kind: Some(pb::command::Kind::Repeat(pb::Repeat {
                        body: vec![action],
                        times: Some(u64::from(case == 9)),
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
                        i32::from(pb::ErrorCode::EvaluationFailed)
                    );
                    assert!(response.outputs.is_empty());
                } else {
                    assert_eq!(response.error, None);
                    assert!(
                        matches!(&response.outputs[0].kind, Some(pb::command_output::Kind::Loop(outcome)) if outcome.iterations == u64::from(case == 9) && outcome.updated == (case == 9))
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
            assert!(response.outputs.is_empty());
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
                assert_eq!(error.code, i32::from(pb::ErrorCode::EvaluationFailed));
            }
            assert!(response.outputs.is_empty());
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
        let integer = program.sorts.iter().position(|sort| matches!(&sort.kind, Some(pb::sort::Kind::Family(family)) if family.name == "i64")).unwrap() as u32;
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
        assert_eq!(response.outputs.len(), 1);
        let graph = &engine.graphs[&id].graph;
        assert_eq!(graph.materialized_eq_classes().len(), 1);
        assert_eq!(graph.num_tuples(), 3);
        assert_eq!(graph.get_size(&native_name("call", "read")), 1);
    }
}
