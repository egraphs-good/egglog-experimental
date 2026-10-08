//! In-process compatibility adapter for encoded protobuf requests.
//!
//! This executable slice supports concrete equality/scalar/Vec sorts,
//! constructors, functions, ordered actions, flat named rulesets, checks,
//! extraction, and table observations. Unsupported forms fail explicitly before
//! installation. In particular, profiling must currently be requested: the
//! native engine cannot yet disable its optional timing collection.
//!
//! Decoded protobuf messages supply all authored semantics. Native ASTs exist
//! during validation and execution; the native engine retains its compiled
//! state, with derived indexes for names and diagnostics. No source or previously
//! supplied AST is accepted by this boundary.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::Arc;

use egglog::ast::{self, Action, Command, Expr, Fact, Literal};
use egglog::proto as pb;
use egglog::{ArcSort, EGraph, Term, TermDag, TermId, Value, span};
use egglog_ast::span::{EgglogSpan, SrcFile};
use prost::Message;

pub mod source;

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
    graphs: HashMap<u64, Session>,
}

#[derive(Clone)]
struct Session {
    graph: EGraph,
    // Authored definitions and presentation/default closures, never execution ASTs.
    definitions: pb::Program,
    names: NativeNames,
    request: u64,
    rulesets: HashMap<String, String>,
    // Native rule identifiers are an adapter index, never authored identity.
    origins: HashMap<String, pb::RuleAttribution>,
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
    /// Decodes a creation request and returns an encoded handle.
    pub fn create(&mut self, bytes: &[u8]) -> Result<Vec<u8>, TransportError> {
        let request = pb::CreateEGraphRequest::decode(bytes)?;
        if let Some(options) = &request.options
            && options.execution_mode != i32::from(pb::ExecutionMode::Normal)
        {
            return Err(TransportError(format!(
                "unsupported execution mode {}; only NORMAL executes in this adapter",
                options.execution_mode
            )));
        }
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
        let mut graph = crate::new_experimental_egraph();
        for (index, sort) in program.sorts.iter().enumerate() {
            let name = sort_name(&program.sorts, index as u32).map_err(TransportError)?;
            let native = graph
                .get_sort_by_name(&name)
                .ok_or_else(|| TransportError(format!("unknown creation sort {name}")))?;
            if native.is_eq_sort() != matches!(sort.kind, Some(pb::sort::Kind::Eq(_))) {
                return Err(TransportError(format!(
                    "creation sort kind mismatch for {name}"
                )));
            }
            native_span(&program, sort.span.as_ref()).map_err(TransportError)?;
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
                definitions: pb::Program::default(),
                names: NativeNames::default(),
                request: 0,
                rulesets: HashMap::new(),
                origins: HashMap::new(),
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
                session.graph.set_num_threads(threads);
            }
        }
        Ok(pb::ConfigureEGraphResourcesResponse {
            threads: u64::try_from(session.graph.num_threads())
                .map_err(|_| TransportError("native thread count exceeds uint64".into()))?,
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
        match prepared {
            Ok((staged, _)) => *session = staged,
            Err(error) => {
                response.error = Some(*error.0);
                return Ok(response.encode_to_vec());
            }
        }
        for (index, command) in program.commands.iter().enumerate() {
            let location = pb::CommandLocation {
                path: vec![index as u32],
                iterations: vec![],
            };
            let result = session.execute(&program, command, &location, &mut response);
            if let Err(error) = result {
                let code = match &error {
                    egglog::Error::CheckError(..) => pb::ErrorCode::CheckFailed,
                    egglog::Error::ExtractError(..) => pb::ErrorCode::ExtractionFailed,
                    egglog::Error::NoSuchRuleset(..) => pb::ErrorCode::UnknownName,
                    _ if matches!(
                        &command.kind,
                        Some(pb::command::Kind::Action(pb::Action {
                            kind: Some(pb::action::Kind::Panic(_)),
                            ..
                        }))
                    ) =>
                    {
                        pb::ErrorCode::Panic
                    }
                    _ => pb::ErrorCode::EvaluationFailed,
                };
                response.error = Some(pb::Error {
                    code: code.into(),
                    message: error.to_string(),
                    span: match &command.kind {
                        Some(pb::command::Kind::Action(action)) => action.span.or(command.span),
                        _ => command.span,
                    },
                    location: Some(location),
                    ..Default::default()
                });
                break;
            }
        }
        response.profile.as_mut().unwrap().complete = response.error.is_none();
        Ok(response.encode_to_vec())
    }
}

impl Session {
    // Work on a clone until every definition, node annotation, and command has
    // been checked. Only supported declaration commands run here, never actions.
    fn prepare(&self, program: &mut pb::Program) -> Result<(Self, Vec<Command>), PreparationError> {
        if program.ir_version != 1 {
            return Err(format!("unsupported IR version {}", program.ir_version).into());
        }
        let mut staged = self.clone();
        staged.request += 1;
        if staged.definitions.ir_version == 0 {
            staged.definitions = staged.graph.type_info().builtin_catalog()?.definitions;
        }
        let added =
            egglog::builtin::definitions::reconcile_declarations(program, &mut staged.definitions)?;
        validate_private_names(program)?;
        staged.names = project_names(program, &staged.definitions);
        for (declaration, added) in program.declarations.iter().zip(&added) {
            if !added {
                continue;
            }
            let name = match &declaration.kind {
                Some(pb::declaration::Kind::EqSort(s)) => &s.name,
                Some(pb::declaration::Kind::Constructor(f)) => &f.name,
                Some(pb::declaration::Kind::Function(f)) => &f.name,
                _ => continue,
            };
            if staged.graph.get_sort_by_name(name).is_some()
                || staged.graph.get_function(name).is_some()
                || staged.graph.type_info().is_primitive(name)
            {
                return Err(format!("native declaration namespace collision: {name}").into());
            }
        }
        for (declaration, added) in program.declarations.iter().zip(&added) {
            if !added {
                continue;
            }
            if let Some(pb::declaration::Kind::EqSort(sort)) = &declaration.kind {
                if sort.name.is_empty() {
                    return Err("equality sort name must not be empty".into());
                }
                let command = Command::Sort {
                    span: native_span(program, declaration.span.as_ref())?,
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
                    .run_program(vec![command])
                    .map_err(|error| error.to_string())?;
            }
        }
        let materialized = materialize_sorts(program, &mut staged.graph)?;
        for (index, sort) in program.sorts.iter().enumerate() {
            native_span(program, sort.span.as_ref())?;
            let Some(name) =
                structural_sort_name(&program.sorts, index as u32, &mut HashSet::new())?
            else {
                continue;
            };
            let native = staged
                .graph
                .get_sort_by_name(&name)
                .ok_or_else(|| format!("unknown sort {name}"))?;
            if native.is_eq_sort() != matches!(sort.kind, Some(pb::sort::Kind::Eq(_))) {
                return Err(format!("sort kind mismatch for {name}").into());
            }
        }
        validate_host_declarations(program, &mut staged.graph)?;
        lower_vec_values(program)?;
        // The canonical records above remain intact. The execution/rendering
        // copy contains only genuinely new native declarations.
        program.declarations = std::mem::take(&mut program.declarations)
            .into_iter()
            .zip(added)
            .filter_map(|(d, added)| {
                (added
                    || matches!(
                        d.kind,
                        Some(
                            pb::declaration::Kind::HostPrimitive(_)
                                | pb::declaration::Kind::HostSortFamily(_)
                        )
                    ))
                .then_some(d)
            })
            .collect();
        // Expression lowering detects invalid indices/cycles even in unused
        // arena entries; variables acquire their binder at each use below.
        for (index, node) in program.nodes.iter().enumerate() {
            node_sort(program, index as u32)?;
            native_span(program, node.span.as_ref())?;
            if let Some(pb::node::Kind::Union(union)) = &node.kind {
                if union.members.len() < 2 {
                    return Err("empty/single-member class identities are not supported yet".into());
                }
                for member in &union.members {
                    if node_sort(program, *member)? != node_sort(program, index as u32)? {
                        return Err("Union member sort mismatch".into());
                    }
                    expression(program, *member, &mut HashSet::new())?;
                }
            } else {
                expression(program, index as u32, &mut HashSet::new())?;
            }
        }
        for declaration in program
            .declarations
            .iter()
            .filter(|declaration| {
                !matches!(declaration.kind, Some(pb::declaration::Kind::Function(_)))
            })
            .chain(program.declarations.iter().filter(|declaration| {
                matches!(declaration.kind, Some(pb::declaration::Kind::Function(_)))
            }))
        {
            if matches!(
                declaration.kind,
                Some(
                    pb::declaration::Kind::HostPrimitive(_)
                        | pb::declaration::Kind::HostSortFamily(_)
                )
            ) {
                continue; // Already checked against the native catalog above.
            }
            let span = native_span(program, declaration.span.as_ref())?;
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
                    Command::Constructor { span, name: constructor.name.clone(), schema: signature(program, &constructor.inputs, constructor.output)?, cost, unextractable: constructor.unextractable, hidden: false, let_binding: false, term_constructor: None }
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
                        let mut pending = vec![index];
                        let mut seen = HashSet::new();
                        while let Some(index) = pending.pop() {
                            if !seen.insert(index) { continue; }
                            if let Some(pb::node::Kind::Call(call)) = &program.nodes[index as usize].kind {
                                if !staged.graph.get_function(&call.func).is_some_and(|function| function.func_type().subtype == ast::FunctionSubtype::Constructor) {
                                    return Err("merge table reads are not supported by this slice".into());
                                }
                                pending.extend(&call.args);
                            }
                        }
                    }
                    Command::Function { span, name: function.name.clone(), schema, merge: function.merge.map(|index| expression(program, index, &mut HashSet::new())).transpose()?, hidden: false, let_binding: false, term_constructor: None, unextractable: true }
                },
                _ => return Err("only equality-sort, constructor, and function declarations execute in this slice".into()),
            };
            staged
                .graph
                .run_program(vec![command])
                .map_err(|error| error.to_string())?;
        }
        for node in &program.nodes {
            if let Some(pb::node::Kind::Call(call)) = &node.kind
                && let Some(signature) = staged.graph.type_info().get_func_type(&call.func).cloned()
            {
                if signature.input.len() != call.args.len()
                    || signature.output.name() != sort_name(&program.sorts, node.sort_id)?
                {
                    return Err(format!("call signature mismatch for {}", call.func).into());
                }
                for (argument, expected) in call.args.iter().zip(&signature.input) {
                    if node_sort(program, *argument)? != expected.name() {
                        return Err(format!("argument sort mismatch for {}", call.func).into());
                    }
                }
            }
        }
        lower_builtin_calls(program, &mut staged.graph)?;
        for action in program
            .commands
            .iter()
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
                _ => continue,
            };
            let function = staged.graph.get_function(&call.func).ok_or_else(|| {
                PreparationError(Box::new(pb::Error {
                    code: pb::ErrorCode::UnknownName.into(),
                    message: format!("unknown action target {}", call.func),
                    span: action.span,
                    ..Default::default()
                }))
            })?;
            if expected.is_some_and(|expected| function.func_type().subtype != expected) {
                return Err(format!("invalid action target subtype: {}", call.func).into());
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
                if !staged
                    .graph
                    .get_function(&call.func)
                    .is_some_and(|function| {
                        function.func_type().subtype == ast::FunctionSubtype::Constructor
                    })
                {
                    return Err("subsuming rewrite lhs must be a constructor call".into());
                }
            }
        }
        let mut used = HashSet::new();
        for (index, ruleset) in program.rulesets.iter().enumerate() {
            let name = ruleset
                .name
                .as_ref()
                .ok_or("anonymous rulesets are not supported yet")?;
            if staged.rulesets.contains_key(name) {
                return Err(
                    "ruleset resupply requires occurrence matching, not implemented yet".into(),
                );
            }
            let Some(pb::ruleset::Kind::Rules(rules)) = &ruleset.kind else {
                return Err("combined rulesets are not supported yet".into());
            };
            let native_name = format!("__protobuf_{}_{}", staged.request, index);
            staged
                .graph
                .run_program(vec![Command::AddRuleset(
                    native_span(program, ruleset.span.as_ref())?,
                    native_name.clone(),
                )])
                .map_err(|error| error.to_string())?;
            let mut leaf_used = HashSet::new();
            for (ordinal, rule_index) in rules.rules.iter().enumerate() {
                if !leaf_used.insert(*rule_index) {
                    continue;
                }
                if !used.insert(*rule_index) {
                    return Err(
                        "sharing a rule between distinct rulesets is not supported yet".into(),
                    );
                }
                let rule = program
                    .rules
                    .get(*rule_index as usize)
                    .ok_or("rule index out of bounds")?;
                let native_rule_name = format!("__protobuf_{}_rule_{}", staged.request, rule_index);
                let command = lower_rule(program, rule, &native_name, &native_rule_name)?;
                staged
                    .graph
                    .run_program(vec![command])
                    .map_err(|error| error.to_string())?;
                staged.origins.insert(
                    native_rule_name,
                    pb::RuleAttribution {
                        root: Some(pb::RulesetRef {
                            kind: Some(pb::ruleset_ref::Kind::Name(name.clone())),
                        }),
                        rule: ordinal as u32,
                        name: rule.name.clone(),
                        ..Default::default()
                    },
                );
            }
            staged.rulesets.insert(name.clone(), native_name);
        }
        // Native resolution verifies groundedness, binders, and action contexts
        // on a scratch type environment. No runtime actions occur in this pass.
        let mut checker = staged.graph.clone();
        for rule in &program.rules {
            let command = lower_rule(program, rule, "", "__protobuf_validate_unused")?;
            checker
                .resolve_command_before_proofs(command)
                .map_err(|error| error.to_string())?;
        }
        for command in &program.commands {
            native_span(program, command.span.as_ref())?;
            let lowered = staged.lower_command(program, command)?;
            for command in lowered {
                checker
                    .resolve_command_before_proofs(command)
                    .map_err(|error| error.to_string())?;
            }
        }
        Ok((staged, materialized))
    }

    fn lower_command(
        &self,
        program: &pb::Program,
        command: &pb::Command,
    ) -> Result<Vec<Command>, PreparationError> {
        let span = native_span(program, command.span.as_ref())?;
        let command = match command.kind.as_ref().ok_or("missing command kind")? {
            pb::command::Kind::Action(action) => {
                return Ok(lower_action(program, action)?
                    .into_iter()
                    .map(Command::Action)
                    .collect());
            }
            pb::command::Kind::Check(check) => Command::Check(span, facts(program, &check.facts)?),
            pb::command::Kind::Run(run) => {
                if !run.scheduler.is_empty() {
                    return Err(PreparationError(Box::new(pb::Error {
                        code: pb::ErrorCode::UnknownName.into(),
                        message: format!(
                            "unknown scheduler {} (scheduler bindings are not implemented)",
                            run.scheduler
                        ),
                        span: command.span,
                        ..Default::default()
                    })));
                }
                let name = match run
                    .ruleset
                    .as_ref()
                    .and_then(|reference| reference.kind.as_ref())
                    .ok_or("missing ruleset reference")?
                {
                    pb::ruleset_ref::Kind::Name(name) => name,
                    pb::ruleset_ref::Kind::Index(index) => program
                        .rulesets
                        .get(*index as usize)
                        .ok_or("ruleset index out of bounds")?
                        .name
                        .as_ref()
                        .ok_or("anonymous ruleset")?,
                };
                let native = self.rulesets.get(name).ok_or_else(|| {
                    PreparationError(Box::new(pb::Error {
                        code: pb::ErrorCode::UnknownName.into(),
                        message: format!("unknown ruleset {name}"),
                        span: command.span,
                        ..Default::default()
                    }))
                })?;
                Command::RunSchedule(ast::Schedule::Run(
                    span,
                    ast::RunConfig {
                        ruleset: native.clone(),
                        until: None,
                    },
                ))
            }
            pb::command::Kind::Extract(extract) => {
                if extract.roots.is_empty()
                    || extract.variants == 0
                    || !matches!(
                        pb::Extractor::try_from(extract.extractor),
                        Ok(pb::Extractor::Tree | pb::Extractor::GreedyDag)
                    )
                {
                    return Err("extraction requires roots, a positive variant count, and a specified extractor".into());
                }
                if !extract.cost_model.is_empty() {
                    return Err(PreparationError(Box::new(pb::Error {
                        code: pb::ErrorCode::UnknownName.into(),
                        message: format!("unknown cost model {}", extract.cost_model),
                        span: command.span,
                        ..Default::default()
                    })));
                }
                if extract.extractor != i32::from(pb::Extractor::Tree) {
                    return Err(PreparationError(Box::new(pb::Error {
                        code: pb::ErrorCode::ExtractionFailed.into(),
                        message: "this adapter currently supports only tree extraction".into(),
                        span: command.span,
                        ..Default::default()
                    })));
                }
                return extract
                    .roots
                    .iter()
                    .map(|index| {
                        Ok(Command::Action(Action::Expr(
                            span.clone(),
                            expression(program, *index, &mut HashSet::new())?,
                        )))
                    })
                    .collect();
            }
            pb::command::Kind::PrintFunction(print) => {
                if print.table.is_empty() {
                    return Err("table name must not be empty".into());
                }
                if self.graph.get_function(&print.table).is_none() {
                    return Err(PreparationError(Box::new(pb::Error {
                        code: pb::ErrorCode::UnknownName.into(),
                        message: format!("unknown table {}", print.table),
                        span: command.span,
                        ..Default::default()
                    })));
                }
                return Ok(vec![]);
            }
            _ => {
                return Err(
                    "this command kind is not supported by the initial byte adapter".into(),
                );
            }
        };
        Ok(vec![command])
    }

    fn execute(
        &mut self,
        program: &pb::Program,
        command: &pb::Command,
        location: &pb::CommandLocation,
        response: &mut pb::RunProgramResponse,
    ) -> Result<(), egglog::Error> {
        let output = match command.kind.as_ref().unwrap() {
            pb::command::Kind::Extract(extract) => {
                let roots = extract
                    .roots
                    .iter()
                    .map(|index| {
                        self.graph.eval_expr(
                            &expression(program, *index, &mut HashSet::new())
                                .expect("validated expression"),
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let sorts: Vec<_> = roots.iter().map(|(sort, _)| sort.clone()).collect();
                let extracted = self
                    .graph
                    .extract_variants(roots, extract.variants as usize)?;
                let mut cache = HashMap::new();
                let mut output = pb::ExtractResult::default();
                for (variants, sort) in extracted.variants.iter().zip(sorts) {
                    let mut root = pb::ExtractedRoot::default();
                    for variant in variants {
                        let term = encode_term(
                            &self.graph,
                            &self.names,
                            &extracted.termdag,
                            variant.term,
                            &sort,
                            response,
                            &mut cache,
                        )?;
                        let cost = i64::try_from(variant.cost).map_err(|_| {
                            egglog::Error::ExtractError(
                                "native u64 cost is outside this handle's i64 domain".into(),
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
            pb::command::Kind::PrintFunction(print) => {
                let function = self.graph.get_function(&print.table).unwrap();
                let signature = function.func_type().clone();
                let mut rows: Vec<(Vec<Value>, Value, bool)> = vec![];
                if crate::table_rows::is_constructor(&self.graph, &print.table)? {
                    self.graph.constructor_enodes(&print.table, |row| {
                        rows.push((row.children.to_vec(), row.eclass, row.subsumed))
                    })?;
                } else {
                    self.graph.function_entries(&print.table, |row| {
                        rows.push((row.inputs.to_vec(), row.output, row.subsumed))
                    })?;
                }
                if print.max_rows > 0 {
                    rows.truncate(usize::try_from(print.max_rows).unwrap_or(usize::MAX));
                }
                let roots = rows
                    .iter()
                    .flat_map(|(args, value, _)| {
                        args.iter()
                            .zip(&signature.input)
                            .map(|(value, sort)| (sort.clone(), *value))
                            .chain(std::iter::once((signature.output.clone(), *value)))
                    })
                    .collect();
                let extracted = self.graph.extract_best(roots)?;
                let mut terms = extracted.terms.iter();
                let mut cache = HashMap::new();
                let mut output = pb::PrintedFunction {
                    table: self
                        .names
                        .callables
                        .get(&print.table)
                        .unwrap_or(&print.table)
                        .clone(),
                    rows: vec![],
                };
                for (_, _, subsumed) in rows {
                    let mut cells = vec![];
                    for sort in signature
                        .input
                        .iter()
                        .chain(std::iter::once(&signature.output))
                    {
                        let term = terms.next().unwrap().as_ref().ok_or_else(|| {
                            egglog::Error::ExtractError(
                                "table cell has no finite extraction".into(),
                            )
                        })?;
                        cells.push(encode_term(
                            &self.graph,
                            &self.names,
                            &extracted.termdag,
                            term.term,
                            sort,
                            response,
                            &mut cache,
                        )?);
                    }
                    let output_cell = cells.pop().unwrap();
                    output.rows.push(pb::FunctionRow {
                        args: cells,
                        output: output_cell,
                        subsumed,
                    });
                }
                Some(pb::command_output::Kind::PrintedFunction(output))
            }
            _ => {
                let commands = self
                    .lower_command(program, command)
                    .expect("validated command");
                if matches!(command.kind, Some(pb::command::Kind::Run(_))) {
                    response
                        .profile
                        .as_mut()
                        .unwrap()
                        .runs
                        .push(pb::RunSummary {
                            command_path: location.path.clone(),
                            invocations: 1,
                            ..Default::default()
                        });
                }
                let outputs = self.graph.run_program(commands)?;
                let mut outcome = None;
                for output in outputs {
                    if let egglog::CommandOutput::RunSchedule(report) = output {
                        let mut rules = vec![];
                        for (name, matches) in &report.num_matches_per_rule {
                            if let Some(origin) = self.origins.get(name.as_ref()) {
                                let index = response
                                    .rules
                                    .iter()
                                    .position(|existing| existing == origin)
                                    .unwrap_or_else(|| {
                                        response.rules.push(origin.clone());
                                        response.rules.len() - 1
                                    });
                                rules.push(pb::RuleSummary {
                                    rule: Some(index as u32),
                                    matches: Some(*matches as u64),
                                    search_and_apply_nanos: report
                                        .search_and_apply_time_per_rule
                                        .get(name)
                                        .and_then(|duration| duration.as_nanos().try_into().ok()),
                                });
                            }
                        }
                        *response.profile.as_mut().unwrap().runs.last_mut().unwrap() =
                            pb::RunSummary {
                                command_path: location.path.clone(),
                                invocations: 1,
                                rules,
                                search_and_apply_nanos: report
                                    .search_and_apply_time_per_ruleset
                                    .values()
                                    .map(|duration| duration.as_nanos())
                                    .sum::<u128>()
                                    .try_into()
                                    .ok(),
                                merge_nanos: report
                                    .merge_time_per_ruleset
                                    .values()
                                    .map(|duration| duration.as_nanos())
                                    .sum::<u128>()
                                    .try_into()
                                    .ok(),
                                rebuild_nanos: report
                                    .rebuild_time_per_ruleset
                                    .values()
                                    .map(|duration| duration.as_nanos())
                                    .sum::<u128>()
                                    .try_into()
                                    .ok(),
                            };
                        outcome = Some(pb::command_output::Kind::Run(pb::RunOutcome {
                            updated: report.updated,
                            can_stop: report.can_stop,
                        }));
                    }
                }
                outcome
            }
        };
        if let Some(kind) = output {
            response.outputs.push(pb::CommandOutput {
                kind: Some(kind),
                location: Some(location.clone()),
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
        match &mut declaration.kind {
            Some(pb::declaration::Kind::EqSort(s)) => s.name = native_name("sort", &s.name),
            Some(pb::declaration::Kind::Constructor(f)) => f.name = native_name("call", &f.name),
            Some(pb::declaration::Kind::Function(f)) => f.name = native_name("call", &f.name),
            _ => (),
        }
    }
    for node in &mut program.nodes {
        if let Some(pb::node::Kind::Call(call)) = &mut node.kind {
            project_call(&mut call.func);
        }
    }
    for command in &mut program.commands {
        if let Some(pb::command::Kind::PrintFunction(print)) = &mut command.kind {
            project_call(&mut print.table);
        }
    }
    for action in program
        .commands
        .iter_mut()
        .filter_map(|c| match &mut c.kind {
            Some(pb::command::Kind::Action(a)) => Some(a),
            _ => None,
        })
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
            Some(pb::action::Kind::Delete(call) | pb::action::Kind::Subsume(call)) => {
                project_call(&mut call.func)
            }
            _ => (),
        }
    }
    names
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
        Some(pb::sort::Kind::Family(family)) if family.name == "Vec" && family.args.len() == 1 => {
            structural_sort_name(sorts, family.args[0], active).and_then(|child| {
                child
                    .map(|child| {
                        if child.len() > 65_536 {
                            return Err("native sort name exceeds adapter limit".into());
                        }
                        Ok(format!("__egglog_proto_vec_{}_{}", child.len(), child))
                    })
                    .transpose()
            })
        }
        Some(pb::sort::Kind::Family(family))
            if family.args.is_empty()
                && matches!(
                    family.name.as_str(),
                    "i64" | "f64" | "String" | "bool" | "Unit"
                ) =>
        {
            Ok(Some(family.name.clone()))
        }
        _ => Err("only equality, scalar and Vec sorts are supported yet".into()),
    };
    active.remove(&index);
    result
}

fn sort_name(sorts: &[pb::Sort], index: u32) -> Result<String, String> {
    structural_sort_name(sorts, index, &mut HashSet::new())?
        .ok_or_else(|| "runtime sort contains an open type parameter".into())
}

fn validate_private_names(program: &pb::Program) -> Result<(), String> {
    let reserved =
        |name: &str| name.starts_with("__egglog_proto_") || name.starts_with("__egglog_instance_");
    for sort in &program.sorts {
        if let Some(pb::sort::Kind::Eq(name)) = &sort.kind
            && reserved(name)
        {
            return Err("adapter private sort namespace is reserved in this slice".into());
        }
    }
    for declaration in &program.declarations {
        let name = match &declaration.kind {
            Some(pb::declaration::Kind::EqSort(s)) => &s.name,
            Some(pb::declaration::Kind::Constructor(f)) => &f.name,
            Some(pb::declaration::Kind::Function(f)) => &f.name,
            _ => continue,
        };
        if reserved(name) {
            return Err("adapter private declaration namespace is reserved in this slice".into());
        }
    }
    Ok(())
}

// Materialization runs on staged state. Open patterns remain in their signature
// arenas; only closed shapes install native sorts, in child-before-parent order.
fn materialize_sorts(program: &pb::Program, graph: &mut EGraph) -> Result<Vec<Command>, String> {
    fn visit(
        program: &pb::Program,
        index: u32,
        graph: &mut EGraph,
        commands: &mut Vec<Command>,
        seen: &mut HashSet<u32>,
    ) -> Result<(), String> {
        if !seen.insert(index) {
            return Ok(());
        }
        let name = structural_sort_name(&program.sorts, index, &mut HashSet::new())?;
        let Some(name) = name else {
            return Ok(());
        };
        let Some(pb::sort::Kind::Family(family)) = &program.sorts[index as usize].kind else {
            return Ok(());
        };
        if family.args.is_empty() {
            return Ok(());
        }
        for child in &family.args {
            visit(program, *child, graph, commands, seen)?;
        }
        if let Some(existing) = graph.get_sort_by_name(&name) {
            let mut expected = vec![];
            let expected_id = egglog::builtin::import_sort(&program.sorts, index, &mut expected)?;
            if graph.export_sort(existing, &mut expected)? != expected_id {
                return Err("private sort name collision".into());
            }
            return Ok(());
        }
        let command = Command::Sort {
            span: native_span(program, program.sorts[index as usize].span.as_ref())?,
            name,
            presort_and_args: Some((
                family.name.clone(),
                family
                    .args
                    .iter()
                    .map(|i| sort_name(&program.sorts, *i).map(|name| Expr::Var(span!(), name)))
                    .collect::<Result<_, _>>()?,
            )),
            uf: None,
            proof_func: None,
            container_rebuild: None,
            proof_constructors: None,
            unionable: true,
        };
        graph
            .run_program(vec![command.clone()])
            .map_err(|e| e.to_string())?;
        commands.push(command);
        Ok(())
    }
    let mut commands = vec![];
    let mut seen = HashSet::new();
    for index in 0..program.sorts.len() {
        visit(program, index as u32, graph, &mut commands, &mut seen)?;
    }
    Ok(commands)
}

// This ephemeral lowering copy is never emitted as wire IR. Complete annotations
// choose compiler instance keys before the native AST drops result types.
fn lower_builtin_calls(program: &mut pb::Program, graph: &mut EGraph) -> Result<(), String> {
    let mut replacements = vec![];
    for (index, node) in program.nodes.iter().enumerate() {
        if let Some(pb::node::Kind::Call(call)) = &node.kind {
            if graph.type_info().get_func_type(&call.func).is_some() {
                continue;
            }
            let args: Vec<_> = call
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
            let sorts = args
                .iter()
                .copied()
                .chain([node.sort_id])
                .map(|i| {
                    graph
                        .get_sort_by_name(&sort_name(&program.sorts, i)?)
                        .cloned()
                        .ok_or_else(|| "unknown closed sort".into())
                })
                .collect::<Result<Vec<_>, String>>()?;
            replacements.push((
                index,
                graph.type_info().resolve_builtin(
                    program,
                    &call.func,
                    &args,
                    node.sort_id,
                    &sorts,
                )?,
            ));
        }
    }
    for (index, name) in replacements {
        let Some(pb::node::Kind::Call(call)) = &mut program.nodes[index].kind else {
            unreachable!()
        };
        call.func = name;
    }
    Ok(())
}

// The native Vec constructor interns precisely this ordered container payload.
// Validate contents first; the resulting calls are internal compatibility code,
// never a claim that the wire value payload was a symbolic authored Call.
fn lower_vec_values(program: &mut pb::Program) -> Result<(), String> {
    let mut replacements = vec![];
    for (index, node) in program.nodes.iter().enumerate() {
        if let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Vec(values)),
        })) = &node.kind
        {
            let Some(pb::sort::Kind::Family(family)) = program
                .sorts
                .get(node.sort_id as usize)
                .and_then(|s| s.kind.as_ref())
            else {
                return Err("Vec payload requires Vec sort".into());
            };
            if family.name != "Vec" || family.args.len() != 1 {
                return Err("Vec payload/sort mismatch".into());
            }
            let expected = sort_name(&program.sorts, family.args[0])?;
            for item in &values.items {
                if node_sort(program, *item)? != expected {
                    return Err("Vec payload element sort mismatch".into());
                }
            }
            replacements.push((index, values.items.clone()));
        }
    }
    for (index, args) in replacements {
        program.nodes[index].kind = Some(pb::node::Kind::Call(pb::Call {
            func: "egglog.core.vec.of".into(),
            args,
        }));
    }
    Ok(())
}

fn node_sort(program: &pb::Program, index: u32) -> Result<String, String> {
    let node = program
        .nodes
        .get(index as usize)
        .ok_or("node index out of bounds")?;
    sort_name(&program.sorts, node.sort_id)
}

fn native_span(program: &pb::Program, span: Option<&pb::Span>) -> Result<ast::Span, String> {
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
        return Ok(ast::Span::Egglog(Arc::new(EgglogSpan {
            file: Arc::new(SrcFile {
                name: Some(file.name.clone()),
                contents: contents.clone(),
            }),
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
                    .check_builtin_signature(program, primitive)?;
            }
            Some(pb::declaration::Kind::HostSortFamily(family)) => {
                if family.name == "Vec" {
                    if family.arity != 1 || declaration.bindings.is_some() {
                        return Err("unsupported or incompatible Vec family descriptor".into());
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
) -> Result<Expr, String> {
    // The compatibility AST is a tree. Bound expansion of a compact shared DAG
    // before it can allocate exponentially; a later native-IR path can lift this.
    lower_expression(program, index, visiting, &mut 65_536)
}

fn lower_expression(
    program: &pb::Program,
    index: u32,
    visiting: &mut HashSet<u32>,
    remaining: &mut usize,
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
    let span = native_span(program, node.span.as_ref())?;
    let result = match node.kind.as_ref().ok_or("missing node kind")? {
        pb::node::Kind::Var(name) if !name.is_empty() => Expr::Var(span, name.clone()),
        pb::node::Kind::Call(call) => Expr::Call(
            span,
            call.func.clone(),
            call.args
                .iter()
                .map(|argument| lower_expression(program, *argument, visiting, remaining))
                .collect::<Result<_, _>>()?,
        ),
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

fn facts(program: &pb::Program, indices: &[u32]) -> Result<Vec<Fact>, String> {
    let mut result = vec![];
    for index in indices {
        let node = program
            .nodes
            .get(*index as usize)
            .ok_or("fact index out of bounds")?;
        if let Some(pb::node::Kind::Union(union)) = &node.kind {
            let first = *union.members.first().ok_or("empty equality fact")?;
            for other in union.members.iter().skip(1) {
                result.push(Fact::Eq(
                    native_span(program, node.span.as_ref())?,
                    expression(program, first, &mut HashSet::new())?,
                    expression(program, *other, &mut HashSet::new())?,
                ));
            }
        } else {
            result.push(Fact::Fact(expression(
                program,
                *index,
                &mut HashSet::new(),
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

fn lower_action(program: &pb::Program, action: &pb::Action) -> Result<Vec<Action>, String> {
    let span = native_span(program, action.span.as_ref())?;
    let lowered = match action.kind.as_ref().ok_or("missing action kind")? {
        pb::action::Kind::Term(index) => {
            let node = program
                .nodes
                .get(*index as usize)
                .ok_or("action node out of bounds")?;
            if matches!(node.kind, Some(pb::node::Kind::Union(_))) {
                return Err("action Union identity is not supported yet".into());
            }
            Action::Expr(span, expression(program, *index, &mut HashSet::new())?)
        }
        pb::action::Kind::Set(set) => {
            let target = set.target.as_ref().ok_or("missing set target")?;
            Action::Set(
                span,
                target.func.clone(),
                target
                    .args
                    .iter()
                    .map(|index| expression(program, *index, &mut HashSet::new()))
                    .collect::<Result<_, _>>()?,
                expression(
                    program,
                    set.value.ok_or("missing set value")?,
                    &mut HashSet::new(),
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
                .map(|index| expression(program, *index, &mut HashSet::new()))
                .collect::<Result<_, _>>()?,
        ),
        pb::action::Kind::Panic(message) => Action::Panic(span, message.clone()),
        _ => return Err("SetCost is not supported yet".into()),
    };
    Ok(vec![lowered])
}

fn lower_rule(
    program: &pb::Program,
    rule: &pb::RuleDecl,
    ruleset: &str,
    name: &str,
) -> Result<Command, String> {
    if rule.name.as_ref().is_some_and(String::is_empty) {
        return Err("an explicit rule label must not be empty".into());
    }
    if rule.eval_mode != i32::from(pb::RuleEvalMode::Seminaive)
        || rule.no_decomp
        || rule.include_subsumed
    {
        return Err("only default seminaive rule options execute in this slice".into());
    }
    let span = native_span(program, rule.span.as_ref())?;
    match rule.kind.as_ref().ok_or("missing rule kind")? {
        pb::rule_decl::Kind::Rewrite(rewrite) => {
            if node_sort(program, rewrite.lhs)? != node_sort(program, rewrite.rhs)? {
                return Err("rewrite output sort mismatch".into());
            }
            let mut bindings = HashMap::new();
            check_variables(program, &[rewrite.lhs], &mut bindings, true)?;
            check_variables(program, &rewrite.conditions, &mut bindings, true)?;
            check_variables(program, &[rewrite.rhs], &mut bindings, false)?;
            Ok(Command::Rewrite(
                ruleset.into(),
                ast::Rewrite {
                    span,
                    lhs: expression(program, rewrite.lhs, &mut HashSet::new())?
                        .map_symbols(&mut |h| h, &mut |v: String| native_name("var", &v)),
                    rhs: expression(program, rewrite.rhs, &mut HashSet::new())?
                        .map_symbols(&mut |h| h, &mut |v: String| native_name("var", &v)),
                    conditions: facts(program, &rewrite.conditions)?,
                    name: name.into(),
                },
                rewrite.subsume,
            ))
        }
        pb::rule_decl::Kind::Rule(body) => {
            let mut bindings = HashMap::new();
            check_variables(program, &body.query, &mut bindings, true)?;
            for action in &body.head {
                let roots = match action.kind.as_ref().ok_or("missing action kind")? {
                    pb::action::Kind::Term(index) => vec![*index],
                    pb::action::Kind::Set(set) => {
                        let mut roots = set
                            .target
                            .as_ref()
                            .ok_or("missing set target")?
                            .args
                            .clone();
                        roots.push(set.value.ok_or("missing set value")?);
                        roots
                    }
                    pb::action::Kind::Delete(call) | pb::action::Kind::Subsume(call) => {
                        call.args.clone()
                    }
                    pb::action::Kind::Panic(_) => vec![],
                    _ => return Err("SetCost is not supported yet".into()),
                };
                check_variables(program, &roots, &mut bindings, false)?;
            }
            if body
                .head
                .iter()
                .any(|action| matches!(action.kind, Some(pb::action::Kind::Panic(_))))
            {
                return Err("rule panic attribution is not supported yet".into());
            }
            Ok(Command::Rule {
                rule: ast::Rule {
                    span,
                    head: ast::GenericActions(
                        body.head
                            .iter()
                            .map(|action| lower_action(program, action))
                            .collect::<Result<Vec<_>, _>>()?
                            .into_iter()
                            .flatten()
                            .collect(),
                    )
                    .map_symbols(&mut |h| h, &mut |v: String| native_name("var", &v)),
                    body: facts(program, &body.query)?,
                    name: name.into(),
                    ruleset: ruleset.into(),
                    eval_mode: ast::RuleEvalMode::Seminaive,
                    no_decomp: false,
                    include_subsumed: false,
                },
            })
        }
        _ => Err("bidirectional rewrites are not supported yet".into()),
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
            pb::node::Kind::Call(call) => pending.extend(&call.args),
            pb::node::Kind::Union(union) => pending.extend(&union.members),
            pb::node::Kind::PrimitiveValue(_) => (),
            _ => return Err("unsupported variable-bearing node".into()),
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
    egglog::builtin::import_sort(&sorts, index, &mut response.sorts)
        .map_err(egglog::Error::ExtractError)
}

fn encode_term(
    graph: &EGraph,
    names: &NativeNames,
    terms: &TermDag,
    term: TermId,
    sort: &ArcSort,
    response: &mut pb::RunProgramResponse,
    cache: &mut HashMap<(TermId, String), u32>,
) -> Result<u32, egglog::Error> {
    let key = (term, sort.name().to_owned());
    if let Some(index) = cache.get(&key) {
        return Ok(*index);
    }
    let kind = match terms.get(term) {
        Term::Lit(literal) => pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(match literal {
                Literal::Int(value) => pb::primitive_value::Value::I64(*value),
                Literal::Float(value) => pb::primitive_value::Value::F64Bits(value.0.to_bits()),
                Literal::String(value) => pb::primitive_value::Value::String(value.clone()),
                Literal::Bool(value) => pb::primitive_value::Value::Bool(*value),
                Literal::Unit => pb::primitive_value::Value::Unit(pb::Unit {}),
            }),
        }),
        Term::App(name, children)
            if (name == "vec-of" || name == "vec-empty") && sort.is_container_sort() =>
        {
            let sort_id = encode_sort(graph, names, sort, response)?;
            if !matches!(&response.sorts[sort_id as usize].kind, Some(pb::sort::Kind::Family(family)) if family.name == "Vec")
            {
                return Err(egglog::Error::ExtractError("Vec term/sort mismatch".into()));
            }
            let element = &sort.inner_sorts()[0];
            let elements = children
                .iter()
                .map(|child| encode_term(graph, names, terms, *child, element, response, cache))
                .collect::<Result<_, _>>()?;
            pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Vec(pb::ValueList {
                    items: elements,
                })),
            })
        }
        Term::App(name, children) => {
            let signature = graph
                .get_function(name)
                .ok_or_else(|| {
                    egglog::Error::ExtractError(format!("unsupported extracted host value {name}"))
                })?
                .func_type();
            let args = children
                .iter()
                .zip(&signature.input)
                .map(|(child, sort)| {
                    encode_term(graph, names, terms, *child, sort, response, cache)
                })
                .collect::<Result<_, _>>()?;
            pb::node::Kind::Call(pb::Call {
                func: names.callables.get(name).unwrap_or(name).clone(),
                args,
            })
        }
        Term::Var(_) => {
            return Err(egglog::Error::ExtractError(
                "extracted variable is not closed data".into(),
            ));
        }
    };
    let sort_id = encode_sort(graph, names, sort, response)?;
    let index = response.nodes.len() as u32;
    response.nodes.push(pb::Node {
        sort_id,
        kind: Some(kind),
        ..Default::default()
    });
    cache.insert(key, index);
    Ok(index)
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn unsupported_creation_modes_do_not_allocate_handles() {
        let mut engine = Engine::default();
        for execution_mode in [1, 2, 3, 99, -1] {
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
                    definitions: pb::Program::default(),
                    names: NativeNames::default(),
                    request: 0,
                    rulesets: HashMap::new(),
                    origins: HashMap::new(),
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
}
