use super::{
    EgglogValue, TypedError,
    expr::{Expr, ValueInput},
    pb,
    rule::{Actions, Facts, ensure_sort},
    storage::{
        Arena, DeclarationKind, Packer, Record, Slot, closure, publish, visit, visit_action,
    },
};
use prost::Message;
use std::{
    collections::{HashMap, HashSet},
    ops::ControlFlow,
    sync::{Arc, Mutex, MutexGuard, TryLockError},
};

// A request plan retains locations and destination bindings only. Generated
// actions/initializers remain the sole execution recipe, and nothing is cached.
struct CapturePlan {
    known: HashMap<String, (Record, String)>,
    reserved: HashSet<String>,
    next: u64,
}

impl CapturePlan {
    fn new(graph: &EGraph, roots: &[Record]) -> Result<Self, TypedError> {
        let records = closure(roots)?;
        let mut recipes = HashMap::new();
        let mut private_declarations = HashSet::new();
        for record in &records {
            if let Some(capture) = record.capture()? {
                let key = (
                    capture.declaration.owner.as_ref().unwrap().id,
                    capture.declaration.arena,
                    capture.declaration.index,
                );
                private_declarations.insert(key);
                if let Some(previous) = recipes.insert(capture.name.clone(), record.clone())
                    && Expr(previous) != Expr(record.clone())
                {
                    return Err(TypedError::Invalid(
                        "conflicting capture label, sort or initializer".into(),
                    ));
                }
                if let Some((previous, _)) = graph.captures.get(&capture.name)
                    && Expr(previous.clone()) != Expr(record.clone())
                {
                    return Err(TypedError::Invalid(
                        "conflicting capture label, sort or initializer".into(),
                    ));
                }
            }
        }
        let mut reserved = graph.reserved_names.clone();
        for record in records {
            let owner = record.owner.as_ref().unwrap();
            let name = match record.arena {
                Arena::Declaration if !private_declarations.contains(&record.key()) => {
                    match &owner.program().unwrap().declarations[record.index as usize].kind {
                        Some(pb::declaration::Kind::Constructor(c)) => Some(&c.name),
                        Some(pb::declaration::Kind::Function(f)) => Some(&f.name),
                        Some(pb::declaration::Kind::Relation(r)) => Some(&r.name),
                        Some(pb::declaration::Kind::UserDefinedPrimitive(p)) => Some(&p.name),
                        _ => None,
                    }
                }
                Arena::Primitive => Some(&record.primitive()?.name),
                Arena::Node if record.capture()?.is_none() => {
                    match &owner.program().unwrap().nodes[record.index as usize].kind {
                        Some(pb::node::Kind::Call(c)) => Some(&c.func),
                        _ => None,
                    }
                }
                _ => None,
            };
            if let Some(name) = name {
                if graph.private_slots.contains(name) {
                    return Err(TypedError::Invalid(
                        "ordinary callable collides with private capture storage".into(),
                    ));
                }
                reserved.insert(name.clone());
            }
        }
        Ok(Self {
            known: graph.captures.clone(),
            reserved,
            next: graph.next_capture,
        })
    }

    fn materialize(
        &mut self,
        roots: &[Record],
        fresh: bool,
        packer: &mut Packer,
    ) -> Result<(), TypedError> {
        let mut pending: Vec<_> = self
            .frontier(roots, fresh)?
            .into_iter()
            .rev()
            .map(|r| (r, false))
            .collect();
        while let Some((record, finish)) = pending.pop() {
            let recipe = record.capture()?.expect("capture frontier");
            let slot = if let Some((previous, slot)) = self.known.get(&recipe.name) {
                if Expr(previous.clone()) != Expr(record.clone()) {
                    return Err(TypedError::Invalid(
                        "conflicting capture label, sort or initializer".into(),
                    ));
                }
                slot.clone()
            } else if !fresh {
                return Err(TypedError::Invalid(
                    "check requires an established capture".into(),
                ));
            } else if !finish {
                let children = self.frontier(std::slice::from_ref(&recipe.initializer), true)?;
                pending.push((record, true));
                pending.extend(children.into_iter().rev().map(|r| (r, false)));
                continue;
            } else {
                let slot = loop {
                    let ordinal = self.next;
                    self.next = self.next.checked_add(1).ok_or_else(|| {
                        TypedError::Invalid("capture name space exhausted".into())
                    })?;
                    let name = format!("__typed_capture_{ordinal}");
                    if self.reserved.insert(name.clone()) {
                        break name;
                    }
                };
                self.known
                    .insert(recipe.name.clone(), (record.clone(), slot.clone()));
                // Bind all three source locations before importing the Set. No
                // ordinary call/declaration is renamed merely by its spelling.
                for source in [&record, &recipe.declaration, &recipe.initialization] {
                    packer.captures.insert(
                        (
                            source.owner.as_ref().unwrap().id,
                            source.arena,
                            source.index,
                        ),
                        slot.clone(),
                    );
                }
                let index = packer.intern(recipe.initialization.clone(), 0);
                packer
                    .initializations
                    .push((index, record.clone(), slot.clone()));
                slot
            };
            for source in [&record, &recipe.declaration, &recipe.initialization] {
                packer.captures.insert(
                    (
                        source.owner.as_ref().unwrap().id,
                        source.arena,
                        source.index,
                    ),
                    slot.clone(),
                );
            }
        }
        Ok(())
    }

    // Find capture boundaries without entering their initializer regions.
    // Unclassified host calls are not assumed total; established captures are
    // closed leaves. Set keys and RHS are supplied together in native order.
    fn frontier(&self, roots: &[Record], evaluated: bool) -> Result<Vec<Record>, TypedError> {
        let mut pending: Vec<_> = roots.iter().rev().cloned().collect();
        let mut seen = HashSet::new();
        let mut captures = vec![];
        let mut eligible = true;
        while let Some(record) = pending.pop() {
            let owner = record.owner.as_ref().unwrap();
            if !seen.insert(record.key()) {
                continue;
            }
            if record.capture()?.is_some() {
                captures.push(record);
                continue;
            }
            let node = &owner.program().unwrap().nodes[record.index as usize];
            match &node.kind {
                Some(pb::node::Kind::Var(_)) if evaluated => {
                    return Err(TypedError::Invalid(
                        "free variable in evaluated input".into(),
                    ));
                }
                Some(pb::node::Kind::Union(_) | pb::node::Kind::Apply(_)) => eligible = false,
                Some(pb::node::Kind::Call(call)) => {
                    let declaration = record.declaration(&call.func, DeclarationKind::Callable)?;
                    eligible &= declaration.arena == Arena::Declaration
                        && matches!(
                            declaration
                                .owner
                                .as_ref()
                                .unwrap()
                                .program()
                                .unwrap()
                                .declarations[declaration.index as usize]
                                .kind,
                            Some(pb::declaration::Kind::Constructor(_))
                        );
                }
                _ => (),
            }
            let mut one = pb::Program {
                nodes: vec![node.clone()],
                ..Default::default()
            };
            let mut children = vec![];
            visit(&mut one, Arena::Node, 0, |arena, index| {
                if arena == Arena::Node {
                    children.push(record.resolve(arena, index)?);
                }
                Ok(index)
            })?;
            pending.extend(children.into_iter().rev());
        }
        if evaluated
            && !eligible
            && captures.iter().any(|record| {
                record.capture().is_ok_and(|recipe| {
                    recipe.is_some_and(|recipe| !self.known.contains_key(&recipe.name))
                })
            })
        {
            return Err(TypedError::Invalid("fresh nested capture requires constructor/value-only surrounding syntax; host eligibility is unavailable".into()));
        }
        Ok(captures)
    }
}

// Saved handles are private and never executed while on the stack. Push only
// saves healthy state, so restoring these observations also restores health.
struct SavedScope {
    handle: u64,
    declarations: HashMap<String, Record>,
    captures: HashMap<String, (Record, String)>,
    private_slots: HashSet<String>,
}

/// A byte-protocol session. No native EGraph or AST execution escape hatch.
pub struct EGraph {
    engine: Arc<Mutex<crate::protobuf::Engine>>,
    builtins: Record,
    discarded: Arc<Mutex<Vec<u64>>>,
    handle: u64,
    // An uncertain response cannot establish the completed action prefix.
    usable: bool,
    declarations: HashMap<String, Record>,
    scopes: Vec<SavedScope>,
    captures: HashMap<String, (Record, String)>,
    private_slots: HashSet<String>,
    reserved_names: HashSet<String>,
    next_capture: u64,
    #[cfg(test)]
    last_wire: Option<(Vec<u8>, Vec<Vec<u8>>)>,
}

// Destruction may be requested from a snapshot callback while the engine is
// exclusively borrowed. Drain without holding both mutexes during native work.
fn drain_discarded(
    engine: &mut crate::protobuf::Engine,
    discarded: &Mutex<Vec<u64>>,
) -> Result<(), TypedError> {
    let handles = std::mem::take(
        &mut *discarded
            .lock()
            .unwrap_or_else(|poison| poison.into_inner()),
    );
    for (index, handle) in handles.iter().enumerate() {
        if let Err(error) =
            engine.destroy(&pb::DestroyEGraphRequest { egraph_id: *handle }.encode_to_vec())
        {
            discarded
                .lock()
                .unwrap_or_else(|poison| poison.into_inner())
                .extend_from_slice(&handles[index..]);
            return Err(TypedError::Invalid(error.to_string()));
        }
    }
    Ok(())
}

impl Drop for EGraph {
    fn drop(&mut self) {
        let handles =
            std::iter::once(self.handle).chain(self.scopes.iter().map(|scope| scope.handle));
        if let Ok(mut engine) = self.engine.try_lock() {
            let _ = drain_discarded(&mut engine, &self.discarded);
            for handle in handles {
                if engine
                    .destroy(&pb::DestroyEGraphRequest { egraph_id: handle }.encode_to_vec())
                    .is_err()
                {
                    self.discarded
                        .lock()
                        .unwrap_or_else(|poison| poison.into_inner())
                        .push(handle);
                }
            }
        } else {
            self.discarded
                .lock()
                .unwrap_or_else(|poison| poison.into_inner())
                .extend(handles);
        }
    }
}

impl Default for EGraph {
    fn default() -> Self {
        Self::new().expect("default byte engine creation")
    }
}

impl EGraph {
    // Reject callback reentry instead of waiting on the mutex we already own.
    // A successful guard also completes graph destruction deferred by callbacks.
    fn lock_engine(&self) -> Result<MutexGuard<'_, crate::protobuf::Engine>, TypedError> {
        let mut engine = self.engine.try_lock().map_err(|error| {
            TypedError::Invalid(match error {
                TryLockError::WouldBlock => "byte engine is already executing".into(),
                TryLockError::Poisoned(_) => "byte engine mutex poisoned".into(),
            })
        })?;
        drain_discarded(&mut engine, &self.discarded)?;
        Ok(engine)
    }

    /// Create a byte engine with the adapter's supported i64 cost domain.
    pub fn new() -> Result<Self, TypedError> {
        Self::with_recording(false)
    }

    /// Create a byte engine with optional input Program history.
    /// Recording is unbounded when enabled and independent of logical Freeze.
    pub fn with_recording(record_history: bool) -> Result<Self, TypedError> {
        let mut engine = crate::protobuf::Engine::default();
        let bytes = engine
            .get_builtins(&pb::GetBuiltinsRequest {}.encode_to_vec())
            .map_err(|e| TypedError::Invalid(e.to_string()))?;
        let builtins = super::storage::publish_catalog(
            pb::BuiltinCatalog::decode(bytes.as_slice())
                .map_err(|e| TypedError::Decode(e.to_string()))?,
        )?;
        // Creation's fixed i64 cost domain is an adapter requirement, not a
        // Rust primitive callable registry.
        let request = pb::CreateEGraphRequest {
            record_history,
            sorts: vec![pb::Sort {
                kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                    name: "i64".into(),
                    args: vec![],
                })),
                ..Default::default()
            }],
            options: Some(pb::EGraphOptions {
                cost_sort: Some(0),
                execution_mode: pb::ExecutionMode::Normal as i32,
                ..Default::default()
            }),
            ..Default::default()
        };
        let response = engine
            .create(&request.encode_to_vec())
            .map_err(|e| TypedError::Invalid(e.to_string()))?;
        let handle = pb::CreateEGraphResponse::decode(response.as_slice())
            .map_err(|e| TypedError::Decode(e.to_string()))?
            .egraph_id;
        Ok(Self {
            engine: Arc::new(Mutex::new(engine)),
            builtins,
            discarded: Arc::new(Mutex::new(vec![])),
            handle,
            usable: true,
            declarations: HashMap::new(),
            scopes: vec![],
            captures: HashMap::new(),
            private_slots: HashSet::new(),
            reserved_names: HashSet::new(),
            next_capture: 0,
            #[cfg(test)]
            last_wire: None,
        })
    }

    /// Clone native state and cursors through bytes, with independent binding
    /// observations. Subsequent mutations of either handle remain independent.
    /// The clone starts with an empty scope stack, even when the source has scopes.
    pub fn try_clone(&self) -> Result<Self, TypedError> {
        if !self.usable {
            return Err(TypedError::Invalid(
                "session transport state is unknown".into(),
            ));
        }
        let bytes = self
            .lock_engine()?
            .clone_egraph(
                &pb::CloneEGraphRequest {
                    egraph_id: self.handle,
                }
                .encode_to_vec(),
            )
            .map_err(|e| TypedError::Invalid(e.to_string()))?;
        let handle = pb::CloneEGraphResponse::decode(bytes.as_slice())
            .map_err(|e| TypedError::Decode(e.to_string()))?
            .egraph_id;
        Ok(Self {
            engine: self.engine.clone(),
            builtins: self.builtins.clone(),
            discarded: self.discarded.clone(),
            handle,
            usable: true,
            declarations: self.declarations.clone(),
            scopes: vec![],
            captures: self.captures.clone(),
            private_slots: self.private_slots.clone(),
            reserved_names: self.reserved_names.clone(),
            next_capture: self.next_capture,
            #[cfg(test)]
            last_wire: None,
        })
    }

    /// Save native data, cursors and typed binding state in a new scope.
    pub fn push(&mut self) -> Result<(), TypedError> {
        if !self.usable {
            return Err(TypedError::Invalid(
                "session transport state is unknown".into(),
            ));
        }
        let declarations = self.declarations.clone();
        let bytes = self
            .lock_engine()?
            .clone_egraph(
                &pb::CloneEGraphRequest {
                    egraph_id: self.handle,
                }
                .encode_to_vec(),
            )
            .map_err(|e| TypedError::Invalid(e.to_string()))?;
        let handle = pb::CloneEGraphResponse::decode(bytes.as_slice())
            .map_err(|e| TypedError::Decode(e.to_string()))?
            .egraph_id;
        self.scopes.push(SavedScope {
            handle: std::mem::replace(&mut self.handle, handle),
            declarations: std::mem::replace(&mut self.declarations, declarations),
            captures: self.captures.clone(),
            private_slots: self.private_slots.clone(),
        });
        Ok(())
    }

    /// Restore the latest scope, including typed bindings and health.
    /// Destroy the active graph and its diagnostics, then resume saved state.
    /// Fresh-name state survives; an empty stack or rejected destroy changes nothing.
    pub fn pop(&mut self) -> Result<(), TypedError> {
        if self.scopes.is_empty() {
            return Err(TypedError::Invalid("no saved scope".into()));
        }
        let bytes = self
            .lock_engine()?
            .destroy(
                &pb::DestroyEGraphRequest {
                    egraph_id: self.handle,
                }
                .encode_to_vec(),
            )
            .map_err(|e| TypedError::Invalid(e.to_string()))?;
        self.finish_pop(&bytes)
    }

    // A successful destroy has already disposed the active handle. Transfer
    // ownership before decoding its acknowledgement so even a corrupt reply
    // cannot make Drop destroy that handle again.
    fn finish_pop(&mut self, bytes: &[u8]) -> Result<(), TypedError> {
        let saved = self.scopes.pop().expect("pop checked the saved frame");
        self.handle = saved.handle;
        self.declarations = saved.declarations;
        self.captures = saved.captures;
        self.private_slots = saved.private_slots;
        self.usable = true;
        pb::DestroyEGraphResponse::decode(bytes).map_err(|e| {
            self.usable = false;
            TypedError::Decode(e.to_string())
        })?;
        Ok(())
    }

    fn prepare_request(
        &mut self,
        packer: &mut Packer,
        diagnostics: bool,
    ) -> Result<Vec<u8>, TypedError> {
        if !self.usable {
            return Err(TypedError::Invalid(
                "session transport state is unknown".into(),
            ));
        }
        packer.finish()?;
        for demand in &packer.builtin_demands {
            let (name, kind) = if demand.arena == Arena::PrimitiveSort {
                (
                    &demand.primitive_sort()?.name,
                    DeclarationKind::PrimitiveSort,
                )
            } else {
                (&demand.primitive()?.name, DeclarationKind::Callable)
            };
            let actual = self.builtins.declaration(name, kind)?;
            if !super::decl::same_builtin(demand, &actual)? {
                return Err(TypedError::Invalid(format!(
                    "backend builtin signature differs: {name}"
                )));
            }
        }
        if packer.observed_data {
            return Err(TypedError::Invalid(
                "snapshot observations cannot be submitted as live expressions".into(),
            ));
        }
        if packer
            .ordinary_callables
            .iter()
            .any(|name| self.private_slots.contains(name))
        {
            return Err(TypedError::Invalid(
                "ordinary callable collides with private capture storage".into(),
            ));
        }
        // These are attempted-name reservations, not evidence of installation.
        // A no-location or undecodable response must not make a slot reusable.
        self.reserved_names
            .extend(packer.ordinary_callables.iter().cloned());
        for (_, _, name) in &packer.initializations {
            self.private_slots.insert(name.clone());
            self.reserved_names.insert(name.clone());
        }
        if let Some(next) = packer.capture_counter {
            self.next_capture = next;
        }
        let message = pb::RunProgramRequest {
            egraph_id: self.handle,
            program: Some(std::mem::take(&mut packer.program)),
            diagnostics,
        };
        let request = message.encode_to_vec();
        packer.program = message.program.unwrap();
        Ok(request)
    }

    fn execute(
        &mut self,
        mut packer: Packer,
        diagnostics: bool,
    ) -> Result<Vec<pb::RunProgramResponse>, TypedError> {
        let request = self.prepare_request(&mut packer, diagnostics)?;
        let bytes = self
            .lock_engine()?
            .run(&request)
            .map_err(|e| TypedError::Invalid(e.to_string()))?;
        #[cfg(test)]
        {
            self.last_wire = Some((request, bytes.clone()));
        }
        self.accept_response(packer, &bytes)
    }

    // Retain the actual frame sequence. A malformed later frame cannot erase a
    // known earlier prefix, but it does make subsequent execution uncertain.
    fn accept_response(
        &mut self,
        packer: Packer,
        bytes: &[Vec<u8>],
    ) -> Result<Vec<pb::RunProgramResponse>, TypedError> {
        let mut frames = Vec::with_capacity(bytes.len());
        for bytes in bytes {
            match pb::RunProgramResponse::decode(bytes.as_slice()) {
                Ok(frame) if frame.result.is_some() => frames.push(frame),
                result => {
                    let _ = self.acknowledge(packer, &frames, false);
                    self.usable = false;
                    return Err(TypedError::Decode(match result {
                        Err(error) => error.to_string(),
                        _ => "missing response frame result".into(),
                    }));
                }
            }
        }
        let valid_terminal = frames.last().is_some_and(|frame| match &frame.result {
            Some(pb::run_program_response::Result::Error(_)) => true,
            Some(pb::run_program_response::Result::Output(output)) => {
                output.outputs.is_empty() && output.nodes.is_empty() && output.sorts.is_empty()
            }
            None => false,
        });
        if !valid_terminal
            || frames
                .iter()
                .take(frames.len().saturating_sub(1))
                .any(|frame| {
                    matches!(
                        frame.result,
                        Some(pb::run_program_response::Result::Error(_))
                    )
                })
        {
            let _ = self.acknowledge(packer, &frames, false);
            self.usable = false;
            return Err(TypedError::Decode("invalid terminal response frame".into()));
        }
        self.acknowledge(packer, &frames, true)?;
        if frames.last().is_some_and(|frame| {
            matches!(
                frame.result,
                Some(pb::run_program_response::Result::Error(_))
            )
        }) {
            return Err(TypedError::Engine(Box::new(frames.pop().unwrap())));
        }
        Ok(frames)
    }

    // Apply only completed observations or the real located terminal failure.
    // Cancellation acknowledges no fabricated result or successful completion.
    fn acknowledge(
        &mut self,
        packer: Packer,
        frames: &[pb::RunProgramResponse],
        finished: bool,
    ) -> Result<(), TypedError> {
        let error = frames.iter().find_map(|frame| match &frame.result {
            Some(pb::run_program_response::Result::Error(error)) => Some(error),
            _ => None,
        });
        let observed = frames
            .iter()
            .filter_map(|frame| match &frame.result {
                Some(pb::run_program_response::Result::Output(output)) => Some(&output.outputs),
                _ => None,
            })
            .flatten()
            .collect::<Vec<_>>();
        let completed = match error {
            None if finished => packer.program.commands.len(),
            None => observed
                .iter()
                .filter_map(|output| output.location.as_ref()?.path.first())
                .copied()
                .max()
                .unwrap_or(0) as usize,
            Some(error) => match &error.location {
                None => 0,
                Some(location) => {
                    if location.path.is_empty()
                        || location.path.len() != location.iterations.len() + 1
                        || location.path[0] as usize >= packer.program.commands.len()
                        || error.code == pb::ErrorCode::InvalidProgram as i32
                    {
                        self.usable = false;
                        return Err(TypedError::Decode(
                            "invalid command failure location; completion unknown".into(),
                        ));
                    }
                    let mut command = &packer.program.commands[location.path[0] as usize];
                    for child in &location.path[1..] {
                        let Some(pb::command::Kind::Loop(body)) = &command.kind else {
                            self.usable = false;
                            return Err(TypedError::Decode(
                                "failure path enters a non-loop".into(),
                            ));
                        };
                        let Some(next) = body.body.get(*child as usize) else {
                            self.usable = false;
                            return Err(TypedError::Decode(
                                "failure child index out of bounds".into(),
                            ));
                        };
                        command = next;
                    }
                    location.path[0] as usize
                }
            },
        };
        if finished && error.is_none()
            || error.is_some_and(|e| e.location.is_some())
            || !observed.is_empty()
        {
            self.declarations.extend(packer.declarations);
        }
        for (index, recipe, slot) in packer.initializations {
            if (index as usize) < completed {
                let name = recipe.capture()?.expect("planned capture").name;
                self.captures.insert(name, (recipe, slot));
            }
        }
        Ok(())
    }

    /// Submit expressions and row writes/deletions as ordered top-level actions.
    pub fn register(&mut self, values: impl Actions) -> Result<(), TypedError> {
        let mut packer = Packer::default();
        let mut actions = vec![];
        let mut declarations = vec![];
        let mut operands = vec![];
        values.append_actions(&mut actions, &mut declarations, &mut |expr| {
            let index = u32::try_from(operands.len()).expect("protobuf arena exceeds u32");
            operands.push(expr.0);
            index
        })?;
        let roots: Vec<_> = operands
            .iter()
            .cloned()
            .chain(declarations.iter().map(|d| d.0.clone()))
            .collect();
        let mut captures = CapturePlan::new(self, &roots)?;
        for declaration in declarations {
            packer.intern(declaration.0, 0);
        }
        for mut action in actions {
            let mut roots = vec![];
            visit_action(&mut action, |index| {
                roots.push(operands[index as usize].clone());
                Ok(index)
            })?;
            captures.materialize(&roots, true, &mut packer)?;
            if matches!(&action.kind, Some(pb::action::Kind::Term(index)) if operands[*index as usize].capture()?.is_some())
            {
                continue;
            }
            visit_action(&mut action, |index| {
                Ok(packer.intern(operands[index as usize].clone(), 0))
            })?;
            packer.program.commands.push(pb::Command {
                kind: Some(pb::command::Kind::Action(action)),
                ..Default::default()
            });
        }
        packer.capture_counter = Some(captures.next);
        self.execute(packer, false)?;
        Ok(())
    }

    /// Execute an authored schedule with optional diagnostics collection disabled.
    pub fn run(
        &mut self,
        schedule: impl Into<super::Schedule>,
    ) -> Result<super::RunResult, TypedError> {
        let response = self.execute(pack_schedule(schedule.into(), false)?, false)?;
        Ok(select_run(response, false)?.0)
    }

    /// Execute a schedule and return its backend-specific diagnostic document.
    pub fn run_with_diagnostics(
        &mut self,
        schedule: impl Into<super::Schedule>,
    ) -> Result<(super::RunResult, super::Diagnostic), TypedError> {
        let response = self.execute(pack_schedule(schedule.into(), false)?, true)?;
        let (result, diagnostic) = select_run(response, true)?;
        Ok((
            result,
            diagnostic.expect("required diagnostic was validated"),
        ))
    }

    /// Deliver the owned snapshots requested by Schedule::with_snapshots while
    /// the schedule is still executing. Break cancels at a safe command boundary;
    /// completed effects remain, and cancellation does not return a RunResult.
    pub fn run_stream(
        &mut self,
        schedule: impl Into<super::Schedule>,
        mut observe: impl FnMut(super::Snapshot) -> ControlFlow<()>,
    ) -> Result<super::RunResult, TypedError> {
        let mut packer = pack_schedule(schedule.into(), true)?;
        let request = self.prepare_request(&mut packer, false)?;
        let captures = self.captures.values().cloned().collect::<Vec<_>>();
        let builtins = self.builtins.clone();
        let mut prefix = None;
        let mut terminal_error = None;
        let mut result = None;
        let mut decode_error = None;
        let mut observer_panic = None;
        let (transport, cleanup) = {
            let mut engine = self.lock_engine()?;
            let transport = engine.run_stream(&request, &mut |frame| {
                let mut flow = ControlFlow::Continue(());
                match &frame.result {
                    Some(pb::run_program_response::Result::Output(payload)) => {
                        for output in &payload.outputs {
                            match &output.kind {
                                Some(pb::command_output::Kind::Snapshot(export)) => {
                                    match super::Snapshot::from_export(
                                        export.clone(),
                                        captures.clone(),
                                        &builtins,
                                    ) {
                                        Ok(snapshot) => match std::panic::catch_unwind(
                                            std::panic::AssertUnwindSafe(|| observe(snapshot)),
                                        ) {
                                            Ok(next) => flow = next,
                                            Err(payload) => {
                                                observer_panic = Some(payload);
                                                flow = ControlFlow::Break(());
                                            }
                                        },
                                        Err(error) => {
                                            decode_error = Some(error);
                                            flow = ControlFlow::Break(());
                                        }
                                    }
                                }
                                Some(pb::command_output::Kind::Run(value)) if result.is_none() => {
                                    result = Some(*value)
                                }
                                _ => {
                                    decode_error = Some(TypedError::Decode(
                                        "unexpected streamed schedule observation".into(),
                                    ));
                                    flow = ControlFlow::Break(());
                                }
                            }
                            if flow.is_break() {
                                break;
                            }
                        }
                        if !payload.outputs.is_empty() {
                            prefix = Some(frame);
                        }
                    }
                    Some(pb::run_program_response::Result::Error(_)) => {
                        terminal_error = Some(frame)
                    }
                    None => {
                        decode_error =
                            Some(TypedError::Decode("missing streamed frame result".into()));
                        flow = ControlFlow::Break(());
                    }
                }
                flow
            });
            let cleanup = drain_discarded(&mut engine, &self.discarded);
            (transport, cleanup)
        };
        let mut frames = prefix.into_iter().collect::<Vec<_>>();
        if let Some(error) = terminal_error {
            frames.push(error);
        }
        if let Some(payload) = observer_panic {
            let _ = self.acknowledge(packer, &frames, false);
            std::panic::resume_unwind(payload);
        }
        self.acknowledge(packer, &frames, transport.is_ok())?;
        if let Some(error) = decode_error {
            return Err(error);
        }
        if frames.last().is_some_and(|frame| {
            matches!(
                frame.result,
                Some(pb::run_program_response::Result::Error(_))
            )
        }) {
            return Err(TypedError::Engine(Box::new(frames.pop().unwrap())));
        }
        cleanup?;
        transport.map_err(|error| TypedError::Invalid(error.to_string()))?;
        result.ok_or_else(|| TypedError::Decode("missing completed schedule result".into()))
    }

    /// Observe cumulative backend diagnostics without executing a schedule.
    pub fn stats(&mut self) -> Result<super::Diagnostic, TypedError> {
        let mut packer = Packer::default();
        packer.program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Stats(pb::Unit {})),
            ..Default::default()
        });
        let (response, _files) = one_observation(self.execute(packer, false)?)?;
        let [output] = response.outputs.as_slice() else {
            return Err(TypedError::Decode(
                "missing or extra statistics observation".into(),
            ));
        };
        if output
            .location
            .as_ref()
            .is_none_or(|location| location.path != [0] || !location.iterations.is_empty())
        {
            return Err(TypedError::Decode("unexpected statistics location".into()));
        }
        let Some(pb::command_output::Kind::Diagnostic(diagnostic)) = &output.kind else {
            return Err(TypedError::Decode(
                "wrong statistics observation kind".into(),
            ));
        };
        Ok(diagnostic.clone())
    }

    /// Observe independent logical state through Freeze bytes without evaluating roots.
    /// This observation is included when execution recording is enabled.
    pub fn freeze(&mut self) -> Result<super::Snapshot, TypedError> {
        let mut packer = Packer::default();
        packer.program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Freeze(pb::Freeze {})),
            ..Default::default()
        });
        let (response, _files) = one_observation(self.execute(packer, false)?)?;
        let mut outputs = response.outputs.into_iter();
        let Some(pb::CommandOutput {
            kind: Some(pb::command_output::Kind::Snapshot(snapshot)),
            ..
        }) = outputs.next()
        else {
            return Err(TypedError::Decode("missing Freeze observation".into()));
        };
        if outputs.next().is_some() {
            return Err(TypedError::Decode("extra Freeze observations".into()));
        }
        super::Snapshot::from_export(
            snapshot,
            self.captures.values().cloned().collect(),
            &self.builtins,
        )
    }

    /// Retrieve accumulated accepted inputs; errors when recording is off.
    /// Retrieval adds no commands. Pop restores the saved history prefix.
    pub fn history(&self) -> Result<pb::Program, TypedError> {
        let mut engine = match self.engine.try_lock() {
            Ok(engine) => engine,
            Err(TryLockError::Poisoned(poison)) => poison.into_inner(),
            Err(TryLockError::WouldBlock) => {
                return Err(TypedError::Invalid(
                    "byte engine is already executing".into(),
                ));
            }
        };
        drain_discarded(&mut engine, &self.discarded)?;
        let bytes = engine
            .get_history(
                &pb::GetHistoryRequest {
                    egraph_id: self.handle,
                }
                .encode_to_vec(),
            )
            .map_err(|error| TypedError::Invalid(error.to_string()))?;
        pb::Program::decode(bytes.as_slice()).map_err(|error| TypedError::Decode(error.to_string()))
    }

    /// Count visible portable table rows without evaluating any expression.
    pub fn num_tuples(&mut self) -> Result<usize, TypedError> {
        let mut packer = Packer::default();
        packer.program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::TableSizes(pb::GetTableSizes::default())),
            ..Default::default()
        });
        let (response, _files) = one_observation(self.execute(packer, false)?)?;
        let mut outputs = response.outputs.into_iter();
        let Some(pb::CommandOutput {
            kind: Some(pb::command_output::Kind::Sizes(sizes)),
            ..
        }) = outputs.next()
        else {
            return Err(TypedError::Decode("missing table size observation".into()));
        };
        if outputs.next().is_some() {
            return Err(TypedError::Decode("extra table size observations".into()));
        }
        sizes.sizes.into_iter().try_fold(0usize, |total, size| {
            usize::try_from(size.rows)
                .ok()
                .and_then(|size| total.checked_add(size))
                .ok_or_else(|| TypedError::Decode("table row count exceeds usize".into()))
        })
    }

    /// Query all facts in one binder without inserting missing rows.
    pub fn check(&mut self, facts: impl Facts) -> Result<bool, TypedError> {
        let mut roots = vec![];
        facts.append(&mut roots);
        let roots: Vec<_> = roots.into_iter().map(|e| e.0).collect();
        let mut packer = Packer::default();
        CapturePlan::new(self, &roots)?.materialize(&roots, false, &mut packer)?;
        packer.binders.push(super::close::binder(&roots)?);
        let facts = roots.into_iter().map(|r| packer.intern(r, 1)).collect();
        packer.program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Check(pb::Check { facts })),
            ..Default::default()
        });
        match self.execute(packer, false) {
            Ok(_) => Ok(true),
            Err(TypedError::Engine(frame)) if matches!(&frame.result, Some(pb::run_program_response::Result::Error(error)) if error.code == pb::ErrorCode::CheckFailed as i32) => {
                Ok(false)
            }
            Err(error) => Err(error),
        }
    }

    /// Tree-extract a value and own its finite constructor/scalar/container closure.
    pub fn extract<L: ValueInput>(&mut self, root: L) -> Result<L::Owned, TypedError> {
        let mut packer = Packer::default();
        let root = root.borrow().expression().0.clone();
        let mut captures = CapturePlan::new(self, std::slice::from_ref(&root))?;
        captures.materialize(std::slice::from_ref(&root), true, &mut packer)?;
        packer.capture_counter = Some(captures.next);
        let index = packer.intern(root, 0);
        packer.program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Extract(pb::Extract {
                roots: vec![index],
                variants: 1,
                extractor: pb::Extractor::Tree.into(),
                ..Default::default()
            })),
            ..Default::default()
        });
        let (response, _files) = one_observation(self.execute(packer, false)?)?;
        let term = response
            .outputs
            .iter()
            .find_map(|output| match &output.kind {
                Some(pb::command_output::Kind::Extraction(result)) => {
                    result.roots.first()?.variants.first().map(|v| v.term)
                }
                _ => None,
            })
            .ok_or_else(|| TypedError::Decode("missing extraction result".into()))?;
        ensure_sort(adopt(
            &response,
            term,
            self.declarations.values().cloned().collect(),
            &self.builtins,
        )?)
    }
}

// Pack one high-level schedule as a single control result, keeping AddRules
// ordered before its selected groups and snapshots at the authored cadence.
fn pack_schedule(schedule: super::Schedule, snapshots: bool) -> Result<Packer, TypedError> {
    let mut pending = schedule.commands.iter().collect::<Vec<_>>();
    while let Some(command) = pending.pop() {
        match &command.kind {
            Some(pb::command::Kind::Loop(repeat)) => pending.extend(&repeat.body),
            Some(pb::command::Kind::Freeze(_)) if !snapshots => {
                return Err(TypedError::Invalid(
                    "snapshot schedules require run_stream".into(),
                ));
            }
            _ => (),
        }
    }
    let mut packer = Packer::default();
    for group in schedule.rulesets {
        if let Some(error) = group.1 {
            return Err(TypedError::Invalid(error));
        }
        for addition in group.0 {
            packer.intern(addition, 0);
        }
    }
    packer.finish()?;
    packer.program.commands.extend(schedule.commands);
    if packer.program.commands.len() != 1
        || !matches!(
            packer.program.commands[0].kind,
            Some(pb::command::Kind::Run(_) | pb::command::Kind::Loop(_))
        )
    {
        packer.program.commands = vec![pb::Command {
            kind: Some(pb::command::Kind::Loop(pb::Loop {
                body: std::mem::take(&mut packer.program.commands),
                max_iterations: Some(1),
                ..Default::default()
            })),
            ..Default::default()
        }];
    }
    Ok(packer)
}

// The diagnostic is an opaque document, never a second source of control flags.
fn select_run(
    frames: Vec<pb::RunProgramResponse>,
    diagnostics: bool,
) -> Result<(pb::RunResult, Option<pb::Diagnostic>), TypedError> {
    let mut outputs = frames
        .into_iter()
        .filter_map(|frame| match frame.result {
            Some(pb::run_program_response::Result::Output(output)) => Some(output.outputs),
            _ => None,
        })
        .flatten();
    let first = outputs
        .next()
        .ok_or_else(|| TypedError::Decode("missing schedule result".into()))?;
    if first
        .location
        .as_ref()
        .is_none_or(|location| location.path != [0] || !location.iterations.is_empty())
    {
        return Err(TypedError::Decode(
            "unexpected schedule result location".into(),
        ));
    }
    let Some(pb::command_output::Kind::Run(result)) = first.kind else {
        return Err(TypedError::Decode("wrong schedule result kind".into()));
    };
    let diagnostic = if diagnostics {
        let next = outputs
            .next()
            .ok_or_else(|| TypedError::Decode("missing schedule diagnostic".into()))?;
        if next.location != first.location {
            return Err(TypedError::Decode(
                "diagnostic location differs from its result".into(),
            ));
        }
        let Some(pb::command_output::Kind::Diagnostic(diagnostic)) = next.kind else {
            return Err(TypedError::Decode("wrong schedule diagnostic kind".into()));
        };
        Some(diagnostic)
    } else {
        None
    };
    if outputs.next().is_some() {
        return Err(TypedError::Decode("extra schedule observations".into()));
    }
    Ok((result, diagnostic))
}

// A selected observation keeps exactly its actual frame's graph and origins.
// Empty completion frames carry no observation and are never a data owner.
fn one_observation(
    frames: Vec<pb::RunProgramResponse>,
) -> Result<(pb::RunProgramOutput, Vec<pb::SourceFile>), TypedError> {
    let mut selected = None;
    for frame in frames {
        let Some(pb::run_program_response::Result::Output(output)) = frame.result else {
            return Err(TypedError::Decode(
                "expected a successful observation frame".into(),
            ));
        };
        if output.outputs.is_empty() {
            continue;
        }
        if output.outputs.len() != 1 || selected.is_some() {
            return Err(TypedError::Decode("missing or extra observation".into()));
        }
        selected = Some((output, frame.files));
    }
    selected.ok_or_else(|| TypedError::Decode("missing observation".into()))
}

// Adopt only the selected inert term closure. Other response nodes can be
// scalar costs or independent observations and are not this expression's roots.
fn adopt(
    response: &pb::RunProgramOutput,
    root: u32,
    mut declarations: Vec<Record>,
    builtins: &Record,
) -> Result<Expr, TypedError> {
    let mut program = pb::Program {
        ..Default::default()
    };
    let mut ids = HashMap::from([(root, 0u32)]);
    let mut pending = vec![root];
    let mut sorts = HashMap::new();
    let mut sort_pending = vec![];
    let mut cursor = 0;
    while cursor < pending.len() {
        let old = pending[cursor];
        let mut node = response
            .nodes
            .get(old as usize)
            .cloned()
            .ok_or_else(|| TypedError::Decode("invalid response node index".into()))?;
        let index = if let Some(index) = sorts.get(&node.sort_id) {
            *index
        } else {
            let index = program.sorts.len() as u32;
            program.sorts.push(pb::Sort::default());
            sort_pending.push(node.sort_id);
            sorts.insert(node.sort_id, index);
            index
        };
        node.sort_id = index;
        let mut relocate = |child: &mut u32| {
            let next = ids.len() as u32;
            if let std::collections::hash_map::Entry::Vacant(entry) = ids.entry(*child) {
                entry.insert(next);
                pending.push(*child);
            }
            *child = ids[child];
        };
        match &mut node.kind {
            Some(pb::node::Kind::Call(call)) => call.args.iter_mut().for_each(&mut relocate),
            Some(pb::node::Kind::Apply(apply)) => {
                apply.function.iter_mut().for_each(&mut relocate);
                apply.args.iter_mut().for_each(&mut relocate);
            }
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::PartialCall(call)),
            })) => call.args.iter_mut().for_each(&mut relocate),
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Maybe(maybe)),
            })) => maybe.value.iter_mut().for_each(&mut relocate),
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value:
                    Some(
                        pb::primitive_value::Value::Vec(values)
                        | pb::primitive_value::Value::Set(values)
                        | pb::primitive_value::Value::Multiset(values),
                    ),
            })) => values.items.iter_mut().for_each(&mut relocate),
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Map(map)),
            })) => {
                for entry in &mut map.entries {
                    for child in [&mut entry.key, &mut entry.value] {
                        relocate(
                            child
                                .as_mut()
                                .ok_or_else(|| TypedError::Decode("missing Map child".into()))?,
                        );
                    }
                }
            }
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Pair(pair)),
            })) => {
                for child in [&mut pair.first, &mut pair.second] {
                    relocate(
                        child
                            .as_mut()
                            .ok_or_else(|| TypedError::Decode("missing Pair child".into()))?,
                    );
                }
            }
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
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
            })) => {}
            _ => {
                return Err(TypedError::Decode(
                    "extraction must contain inert constructor/value data".into(),
                ));
            }
        }
        program.nodes.push(node);
        cursor += 1;
    }
    let mut cursor = 0;
    while cursor < sort_pending.len() {
        let old = sort_pending[cursor];
        let mut sort = response
            .sorts
            .get(old as usize)
            .cloned()
            .ok_or_else(|| TypedError::Decode("invalid response sort index".into()))?;
        match &mut sort.kind {
            Some(pb::sort::Kind::Eq(name)) => program.declarations.push(pb::Declaration {
                kind: Some(pb::declaration::Kind::EqSort(pb::EqSort {
                    name: name.clone(),
                })),
                ..Default::default()
            }),
            Some(pb::sort::Kind::Application(f))
                if (matches!(f.name.as_str(), "Vec" | "Set" | "MultiSet" | "Maybe")
                    && f.args.len() == 1)
                    || (matches!(f.name.as_str(), "Pair" | "Map") && f.args.len() == 2)
                    || (matches!(
                        f.name.as_str(),
                        "i64"
                            | "f64"
                            | "String"
                            | "bool"
                            | "Unit"
                            | "BigInt"
                            | "BigRat"
                            | "Rational"
                    ) && f.args.is_empty()) =>
            {
                declarations.push(
                    super::storage::builtin_catalog()
                        .declaration(&f.name, DeclarationKind::PrimitiveSort)?,
                );
                for child in &mut f.args {
                    let next = sorts.len() as u32;
                    if let std::collections::hash_map::Entry::Vacant(entry) = sorts.entry(*child) {
                        entry.insert(next);
                        sort_pending.push(*child);
                        program.sorts.push(pb::Sort::default());
                    }
                    *child = sorts[child];
                }
            }
            Some(pb::sort::Kind::Func(function)) => {
                for child in function.params.iter_mut().chain([&mut function.result]) {
                    let next = sorts.len() as u32;
                    if let std::collections::hash_map::Entry::Vacant(entry) = sorts.entry(*child) {
                        entry.insert(next);
                        sort_pending.push(*child);
                        program.sorts.push(pb::Sort::default());
                    }
                    *child = sorts[child];
                }
            }
            _ => return Err(TypedError::Decode("unsupported extracted sort".into())),
        }
        program.sorts[sorts[&old] as usize] = sort;
        cursor += 1;
    }
    let mut slots = std::array::from_fn(|_| vec![]);
    slots[Arena::Node as usize] = (0..program.nodes.len() as u32).map(Slot::Local).collect();
    slots[Arena::Sort as usize] = (0..program.sorts.len() as u32).map(Slot::Local).collect();
    let mut record = publish(program, slots, declarations, Arena::Node, 0, vec![])?;
    std::sync::Arc::get_mut(record.owner.as_mut().unwrap())
        .expect("fresh adopted owner")
        .ambient = builtins.owner.clone();
    let result = Expr(record);
    result.validate_inert()?;
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typed::Ruleset;
    use crate::typed::tests::observations::Observed;

    fn diagnostic_matches(diagnostic: &pb::Diagnostic) -> u64 {
        assert_eq!(diagnostic.format, "application/vnd.egglog.run-report+json");
        let value: serde_json::Value = serde_json::from_slice(&diagnostic.content).unwrap();
        assert!(value.get("updated").is_none());
        assert!(value.get("can_stop").is_none());
        value["num_matches_per_rule"]
            .as_object()
            .unwrap()
            .values()
            .map(|value| value.as_u64().unwrap())
            .sum()
    }

    fn pack_run(group: &Ruleset) -> Packer {
        let schedule = super::super::Schedule::from(group);
        let mut packer = Packer::default();
        for addition in &group.0 {
            packer.intern(addition.clone(), 0);
        }
        packer.finish().unwrap();
        packer.program.commands.extend(schedule.commands);
        packer
    }

    #[test]
    fn input_history_is_opt_in_and_scopes_restore_the_saved_prefix() {
        assert!(EGraph::new().unwrap().history().is_err());
        let mut graph = EGraph::with_recording(true).unwrap();
        assert_eq!(graph.history().unwrap().commands.len(), 0);
        graph.stats().unwrap();
        let mut cloned = graph.try_clone().unwrap();
        assert_eq!(graph.history().unwrap().commands.len(), 1);
        assert_eq!(cloned.history().unwrap().commands.len(), 1);
        cloned.freeze().unwrap();
        assert_eq!(cloned.history().unwrap().commands.len(), 2);
        assert_eq!(graph.history().unwrap().commands.len(), 1);
        graph.push().unwrap();
        let active = graph.handle;
        graph.stats().unwrap();
        graph.pop().unwrap();
        let history = graph.history().unwrap();
        assert_eq!(history.commands.len(), 1);
        assert_eq!(graph.history().unwrap(), history);
        assert_eq!(cloned.history().unwrap().commands.len(), 2);
        assert!(
            graph
                .engine
                .lock()
                .unwrap()
                .get_history(&pb::GetHistoryRequest { egraph_id: active }.encode_to_vec())
                .is_err()
        );
    }

    #[test]
    fn input_history_remains_readable_after_engine_mutex_is_poisoned() {
        let graph = EGraph::with_recording(true).unwrap();
        let engine = graph.engine.clone();
        assert!(
            std::thread::spawn(move || {
                let _guard = engine.lock().unwrap();
                panic!("native unwind while holding engine");
            })
            .join()
            .is_err()
        );
        assert_eq!(graph.history().unwrap().commands.len(), 0);
        assert!(graph.try_clone().is_err());
    }

    #[test]
    fn generated_predicate_and_size_views_execute_encoded_method_requests() {
        use crate::typed::builtins::{Bool, I64, bool_ne, get_node_size, get_table_size, value_eq};
        let mut graph = EGraph::default();
        for (value, expected, identity) in [
            (bool_ne(I64::from(2), 3_i64), true, "egglog.core.bool_ne"),
            (
                I64::from(2).bool_eq(3_i64),
                false,
                "egglog.core.i64.bool_eq",
            ),
        ] {
            assert_eq!(
                bool::try_from(&graph.extract(value).unwrap()).unwrap(),
                expected
            );
            let request =
                pb::RunProgramRequest::decode(graph.last_wire.as_ref().unwrap().0.as_slice())
                    .unwrap()
                    .program
                    .unwrap();
            assert!(
                request.nodes.iter().any(
                    |n| matches!(&n.kind, Some(pb::node::Kind::Call(c)) if c.func == identity)
                )
            );
        }
        for (fact, expected, identity) in [
            (Bool::from(true).guard(), true, "egglog.core.bool.guard"),
            (Bool::from(false).guard(), false, "egglog.core.bool.guard"),
            (value_eq(I64::from(2), 2_i64), true, "egglog.core.value_eq"),
            (value_eq(I64::from(2), 3_i64), false, "egglog.core.value_eq"),
        ] {
            assert_eq!(graph.check(fact).unwrap(), expected);
            let request =
                pb::RunProgramRequest::decode(graph.last_wire.as_ref().unwrap().0.as_slice())
                    .unwrap()
                    .program
                    .unwrap();
            assert!(matches!(
                request.commands[0].kind,
                Some(pb::command::Kind::Check(_))
            ));
            assert!(
                request.nodes.iter().any(
                    |n| matches!(&n.kind, Some(pb::node::Kind::Call(c)) if c.func == identity)
                )
            );
        }
        for (value, identity, arity) in [
            (get_node_size(), "egglog.experimental.size.nodes", 0),
            (
                get_table_size(std::iter::empty::<&str>()),
                "egglog.experimental.size.tables",
                0,
            ),
            (
                get_table_size(["absent-a", "absent-b"]),
                "egglog.experimental.size.tables",
                2,
            ),
        ] {
            assert_eq!(i64::try_from(&graph.extract(value).unwrap()).unwrap(), 0);
            let request =
                pb::RunProgramRequest::decode(graph.last_wire.as_ref().unwrap().0.as_slice())
                    .unwrap()
                    .program
                    .unwrap();
            assert!(request.nodes.iter().any(|n| matches!(&n.kind, Some(pb::node::Kind::Call(c)) if c.func == identity && c.args.len() == arity)));
        }
    }

    #[test]
    fn generated_function_input_views_execute_encoded_method_requests() {
        use crate::typed::builtins::{Function, I64, Map, Maybe, Vec as EVec};
        let mut graph = EGraph::default();
        let callback =
            Function::<(I64,), I64>::with_captures((I64::from(10),), |(captured,), x| captured + x)
                .unwrap();
        let values = graph
            .extract(EVec::<I64>::of([1_i64, 2]).map(callback))
            .unwrap();
        assert_eq!(
            Vec::<I64>::try_from(&values)
                .unwrap()
                .iter()
                .map(|value| i64::try_from(value).unwrap())
                .collect::<Vec<_>>(),
            [11, 12]
        );
        let mut requests = vec![(
            graph.last_wire.as_ref().unwrap().0.clone(),
            "egglog.core.vec.map",
        )];

        let callback =
            Function::<(I64, I64, I64), I64>::new(|acc, key, value| acc + key + value).unwrap();
        let value = graph
            .extract(
                Map::<I64, I64>::of([(1_i64, 2_i64), (3_i64, 4_i64)])
                    .fold_kv(callback, I64::from(0)),
            )
            .unwrap();
        assert_eq!(i64::try_from(&value).unwrap(), 10);
        requests.push((
            graph.last_wire.as_ref().unwrap().0.clone(),
            "egglog.experimental.map.fold_kv",
        ));

        for (thunk, expected) in [
            (
                Function::<(), I64>::new(|| I64::from(7)).unwrap(),
                Some(I64::from(7)),
            ),
            (
                Function::<(), I64>::new(|| I64::from(1) / I64::from(0)).unwrap(),
                None,
            ),
        ] {
            let value = graph.extract(Maybe::<I64>::catch(thunk)).unwrap();
            assert_eq!(Option::<I64>::try_from(&value).unwrap(), expected);
            requests.push((
                graph.last_wire.as_ref().unwrap().0.clone(),
                "egglog.experimental.maybe.catch",
            ));
        }
        let failing_callback = Function::<(I64,), I64>::new(|x| I64::from(1) / x).unwrap();
        assert_eq!(
            i64::try_from(
                &graph
                    .extract(Maybe::<I64>::none().match_(failing_callback, I64::from(9)))
                    .unwrap()
            )
            .unwrap(),
            9
        );
        requests.push((
            graph.last_wire.as_ref().unwrap().0.clone(),
            "egglog.experimental.maybe.match",
        ));
        let plus_one = Function::<(I64,), I64>::new(|x| x + I64::from(1)).unwrap();
        assert_eq!(
            i64::try_from(
                &graph
                    .extract(Maybe::<I64>::some(2_i64).match_(plus_one, I64::from(9)))
                    .unwrap()
            )
            .unwrap(),
            3
        );
        requests.push((
            graph.last_wire.as_ref().unwrap().0.clone(),
            "egglog.experimental.maybe.match",
        ));
        for (request, identity) in requests {
            let request = pb::RunProgramRequest::decode(request.as_slice())
                .unwrap()
                .program
                .unwrap();
            assert!(
                request.nodes.iter().any(
                    |n| matches!(&n.kind, Some(pb::node::Kind::Call(c)) if c.func == identity)
                )
            );
            assert!(request.nodes.iter().any(|n| matches!(
                &n.kind,
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::PartialCall(_))
                }))
            )));
        }
    }

    #[test]
    fn generated_subst_view_executes_encoded_method_request() {
        use crate::typed::{
            builtins::{I64, Map, subst},
            eq,
            tests::ActionTerm,
        };
        let root = ActionTerm(Expr::call(
            &Callable::constructor(
                "BuiltinSubstRoot",
                vec![],
                ActionTerm::sort_ref(),
                None,
                false,
            ),
            vec![],
        ));
        let replacement = ActionTerm(Expr::call(
            &Callable::constructor(
                "BuiltinSubstReplacement",
                vec![I64::sort_ref()],
                ActionTerm::sort_ref(),
                None,
                false,
            ),
            vec![I64::from(7).expression().clone()],
        ));
        let mut graph = EGraph::default();
        graph.register((&root, &replacement)).unwrap();
        let copied = subst(
            root.clone(),
            Map::<ActionTerm, ActionTerm>::of([(root, replacement.clone())]),
        );
        let copied = graph.extract(copied).unwrap();
        let request = pb::RunProgramRequest::decode(graph.last_wire.as_ref().unwrap().0.as_slice())
            .unwrap()
            .program
            .unwrap();
        assert!(matches!(
            request.commands[0].kind,
            Some(pb::command::Kind::Extract(_))
        ));
        assert!(request.nodes.iter().any(|n| matches!(&n.kind, Some(pb::node::Kind::Call(c)) if c.func == "egglog.experimental.subst" && c.args.len() == 2)));
        assert!(request.nodes.iter().any(|n| matches!(&n.kind, Some(pb::node::Kind::Call(c)) if c.func == "egglog.core.map.of" && c.args.len() == 1)));
        assert!(graph.check(eq(copied, replacement)).unwrap());
    }

    #[test]
    fn function_values_decode_rejects_partial_signature_corruption() {
        use crate::typed::builtins::{Function, I64};
        let callback =
            Function::<(I64,), I64>::with_captures((I64::from(10),), |(captured,), x| captured + x)
                .unwrap();
        let mut packer = Packer::default();
        let root = packer.intern(callback.expression().0.clone(), 0);
        packer.finish().unwrap();
        let response = pb::RunProgramOutput {
            nodes: packer.program.nodes,
            sorts: packer.program.sorts,
            ..Default::default()
        };
        let declarations = packer.declarations.into_values().collect::<Vec<_>>();
        assert!(
            adopt(
                &response,
                root,
                declarations.clone(),
                super::super::storage::builtin_catalog()
            )
            .is_ok()
        );
        for case in 0..7 {
            let mut invalid = response.clone();
            let float = invalid.sorts.len() as u32;
            invalid.sorts.push(pb::Sort {
                kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                    name: "f64".into(),
                    args: vec![],
                })),
                ..Default::default()
            });
            let function_sort = invalid.nodes[root as usize].sort_id;
            let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::PartialCall(call)),
            })) = &mut invalid.nodes[root as usize].kind
            else {
                panic!()
            };
            let capture = call.args[0];
            match case {
                0 => call.args.clear(),
                1 => call.args.push(capture),
                2 => call.func = "missing-function-value-target".into(),
                3 => {
                    invalid.nodes[capture as usize].sort_id = float;
                    invalid.nodes[capture as usize].kind =
                        Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                            value: Some(pb::primitive_value::Value::F64Bits(1.0_f64.to_bits())),
                        }));
                }
                4 | 5 => {
                    let Some(pb::sort::Kind::Func(function)) =
                        &mut invalid.sorts[function_sort as usize].kind
                    else {
                        panic!()
                    };
                    if case == 4 {
                        function.result = float;
                    } else {
                        function.params[0] = float;
                    }
                }
                _ => invalid.nodes[root as usize].sort_id = float,
            }
            assert!(
                adopt(
                    &invalid,
                    root,
                    declarations.clone(),
                    super::super::storage::builtin_catalog()
                )
                .is_err(),
                "corrupt PartialCall signature {case}"
            );
        }
    }

    #[test]
    fn subsume_absent_rows_match_native_before_check() {
        use crate::typed::{builtins::I64, decl::Callable, delete, subsume, tests::ActionTerm};
        for change in ["delete", "subsume"] {
            let definition = Callable::constructor(
                "ActionAbsent",
                vec![I64::sort_ref()],
                ActionTerm::sort_ref(),
                None,
                false,
            );
            let target = ActionTerm(Expr::call(
                &definition,
                vec![I64::from(71).expression().clone()],
            ));
            let mut graph = EGraph::default();
            let observe = |graph: &mut EGraph, definition: Option<Record>| {
                let mut packer = Packer::default();
                if let Some(definition) = definition {
                    packer.intern(definition, 0);
                }
                packer.program.commands.push(pb::Command {
                    kind: Some(pb::command::Kind::TableSizes(pb::GetTableSizes {
                        tables: vec!["ActionAbsent".into()],
                    })),
                    ..Default::default()
                });
                let response = Observed::from_frames(graph.execute(packer, false).unwrap());
                let Some(pb::command_output::Kind::Sizes(sizes)) = &response.output.outputs[0].kind
                else {
                    panic!()
                };
                sizes.sizes[0].rows
            };
            let before = observe(&mut graph, Some(definition.0));
            graph
                .register(if change == "delete" {
                    delete(&target)
                } else {
                    subsume(&target)
                })
                .unwrap();
            let (input, _) = graph.last_wire.as_ref().unwrap();
            let packet = pb::RunProgramRequest::decode(input.as_slice())
                .unwrap()
                .program
                .unwrap();
            assert_eq!(packet.nodes.len(), 1);
            assert!(matches!(
                packet.nodes[0].kind,
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::I64(71))
                }))
            ));
            assert_eq!(packet.commands.len(), 1);
            let Some(pb::command::Kind::Action(action)) = &packet.commands[0].kind else {
                panic!()
            };
            let call = match (change, &action.kind) {
                ("delete", Some(pb::action::Kind::Delete(call)))
                | ("subsume", Some(pb::action::Kind::Subsume(call))) => call,
                _ => panic!(),
            };
            assert_eq!(call.func, "ActionAbsent");
            assert_eq!(call.args, [0]);
            let after_action = observe(&mut graph, None);
            let check = graph.check(&target).unwrap();
            let after_check = observe(&mut graph, None);

            // Explicit native comparator: this tests backend compatibility,
            // never supplies an alternate typed execution path.
            let mut native = crate::new_experimental_egraph();
            native
                .parse_and_run_program(
                    None,
                    "(sort ActionTerm) (constructor ActionAbsent (i64) ActionTerm)",
                )
                .unwrap();
            let count = |native: &mut egglog::EGraph| {
                let output = native
                    .parse_and_run_program(None, "(print-size ActionAbsent)")
                    .unwrap();
                let egglog::CommandOutput::PrintFunctionSize(rows) = output[0] else {
                    panic!()
                };
                rows as u64
            };
            let native_before = count(&mut native);
            native
                .parse_and_run_program(None, &format!("({change} (ActionAbsent 71))"))
                .unwrap();
            let native_after_action = count(&mut native);
            let native_check = native
                .parse_and_run_program(None, "(check (ActionAbsent 71))")
                .is_ok();
            let native_after_check = count(&mut native);
            assert_eq!(
                (before, after_action, check, after_check),
                (
                    native_before,
                    native_after_action,
                    native_check,
                    native_after_check
                )
            );
            assert_eq!(
                (before, after_action, check, after_check),
                if change == "delete" {
                    (0, 0, false, 0)
                } else {
                    (0, 1, true, 1)
                }
            );
        }
    }

    #[test]
    fn union_subsume_actual_bytes_and_corruption() {
        use crate::typed::{
            builtins::I64, decl::Callable, eq, let_, ne, rule, ruleset, set, subsume,
            tests::ActionTerm, union,
        };
        let left = ActionTerm(Expr::call(
            &Callable::constructor(
                "ActionLeft",
                vec![I64::sort_ref(), I64::sort_ref()],
                ActionTerm::sort_ref(),
                None,
                false,
            ),
            vec![
                I64::from(17).expression().clone(),
                I64::from(23).expression().clone(),
            ],
        ));
        let right = ActionTerm(Expr::call(
            &Callable::constructor("ActionRight", vec![], ActionTerm::sort_ref(), None, false),
            vec![],
        ));
        for in_rule in [false, true] {
            let mut graph = EGraph::default();
            let saved_left = let_("left", &left);
            let saved_right = let_("right", &right);
            graph.register((&saved_left, &saved_right)).unwrap();
            assert!(graph.check(ne(&saved_left, &saved_right)).unwrap());
            let actions = (
                set(CaptureRead(91), 1),
                union(&left, &right),
                subsume(&left),
            );
            if in_rule {
                graph.run(ruleset(rule((), actions))).unwrap();
            } else {
                graph.register(actions).unwrap();
            }
            let (request, response) = graph.last_wire.as_ref().unwrap();
            let mut request = pb::RunProgramRequest::decode(request.as_slice()).unwrap();
            let response = Observed::from_frames(
                response
                    .iter()
                    .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()),
            );
            assert!(response.error.is_none());
            if in_rule {
                assert!(
                    response
                        .output
                        .outputs
                        .iter()
                        .any(|out| matches!(&out.kind, Some(pb::command_output::Kind::Run(_))))
                );
            }
            let program = request.program.as_mut().unwrap();
            let actions: Vec<_> = if in_rule {
                let Some(pb::command::Kind::Loop(schedule)) = &program.commands[0].kind else {
                    panic!()
                };
                let Some(pb::command::Kind::AddRules(add)) = &schedule.body[0].kind else {
                    panic!()
                };
                let Some(pb::rule::Kind::Rule(body)) = &add.rules[0].kind else {
                    panic!()
                };
                body.head.iter().collect()
            } else {
                program
                    .commands
                    .iter()
                    .map(|command| {
                        let Some(pb::command::Kind::Action(action)) = &command.kind else {
                            panic!()
                        };
                        action
                    })
                    .collect()
            };
            assert_eq!(actions.len(), 3);
            let Some(pb::action::Kind::Set(set)) = &actions[0].kind else {
                panic!()
            };
            let value = set.value.unwrap();
            let Some(pb::action::Kind::Subsume(call)) = &actions[2].kind else {
                panic!()
            };
            assert_eq!(call.func, "ActionLeft");
            assert_eq!(call.args.len(), 2);
            for (argument, value) in call.args.iter().zip([17, 23]) {
                assert!(
                    matches!(&program.nodes[*argument as usize].kind, Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::I64(actual))
                })) if *actual == value)
                );
            }
            let Some(pb::action::Kind::Term(root)) = &actions[1].kind else {
                panic!()
            };
            let root = *root;
            let node = &program.nodes[root as usize];
            assert_eq!(
                program.sorts[node.sort_id as usize].kind,
                Some(pb::sort::Kind::Eq("ActionTerm".into()))
            );
            let Some(pb::node::Kind::Union(merge)) = &node.kind else {
                panic!()
            };
            assert_eq!(merge.members.len(), 2);
            for (member, (name, args)) in merge
                .members
                .iter()
                .zip([("ActionLeft", call.args.as_slice()), ("ActionRight", &[])])
            {
                assert!(
                    matches!(&program.nodes[*member as usize].kind, Some(pb::node::Kind::Call(c)) if c.func == name && c.args == args)
                );
                assert_eq!(
                    program.sorts[program.nodes[*member as usize].sort_id as usize],
                    program.sorts[node.sort_id as usize]
                );
            }
            assert!(graph.check(eq(&saved_left, &saved_right)).unwrap());
            assert!(!graph.check(ne(&saved_left, &saved_right)).unwrap());
            assert_eq!(graph.extract(&saved_left).unwrap(), right);
            let (_, bytes) = graph.last_wire.as_ref().unwrap();
            let extracted = Observed::from_frames(
                bytes
                    .iter()
                    .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()),
            );
            let Some(pb::command_output::Kind::Extraction(output)) =
                &extracted.output.outputs[0].kind
            else {
                panic!()
            };
            assert!(
                matches!(&extracted.output.nodes[output.roots[0].variants[0].term as usize].kind,
                Some(pb::node::Kind::Call(call)) if call.func == "ActionRight")
            );

            // Replay a damaged actual request with a different sentinel value.
            // Admission failure must occur before either direct or rule effects.
            program.nodes[value as usize].kind =
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::I64(2)),
                }));
            let Some(pb::node::Kind::Union(merge)) = &mut program.nodes[root as usize].kind else {
                panic!()
            };
            merge.members[1] = u32::MAX;
            let bytes = graph
                .engine
                .lock()
                .unwrap()
                .run(&request.encode_to_vec())
                .unwrap();
            let invalid = Observed::from_frames(
                bytes
                    .iter()
                    .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()),
            );
            assert_eq!(
                invalid.error.unwrap().code,
                pb::ErrorCode::InvalidProgram as i32
            );
            assert!(graph.engine.lock().unwrap().run(&[0xff]).is_err());
            assert_eq!(
                i64::try_from(&graph.extract(CaptureRead(91)).unwrap()).unwrap(),
                1
            );
            assert!(matches!(
                graph.accept_response(Packer::default(), &[vec![0xff]]),
                Err(TypedError::Decode(_))
            ));
            assert!(
                matches!(graph.register(union(&left, &right)), Err(TypedError::Invalid(message)) if message == "session transport state is unknown")
            );
        }
    }

    #[allow(non_snake_case)]
    fn CaptureRead(key: i64) -> super::super::builtins::I64 {
        use super::super::{builtins::I64, decl::Callable};
        I64::from_expression(Expr::call(
            &Callable::function(
                "CaptureRead",
                vec![I64::sort_ref()],
                I64::sort_ref(),
                None::<fn(Expr, Expr) -> Expr>,
            ),
            vec![I64::from(key).expression().clone()],
        ))
    }

    #[test]
    fn typed_capture_exact_bytes_order_and_confirmed_reuse() {
        use super::super::{builtins::I64, delete, let_, set};
        let before = let_("before", CaptureRead(1));
        let after = let_("after", CaptureRead(1));
        let mut graph = EGraph::default();
        graph
            .register((
                set(CaptureRead(1), 10),
                &before,
                delete(CaptureRead(1)),
                set(CaptureRead(1), 20),
                &after,
            ))
            .unwrap();
        let (input, output) = graph.last_wire.as_ref().unwrap();
        let request = pb::RunProgramRequest::decode(input.as_slice()).unwrap();
        let response = Observed::from_frames(
            output
                .iter()
                .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()),
        );
        assert!(response.error.is_none());
        let program = request.program.unwrap();
        assert_eq!(program.commands.len(), 5);
        let slots = ["__typed_capture_0", "__typed_capture_1"];
        for (index, target, value) in [
            (0, "CaptureRead", Some(10)),
            (1, slots[0], None),
            (3, "CaptureRead", Some(20)),
            (4, slots[1], None),
        ] {
            let Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Set(set)),
                ..
            })) = &program.commands[index].kind
            else {
                panic!("ordered Set at {index}")
            };
            let call = set.target.as_ref().unwrap();
            assert_eq!(call.func, target);
            let rhs = &program.nodes[set.value.unwrap() as usize];
            if let Some(value) = value {
                assert!(
                    matches!(&rhs.kind, Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue { value: Some(pb::primitive_value::Value::I64(actual)) })) if *actual == value)
                );
                assert_eq!(call.args.len(), 1);
            } else {
                assert!(call.args.is_empty());
                let Some(pb::node::Kind::Call(read)) = &rhs.kind else {
                    panic!("initializer remains an actual Read")
                };
                assert_eq!(read.func, "CaptureRead");
                assert!(matches!(
                    &program.nodes[read.args[0] as usize].kind,
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::I64(1))
                    }))
                ));
            }
        }
        assert!(
            matches!(&program.commands[2].kind, Some(pb::command::Kind::Action(pb::Action { kind: Some(pb::action::Kind::Delete(call)), .. })) if call.func == "CaptureRead" && call.args.len() == 1)
        );
        for slot in slots {
            assert!(program.declarations.iter().any(|d| matches!(&d.kind, Some(pb::declaration::Kind::Function(f)) if f.name == slot && f.inputs.is_empty() && f.merge.is_none())));
        }
        assert_eq!(i64::try_from(&graph.extract(&before).unwrap()).unwrap(), 10);
        assert_eq!(i64::try_from(&graph.extract(&after).unwrap()).unwrap(), 20);
        graph
            .register((delete(CaptureRead(1)), set(CaptureRead(1), 30)))
            .unwrap();
        let borrowed = [before.clone(), before.clone()];
        graph
            .register((borrowed.as_slice(), let_("before", CaptureRead(1))))
            .unwrap();
        let request =
            pb::RunProgramRequest::decode(graph.last_wire.as_ref().unwrap().0.as_slice()).unwrap();
        assert!(
            request.program.unwrap().commands.is_empty(),
            "equal established recipe emits no initializer/read action"
        );
        assert_eq!(i64::try_from(&graph.extract(&before).unwrap()).unwrap(), 10);
        assert_eq!(graph.captures.len(), 2);
        // A direct pure scalar is still an ordinary expression, not a capture.
        graph.register(I64::from(1)).unwrap();
    }

    #[test]
    fn typed_capture_names_guard_every_route_and_restore_scoped_access() {
        use super::super::{builtins::I64, delete, let_, rule, ruleset, set};
        for ordering in 0..3 {
            let ordinary = I64::from_expression(Expr::call(
                &super::super::decl::Callable::function(
                    "__typed_capture_0",
                    vec![],
                    I64::sort_ref(),
                    None::<fn(Expr, Expr) -> Expr>,
                ),
                vec![],
            ));
            let capture = let_("value", I64::from(5));
            let mut graph = EGraph::default();
            if ordering == 0 {
                graph.register((set(&ordinary, 7), &capture)).unwrap();
            } else if ordering == 1 {
                graph.register((&capture, set(&ordinary, 7))).unwrap();
            } else {
                graph.register(set(&ordinary, 7)).unwrap();
                graph.register(&capture).unwrap();
            }
            assert_eq!(
                graph.captures.values().next().unwrap().1,
                "__typed_capture_1"
            );
            assert_eq!(
                i64::try_from(&graph.extract(&ordinary).unwrap()).unwrap(),
                7
            );
        }
        let mut graph = EGraph::default();
        graph.push().unwrap();
        let capture = let_("private", I64::from(5));
        graph.register(&capture).unwrap();
        let slot = graph.captures.values().next().unwrap().1.clone();
        let label_spelling = capture.expression().0.capture().unwrap().unwrap().name;
        let ordinary_recipe = I64::from_expression(Expr::call(
            &super::super::decl::Callable::function(
                &label_spelling,
                vec![],
                I64::sort_ref(),
                None::<fn(Expr, Expr) -> Expr>,
            ),
            vec![],
        ));
        graph.register(set(&ordinary_recipe, 77)).unwrap();
        assert_eq!(
            i64::try_from(&graph.extract(&ordinary_recipe).unwrap()).unwrap(),
            77
        );
        assert_eq!(i64::try_from(&graph.extract(&capture).unwrap()).unwrap(), 5);
        let physical = format!(
            "__egglog_proto_call_{}",
            slot.as_bytes()
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        );
        let native_spelling = I64::from_expression(Expr::call(
            &super::super::decl::Callable::function(
                &physical,
                vec![],
                I64::sort_ref(),
                None::<fn(Expr, Expr) -> Expr>,
            ),
            vec![],
        ));
        graph.register(set(&native_spelling, 99)).unwrap();
        assert_eq!(
            i64::try_from(&graph.extract(&native_spelling).unwrap()).unwrap(),
            99
        );
        assert_eq!(i64::try_from(&graph.extract(&capture).unwrap()).unwrap(), 5);
        let forged = I64::from_expression(Expr::call(
            &super::super::decl::Callable::function(
                &slot,
                vec![],
                I64::sort_ref(),
                None::<fn(Expr, Expr) -> Expr>,
            ),
            vec![],
        ));
        for action in [set(&forged, 7), delete(&forged)] {
            assert!(graph.register((set(CaptureRead(9), 9), &action)).is_err());
            assert!(!graph.check(CaptureRead(9)).unwrap());
        }
        assert!(graph.register((set(CaptureRead(9), 9), &forged)).is_err());
        assert!(graph.extract(&forged).is_err());
        assert!(graph.check(&forged).is_err());
        assert!(graph.run(ruleset(rule((), set(&forged, 7)))).is_err());
        assert!(!graph.check(CaptureRead(9)).unwrap());
        let prefix = I64::from_expression(Expr::call(
            &super::super::decl::Callable::function(
                &format!("{slot}_ordinary"),
                vec![],
                I64::sort_ref(),
                None::<fn(Expr, Expr) -> Expr>,
            ),
            vec![],
        ));
        graph.register(set(&prefix, 8)).unwrap();
        assert_eq!(i64::try_from(&graph.extract(&prefix).unwrap()).unwrap(), 8);
        let mut cloned = graph.try_clone().unwrap();
        assert!(cloned.check(&forged).is_err());
        graph.pop().unwrap();
        graph.register(set(&forged, 7)).unwrap();
        graph.register(&capture).unwrap();
        assert_ne!(graph.captures.values().next().unwrap().1, slot);
        assert_eq!(i64::try_from(&graph.extract(&forged).unwrap()).unwrap(), 7);
        assert_eq!(i64::try_from(&graph.extract(&capture).unwrap()).unwrap(), 5);
        let mut overflow = EGraph::default();
        overflow.next_capture = u64::MAX;
        assert!(
            overflow
                .register((set(CaptureRead(9), 9), &capture))
                .is_err()
        );
        assert!(overflow.last_wire.is_none());
        assert!(overflow.private_slots.is_empty());
    }

    #[test]
    fn typed_capture_failed_initializers_keep_only_completed_prefix_and_retry_fresh() {
        use super::super::{SortRef, builtins::I64, decl::Callable, let_, rule::Fact, set};
        let sort = SortRef::equality("CapturePrefix");
        let node = Expr::call(
            &Callable::constructor(
                "CapturePrefix.Node",
                vec![I64::sort_ref()],
                sort.clone(),
                None,
                false,
            ),
            vec![I64::from(7).expression().clone()],
        );
        let read = I64::from_expression(Expr::call(
            &Callable::function(
                "CaptureMissing",
                vec![sort],
                I64::sort_ref(),
                None::<fn(Expr, Expr) -> Expr>,
            ),
            vec![node.clone()],
        ));
        let left = let_("left", I64::from(10));
        let right = let_("right", &read);
        for left_first in [false, true] {
            let mut graph = EGraph::default();
            let result = if left_first {
                graph.register((&left, &right))
            } else {
                graph.register(&right)
            };
            let Err(TypedError::Engine(frame)) = result else {
                panic!("real missing-row evaluation failure")
            };
            let Some(pb::run_program_response::Result::Error(error)) = &frame.result else {
                panic!("terminal error frame")
            };
            assert_eq!(error.code, pb::ErrorCode::RuntimeFailure as i32);
            assert_eq!(
                error.location.as_ref().unwrap().path,
                [u32::from(left_first)]
            );
            assert_eq!(graph.captures.len(), usize::from(left_first));
            assert!(graph.usable);
            assert!(
                graph.check(Fact(node.clone())).unwrap(),
                "failed initializer retained the native constructor prefix"
            );
            let issued = graph.private_slots.clone();
            graph.register(set(&read, 20)).unwrap();
            graph.register(&right).unwrap();
            let slot = &graph.captures[&right.expression().0.capture().unwrap().unwrap().name].1;
            assert!(
                !issued.contains(slot),
                "failed initializer slot is never recycled"
            );
            assert_eq!(i64::try_from(&graph.extract(&right).unwrap()).unwrap(), 20);
            if left_first {
                assert_eq!(i64::try_from(&graph.extract(&left).unwrap()).unwrap(), 10);
            }
        }
    }

    #[test]
    fn typed_capture_invalid_locations_promote_nothing_and_saved_pop_recovers() {
        use super::super::{builtins::I64, let_, ruleset};
        for (path, iterations, code) in [
            (vec![], vec![], pb::ErrorCode::RuntimeFailure),
            (vec![999], vec![], pb::ErrorCode::RuntimeFailure),
            (vec![0, 0], vec![], pb::ErrorCode::RuntimeFailure),
            (vec![1], vec![0], pb::ErrorCode::RuntimeFailure),
            (vec![1], vec![], pb::ErrorCode::InvalidProgram),
        ] {
            let mut graph = EGraph::default();
            graph.push().unwrap();
            let group = ruleset(());
            let mut packer = pack_run(&group);
            let run = packer.program.commands.pop().unwrap();
            let roots = [
                let_("a", I64::from(1)).expression().0.clone(),
                let_("b", I64::from(2)).expression().0.clone(),
            ];
            let mut plan = CapturePlan::new(&graph, &roots).unwrap();
            plan.materialize(&roots, true, &mut packer).unwrap();
            packer.program.commands.push(run);
            packer.finish().unwrap();
            let response = pb::RunProgramResponse {
                result: Some(pb::run_program_response::Result::Error(pb::Error {
                    code: code.into(),
                    location: Some(pb::CommandLocation { path, iterations }),
                    ..Default::default()
                })),
                ..Default::default()
            };
            assert!(matches!(
                graph.accept_response(packer, &[response.encode_to_vec()]),
                Err(TypedError::Decode(_))
            ));
            assert!(!graph.usable);
            assert!(graph.captures.is_empty());
            assert!(graph.declarations.is_empty());
            assert!(graph.register(I64::from(3)).is_err());
            graph.pop().unwrap();
            assert!(graph.usable);
            graph.register(I64::from(3)).unwrap();
        }
    }

    #[test]
    fn typed_capture_no_location_quarantines_a_possible_installation_without_confirmation() {
        use super::super::{builtins::I64, decl::Callable, let_, set};
        let mut graph = EGraph::default();
        graph.push().unwrap();
        let capture = let_("unconfirmed", I64::from(5));
        let roots = [capture.expression().0.clone()];
        let mut plan = CapturePlan::new(&graph, &roots).unwrap();
        let mut packer = Packer::default();
        plan.materialize(&roots, true, &mut packer).unwrap();
        packer.capture_counter = Some(plan.next);
        packer.finish().unwrap();
        let slot = packer.initializations[0].2.clone();
        // Inject the possible survivor of a partial installation using actual
        // bytes on this same handle: the definition exists, its Set never ran.
        // This is not a claim that normal typed authoring causes that fault.
        let mut definitions = packer.program.clone();
        definitions.commands.clear();
        let installed = graph
            .engine
            .lock()
            .unwrap()
            .run(
                &pb::RunProgramRequest {
                    egraph_id: graph.handle,
                    program: Some(definitions),
                    ..Default::default()
                }
                .encode_to_vec(),
            )
            .unwrap();
        assert!(
            Observed::from_frames(
                installed
                    .iter()
                    .map(|bytes| { pb::RunProgramResponse::decode(bytes.as_slice()).unwrap() })
            )
            .error
            .is_none()
        );
        // The actual failed packet has no command location and no completed Set.
        packer.program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Check(pb::Check {
                facts: vec![u32::MAX],
            })),
            ..Default::default()
        });
        let Err(TypedError::Engine(frame)) = graph.execute(packer, false) else {
            panic!("invalid packet")
        };
        let Some(pb::run_program_response::Result::Error(error)) = &frame.result else {
            panic!("terminal error frame")
        };
        assert!(error.location.is_none());
        assert_eq!(error.code, pb::ErrorCode::InvalidProgram as i32);
        assert!(graph.captures.is_empty());
        assert!(graph.private_slots.contains(&slot));
        assert!(graph.usable);
        assert!(graph.check(&capture).is_err());
        let ordinary = I64::from_expression(Expr::call(
            &Callable::function(
                &slot,
                vec![],
                I64::sort_ref(),
                None::<fn(Expr, Expr) -> Expr>,
            ),
            vec![],
        ));
        assert!(graph.register(set(&ordinary, 8)).is_err());
        graph.register(&capture).unwrap();
        assert_ne!(graph.captures.values().next().unwrap().1, slot);
        graph.pop().unwrap();
        assert!(graph.captures.is_empty());
        assert!(graph.private_slots.is_empty());
        graph.register(set(&ordinary, 8)).unwrap();
        assert_eq!(
            i64::try_from(&graph.extract(&ordinary).unwrap()).unwrap(),
            8
        );
    }

    #[test]
    fn typed_scope_restores_all_observations_and_drops_only_owned_handles() {
        use super::super::{builtins::I64, rule, rule::Fact, ruleset};
        let observations = |graph: &EGraph| {
            graph
                .declarations
                .iter()
                .map(|(name, record)| (name.clone(), record.key()))
                .collect::<HashMap<_, _>>()
        };
        let base = ruleset(());
        let value = Expr::call(
            &Callable::constructor(
                "Scope.Saved",
                vec![],
                SortRef::equality("Scope"),
                None,
                false,
            ),
            vec![],
        );
        let child = ruleset((&base, rule(Fact(value), I64::from(7) + I64::from(8))));
        let inner = ruleset((&child, &child, rule((), I64::from(9))));
        let mut graph = EGraph::default();
        graph.run(&base).unwrap();
        let baseline = observations(&graph);
        let original = graph.handle;
        let engine = graph.engine.clone();
        assert!(graph.pop().is_err());
        assert_eq!(graph.handle, original);
        assert_eq!(observations(&graph), baseline);
        graph.push().unwrap();
        let middle = graph.handle;
        assert_eq!(graph.scopes[0].handle, original);
        graph.run(&child).unwrap();
        assert!(graph.declarations.len() > baseline.len());
        let child_state = observations(&graph);
        graph.push().unwrap();
        let active = graph.handle;
        graph.run(&inner).unwrap();
        graph.pop().unwrap();
        assert_eq!(graph.handle, middle);
        assert_eq!(observations(&graph), child_state);
        graph.pop().unwrap();
        assert_eq!(graph.handle, original);
        assert_eq!(observations(&graph), baseline);
        assert!(graph.scopes.is_empty());
        for consumed in [middle, active] {
            assert!(
                engine
                    .lock()
                    .unwrap()
                    .destroy(
                        &pb::DestroyEGraphRequest {
                            egraph_id: consumed
                        }
                        .encode_to_vec()
                    )
                    .is_err(),
                "Pop already destroyed the active graph"
            );
        }
        graph.run(&inner).unwrap();
        assert!(graph.declarations.len() > baseline.len());
        graph.push().unwrap();
        graph.push().unwrap();
        let owned = std::iter::once(graph.handle)
            .chain(graph.scopes.iter().map(|s| s.handle))
            .collect::<Vec<_>>();
        assert_eq!(owned.iter().collect::<HashSet<_>>().len(), 3);
        let mut independent = graph.try_clone().unwrap();
        assert!(independent.scopes.is_empty());
        assert!(!owned.contains(&independent.handle));
        drop(graph);
        for handle in owned {
            assert!(
                engine
                    .lock()
                    .unwrap()
                    .destroy(&pb::DestroyEGraphRequest { egraph_id: handle }.encode_to_vec())
                    .is_err(),
                "Drop discarded every owned handle"
            );
        }
        independent.run(&inner).unwrap();
    }

    #[test]
    fn typed_scope_rejected_destroy_preserves_frontend_ownership() {
        use super::super::ruleset;
        let group = ruleset(());
        let mut graph = EGraph::default();
        graph.push().unwrap();
        graph.run(&group).unwrap();
        let active = std::mem::replace(&mut graph.handle, u64::MAX);
        let saved = graph.scopes[0].handle;
        // Reject an unknown handle without disposing either owned graph.
        assert!(matches!(graph.pop(), Err(TypedError::Invalid(message))
            if message == "unknown egraph_id"));
        assert_eq!(graph.handle, u64::MAX);
        assert_eq!(graph.scopes.len(), 1);
        assert_eq!(graph.scopes[0].handle, saved);
        assert!(graph.usable);
        graph.handle = active;
        graph.run(&group).unwrap();
        graph.pop().unwrap();
        assert_eq!(graph.handle, saved);
        assert!(graph.scopes.is_empty());
        graph.run(&group).unwrap();
    }

    #[test]
    fn typed_scope_corrupt_destroy_ack_never_destroys_the_active_handle_twice() {
        use super::super::ruleset;
        let mut graph = EGraph::default();
        let mut independent = graph.try_clone().unwrap();
        let saved = graph.handle;
        graph.push().unwrap();
        let active = graph.handle;
        let engine = graph.engine.clone();
        let discarded = graph.discarded.clone();
        let bytes = engine
            .lock()
            .unwrap()
            .destroy(&pb::DestroyEGraphRequest { egraph_id: active }.encode_to_vec())
            .unwrap();
        pb::DestroyEGraphResponse::decode(bytes.as_slice()).unwrap();
        assert!(matches!(
            graph.finish_pop(&[0xff]),
            Err(TypedError::Decode(_))
        ));
        assert_eq!(graph.handle, saved);
        assert!(graph.scopes.is_empty());
        assert!(!graph.usable);
        drop(graph);
        assert!(discarded.lock().unwrap().is_empty());
        for handle in [active, saved] {
            assert!(
                engine
                    .lock()
                    .unwrap()
                    .clone_egraph(&pb::CloneEGraphRequest { egraph_id: handle }.encode_to_vec())
                    .is_err()
            );
        }
        independent.run(ruleset(())).unwrap();
    }

    #[test]
    fn typed_scope_recovers_uncertain_transport_but_not_a_poisoned_mutex() {
        use super::super::ruleset;
        let group = ruleset(());
        let mut graph = EGraph::default();
        graph.run(&group).unwrap();
        graph.push().unwrap();
        let pending = pack_run(&ruleset(()));
        assert!(matches!(
            graph.accept_response(pending, &[vec![0xff]]),
            Err(TypedError::Decode(_))
        ));
        for error in [
            graph.push().unwrap_err(),
            graph.run(&group).unwrap_err(),
            graph.try_clone().err().expect("unusable cannot clone"),
        ] {
            assert!(matches!(error, TypedError::Invalid(message)
                if message == "session transport state is unknown"));
        }
        assert_eq!(graph.scopes.len(), 1);
        graph.pop().unwrap();
        assert!(graph.usable);
        graph.run(&group).unwrap();
        graph.push().unwrap();
        let active = graph.handle;
        let saved = graph.scopes[0].handle;
        let engine = graph.engine.clone();
        assert!(
            std::thread::spawn(move || {
                let _guard = engine.lock().unwrap();
                panic!("test-only scope transport poison");
            })
            .join()
            .is_err()
        );
        for error in [graph.push().unwrap_err(), graph.pop().unwrap_err()] {
            assert!(matches!(error, TypedError::Invalid(message)
                if message == "byte engine mutex poisoned"));
        }
        assert_eq!(graph.handle, active);
        assert_eq!(graph.scopes.len(), 1);
        assert_eq!(graph.scopes[0].handle, saved);
        drop(graph); // Must not panic or implicitly resume scopes.
    }

    #[test]
    fn typed_report_stats_rejects_poisoned_transport() {
        let mut graph = EGraph::default();
        let engine = graph.engine.clone();
        assert!(
            std::thread::spawn(move || {
                let _guard = engine.lock().unwrap();
                panic!("test-only transport poison");
            })
            .join()
            .is_err()
        );
        assert!(
            matches!(graph.stats(), Err(TypedError::Invalid(message)) if message == "byte engine mutex poisoned")
        );
        assert!(graph.last_wire.is_none());
    }

    #[test]
    fn compatible_registration_retries_keep_content_cursors_and_clone_independence() {
        use super::super::{builtins::I64, rule, ruleset};
        let group = ruleset(rule((), I64::from(7)).label("first"));
        let equal = ruleset(rule((), I64::from(7)).label("later"));
        let mut graph = EGraph::default();
        let (_, diagnostic) = graph.run_with_diagnostics(&group).unwrap();
        assert_eq!(diagnostic_matches(&diagnostic), 1);
        let mut cloned = graph.try_clone().unwrap();
        for current in [&mut graph, &mut cloned] {
            let (_, diagnostic) = current.run_with_diagnostics(&equal).unwrap();
            assert_eq!(diagnostic_matches(&diagnostic), 0);
        }
        drop(graph);
        cloned.run(&group).unwrap();
    }

    #[test]
    fn undecodable_response_blocks_calls_and_saved_scope_recovers() {
        use super::super::{builtins::I64, ruleset};
        let mut graph = EGraph::default();
        graph.push().unwrap();
        assert!(matches!(
            graph.accept_response(Packer::default(), &[vec![0xff]]),
            Err(TypedError::Decode(_))
        ));
        assert!(graph.register(I64::from(3)).is_err());
        assert!(graph.try_clone().is_err());
        graph.pop().unwrap();
        graph.run(ruleset(())).unwrap();
    }

    #[test]
    fn run_flags_and_opt_in_diagnostic_are_the_actual_wire_observations() {
        use super::super::{builtins::I64, rule, ruleset};
        let group = ruleset(rule((), I64::from(7)));
        let mut graph = EGraph::default();
        let (result, diagnostic) = graph.run_with_diagnostics(&group).unwrap();
        let (input, output) = graph.last_wire.as_ref().unwrap();
        assert!(
            pb::RunProgramRequest::decode(input.as_slice())
                .unwrap()
                .diagnostics
        );
        let response = Observed::from_frames(
            output
                .iter()
                .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()),
        );
        let [control, detail] = response.output.outputs.as_slice() else {
            panic!("one result and one diagnostic")
        };
        assert_eq!(control.kind, Some(pb::command_output::Kind::Run(result)));
        assert_eq!(
            detail.kind,
            Some(pb::command_output::Kind::Diagnostic(diagnostic.clone()))
        );
        assert_eq!(control.location, detail.location);
        assert_eq!(diagnostic_matches(&diagnostic), 1);
        graph.run(&group).unwrap();
        let (input, output) = graph.last_wire.as_ref().unwrap();
        assert!(
            !pb::RunProgramRequest::decode(input.as_slice())
                .unwrap()
                .diagnostics
        );
        let response = Observed::from_frames(
            output
                .iter()
                .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()),
        );
        assert!(matches!(
            response.output.outputs.as_slice(),
            [pb::CommandOutput {
                kind: Some(pb::command_output::Kind::Run(_)),
                ..
            }]
        ));
        let stats = graph.stats().unwrap();
        assert_eq!(diagnostic_matches(&stats), 1);
        let request = graph.last_wire.as_ref().unwrap().0.clone();
        let direct = graph.engine.lock().unwrap().run(&request).unwrap();
        let direct = Observed::from_frames(
            direct
                .iter()
                .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()),
        );
        assert_eq!(
            direct.output.outputs[0].kind,
            Some(pb::command_output::Kind::Diagnostic(stats))
        );
    }

    fn stream_counter() -> super::super::builtins::I64 {
        use super::super::{builtins::I64, decl::Callable};
        I64::from_expression(Expr::call(
            &Callable::function(
                "StreamCounter",
                vec![],
                I64::sort_ref(),
                Some(|_: Expr, new: Expr| new),
            ),
            vec![],
        ))
    }

    #[test]
    fn failed_scoped_prefix_restores_data_and_discards_active_diagnostics() {
        use super::super::{eq, rule, ruleset, set};
        let counter = stream_counter();
        let group = ruleset(rule(eq(&counter, 0), set(&counter, 1)));
        let mut graph = EGraph::default();
        graph.register(set(&counter, 0)).unwrap();
        graph.push().unwrap();
        let (_, diagnostic) = graph.run_with_diagnostics(&group).unwrap();
        assert_eq!(diagnostic_matches(&diagnostic), 1);
        let mut fail = Packer::default();
        fail.program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Panic("after collected work".into())),
                ..Default::default()
            })),
            ..Default::default()
        });
        assert!(matches!(
            graph.execute(fail, false),
            Err(TypedError::Engine(_))
        ));
        assert!(graph.check(eq(&counter, 1)).unwrap());
        graph.pop().unwrap();
        assert!(graph.check(eq(&counter, 0)).unwrap());
        assert_eq!(diagnostic_matches(&graph.stats().unwrap()), 0);
        assert_eq!(diagnostic_matches(&diagnostic), 1);
        graph.run(&group).unwrap();
        assert!(graph.check(eq(&counter, 1)).unwrap());
    }

    #[test]
    fn snapshots_are_live_owned_and_cancellation_releases_callback_dropped_clones() {
        use super::super::{Schedule, builtins::I64, eq, let_, rule, ruleset, set};
        let counter = stream_counter();
        let group = ruleset((
            rule(eq(&counter, 0), set(&counter, 1)),
            rule(eq(&counter, 1), set(&counter, 2)),
            rule(eq(&counter, 2), I64::from(1) / I64::from(0)),
        ));
        let mut graph = EGraph::with_recording(true).unwrap();
        let capture = let_("initial", &counter);
        graph.register((set(&counter, 0), &capture)).unwrap();
        let mut dropped = Some(graph.try_clone().unwrap());
        let dropped_handle = dropped.as_ref().unwrap().handle;
        let mut other = graph.try_clone().unwrap();
        let mut snapshots = vec![];
        let error = graph.run_stream(Schedule::from(&group).with_snapshots().repeat(3), |snapshot| {
            assert!(matches!(other.check(eq(&counter, 0)), Err(TypedError::Invalid(message)) if message == "byte engine is already executing"));
            drop(dropped.take());
            let observed = snapshot.lookup(&capture).unwrap();
            assert_eq!(i64::try_from(&observed).unwrap(), 0);
            snapshots.push(snapshot);
            ControlFlow::Break(())
        }).unwrap_err();
        assert!(
            matches!(error, TypedError::Invalid(message) if message.contains("execution cancelled"))
        );
        assert_eq!(snapshots.len(), 1);
        assert_eq!(
            i64::try_from(&graph.extract(&counter).unwrap()).unwrap(),
            1,
            "second iteration did not run before first snapshot delivery"
        );
        assert!(graph.discarded.lock().unwrap().is_empty());
        assert!(
            graph
                .engine
                .lock()
                .unwrap()
                .clone_egraph(
                    &pb::CloneEGraphRequest {
                        egraph_id: dropped_handle
                    }
                    .encode_to_vec()
                )
                .is_err()
        );
        assert!(graph.history().unwrap().commands.len() >= 2);
        other.check(eq(&counter, 0)).unwrap();
        drop(graph);
        assert!(
            snapshots[0].rows().next().is_some(),
            "views outlive the executing graph"
        );
    }

    #[test]
    fn observer_unwind_preserves_sibling_reuse_and_drains_callback_drops() {
        use super::super::{Schedule, eq, rule, ruleset, set};
        let mut graph = EGraph::new().unwrap();
        let counter = stream_counter();
        graph.register(set(&counter, 0)).unwrap();
        let mut sibling = graph.try_clone().unwrap();
        let mut discarded = Some(graph.try_clone().unwrap());
        let discarded_handle = discarded.as_ref().unwrap().handle;
        let group = ruleset(rule(eq(&counter, 0), set(&counter, 1)));
        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = graph.run_stream(Schedule::from(&group).with_snapshots().repeat(3), |_| {
                drop(discarded.take());
                std::panic::panic_any("observer witness");
            });
        }))
        .unwrap_err();
        assert_eq!(panic.downcast_ref::<&str>(), Some(&"observer witness"));
        assert!(graph.check(eq(&counter, 1)).unwrap());
        assert!(sibling.check(eq(&counter, 0)).unwrap());
        assert!(graph.discarded.lock().unwrap().is_empty());
        assert!(
            graph
                .lock_engine()
                .unwrap()
                .clone_egraph(
                    &pb::CloneEGraphRequest {
                        egraph_id: discarded_handle
                    }
                    .encode_to_vec(),
                )
                .is_err()
        );
    }

    #[test]
    fn streamed_snapshots_keep_failure_prefix_and_explicit_observation_cadence() {
        use super::super::{Schedule, builtins::I64, eq, rule, ruleset, set};
        let counter = stream_counter();
        let group = ruleset((
            rule(eq(&counter, 0), set(&counter, 1)),
            rule(eq(&counter, 1), set(&counter, 2)),
            rule(eq(&counter, 2), I64::from(1) / I64::from(0)),
        ));
        let mut graph = EGraph::default();
        graph.register(set(&counter, 0)).unwrap();
        let mut snapshots = vec![];
        let error = graph
            .run_stream(
                Schedule::from(&group).with_snapshots().repeat(3),
                |snapshot| {
                    snapshots.push(snapshot);
                    ControlFlow::Continue(())
                },
            )
            .unwrap_err();
        assert!(matches!(error, TypedError::Engine(_)));
        assert_eq!(snapshots.len(), 2);
        assert_eq!(i64::try_from(&graph.extract(&counter).unwrap()).unwrap(), 2);
        let empty = ruleset(());
        let mut count = 0;
        graph
            .run_stream(Schedule::from(&empty).repeat(3).with_snapshots(), |_| {
                count += 1;
                ControlFlow::Continue(())
            })
            .unwrap();
        assert_eq!(
            count, 1,
            "observation belongs after the chosen whole schedule"
        );
        assert!(graph.run(Schedule::from(&empty).with_snapshots()).is_err());
    }

    #[test]
    fn exact_number_response_adoption_rejects_noncanonical_or_mismatched_data() {
        use pb::primitive_value::Value;
        let cases = [
            (
                "BigInt",
                Value::BigInt("-1234567890123456789012345678901".into()),
            ),
            (
                "BigRat",
                Value::BigRat(pb::BigRat {
                    numerator: "-1234567890123456789012345678901".into(),
                    denominator: "2".into(),
                }),
            ),
            (
                "Rational",
                Value::Rational(pb::Rational {
                    numerator: i64::MIN,
                    denominator: 1,
                }),
            ),
        ];
        for (family, value) in cases {
            let response = pb::RunProgramOutput {
                sorts: vec![pb::Sort {
                    kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                        name: family.into(),
                        args: vec![],
                    })),
                    ..Default::default()
                }],
                nodes: vec![pb::Node {
                    sort_id: 0,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(value.clone()),
                    })),
                    ..Default::default()
                }],
                ..Default::default()
            };
            let adopted = adopt(
                &response,
                0,
                vec![],
                super::super::storage::builtin_catalog(),
            )
            .unwrap();
            let mut packed = Packer::default();
            let root = packed.intern(adopted.0, 0);
            packed.finish().unwrap();
            assert_eq!(
                packed.program.nodes[root as usize].kind,
                response.nodes[0].kind
            );
            let mut wrong = response.clone();
            let Some(pb::sort::Kind::Application(sort)) = &mut wrong.sorts[0].kind else {
                unreachable!()
            };
            sort.name = "i64".into();
            assert!(adopt(&wrong, 0, vec![], super::super::storage::builtin_catalog()).is_err());
            let invalid = match value {
                Value::BigInt(_) => ["", "+1", "01", "-0", " 1", "1_0"]
                    .map(|s| Value::BigInt(s.into()))
                    .to_vec(),
                Value::BigRat(_) => [
                    ("1", "0"),
                    ("1", "-2"),
                    ("2", "4"),
                    ("0", "2"),
                    ("01", "2"),
                    ("1", "02"),
                ]
                .map(|(n, d)| {
                    Value::BigRat(pb::BigRat {
                        numerator: n.into(),
                        denominator: d.into(),
                    })
                })
                .to_vec(),
                Value::Rational(_) => [
                    (1, 0),
                    (1, -2),
                    (2, 4),
                    (0, 2),
                    (i64::MIN, 2),
                    (1, i64::MIN),
                ]
                .map(|(n, d)| {
                    Value::Rational(pb::Rational {
                        numerator: n,
                        denominator: d,
                    })
                })
                .to_vec(),
                _ => unreachable!(),
            };
            for value in invalid {
                let mut bad = response.clone();
                bad.nodes[0].kind = Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(value),
                }));
                assert!(
                    adopt(&bad, 0, vec![], super::super::storage::builtin_catalog()).is_err(),
                    "accepted malformed {family} payload"
                );
                assert_eq!(
                    response.nodes[0].kind,
                    packed.program.nodes[root as usize].kind
                );
            }
        }
    }

    #[test]
    fn exact_number_bytes_keep_symbolic_construction_and_return_inert_payloads() {
        use crate::typed::builtins::{BigInt, BigRat, I64, Rational};
        use pb::primitive_value::Value;
        let cases = [
            (
                BigInt::new(I64::from(40) + I64::from(2))
                    .expression()
                    .clone(),
                "egglog.core.bigint.from_i64",
                Value::BigInt("42".into()),
            ),
            (
                BigRat::new(
                    BigInt::from_string("1234567890123456789012345678901"),
                    BigInt::new(2),
                )
                .expression()
                .clone(),
                "egglog.core.bigrat.make",
                Value::BigRat(pb::BigRat {
                    numerator: "1234567890123456789012345678901".into(),
                    denominator: "2".into(),
                }),
            ),
            (
                Rational::new(I64::from(2) + I64::from(-1), 2)
                    .expression()
                    .clone(),
                "egglog.experimental.rational.make",
                Value::Rational(pb::Rational {
                    numerator: 1,
                    denominator: 2,
                }),
            ),
            (
                (Rational::new(1, 2) + Rational::new(1, 3))
                    .expression()
                    .clone(),
                "egglog.experimental.rational.add",
                Value::Rational(pb::Rational {
                    numerator: 5,
                    denominator: 6,
                }),
            ),
        ];
        for (expression, provider, expected) in cases {
            let mut packer = Packer::default();
            let root = packer.intern(expression.0, 0);
            packer.program.commands.push(pb::Command {
                kind: Some(pb::command::Kind::Extract(pb::Extract {
                    roots: vec![root],
                    variants: 1,
                    extractor: pb::Extractor::Tree.into(),
                    ..Default::default()
                })),
                ..Default::default()
            });
            let mut graph = EGraph::default();
            let response = Observed::from_frames(graph.execute(packer, false).unwrap());
            let request =
                pb::RunProgramRequest::decode(graph.last_wire.as_ref().unwrap().0.as_slice())
                    .unwrap()
                    .program
                    .unwrap();
            let Some(pb::node::Kind::Call(call)) = &request.nodes[root as usize].kind else {
                panic!("constructor was folded into a value")
            };
            assert_eq!(call.func, provider);
            assert!(
                call.args.iter().any(|i| matches!(
                    request.nodes[*i as usize].kind,
                    Some(pb::node::Kind::Call(_))
                )),
                "symbolic child was evaluated before submission"
            );
            let Some(pb::command_output::Kind::Extraction(extracted)) =
                &response.output.outputs[0].kind
            else {
                panic!()
            };
            let term = extracted.roots[0].variants[0].term;
            assert_eq!(
                response.output.nodes[term as usize].kind,
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(expected)
                }))
            );
            let adopted = adopt(
                &response.output,
                term,
                vec![],
                super::super::storage::builtin_catalog(),
            )
            .unwrap();
            adopted.validate_inert().unwrap();
        }
    }
    use crate::typed::{SortRef, decl::Callable};

    #[test]
    fn map_bytes_use_fixed_canonical_calls_and_return_map_values() {
        use crate::typed::builtins::{F64, I64, Map};
        let map = Map::<I64, F64>::of([(7_i64, 1.5_f64), (7_i64, 2.5_f64)]);
        let mut graph = EGraph::default();
        let value = graph.extract(&map).unwrap();
        let (request, response) = graph.last_wire.as_ref().unwrap();
        let request = pb::RunProgramRequest::decode(request.as_slice())
            .unwrap()
            .program
            .unwrap();
        for identity in [
            "egglog.core.map.of",
            "egglog.core.vec.of",
            "egglog.core.pair.make",
        ] {
            assert!(
                request.nodes.iter().any(
                    |n| matches!(&n.kind, Some(pb::node::Kind::Call(c)) if c.func == identity)
                )
            );
        }
        assert!(
            request
                .nodes
                .iter()
                .filter_map(|n| match &n.kind {
                    Some(pb::node::Kind::Call(c)) if c.func == "egglog.core.map.of" => Some(c),
                    _ => None,
                })
                .all(|c| c.args.len() == 1)
        );
        assert!(!request.nodes.iter().any(|n| matches!(&n.kind, Some(pb::node::Kind::Call(c)) if c.func == "map-of" || c.func == "map-from-pairs")));
        let response = Observed::from_frames(
            response
                .iter()
                .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()),
        );
        let Some(pb::command_output::Kind::Extraction(extraction)) =
            &response.output.outputs[0].kind
        else {
            panic!()
        };
        let term = extraction.roots[0].variants[0].term;
        assert!(matches!(
            &response.output.nodes[term as usize].kind,
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Map(_))
            }))
        ));
        assert_ne!(map, value);
        drop(graph);
        assert_eq!(value.entries().unwrap(), [(I64::from(7), F64::from(2.5))]);
    }

    #[test]
    fn map_function_vec_input_table_results_and_missing_key_prefix_use_bytes() {
        use crate::typed::builtins::{F64, I64, Map, Pair, Vec as EVec};
        // User functions are still outside the typed declaration subset. This
        // raw-record boundary test composes the genuinely generated Map call
        // with an ordinary wire function, without inventing builtin signatures.
        let pairs = EVec::<Pair<I64, F64>>::of([Pair::new(7_i64, 2.5_f64)]);
        let map = Map::<I64, F64>::from_pairs(EVec::<Pair<I64, F64>>::empty());
        let missing = map.get(99_i64);
        let mut packer = Packer::default();
        let entries = packer.intern(pairs.expression().0.clone(), 0);
        let root = packer.intern(map.expression().0.clone(), 0);
        let missing = packer.intern(missing.expression().0.clone(), 0);
        packer.finish().unwrap();
        let mut program = packer.program;
        let Some(pb::node::Kind::Call(call)) = &program.nodes[root as usize].kind else {
            panic!()
        };
        assert_eq!(call.func, "egglog.core.map.of");
        let argument = call.args[0] as usize;
        program.nodes[argument].kind = Some(pb::node::Kind::Call(pb::Call {
            func: "stored_pairs".into(),
            args: vec![],
        }));
        for (name, output) in [
            ("stored_pairs", program.nodes[argument].sort_id),
            ("stored_map", program.nodes[root as usize].sort_id),
        ] {
            program.declarations.push(pb::Declaration {
                kind: Some(pb::declaration::Kind::Function(pb::Function {
                    name: name.into(),
                    output,
                    ..Default::default()
                })),
                ..Default::default()
            });
        }
        for (name, value) in [("stored_pairs", entries), ("stored_map", root)] {
            program.commands.push(pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Set(pb::Set {
                        target: Some(pb::Call {
                            func: name.into(),
                            args: vec![],
                        }),
                        value: Some(value),
                    })),
                    ..Default::default()
                })),
                ..Default::default()
            });
        }
        program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Extract(pb::Extract {
                roots: vec![root],
                variants: 1,
                extractor: pb::Extractor::Tree.into(),
                ..Default::default()
            })),
            ..Default::default()
        });
        let table = pb::Command {
            kind: Some(pb::command::Kind::TableRows(pb::GetTableRows {
                table: "stored_map".into(),
                max_rows: Some(10),
            })),
            ..Default::default()
        };
        program.commands.push(table.clone());
        program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Term(missing)),
                ..Default::default()
            })),
            ..Default::default()
        });
        let graph = EGraph::default();
        let request = pb::RunProgramRequest {
            egraph_id: graph.handle,
            program: Some(program),
            diagnostics: false,
        }
        .encode_to_vec();
        let bytes = graph.engine.lock().unwrap().run(&request).unwrap();
        let response = Observed::from_frames(
            bytes
                .iter()
                .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()),
        );
        let error = response.error.as_ref().unwrap();
        assert_eq!(error.code, pb::ErrorCode::RuntimeFailure as i32);
        assert_eq!(error.location.as_ref().unwrap().path, [4]);
        assert_eq!(response.output.outputs.len(), 2);
        let Some(pb::command_output::Kind::Extraction(extraction)) =
            &response.output.outputs[0].kind
        else {
            panic!()
        };
        let extracted = Map::<I64, F64>::from_expression(
            adopt(
                &response.output,
                extraction.roots[0].variants[0].term,
                vec![],
                super::super::storage::builtin_catalog(),
            )
            .unwrap(),
        );
        let Some(pb::command_output::Kind::TableRows(table_result)) =
            &response.output.outputs[1].kind
        else {
            panic!()
        };
        assert_eq!(table_result.rows.len(), 1);
        let Some(pb::table_cell::Kind::Term(term)) =
            table_result.rows[0].output.as_ref().unwrap().kind
        else {
            panic!("expected available Map output")
        };
        let observed = Map::<I64, F64>::from_expression(
            adopt(
                &response.output,
                term,
                vec![],
                super::super::storage::builtin_catalog(),
            )
            .unwrap(),
        );
        assert_eq!(observed, extracted);
        assert_eq!(
            observed.entries().unwrap(),
            [(I64::from(7), F64::from(2.5))]
        );
        let bytes = graph
            .engine
            .lock()
            .unwrap()
            .run(
                &pb::RunProgramRequest {
                    egraph_id: graph.handle,
                    program: Some(pb::Program {
                        commands: vec![table],
                        ..Default::default()
                    }),
                    diagnostics: false,
                }
                .encode_to_vec(),
            )
            .unwrap();
        let after = Observed::from_frames(
            bytes
                .iter()
                .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()),
        );
        assert!(after.error.is_none());
        let Some(pb::command_output::Kind::TableRows(table)) = &after.output.outputs[0].kind else {
            panic!()
        };
        let Some(pb::table_cell::Kind::Term(term)) = table.rows[0].output.as_ref().unwrap().kind
        else {
            panic!("expected available Map output")
        };
        assert_eq!(
            adopt(
                &after.output,
                term,
                vec![],
                super::super::storage::builtin_catalog()
            )
            .unwrap(),
            *observed.expression()
        );
        drop(graph);
        assert_eq!(EGraph::default().extract(&extracted).unwrap(), observed);
    }

    #[test]
    fn map_response_adoption_checks_ref_zero_missing_children_sorts_and_cycles() {
        use crate::typed::{
            EgglogValue,
            builtins::{F64, I64, Map},
        };
        let response = pb::RunProgramOutput {
            sorts: vec![
                pb::Sort {
                    kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                        name: "f64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                        name: "Map".into(),
                        args: vec![2, 0],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                        name: "i64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
            ],
            nodes: vec![
                pb::Node {
                    sort_id: 2,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::I64(7)),
                    })),
                    ..Default::default()
                },
                pb::Node::default(), // An unrelated response node is not this closure's root.
                pb::Node {
                    sort_id: 1,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Map(pb::MapValue {
                            entries: vec![
                                pb::MapEntry {
                                    key: Some(0),
                                    value: Some(3),
                                },
                                pb::MapEntry {
                                    key: Some(0),
                                    value: Some(3),
                                },
                            ],
                        })),
                    })),
                    ..Default::default()
                },
                pb::Node {
                    sort_id: 0,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::F64Bits(1.5_f64.to_bits())),
                    })),
                    ..Default::default()
                },
            ],
            ..Default::default()
        };
        let value = Map::<I64, F64>::from_expression(
            adopt(
                &response,
                2,
                vec![],
                super::super::storage::builtin_catalog(),
            )
            .unwrap(),
        );
        let entries = value.entries().unwrap();
        assert_eq!(
            entries,
            [
                (I64::from(7), F64::from(1.5)),
                (I64::from(7), F64::from(1.5))
            ]
        );
        assert_eq!(
            value
                .expression()
                .0
                .owner
                .as_ref()
                .unwrap()
                .program()
                .unwrap()
                .nodes
                .len(),
            3
        );
        assert!(std::sync::Arc::ptr_eq(
            entries[0].0.expression().0.owner.as_ref().unwrap(),
            entries[1].0.expression().0.owner.as_ref().unwrap()
        ));
        assert_eq!(
            entries[0].0.expression().0.index,
            entries[1].0.expression().0.index
        );
        for key in [false, true] {
            for child in [None, Some(99)] {
                let mut malformed = response.clone();
                let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Map(map)),
                })) = &mut malformed.nodes[2].kind
                else {
                    panic!()
                };
                if key {
                    map.entries[0].key = child;
                } else {
                    map.entries[0].value = child;
                }
                let error = adopt(
                    &malformed,
                    2,
                    vec![],
                    super::super::storage::builtin_catalog(),
                )
                .unwrap_err();
                assert!(
                    matches!(error, TypedError::Decode(ref s) if s == if child.is_none() { "missing Map child" } else { "invalid response node index" }),
                    "{error}"
                );
            }
        }
        for child in [0, 3] {
            let mut wrong = response.clone();
            wrong.nodes[child].sort_id = if child == 0 { 0 } else { 2 };
            assert!(
                matches!(adopt(&wrong, 2, vec![], super::super::storage::builtin_catalog()), Err(TypedError::Decode(s)) if s == "Map payload child sort mismatch")
            );
        }
        for kind in [
            pb::sort::Kind::Eq("Map".into()),
            pb::sort::Kind::Application(pb::SortApplication {
                name: "Pair".into(),
                args: vec![2, 0],
            }),
            pb::sort::Kind::Application(pb::SortApplication {
                name: "Map".into(),
                args: vec![2],
            }),
        ] {
            let mut wrong = response.clone();
            wrong.sorts[1].kind = Some(kind);
            assert!(adopt(&wrong, 2, vec![], super::super::storage::builtin_catalog()).is_err());
        }
        let atom = SortRef::equality("A");
        let family = super::super::storage::builtin_catalog()
            .declaration("Map", DeclarationKind::PrimitiveSort)
            .unwrap();
        let sort = SortRef::family(&family, vec![atom.clone(), F64::sort_ref()]).unwrap();
        let pack = Callable::constructor("Pack", vec![sort], atom, None, false);
        let mut cycle = response;
        cycle.sorts[2].kind = Some(pb::sort::Kind::Eq("A".into()));
        cycle.nodes[0].kind = Some(pb::node::Kind::Call(pb::Call {
            func: "Pack".into(),
            args: vec![2],
        }));
        assert!(
            matches!(adopt(&cycle, 2, vec![pack.0], super::super::storage::builtin_catalog()), Err(TypedError::Decode(s)) if s == "cyclic extraction is not inert data")
        );
    }

    #[test]
    fn pair_bytes_use_canonical_calls_and_return_pair_values() {
        use crate::typed::builtins::{F64, I64, Pair};
        let pair = Pair::<I64, F64>::new(7_i64, 1.5_f64);
        let mut graph = EGraph::default();
        let value = graph.extract(&pair).unwrap();
        let (request, response) = graph.last_wire.as_ref().unwrap();
        let request = pb::RunProgramRequest::decode(request.as_slice())
            .unwrap()
            .program
            .unwrap();
        assert!(request.nodes.iter().any(|n| matches!(&n.kind, Some(pb::node::Kind::Call(c)) if c.func == "egglog.core.pair.make")));
        assert!(
            !request
                .nodes
                .iter()
                .any(|n| matches!(&n.kind, Some(pb::node::Kind::Call(c)) if c.func == "pair"))
        );
        let response = Observed::from_frames(
            response
                .iter()
                .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()),
        );
        let Some(pb::command_output::Kind::Extraction(extraction)) =
            &response.output.outputs[0].kind
        else {
            panic!()
        };
        let index = extraction.roots[0].variants[0].term;
        assert!(matches!(
            &response.output.nodes[index as usize].kind,
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Pair(_))
            }))
        ));
        assert_ne!(pair, value);
        drop(graph);
        assert_eq!(value.fields().unwrap(), (I64::from(7), F64::from(1.5)));
    }

    #[test]
    fn pair_response_adoption_checks_ref_zero_absence_sorts_and_cycles() {
        use crate::typed::{
            EgglogValue,
            builtins::{F64, I64},
        };
        let catalog = super::super::storage::builtin_catalog();
        let make = Callable(
            catalog
                .declaration("egglog.core.pair.make", DeclarationKind::Callable)
                .unwrap(),
        );
        let response = pb::RunProgramOutput {
            sorts: vec![
                pb::Sort {
                    kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                        name: "f64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                        name: "Pair".into(),
                        args: vec![2, 0],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                        name: "i64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
            ],
            nodes: vec![
                pb::Node {
                    sort_id: 2,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::I64(7)),
                    })),
                    ..Default::default()
                },
                pb::Node::default(), // Unselected malformed data is not adopted.
                pb::Node {
                    sort_id: 1,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Pair(pb::PairValue {
                            first: Some(0),
                            second: Some(3),
                        })),
                    })),
                    ..Default::default()
                },
                pb::Node {
                    sort_id: 0,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::F64Bits(1.5_f64.to_bits())),
                    })),
                    ..Default::default()
                },
            ],
            ..Default::default()
        };
        let value = adopt(
            &response,
            2,
            vec![],
            super::super::storage::builtin_catalog(),
        )
        .unwrap();
        let [left, right] = value
            .pair_fields(&make, &I64::sort_ref(), &F64::sort_ref())
            .unwrap();
        assert_eq!(i64::try_from(&I64::from_expression(left)).unwrap(), 7);
        assert_eq!(f64::try_from(&F64::from_expression(right)).unwrap(), 1.5);
        assert_eq!(
            value
                .0
                .owner
                .as_ref()
                .unwrap()
                .program()
                .unwrap()
                .nodes
                .len(),
            3
        );
        for first in [false, true] {
            for child in [None, Some(99)] {
                let mut malformed = response.clone();
                let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Pair(pair)),
                })) = &mut malformed.nodes[2].kind
                else {
                    panic!()
                };
                if first {
                    pair.first = child;
                } else {
                    pair.second = child;
                }
                let error = adopt(
                    &malformed,
                    2,
                    vec![],
                    super::super::storage::builtin_catalog(),
                )
                .unwrap_err();
                assert!(
                    matches!(error, TypedError::Decode(ref s) if s == if child.is_none() { "missing Pair child" } else { "invalid response node index" }),
                    "{error}"
                );
            }
        }
        let mut wrong = response.clone();
        wrong.nodes[0].sort_id = 0;
        assert!(
            matches!(adopt(&wrong, 2, vec![], super::super::storage::builtin_catalog()), Err(TypedError::Decode(s)) if s == "Pair payload child sort mismatch")
        );
        for kind in [
            pb::sort::Kind::Eq("Pair".into()),
            pb::sort::Kind::Application(pb::SortApplication {
                name: "Vec".into(),
                args: vec![2],
            }),
            pb::sort::Kind::Application(pb::SortApplication {
                name: "Pair".into(),
                args: vec![2],
            }),
        ] {
            let mut malformed = response.clone();
            malformed.sorts[1].kind = Some(kind);
            assert!(
                adopt(
                    &malformed,
                    2,
                    vec![],
                    super::super::storage::builtin_catalog()
                )
                .is_err()
            );
        }
        let mut repeated = response.clone();
        repeated.sorts[1].kind = Some(pb::sort::Kind::Application(pb::SortApplication {
            name: "Pair".into(),
            args: vec![2, 2],
        }));
        repeated.nodes[2].kind = Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Pair(pb::PairValue {
                first: Some(0),
                second: Some(0),
            })),
        }));
        let shared = adopt(
            &repeated,
            2,
            vec![],
            super::super::storage::builtin_catalog(),
        )
        .unwrap();
        let [left, right] = shared
            .pair_fields(&make, &I64::sort_ref(), &I64::sort_ref())
            .unwrap();
        assert_eq!(left.0.index, right.0.index);
        assert!(std::sync::Arc::ptr_eq(
            left.0.owner.as_ref().unwrap(),
            right.0.owner.as_ref().unwrap()
        ));

        let atom = SortRef::equality("A");
        let pair = SortRef::family(
            &catalog
                .declaration("Pair", DeclarationKind::PrimitiveSort)
                .unwrap(),
            vec![atom.clone(), F64::sort_ref()],
        )
        .unwrap();
        let pack = Callable::constructor("Pack", vec![pair], atom, None, false);
        let mut cycle = response;
        cycle.sorts[2].kind = Some(pb::sort::Kind::Eq("A".into()));
        cycle.nodes[0].kind = Some(pb::node::Kind::Call(pb::Call {
            func: "Pack".into(),
            args: vec![2],
        }));
        assert!(
            matches!(adopt(&cycle, 2, vec![pack.0], super::super::storage::builtin_catalog()), Err(TypedError::Decode(s)) if s == "cyclic extraction is not inert data")
        );
    }

    #[test]
    fn maybe_response_adoption_checks_optional_zero_sorts_cycles_and_sharing() {
        use crate::typed::{
            EgglogValue,
            builtins::{I64, Maybe, Vec as EVec},
        };
        let response = pb::RunProgramOutput {
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
                        name: "Maybe".into(),
                        args: vec![0],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                        name: "Vec".into(),
                        args: vec![1],
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
                pb::Node::default(), // Unselected malformed data is not adopted.
                pb::Node {
                    sort_id: 1,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Maybe(pb::MaybeValue {
                            value: Some(0),
                        })),
                    })),
                    ..Default::default()
                },
                pb::Node {
                    sort_id: 2,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Vec(pb::ValueList {
                            items: vec![2, 2],
                        })),
                    })),
                    ..Default::default()
                },
            ],
            ..Default::default()
        };
        let value = Maybe::<I64>::from_expression(
            adopt(
                &response,
                2,
                vec![],
                super::super::storage::builtin_catalog(),
            )
            .unwrap(),
        );
        assert_eq!(Option::<I64>::try_from(&value).unwrap(), Some(I64::from(7)));
        assert_eq!(
            value
                .expression()
                .0
                .owner
                .as_ref()
                .unwrap()
                .program()
                .unwrap()
                .nodes
                .len(),
            2
        );
        let repeated = EVec::<Maybe<I64>>::from_expression(
            adopt(
                &response,
                3,
                vec![],
                super::super::storage::builtin_catalog(),
            )
            .unwrap(),
        );
        let repeated = Vec::<Maybe<I64>>::try_from(&repeated).unwrap();
        assert_eq!(repeated[0], repeated[1]);
        assert_eq!(
            repeated[0].expression().0.index,
            repeated[1].expression().0.index
        );
        assert!(std::sync::Arc::ptr_eq(
            repeated[0].expression().0.owner.as_ref().unwrap(),
            repeated[1].expression().0.owner.as_ref().unwrap()
        ));
        let mut none = response.clone();
        let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Maybe(payload)),
        })) = &mut none.nodes[2].kind
        else {
            panic!()
        };
        payload.value = None;
        let none = Maybe::<I64>::from_expression(
            adopt(&none, 2, vec![], super::super::storage::builtin_catalog()).unwrap(),
        );
        assert_eq!(Option::<I64>::try_from(&none).unwrap(), None);
        assert_ne!(none, value);
        for case in 0..7 {
            let mut malformed = response.clone();
            match case {
                0 => {
                    malformed.nodes[2].kind =
                        Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                            value: Some(pb::primitive_value::Value::Maybe(pb::MaybeValue {
                                value: Some(99),
                            })),
                        }))
                }
                1 => malformed.nodes[0].sort_id = 1,
                2 => malformed.sorts[1].kind = Some(pb::sort::Kind::Eq("Maybe".into())),
                3 => {
                    malformed.sorts[1].kind =
                        Some(pb::sort::Kind::Application(pb::SortApplication {
                            name: "Vec".into(),
                            args: vec![0],
                        }))
                }
                4 => {
                    malformed.sorts[1].kind =
                        Some(pb::sort::Kind::Application(pb::SortApplication {
                            name: "Maybe".into(),
                            args: vec![],
                        }))
                }
                5 => malformed.nodes[0].kind = Some(pb::node::Kind::Var("symbolic".into())),
                _ => {
                    malformed.nodes[2].kind =
                        Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                            value: Some(pb::primitive_value::Value::Vec(pb::ValueList {
                                items: vec![0],
                            })),
                        }))
                }
            }
            assert!(
                adopt(
                    &malformed,
                    2,
                    vec![],
                    super::super::storage::builtin_catalog()
                )
                .is_err(),
                "Maybe response negative {case}"
            );
        }
        let atom = SortRef::equality("A");
        let family = super::super::storage::builtin_catalog()
            .declaration("Maybe", DeclarationKind::PrimitiveSort)
            .unwrap();
        let sort = SortRef::family(&family, vec![atom.clone()]).unwrap();
        let pack = Callable::constructor("Pack", vec![sort], atom, None, false);
        let mut cycle = response;
        cycle.sorts[0].kind = Some(pb::sort::Kind::Eq("A".into()));
        cycle.nodes[0].kind = Some(pb::node::Kind::Call(pb::Call {
            func: "Pack".into(),
            args: vec![2],
        }));
        assert!(
            matches!(adopt(&cycle, 2, vec![pack.0], super::super::storage::builtin_catalog()), Err(TypedError::Decode(s)) if s == "cyclic extraction is not inert data")
        );
    }

    #[test]
    fn vec_response_adoption_checks_relocation_payloads_and_cycles() {
        use crate::typed::{EgglogValue, builtins::I64};
        let response = pb::RunProgramOutput {
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
                        name: "Vec".into(),
                        args: vec![0],
                    })),
                    ..Default::default()
                },
            ],
            nodes: vec![
                pb::Node {
                    sort_id: 1,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Vec(pb::ValueList {
                            items: vec![1, 2, 1],
                        })),
                    })),
                    ..Default::default()
                },
                pb::Node {
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::I64(7)),
                    })),
                    ..Default::default()
                },
                pb::Node {
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::I64(11)),
                    })),
                    ..Default::default()
                },
            ],
            ..Default::default()
        };
        let value = adopt(
            &response,
            0,
            vec![],
            super::super::storage::builtin_catalog(),
        )
        .unwrap();
        let children = value.sequence_elements(&I64::sort_ref(), "Vec").unwrap();
        assert_eq!(children[0].0.index, children[2].0.index);
        assert_eq!(
            children
                .iter()
                .map(|c| i64::try_from(&I64::from_expression(c.clone())).unwrap())
                .collect::<Vec<_>>(),
            [7, 11, 7]
        );
        let mut missing = response.clone();
        let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Vec(items)),
        })) = &mut missing.nodes[0].kind
        else {
            panic!()
        };
        items.items[0] = 99;
        assert!(
            matches!(adopt(&missing, 0, vec![], super::super::storage::builtin_catalog()), Err(TypedError::Decode(s)) if s == "invalid response node index")
        );
        let mut wrong = response.clone();
        wrong.nodes[1].sort_id = 1;
        assert!(
            matches!(adopt(&wrong, 0, vec![], super::super::storage::builtin_catalog()), Err(TypedError::Decode(s)) if s == "Vec payload element sort mismatch")
        );
        let mut cyclic_sort = response;
        let Some(pb::sort::Kind::Application(f)) = &mut cyclic_sort.sorts[1].kind else {
            panic!()
        };
        f.args[0] = 1;
        assert!(
            matches!(adopt(&cyclic_sort, 0, vec![], super::super::storage::builtin_catalog()), Err(TypedError::Invalid(s)) if s == "cyclic concrete sort")
        );

        let atom = SortRef::equality("A");
        let family = super::super::storage::builtin_catalog()
            .declaration("Vec", DeclarationKind::PrimitiveSort)
            .unwrap();
        let vector = SortRef::family(&family, vec![atom.clone()]).unwrap();
        let pack = Callable::constructor("Pack", vec![vector], atom, None, false);
        let cycle = pb::RunProgramOutput {
            sorts: vec![
                pb::Sort {
                    kind: Some(pb::sort::Kind::Eq("A".into())),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                        name: "Vec".into(),
                        args: vec![0],
                    })),
                    ..Default::default()
                },
            ],
            nodes: vec![
                pb::Node {
                    sort_id: 1,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Vec(pb::ValueList {
                            items: vec![1],
                        })),
                    })),
                    ..Default::default()
                },
                pb::Node {
                    kind: Some(pb::node::Kind::Call(pb::Call {
                        func: "Pack".into(),
                        args: vec![0],
                    })),
                    ..Default::default()
                },
            ],
            ..Default::default()
        };
        assert!(
            matches!(adopt(&cycle, 0, vec![pack.0], super::super::storage::builtin_catalog()), Err(TypedError::Decode(s)) if s == "cyclic extraction is not inert data")
        );
    }

    #[test]
    fn new_scalar_bytes_preserve_canonical_calls_payloads_and_tail_views() {
        use crate::typed::builtins::{Bool, I64, String as EString, Unit, join};
        use pb::primitive_value::Value;
        let a = EString::from("a\0b\n☃");
        let b = EString::from("tail");
        let false_value = Bool::from(false);
        let true_value = Bool::from(true);
        let mut cases = vec![
            (
                a.expression().clone(),
                "",
                vec![],
                Value::String("a\0b\n☃".into()),
            ),
            (
                false_value.expression().clone(),
                "",
                vec![],
                Value::Bool(false),
            ),
            (
                Unit::from(()).expression().clone(),
                "",
                vec![],
                Value::Unit(pb::Unit {}),
            ),
            (
                (&a + &b).expression().clone(),
                "egglog.core.string.concat",
                vec![
                    Value::String("a\0b\n☃".into()),
                    Value::String("tail".into()),
                ],
                Value::String("a\0b\n☃tail".into()),
            ),
            (
                a.clone().replace("b", "B").expression().clone(),
                "egglog.core.string.replace",
                vec![
                    Value::String("a\0b\n☃".into()),
                    Value::String("b".into()),
                    Value::String("B".into()),
                ],
                Value::String("a\0B\n☃".into()),
            ),
            (
                I64::from(-7).to_string().expression().clone(),
                "egglog.core.i64.to_string",
                vec![Value::I64(-7)],
                Value::String("-7".into()),
            ),
            (
                (!&false_value).expression().clone(),
                "egglog.core.bool.not",
                vec![Value::Bool(false)],
                Value::Bool(true),
            ),
            (
                (&false_value & &true_value).expression().clone(),
                "egglog.core.bool.and",
                vec![Value::Bool(false), Value::Bool(true)],
                Value::Bool(false),
            ),
            (
                (&false_value | &true_value).expression().clone(),
                "egglog.core.bool.or",
                vec![Value::Bool(false), Value::Bool(true)],
                Value::Bool(true),
            ),
            (
                (&false_value ^ &true_value).expression().clone(),
                "egglog.core.bool.xor",
                vec![Value::Bool(false), Value::Bool(true)],
                Value::Bool(true),
            ),
            (
                true_value
                    .clone()
                    .implies(&false_value)
                    .expression()
                    .clone(),
                "egglog.core.bool.implies",
                vec![Value::Bool(true), Value::Bool(false)],
                Value::Bool(false),
            ),
        ];
        for parts in [vec![], vec!["one"], vec!["a", "b", "c", "d", "e"]] {
            cases.push((
                join(parts.clone()).expression().clone(),
                "egglog.core.string.concat",
                parts
                    .iter()
                    .map(|part| Value::String((*part).into()))
                    .collect(),
                Value::String(parts.concat()),
            ));
        }
        // The public Rust Bool surface is binary. Exercise the actual canonical
        // provider's remaining arities through its retained record and bytes.
        let callable = Callable(
            super::super::storage::builtin_catalog()
                .declaration("egglog.core.bool.or", DeclarationKind::Callable)
                .unwrap(),
        );
        for values in [vec![], vec![false], vec![false, true, false, false, false]] {
            cases.push((
                Expr::call_with_result(
                    &callable,
                    values
                        .iter()
                        .map(|value| Bool::from(value).expression().clone())
                        .collect(),
                    Bool::sort_ref(),
                )
                .unwrap(),
                "egglog.core.bool.or",
                values.iter().copied().map(Value::Bool).collect(),
                Value::Bool(values.iter().any(|value| *value)),
            ));
        }
        for (expression, provider, inputs, expected) in cases {
            let mut packer = Packer::default();
            let root = packer.intern(expression.0, 0);
            packer.program.commands.push(pb::Command {
                kind: Some(pb::command::Kind::Extract(pb::Extract {
                    roots: vec![root],
                    variants: 1,
                    extractor: pb::Extractor::Tree.into(),
                    ..Default::default()
                })),
                ..Default::default()
            });
            let mut graph = EGraph::default();
            let response = Observed::from_frames(graph.execute(packer, false).unwrap());
            let request =
                pb::RunProgramRequest::decode(graph.last_wire.as_ref().unwrap().0.as_slice())
                    .unwrap()
                    .program
                    .unwrap();
            assert_eq!(
                pb::Program::decode(request.encode_to_vec().as_slice()).unwrap(),
                request
            );
            if !provider.is_empty() {
                let Some(pb::node::Kind::Call(call)) = &request.nodes[root as usize].kind else {
                    panic!()
                };
                assert_eq!(call.func, provider);
                let actual = call
                    .args
                    .iter()
                    .map(|index| {
                        let Some(pb::node::Kind::PrimitiveValue(value)) =
                            &request.nodes[*index as usize].kind
                        else {
                            panic!()
                        };
                        value.value.clone().unwrap()
                    })
                    .collect::<Vec<_>>();
                assert_eq!(actual, inputs);
            }
            let Some(pb::command_output::Kind::Extraction(extracted)) =
                &response.output.outputs[0].kind
            else {
                panic!()
            };
            let term = extracted.roots[0].variants[0].term;
            assert_eq!(
                response.output.nodes[term as usize].kind,
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(expected.clone())
                }))
            );
            let adopted = adopt(
                &response.output,
                term,
                vec![],
                super::super::storage::builtin_catalog(),
            )
            .unwrap();
            match expected {
                Value::String(value) => assert_eq!(
                    String::try_from(&ensure_sort::<EString>(adopted).unwrap()).unwrap(),
                    value
                ),
                Value::Bool(value) => assert_eq!(
                    bool::try_from(&ensure_sort::<Bool>(adopted).unwrap()).unwrap(),
                    value
                ),
                Value::Unit(_) => <()>::try_from(&ensure_sort::<Unit>(adopted).unwrap()).unwrap(),
                _ => panic!(),
            }
            let mut malformed = response.clone();
            malformed.output.nodes[term as usize].kind =
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(Value::I64(0)),
                }));
            assert!(
                adopt(
                    &malformed.output,
                    term,
                    vec![],
                    super::super::storage::builtin_catalog()
                )
                .is_err(),
                "wrong scalar payload for {provider}"
            );
            let sort = response.output.nodes[term as usize].sort_id;
            malformed = response;
            let Some(pb::sort::Kind::Application(family)) =
                &mut malformed.output.sorts[sort as usize].kind
            else {
                panic!()
            };
            family.name = "UnsupportedScalar".into();
            assert!(
                adopt(
                    &malformed.output,
                    term,
                    vec![],
                    super::super::storage::builtin_catalog()
                )
                .is_err()
            );
        }
    }

    #[test]
    fn scalar_bytes_and_decoder_payload_types() {
        use crate::typed::builtins::{F64, I64};
        let mut graph = EGraph::default();
        let result = graph.extract(I64::from(2) + I64::from(3)).unwrap();
        assert_eq!(i64::try_from(&result).unwrap(), 5);
        let (input, output) = graph.last_wire.as_ref().unwrap();
        let request = pb::RunProgramRequest::decode(input.as_slice()).unwrap();
        let p = request.program.unwrap();
        assert!(p.nodes.iter().any(|n| matches!(&n.kind,
            Some(pb::node::Kind::Call(c)) if c.func == "egglog.core.i64.add")));
        assert!(!p.nodes.iter().any(|n| matches!(&n.kind,
            Some(pb::node::Kind::Call(c)) if c.func == "+")));
        let mut response = Observed::from_frames(
            output
                .iter()
                .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()),
        );
        let Some(pb::command_output::Kind::Extraction(extracted)) =
            &response.output.outputs[0].kind
        else {
            panic!()
        };
        let term = extracted.roots[0].variants[0].term;
        let declarations = graph.declarations.values().cloned().collect::<Vec<_>>();
        assert!(
            ensure_sort::<I64>(
                adopt(
                    &response.output,
                    term,
                    declarations.clone(),
                    super::super::storage::builtin_catalog()
                )
                .unwrap()
            )
            .is_ok()
        );
        assert!(
            ensure_sort::<F64>(
                adopt(
                    &response.output,
                    term,
                    declarations.clone(),
                    super::super::storage::builtin_catalog()
                )
                .unwrap()
            )
            .is_err()
        );
        response.output.nodes[term as usize].kind =
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::F64Bits(0)),
            }));
        assert!(
            adopt(
                &response.output,
                term,
                declarations.clone(),
                super::super::storage::builtin_catalog()
            )
            .is_err(),
            "f64 payload in i64 sort"
        );
        let sort_id = response.output.nodes[term as usize].sort_id;
        let first = response.output.nodes.len() as u32;
        for value in [2, 3] {
            response.output.nodes.push(pb::Node {
                sort_id,
                kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::I64(value)),
                })),
                ..Default::default()
            });
        }
        response.output.nodes[term as usize].kind = Some(pb::node::Kind::Call(pb::Call {
            func: "egglog.core.i64.add".into(),
            args: vec![first, first + 1],
        }));
        let mut declarations = declarations;
        declarations.push(
            super::super::storage::builtin_catalog()
                .declaration("egglog.core.i64.add", DeclarationKind::Callable)
                .unwrap(),
        );
        let error = adopt(
            &response.output,
            term,
            declarations,
            super::super::storage::builtin_catalog(),
        )
        .unwrap_err();
        assert!(
            matches!(error, TypedError::Decode(ref message) if message == "extracted call is not a constructor"),
            "wrong rejection guard: {error}"
        );
    }

    fn response(args: Vec<u32>, child: bool) -> (pb::RunProgramOutput, Vec<Record>) {
        let sort = SortRef::equality("M");
        let pair = Callable::constructor(
            "Pair",
            vec![sort.clone(), sort.clone()],
            sort.clone(),
            None,
            false,
        );
        let leaf = Callable::constructor("Leaf", vec![], sort, None, false);
        let mut response = pb::RunProgramOutput {
            sorts: vec![pb::Sort {
                kind: Some(pb::sort::Kind::Eq("M".into())),
                ..Default::default()
            }],
            nodes: vec![pb::Node {
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "Pair".into(),
                    args,
                })),
                ..Default::default()
            }],
            ..Default::default()
        };
        if child {
            response.nodes.push(pb::Node {
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "Leaf".into(),
                    args: vec![],
                })),
                ..Default::default()
            });
        }
        (response, vec![pair.0, leaf.0])
    }

    #[test]
    fn decoded_data_rejects_cycles_missing_children_and_bad_signatures() {
        let (r, declarations) = response(vec![0, 0], false);
        assert!(
            adopt(
                &r,
                0,
                declarations,
                super::super::storage::builtin_catalog()
            )
            .is_err(),
            "call-only cycle is not inert data"
        );
        let (r, declarations) = response(vec![1, 1], false);
        assert!(
            adopt(
                &r,
                0,
                declarations,
                super::super::storage::builtin_catalog()
            )
            .is_err(),
            "missing child"
        );
        let (r, declarations) = response(vec![], false);
        assert!(
            adopt(
                &r,
                0,
                declarations,
                super::super::storage::builtin_catalog()
            )
            .is_err(),
            "wrong call arity"
        );
        let (mut r, declarations) = response(vec![1, 1], true);
        r.sorts.push(pb::Sort {
            kind: Some(pb::sort::Kind::Eq("N".into())),
            ..Default::default()
        });
        r.nodes[1].sort_id = 1;
        assert!(
            adopt(
                &r,
                0,
                declarations,
                super::super::storage::builtin_catalog()
            )
            .is_err(),
            "wrong child/output sort"
        );
        let (mut r, declarations) = response(vec![1, 1], true);
        r.sorts.push(pb::Sort {
            kind: Some(pb::sort::Kind::Eq("N".into())),
            ..Default::default()
        });
        r.nodes[0].sort_id = 1;
        assert!(
            adopt(
                &r,
                0,
                declarations,
                super::super::storage::builtin_catalog()
            )
            .is_err(),
            "wrong root output sort"
        );
        let (r, declarations) = response(vec![1, 1], true);
        assert!(
            adopt(
                &r,
                0,
                declarations,
                super::super::storage::builtin_catalog()
            )
            .is_ok(),
            "shared finite child is valid"
        );
    }

    #[test]
    fn set_adoption_relocates_exact_slots_and_rejects_malformed_closures() {
        use crate::typed::{
            EgglogValue,
            builtins::{I64, Set},
        };
        let response = pb::RunProgramOutput {
            sorts: vec![
                pb::Sort {
                    kind: Some(pb::sort::Kind::Eq("Unused".into())),
                    ..Default::default()
                },
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
                        args: vec![1],
                    })),
                    ..Default::default()
                },
            ],
            nodes: vec![
                pb::Node {
                    sort_id: 1,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::I64(7)),
                    })),
                    ..Default::default()
                },
                pb::Node {
                    kind: Some(pb::node::Kind::Var("unrelated invalid observation".into())),
                    ..Default::default()
                },
                pb::Node {
                    sort_id: 2,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Set(pb::ValueList {
                            items: vec![3, 0],
                        })),
                    })),
                    ..Default::default()
                },
                pb::Node {
                    sort_id: 1,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::I64(11)),
                    })),
                    ..Default::default()
                },
            ],
            ..Default::default()
        };
        let adopted = ensure_sort::<Set<I64>>(
            adopt(
                &response,
                2,
                vec![],
                super::super::storage::builtin_catalog(),
            )
            .unwrap(),
        )
        .unwrap();
        assert_eq!(
            Vec::<I64>::try_from(&adopted).unwrap(),
            [I64::from(11), I64::from(7)]
        );
        assert_eq!(
            adopted
                .expression()
                .0
                .owner
                .as_ref()
                .unwrap()
                .program()
                .unwrap()
                .nodes
                .len(),
            3
        );
        for case in 0..8 {
            let mut malformed = response.clone();
            match case {
                0 => {
                    malformed.nodes[2].kind =
                        Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                            value: Some(pb::primitive_value::Value::Vec(pb::ValueList {
                                items: vec![],
                            })),
                        }))
                }
                1 => {
                    let Some(pb::sort::Kind::Application(f)) = &mut malformed.sorts[2].kind else {
                        panic!()
                    };
                    f.name = "Vec".into();
                }
                2..=4 => {
                    let Some(pb::sort::Kind::Application(f)) = &mut malformed.sorts[2].kind else {
                        panic!()
                    };
                    f.args = match case {
                        2 => vec![],
                        3 => vec![1, 1],
                        _ => vec![2],
                    };
                }
                5 => {
                    malformed.nodes[2].kind =
                        Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                            value: Some(pb::primitive_value::Value::Set(pb::ValueList {
                                items: vec![99],
                            })),
                        }))
                }
                6 => malformed.nodes[0].sort_id = 2,
                7 => malformed.nodes[0].kind = Some(pb::node::Kind::Var("unbound".into())),
                _ => unreachable!(),
            }
            assert!(
                adopt(
                    &malformed,
                    2,
                    vec![],
                    super::super::storage::builtin_catalog()
                )
                .is_err(),
                "Set adoption negative {case}"
            );
        }
        let mut symbolic = response;
        symbolic.nodes[0].kind = Some(pb::node::Kind::Call(pb::Call {
            func: "egglog.core.i64.add".into(),
            args: vec![3, 3],
        }));
        let add = super::super::storage::builtin_catalog()
            .declaration("egglog.core.i64.add", DeclarationKind::Callable)
            .unwrap();
        assert!(
            matches!(adopt(&symbolic, 2, vec![add], super::super::storage::builtin_catalog()), Err(TypedError::Decode(message)) if message == "extracted call is not a constructor")
        );

        let atom = SortRef::equality("SetCycle");
        let family = super::super::storage::builtin_catalog()
            .declaration("Set", DeclarationKind::PrimitiveSort)
            .unwrap();
        let set = SortRef::family(&family, vec![atom.clone()]).unwrap();
        let pack = Callable::constructor("Pack", vec![set], atom, None, false);
        let cyclic = pb::RunProgramOutput {
            sorts: vec![
                pb::Sort {
                    kind: Some(pb::sort::Kind::Eq("SetCycle".into())),
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
                    sort_id: 1,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Set(pb::ValueList {
                            items: vec![1],
                        })),
                    })),
                    ..Default::default()
                },
                pb::Node {
                    kind: Some(pb::node::Kind::Call(pb::Call {
                        func: "Pack".into(),
                        args: vec![0],
                    })),
                    ..Default::default()
                },
            ],
            ..Default::default()
        };
        assert!(
            matches!(adopt(&cyclic, 0, vec![pack.0], super::super::storage::builtin_catalog()), Err(TypedError::Decode(message)) if message == "cyclic extraction is not inert data")
        );
    }

    #[test]
    fn generated_ne_uses_actual_catalog_calls_bytes_and_native_class_equality() {
        use crate::typed::{
            builtins::{I64, Unit, Vec as EggVec},
            ne,
            prelude::*,
        };
        // Declaration macros target external clients; their public path is
        // covered in typed_proto. This internal witness needs private wire access.
        #[derive(Clone, Debug, PartialEq, Eq, Hash)]
        struct NeByteTerm(Expr);
        impl super::super::expr::ValueInput for NeByteTerm {
            type Owned = Self;
        }
        impl From<&NeByteTerm> for NeByteTerm {
            fn from(value: &NeByteTerm) -> Self {
                value.clone()
            }
        }
        impl EgglogValue for NeByteTerm {
            fn sort_ref() -> SortRef {
                SortRef::equality("NeByteTerm")
            }
            fn expression(&self) -> &Expr {
                &self.0
            }
            fn from_expression(expr: Expr) -> Self {
                Self(expr)
            }
        }
        impl EqualitySort for NeByteTerm {}

        // Observe each submitted call and the native reply, including failed
        // checks. This is not a synthetic response or an alternate evaluator.
        let observe = |graph: &mut EGraph, fact: Unit, expected: bool| {
            assert_eq!(graph.check(&fact).unwrap(), expected);
            let (input, output) = graph.last_wire.as_ref().unwrap();
            let request = pb::RunProgramRequest::decode(input.as_slice()).unwrap();
            let program = request.program.unwrap();
            let Some(pb::command::Kind::Check(check)) = &program.commands[0].kind else {
                panic!()
            };
            assert_eq!(check.facts.len(), 1);
            let root = &program.nodes[check.facts[0] as usize];
            let Some(pb::node::Kind::Call(call)) = &root.kind else {
                panic!()
            };
            assert_eq!(call.func, "egglog.core.ne");
            assert_eq!(call.args.len(), 2);
            // Distinct expression owners can relocate equal sorts into distinct
            // slots. Reuse the ordinary SortRef comparison on the actual packet.
            let mut slots = std::array::from_fn(|_| vec![]);
            slots[Arena::Sort as usize] =
                (0..program.sorts.len() as u32).map(Slot::Local).collect();
            slots[Arena::Declaration as usize] = (0..program.declarations.len() as u32)
                .map(Slot::Local)
                .collect();
            let sorts = publish(
                pb::Program {
                    sorts: program.sorts.clone(),
                    declarations: program.declarations.clone(),
                    ..Default::default()
                },
                slots,
                vec![graph.builtins.clone()],
                Arena::Sort,
                root.sort_id,
                vec![],
            )
            .unwrap();
            assert!(
                SortRef(
                    sorts
                        .resolve(Arena::Sort, program.nodes[call.args[0] as usize].sort_id)
                        .unwrap()
                ) == SortRef(
                    sorts
                        .resolve(Arena::Sort, program.nodes[call.args[1] as usize].sort_id)
                        .unwrap()
                ),
            );
            assert!(matches!(&program.sorts[root.sort_id as usize].kind,
                Some(pb::sort::Kind::Application(f)) if f.name == "Unit" && f.args.is_empty()));
            let declaration = graph
                .builtins
                .declaration(&call.func, DeclarationKind::Callable)
                .unwrap();
            let primitive = declaration.primitive().unwrap();
            let Some(signature) = &primitive.signature else {
                panic!()
            };
            assert_eq!(signature.type_param_count as usize, 1);
            assert_eq!(signature.inputs.len(), 2);
            assert!(signature.varargs.is_empty());
            assert_eq!(signature.inputs[0].sort, signature.inputs[1].sort);
            assert_eq!(
                declaration
                    .resolve(Arena::Sort, signature.inputs[0].sort)
                    .unwrap()
                    .sort()
                    .unwrap()
                    .kind,
                Some(pb::sort::Kind::Var(0))
            );
            assert!(
                SortRef(
                    declaration
                        .resolve(Arena::Sort, signature.output.unwrap())
                        .unwrap()
                ) == SortRef(sorts)
            );
            let generated = crate::typed::storage::builtin_catalog()
                .declaration(&call.func, DeclarationKind::Callable)
                .unwrap();
            assert!(crate::typed::decl::same_builtin(&declaration, &generated).unwrap());
            let response = Observed::from_frames(
                output
                    .iter()
                    .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()),
            );
            assert_eq!(
                response.error.as_ref().map(|e| e.code),
                (!expected).then_some(pb::ErrorCode::CheckFailed as i32)
            );
            program
        };
        let mut graph = EGraph::default();
        let program = observe(&mut graph, ne(I64::from(17), 23), true);
        let call = program
            .nodes
            .iter()
            .find_map(|n| match &n.kind {
                Some(pb::node::Kind::Call(call)) if call.func == "egglog.core.ne" => Some(call),
                _ => None,
            })
            .unwrap();
        for (index, expected) in call.args.iter().zip([17, 23]) {
            assert!(matches!(&program.nodes[*index as usize].kind,
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::I64(actual)),
                })) if *actual == expected));
        }
        observe(&mut graph, ne(I64::from(17), 17), false);
        let left = NeByteTerm(Expr::call(
            &Callable::constructor(
                "NeByteTerm.Left",
                vec![],
                NeByteTerm::sort_ref(),
                None,
                false,
            ),
            vec![],
        ));
        let right = NeByteTerm(Expr::call(
            &Callable::constructor(
                "NeByteTerm.Right",
                vec![],
                NeByteTerm::sort_ref(),
                None,
                false,
            ),
            vec![],
        ));
        let left_vec = EggVec::<NeByteTerm>::of([&left]);
        let right_vec = EggVec::<NeByteTerm>::of([&right]);
        graph
            .register((&left, &right, &left_vec, &right_vec))
            .unwrap();
        observe(&mut graph, ne(&left, &right), true);
        observe(&mut graph, ne(&left_vec, &right_vec), true);
        graph.run(ruleset(rewrite(&left, &right))).unwrap();
        observe(&mut graph, ne(&left, &right), false);
        observe(&mut graph, ne(&left_vec, &right_vec), false);
        assert_ne!(left, right);
        assert_ne!(left_vec, right_vec);
        observe(&mut graph, ne(I64::from(17), 23), true);

        // Corrupt bytes cannot turn failed checks into success or permit a
        // subsequent call on a session with unknown transport state.
        assert!(matches!(
            graph.accept_response(Packer::default(), &[vec![0xff]]),
            Err(TypedError::Decode(_))
        ));
        assert!(matches!(graph.check(ne(I64::from(17), 23)),
            Err(TypedError::Invalid(message)) if message == "session transport state is unknown"));
    }

    #[test]
    fn generated_set_input_and_output_are_observed_in_actual_bytes() {
        use crate::typed::{
            EgglogValue,
            builtins::{I64, Set},
        };
        let a = I64::from(2);
        let b = I64::from(1);
        let authored = Set::<I64>::of([&a, &b, &a]);
        let mut graph = EGraph::default();
        let extracted = graph.extract(&authored).unwrap();
        let (input, output) = graph.last_wire.as_ref().unwrap();
        let request = pb::RunProgramRequest::decode(input.as_slice()).unwrap();
        let program = request.program.unwrap();
        let Some(pb::command::Kind::Extract(extract)) = &program.commands[0].kind else {
            panic!()
        };
        let root = &program.nodes[extract.roots[0] as usize];
        let Some(pb::node::Kind::Call(call)) = &root.kind else {
            panic!()
        };
        assert_eq!(call.func, "egglog.core.set.of");
        assert_eq!(call.args.len(), 3);
        assert_eq!(call.args[0], call.args[2]);
        for (index, expected) in call.args.iter().zip([2, 1, 2]) {
            assert!(
                matches!(&program.nodes[*index as usize].kind, Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue { value: Some(pb::primitive_value::Value::I64(value)) })) if *value == expected)
            );
        }
        let response = Observed::from_frames(
            output
                .iter()
                .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()),
        );
        assert!(response.error.is_none());
        let term = response
            .output
            .outputs
            .iter()
            .find_map(|out| match &out.kind {
                Some(pb::command_output::Kind::Extraction(e)) => Some(e.roots[0].variants[0].term),
                _ => None,
            })
            .unwrap();
        let root = &response.output.nodes[term as usize];
        let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Set(items)),
        })) = &root.kind
        else {
            panic!()
        };
        assert_eq!(items.items.len(), 2);
        let Some(pb::sort::Kind::Application(family)) =
            &response.output.sorts[root.sort_id as usize].kind
        else {
            panic!()
        };
        assert_eq!(family.name, "Set");
        assert_eq!(family.args.len(), 1);
        for child in &items.items {
            assert_eq!(
                response.output.nodes[*child as usize].sort_id,
                family.args[0]
            );
        }
        let independently_adopted = ensure_sort::<Set<I64>>(
            adopt(
                &response.output,
                term,
                vec![],
                super::super::storage::builtin_catalog(),
            )
            .unwrap(),
        )
        .unwrap();
        assert_eq!(extracted, independently_adopted);
        assert_eq!(Vec::<I64>::try_from(&extracted).unwrap().len(), 2);
        assert_ne!(authored.expression(), extracted.expression());
    }

    #[test]
    fn actual_bytes_are_encoded_executed_and_decoded() {
        let sort = SortRef::equality("ByteWitness");
        let leaf = Callable::constructor("ByteWitness.Leaf", vec![], sort, None, false);
        let expression = Expr::call(&leaf, vec![]);
        let mut packer = Packer::default();
        let root = packer.intern(expression.0, 0);
        packer.program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Extract(pb::Extract {
                roots: vec![root],
                variants: 1,
                extractor: pb::Extractor::Tree.into(),
                ..Default::default()
            })),
            ..Default::default()
        });
        let mut graph = EGraph::default();
        let response = graph.execute(packer, false).unwrap();
        let (input, output) = graph.last_wire.as_ref().unwrap();
        let request = pb::RunProgramRequest::decode(input.as_slice()).unwrap();
        assert_eq!(request.egraph_id, graph.handle);
        assert!(!request.diagnostics);
        assert!(
            matches!(&request.program.unwrap().nodes[root as usize].kind, Some(pb::node::Kind::Call(c)) if c.func == "ByteWitness.Leaf")
        );
        assert_eq!(
            output
                .iter()
                .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap())
                .collect::<Vec<_>>(),
            response
        );
        let observed = Observed::from_frames(response);
        assert!(matches!(
            observed.output.outputs[0].kind,
            Some(pb::command_output::Kind::Extraction(_))
        ));
    }

    #[test]
    fn explicit_group_names_and_named_captures_lower_to_additions() {
        use super::super::{builtins::I64, rule, rule::named_ruleset, ruleset};
        let child = ruleset(rule((), I64::from(7)));
        let mut graph = EGraph::default();
        for explicit in ["chosen", "", "__typed_ruleset_3"] {
            let group = named_ruleset(|| Some(explicit.into()), (&child, &child));
            graph.run(group).unwrap();
            let request =
                pb::RunProgramRequest::decode(graph.last_wire.as_ref().unwrap().0.as_slice())
                    .unwrap();
            let program = request.program.unwrap();
            let Some(pb::command::Kind::Loop(repeat)) = &program.commands[0].kind else {
                panic!("one report scope")
            };
            let Some(pb::command::Kind::AddRules(add)) = &repeat.body[0].kind else {
                panic!("ordered registration")
            };
            assert_eq!(add.group, explicit);
            assert_eq!(add.rules.len(), 2);
            assert_eq!(add.rules[0], add.rules[1]);
            let Some(pb::command::Kind::Run(run)) = &repeat.body[1].kind else {
                panic!("group selection")
            };
            assert_eq!(run.groups, [explicit]);
        }
    }
}
