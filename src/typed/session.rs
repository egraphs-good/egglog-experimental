use super::{
    EgglogValue, TypedError,
    expr::{Expr, ValueInput},
    pb,
    rule::{Actions, Facts, ensure_sort},
    storage::{
        Arena, DeclarationKind, Key, Packer, Record, Slot, closure, publish, visit, visit_action,
    },
};
use prost::Message;
use std::{
    collections::{HashMap, HashSet},
    sync::{Arc, Mutex},
};

// Locations and binding observations only. Canonical records remain the sole
// definition of bodies, composition, and sharing; no failed Program is retained.
#[derive(Clone, Default)]
struct Publication {
    reserved: HashMap<Key, String>,
    confirmed: HashMap<Key, (Record, String)>,
    anchors: HashMap<Key, Key>,
}

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
                    match &owner.program.declarations[record.index as usize].kind {
                        Some(pb::declaration::Kind::Constructor(c)) => Some(&c.name),
                        Some(pb::declaration::Kind::Function(f)) => Some(&f.name),
                        Some(pb::declaration::Kind::Relation(r)) => Some(&r.name),
                        Some(pb::declaration::Kind::HostPrimitive(p)) => Some(&p.name),
                        _ => None,
                    }
                }
                Arena::Node if record.capture()?.is_none() => {
                    match &owner.program.nodes[record.index as usize].kind {
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
            let node = &owner.program.nodes[record.index as usize];
            match &node.kind {
                Some(pb::node::Kind::Var(_)) if evaluated => {
                    return Err(TypedError::Invalid(
                        "free variable in evaluated input".into(),
                    ));
                }
                Some(pb::node::Kind::Union(_)) => eligible = false,
                Some(pb::node::Kind::Call(call)) => {
                    let declaration = record.declaration(&call.func, DeclarationKind::Callable)?;
                    eligible &= matches!(
                        declaration.owner.as_ref().unwrap().program.declarations
                            [declaration.index as usize]
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

// Walk group edges, including empty groups and distinct equal rule occurrences.
// Node/declaration bodies are left to the existing canonical packer.
fn occurrences(root: &Record) -> Result<Vec<Record>, TypedError> {
    let mut pending = vec![root.clone()];
    let mut seen = HashSet::new();
    let mut result = vec![];
    while let Some(record) = pending.pop() {
        let owner = record.owner.as_ref().unwrap();
        if !seen.insert(record.key()) {
            continue;
        }
        if record.arena == Arena::Ruleset {
            let mut one = pb::Program {
                rulesets: vec![owner.program.rulesets[record.index as usize].clone()],
                ..Default::default()
            };
            let mut children = vec![];
            super::storage::visit(&mut one, Arena::Ruleset, 0, |arena, index| {
                children.push(record.resolve(arena, index)?);
                Ok(index)
            })?;
            pending.extend(children.into_iter().rev());
        }
        result.push(record);
    }
    Ok(result)
}

impl Publication {
    fn prepare_run(&mut self, root: &Record) -> Result<Packer, TypedError> {
        let target = occurrences(root)?;
        let target_keys: HashSet<_> = target.iter().map(|r| r.key()).collect();
        let root_key = root.key();
        // Reserve every authored name before choosing a private root name.
        for record in &target {
            let owner = record.owner.as_ref().unwrap();
            if record.arena == Arena::Ruleset
                && let Some(name) = &owner.program.rulesets[record.index as usize].name
            {
                self.reserved.insert(record.key(), name.clone());
            }
        }
        if !self.reserved.contains_key(&root_key) {
            let mut ordinal = self.reserved.len();
            let name = loop {
                let name = format!("__typed_ruleset_{ordinal}");
                if !self.reserved.values().any(|reserved| reserved == &name) {
                    break name;
                }
                ordinal += 1;
            };
            self.reserved.insert(root_key, name);
        }
        let name = self.reserved[&root_key].clone();
        let mut packer = Packer::default();
        let root_index = packer.intern(root.clone(), 0);
        let mut covered = HashSet::new();
        for record in &target {
            let key = record.key();
            if covered.contains(&key) {
                continue;
            }
            if let Some(anchor) = self.anchors.get(&key) {
                let (anchor, _) = &self.confirmed[anchor];
                packer.intern(anchor.clone(), 0);
                covered.extend(occurrences(anchor)?.iter().map(|r| r.key()));
            }
        }
        packer.finish()?;
        for (index, record) in packer.rulesets.iter().enumerate() {
            let key = record.key();
            let confirmed = self.confirmed.get(&key).map(|(_, name)| name.clone());
            let packed = &mut packer.program.rulesets[index];
            if target_keys.contains(&key) {
                // An explicit empty name remains a flat default RuleList.
                packed.name = packed.name.take().or(confirmed);
            } else {
                // An anchor is evidence, not a retry of uncompleted descendant
                // first-name proposals in its retained source closure.
                packed.name = confirmed;
            }
        }
        packer.program.rulesets[root_index as usize].name = Some(name.clone());
        packer.program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Run(pb::Run {
                ruleset: Some(pb::RulesetRef {
                    kind: Some(pb::ruleset_ref::Kind::Name(name)),
                }),
                ..Default::default()
            })),
            ..Default::default()
        });
        Ok(packer)
    }

    fn observe(
        &mut self,
        packer: &Packer,
        response: &pb::RunProgramResponse,
    ) -> Result<(), TypedError> {
        let receipt = response.ruleset_publication.as_ref().ok_or_else(|| {
            TypedError::Decode("missing ruleset publication receipt; publication unknown".into())
        })?;
        if packer.program.rulesets.len() != packer.rulesets.len() {
            return Err(TypedError::Invalid(
                "missing source ruleset locations".into(),
            ));
        }
        let mut submitted: HashMap<&str, Vec<&Record>> = HashMap::new();
        for (ruleset, record) in packer.program.rulesets.iter().zip(&packer.rulesets) {
            if let Some(name) = &ruleset.name {
                submitted.entry(name).or_default().push(record);
            }
        }
        let mut names = HashSet::new();
        for name in &receipt.names {
            if !names.insert(name.as_str()) || !submitted.contains_key(name.as_str()) {
                return Err(TypedError::Decode(
                    "duplicate or unsubmitted ruleset publication name".into(),
                ));
            }
        }
        let complete = response.error.as_ref().is_none_or(|e| e.location.is_some());
        if complete && names.len() != submitted.len() {
            return Err(TypedError::Decode(
                "incomplete ruleset publication receipt".into(),
            ));
        }
        if response
            .error
            .as_ref()
            .is_some_and(|e| e.code == pb::ErrorCode::InvalidProgram as i32)
            && !names.is_empty()
        {
            return Err(TypedError::Decode(
                "invalid-program response confirms ruleset publication".into(),
            ));
        }
        // Validate all locations before any promotion. Arena indices are used
        // only to decode this request; retained identities are source locations.
        let mut confirmed = vec![];
        for name in &receipt.names {
            for record in &submitted[name.as_str()] {
                confirmed.push(((*record).clone(), name.clone(), occurrences(record)?));
            }
        }
        for (record, name, closure) in confirmed {
            let key = record.key();
            for child in closure {
                self.anchors.entry(child.key()).or_insert(key);
            }
            self.anchors.insert(key, key);
            self.confirmed.insert(key, (record, name));
        }
        Ok(())
    }
}

// Saved handles are private and never executed while on the stack. Push only
// saves healthy state, so restoring these observations also restores health.
struct SavedScope {
    handle: u64,
    publication: Publication,
    declarations: HashMap<String, Record>,
    captures: HashMap<String, (Record, String)>,
    private_slots: HashSet<String>,
}

/// A byte-protocol session. No native EGraph or AST execution escape hatch.
pub struct EGraph {
    engine: Arc<Mutex<crate::protobuf::Engine>>,
    handle: u64,
    // An uncertain response cannot be repaired by guessing fresh identities.
    usable: bool,
    publication: Publication,
    declarations: HashMap<String, Record>,
    scopes: Vec<SavedScope>,
    captures: HashMap<String, (Record, String)>,
    private_slots: HashSet<String>,
    reserved_names: HashSet<String>,
    next_capture: u64,
    #[cfg(test)]
    last_wire: Option<(Vec<u8>, Vec<u8>)>,
}

impl Drop for EGraph {
    fn drop(&mut self) {
        // Never recover a poisoned engine or panic during destruction. A
        // poisoned transport's remaining storage is released with its last Arc.
        if let Ok(mut engine) = self.engine.lock() {
            for handle in std::iter::once(self.handle).chain(self.scopes.iter().map(|s| s.handle)) {
                let _ =
                    engine.destroy(&pb::DestroyEGraphRequest { egraph_id: handle }.encode_to_vec());
            }
        }
    }
}

impl Default for EGraph {
    fn default() -> Self {
        Self::new().expect("default byte engine creation")
    }
}

impl EGraph {
    /// Create a byte engine with the adapter's supported i64 cost domain.
    pub fn new() -> Result<Self, TypedError> {
        Self::with_recording(false)
    }

    /// Create a byte engine with optional structured execution history.
    /// Recording is unbounded when enabled and independent of logical Freeze.
    pub fn with_recording(record_history: bool) -> Result<Self, TypedError> {
        let mut engine = crate::protobuf::Engine::default();
        // Creation's fixed i64 cost domain is an adapter requirement, not a
        // Rust primitive callable registry.
        let request = pb::CreateEGraphRequest {
            record_history,
            sorts: vec![pb::Sort {
                kind: Some(pb::sort::Kind::Family(pb::HostSort {
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
            handle,
            usable: true,
            publication: Publication::default(),
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
                "session publication state is unknown".into(),
            ));
        }
        let bytes = self
            .engine
            .lock()
            .map_err(|_| TypedError::Invalid("byte engine mutex poisoned".into()))?
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
            handle,
            usable: true,
            publication: self.publication.clone(),
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

    /// Save native data, cursors and typed publication state in a new scope.
    pub fn push(&mut self) -> Result<(), TypedError> {
        if !self.usable {
            return Err(TypedError::Invalid(
                "session publication state is unknown".into(),
            ));
        }
        let publication = self.publication.clone();
        let declarations = self.declarations.clone();
        let bytes = self
            .engine
            .lock()
            .map_err(|_| TypedError::Invalid("byte engine mutex poisoned".into()))?
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
            publication: std::mem::replace(&mut self.publication, publication),
            declarations: std::mem::replace(&mut self.declarations, declarations),
            captures: self.captures.clone(),
            private_slots: self.private_slots.clone(),
        });
        Ok(())
    }

    /// Restore the latest scope, including known publication state and health.
    /// Cumulative native statistics and fresh-name state survive the pop.
    /// An empty stack or rejected native return leaves this session unchanged.
    pub fn pop(&mut self) -> Result<(), TypedError> {
        let saved = self
            .scopes
            .last()
            .ok_or_else(|| TypedError::Invalid("no saved scope".into()))?;
        let bytes = self
            .engine
            .lock()
            .map_err(|_| TypedError::Invalid("byte engine mutex poisoned".into()))?
            .return_to(
                &pb::ReturnToEGraphRequest {
                    active_id: self.handle,
                    saved_id: saved.handle,
                }
                .encode_to_vec(),
            )
            .map_err(|e| TypedError::Invalid(e.to_string()))?;
        // Native success already consumed the active handle. Transfer ownership
        // before decoding its empty acknowledgement; never destroy that child.
        let saved = self.scopes.pop().unwrap();
        self.handle = saved.handle;
        self.publication = saved.publication;
        self.declarations = saved.declarations;
        self.captures = saved.captures;
        self.private_slots = saved.private_slots;
        self.usable = true;
        pb::ReturnToEGraphResponse::decode(bytes.as_slice()).map_err(|e| {
            self.usable = false;
            TypedError::Decode(e.to_string())
        })?;
        Ok(())
    }

    fn execute(
        &mut self,
        mut packer: Packer,
        include_run_reports: bool,
    ) -> Result<pb::RunProgramResponse, TypedError> {
        if !self.usable {
            return Err(TypedError::Invalid(
                "session publication state is unknown".into(),
            ));
        }
        packer.finish()?;
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
            profile: true,
            include_run_reports,
        };
        let request = message.encode_to_vec();
        packer.program = message.program.unwrap();
        let bytes = self
            .engine
            .lock()
            .map_err(|_| TypedError::Invalid("byte engine mutex poisoned".into()))?
            .run(&request)
            .map_err(|e| TypedError::Invalid(e.to_string()))?;
        #[cfg(test)]
        {
            self.last_wire = Some((request, bytes.clone()));
        }
        self.accept_response(packer, &bytes)
    }

    // The effect boundary: reject uncertain replies without inventing recovery,
    // but promote valid receipts before returning ordinary native errors.
    fn accept_response(
        &mut self,
        packer: Packer,
        bytes: &[u8],
    ) -> Result<pb::RunProgramResponse, TypedError> {
        let response = pb::RunProgramResponse::decode(bytes).map_err(|e| {
            self.usable = false;
            TypedError::Decode(e.to_string())
        })?;
        let completed = match &response.error {
            None => packer.program.commands.len(),
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
                        let body = match &command.kind {
                            Some(pb::command::Kind::Repeat(repeat)) => &repeat.body,
                            Some(pb::command::Kind::Saturate(saturate)) => &saturate.body,
                            _ => {
                                self.usable = false;
                                return Err(TypedError::Decode(
                                    "failure path enters a non-loop".into(),
                                ));
                            }
                        };
                        let Some(next) = body.get(*child as usize) else {
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
        if let Err(error) = self.publication.observe(&packer, &response) {
            self.usable = false;
            return Err(error);
        }
        if response.error.as_ref().is_none_or(|e| e.location.is_some()) {
            self.declarations.extend(packer.declarations);
        }
        for (index, recipe, slot) in packer.initializations {
            if (index as usize) < completed {
                let name = recipe.capture()?.expect("planned capture").name;
                self.captures.insert(name, (recipe, slot));
            }
        }
        if let Some(error) = response.error.clone() {
            return Err(TypedError::Engine(Box::new(error)));
        }
        Ok(response)
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

    /// Execute an authored schedule and return its exact native report with
    /// validated rule attribution, profiling and publication observations.
    pub fn run(
        &mut self,
        schedule: impl Into<super::Schedule>,
    ) -> Result<super::RunReport, TypedError> {
        select_report(self.run_response(schedule)?, false)
    }

    fn run_response(
        &mut self,
        schedule: impl Into<super::Schedule>,
    ) -> Result<pb::RunProgramResponse, TypedError> {
        let mut schedule = schedule.into();
        if !self.usable {
            return Err(TypedError::Invalid(
                "session publication state is unknown".into(),
            ));
        }
        for ruleset in &schedule.rulesets {
            if let Some(error) = &ruleset.1 {
                return Err(TypedError::Invalid(error.clone()));
            }
        }
        let root = if schedule.rulesets.len() == 1 {
            schedule.rulesets[0].clone()
        } else {
            super::rule::ruleset(schedule.rulesets.clone())
        };
        let mut packer = self.publication.prepare_run(&root.0)?;
        packer.program.commands.clear();
        let indices: Vec<_> = schedule
            .rulesets
            .iter()
            .map(|ruleset| packer.intern(ruleset.0.clone(), 0))
            .collect();
        super::schedule::relocate(&mut schedule.commands, |index| {
            let index = indices[index as usize];
            match &packer.program.rulesets[index as usize].name {
                Some(name) => pb::ruleset_ref::Kind::Name(name.clone()),
                None => pb::ruleset_ref::Kind::Index(index),
            }
        });
        if schedule.commands.len() == 1 {
            packer.program.commands = schedule.commands;
        } else {
            packer.program.commands.push(pb::Command {
                kind: Some(pb::command::Kind::Repeat(pb::Repeat {
                    body: schedule.commands,
                    times: Some(1),
                    ..Default::default()
                })),
                ..Default::default()
            });
        }
        self.execute(packer, true)
    }

    /// Observe actual cumulative native statistics, with their attribution catalog.
    /// Returns native detail and its attribution, not a reconstruction from prior runs.
    pub fn stats(&mut self) -> Result<super::RunReport, TypedError> {
        select_report(self.stats_response()?, true)
    }

    fn stats_response(&mut self) -> Result<pb::RunProgramResponse, TypedError> {
        let mut packer = Packer::default();
        packer.program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Stats(pb::Unit {})),
            ..Default::default()
        });
        self.execute(packer, false)
    }

    /// Observe independent logical state through Freeze bytes without evaluating roots.
    /// This observation is included when execution recording is enabled.
    pub fn freeze(&mut self) -> Result<super::Snapshot, TypedError> {
        let mut packer = Packer::default();
        packer.program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Freeze(pb::Freeze {})),
            ..Default::default()
        });
        let response = self.execute(packer, false)?;
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
        super::Snapshot::from_export(snapshot, self.captures.values().cloned().collect())
    }

    /// Retrieve structured request/outcome history; errors when recording is off.
    /// Retrieval adds no entry and does not require healthy publication state.
    /// A poisoned native engine remains inspectable through this read-only audit.
    pub fn history(&self) -> Result<pb::GetHistoryResponse, TypedError> {
        let bytes = self
            .engine
            .lock()
            .unwrap_or_else(|poison| poison.into_inner())
            .get_history(
                &pb::GetHistoryRequest {
                    egraph_id: self.handle,
                }
                .encode_to_vec(),
            )
            .map_err(|error| TypedError::Invalid(error.to_string()))?;
        pb::GetHistoryResponse::decode(bytes.as_slice())
            .map_err(|error| TypedError::Decode(error.to_string()))
    }

    /// Count visible portable table rows without evaluating any expression.
    pub fn num_tuples(&mut self) -> Result<usize, TypedError> {
        let mut packer = Packer::default();
        packer.program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::PrintSize(pb::PrintSize::default())),
            ..Default::default()
        });
        let response = self.execute(packer, false)?;
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
            Err(TypedError::Engine(error)) if error.code == pb::ErrorCode::CheckFailed as i32 => {
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
        let response = self.execute(packer, false)?;
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
        )?)
    }
}

// A high-level observation selects its natural result and validates all
// required metrics here; consumers never interpret generic command outputs.
fn select_report(
    response: pb::RunProgramResponse,
    statistics: bool,
) -> Result<super::RunReport, TypedError> {
    let rules = response.rules;
    let profile = response.profile;
    let ruleset_publication = response.ruleset_publication;
    let mut outputs = response.outputs.into_iter();
    let output = outputs
        .next()
        .ok_or_else(|| TypedError::Decode("missing run report".into()))?;
    if outputs.next().is_some()
        || output
            .location
            .as_ref()
            .is_none_or(|location| location.path != [0] || !location.iterations.is_empty())
    {
        return Err(TypedError::Decode(
            "unexpected report observation location".into(),
        ));
    }
    let report = match output.kind {
        Some(pb::command_output::Kind::Statistics(report)) if statistics => report,
        Some(pb::command_output::Kind::Run(outcome)) if !statistics => {
            let report = output
                .run_report
                .ok_or_else(|| TypedError::Decode("run detail is missing".into()))?;
            if outcome.updated != report.updated || outcome.can_stop != report.can_stop {
                return Err(TypedError::Decode(
                    "run outcome disagrees with its report".into(),
                ));
            }
            report
        }
        Some(pb::command_output::Kind::Loop(outcome)) if !statistics => {
            let report = output
                .run_report
                .ok_or_else(|| TypedError::Decode("loop detail is missing".into()))?;
            if outcome.updated != report.updated || outcome.termination.is_none() {
                return Err(TypedError::Decode(
                    "loop outcome disagrees with its report".into(),
                ));
            }
            report
        }
        _ => return Err(TypedError::Decode("wrong report observation kind".into())),
    };
    if report.updated && report.can_stop {
        return Err(TypedError::Decode(
            "updated report cannot permit stopping".into(),
        ));
    }
    let duration = |value: Option<&pb::ReportDuration>| -> Result<(), TypedError> {
        if value.is_none_or(|duration| duration.nanos >= 1_000_000_000) {
            Err(TypedError::Decode(
                "invalid required report duration".into(),
            ))
        } else {
            Ok(())
        }
    };
    for value in &report.search_and_apply_time_per_rule {
        duration(value.value.as_ref())?;
    }
    for (rule, direction) in report
        .search_and_apply_time_per_rule
        .iter()
        .map(|entry| (entry.rule, entry.direction))
        .chain(
            report
                .num_matches_per_rule
                .iter()
                .map(|entry| (entry.rule, entry.direction)),
        )
        .chain(
            report
                .iterations
                .iter()
                .flat_map(|iteration| iteration.rule_set_report.iter())
                .flat_map(|report| &report.rule_reports)
                .map(|entry| (entry.rule, entry.direction)),
        )
    {
        if rule.is_some() != direction.is_some()
            || rule.is_some_and(|index| index as usize >= rules.len())
        {
            return Err(TypedError::Decode("invalid report rule attribution".into()));
        }
    }
    for value in report
        .search_and_apply_time_per_ruleset
        .iter()
        .chain(&report.merge_time_per_ruleset)
        .chain(&report.rebuild_time_per_ruleset)
    {
        duration(value.value.as_ref())?;
    }
    for iteration in &report.iterations {
        duration(iteration.rebuild_time.as_ref())?;
        let ruleset = iteration
            .rule_set_report
            .as_ref()
            .ok_or_else(|| TypedError::Decode("missing iteration ruleset report".into()))?;
        duration(ruleset.search_and_apply_time.as_ref())?;
        duration(ruleset.merge_time.as_ref())?;
        for entry in &ruleset.rule_reports {
            for rule in &entry.reports {
                duration(rule.search_and_apply_time.as_ref())?;
                if let Some(plan) = &rule.plan {
                    for stage in &plan.stages {
                        if stage.kind.is_none()
                            || stage
                                .next
                                .iter()
                                .any(|next| *next as usize >= plan.stages.len())
                        {
                            return Err(TypedError::Decode("invalid report plan stage".into()));
                        }
                    }
                }
            }
        }
    }
    Ok(super::RunReport {
        detail: report,
        rules,
        profile,
        ruleset_publication,
    })
}

// Adopt only the selected inert term closure. Other response nodes can be
// scalar costs or independent observations and are not this expression's roots.
fn adopt(
    response: &pb::RunProgramResponse,
    root: u32,
    mut declarations: Vec<Record>,
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
                    ..Default::default()
                })),
                ..Default::default()
            }),
            Some(pb::sort::Kind::Family(f))
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
                        .declaration(&f.name, DeclarationKind::HostSortFamily)?,
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
    let result = Expr(publish(program, slots, declarations, Arena::Node, 0)?);
    result.validate_inert()?;
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typed::Ruleset;

    #[test]
    fn structured_history_is_opt_in_and_tracks_typed_observations_and_clones() {
        assert!(EGraph::new().unwrap().history().is_err());
        let mut graph = EGraph::with_recording(true).unwrap();
        assert_eq!(graph.history().unwrap().entries.len(), 1);
        graph.stats().unwrap();
        let mut cloned = graph.try_clone().unwrap();
        assert_eq!(graph.history().unwrap().entries.len(), 3);
        assert_eq!(cloned.history().unwrap().entries.len(), 3);
        cloned.freeze().unwrap();
        assert_eq!(cloned.history().unwrap().entries.len(), 4);
        assert_eq!(graph.history().unwrap().entries.len(), 3);
        graph.push().unwrap();
        graph.stats().unwrap();
        graph.pop().unwrap();
        let history = graph.history().unwrap();
        assert!(history.entries.iter().any(|entry| matches!(
            entry.outcome,
            Some(pb::history_entry::Outcome::ReturnToResponse(_))
        )));
        assert_eq!(graph.history().unwrap(), history);
    }

    #[test]
    fn structured_history_remains_readable_after_engine_mutex_is_poisoned() {
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
        assert_eq!(graph.history().unwrap().entries.len(), 1);
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
        let response = pb::RunProgramResponse {
            nodes: packer.program.nodes,
            sorts: packer.program.sorts,
            ..Default::default()
        };
        let declarations = packer.declarations.into_values().collect::<Vec<_>>();
        assert!(adopt(&response, root, declarations.clone()).is_ok());
        for case in 0..7 {
            let mut invalid = response.clone();
            let float = invalid.sorts.len() as u32;
            invalid.sorts.push(pb::Sort {
                kind: Some(pb::sort::Kind::Family(pb::HostSort {
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
                adopt(&invalid, root, declarations.clone()).is_err(),
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
                    kind: Some(pb::command::Kind::PrintSize(pb::PrintSize {
                        tables: vec!["ActionAbsent".into()],
                    })),
                    ..Default::default()
                });
                let response = graph.execute(packer, false).unwrap();
                let Some(pb::command_output::Kind::Sizes(sizes)) = &response.outputs[0].kind else {
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
                graph.run_response(ruleset(rule((), actions))).unwrap();
            } else {
                graph.register(actions).unwrap();
            }
            let (request, response) = graph.last_wire.as_ref().unwrap();
            let mut request = pb::RunProgramRequest::decode(request.as_slice()).unwrap();
            let response = pb::RunProgramResponse::decode(response.as_slice()).unwrap();
            assert!(response.error.is_none());
            if in_rule {
                assert!(
                    response
                        .outputs
                        .iter()
                        .any(|out| matches!(&out.kind, Some(pb::command_output::Kind::Run(_))))
                );
            }
            let program = request.program.as_mut().unwrap();
            let actions: Vec<_> = if in_rule {
                let Some(pb::rule::Kind::Rule(body)) = &program.rules[0].kind else {
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
            let extracted = pb::RunProgramResponse::decode(bytes.as_slice()).unwrap();
            let Some(pb::command_output::Kind::Extraction(output)) = &extracted.outputs[0].kind
            else {
                panic!()
            };
            assert!(
                matches!(&extracted.nodes[output.roots[0].variants[0].term as usize].kind,
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
            let invalid = pb::RunProgramResponse::decode(bytes.as_slice()).unwrap();
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
                graph.accept_response(Packer::default(), &[0xff]),
                Err(TypedError::Decode(_))
            ));
            assert!(
                matches!(graph.register(union(&left, &right)), Err(TypedError::Invalid(message)) if message == "session publication state is unknown")
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
        let response = pb::RunProgramResponse::decode(output.as_slice()).unwrap();
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
        assert!(
            graph
                .run_response(ruleset(rule((), set(&forged, 7))))
                .is_err()
        );
        assert!(graph.publication.confirmed.is_empty());
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
            let Err(TypedError::Engine(error)) = result else {
                panic!("real missing-row evaluation failure")
            };
            assert_eq!(error.code, pb::ErrorCode::EvaluationFailed as i32);
            assert_eq!(error.location.unwrap().path, [u32::from(left_first)]);
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
            (vec![], vec![], pb::ErrorCode::EvaluationFailed),
            (vec![999], vec![], pb::ErrorCode::EvaluationFailed),
            (vec![0, 0], vec![], pb::ErrorCode::EvaluationFailed),
            (vec![1], vec![0], pb::ErrorCode::EvaluationFailed),
            (vec![1], vec![], pb::ErrorCode::InvalidProgram),
        ] {
            let mut graph = EGraph::default();
            graph.push().unwrap();
            let group = ruleset(());
            let mut packer = graph.publication.prepare_run(&group.0).unwrap();
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
                error: Some(pb::Error {
                    code: code.into(),
                    location: Some(pb::CommandLocation { path, iterations }),
                    ..Default::default()
                }),
                ruleset_publication: Some(pb::RulesetPublication {
                    names: packer
                        .program
                        .rulesets
                        .iter()
                        .filter_map(|r| r.name.clone())
                        .collect(),
                }),
                ..Default::default()
            };
            assert!(matches!(
                graph.accept_response(packer, &response.encode_to_vec()),
                Err(TypedError::Decode(_))
            ));
            assert!(!graph.usable);
            assert!(graph.captures.is_empty());
            assert!(graph.declarations.is_empty());
            assert!(graph.publication.confirmed.is_empty());
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
                    profile: true,
                    ..Default::default()
                }
                .encode_to_vec(),
            )
            .unwrap();
        assert!(
            pb::RunProgramResponse::decode(installed.as_slice())
                .unwrap()
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
        let Err(TypedError::Engine(error)) = graph.execute(packer, false) else {
            panic!("invalid packet")
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
            let identity = |record: &Record| record.key();
            (
                graph.publication.reserved.clone(),
                graph
                    .publication
                    .confirmed
                    .iter()
                    .map(|(key, (record, name))| (*key, (identity(record), name.clone())))
                    .collect::<HashMap<_, _>>(),
                graph.publication.anchors.clone(),
                graph
                    .declarations
                    .iter()
                    .map(|(name, record)| (name.clone(), identity(record)))
                    .collect::<HashMap<_, _>>(),
            )
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
        graph.run_response(&base).unwrap();
        let baseline = observations(&graph);
        let original = graph.handle;
        let engine = graph.engine.clone();
        assert!(graph.pop().is_err());
        assert_eq!(graph.handle, original);
        assert_eq!(observations(&graph), baseline);
        graph.push().unwrap();
        let middle = graph.handle;
        assert_eq!(graph.scopes[0].handle, original);
        graph.run_response(&child).unwrap();
        assert!(graph.declarations.len() > baseline.3.len());
        let child_state = observations(&graph);
        graph.push().unwrap();
        let active = graph.handle;
        graph.run_response(&inner).unwrap();
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
                "Return already consumed the child"
            );
        }
        graph.run_response(&inner).unwrap();
        assert!(graph.publication.confirmed.len() > baseline.1.len());
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
        independent.run_response(&inner).unwrap();
    }

    #[test]
    fn typed_scope_stale_return_preserves_frontend_ownership() {
        use super::super::ruleset;
        let group = ruleset(());
        let mut graph = EGraph::default();
        graph.push().unwrap();
        graph.run_response(&group).unwrap();
        let active = graph.handle;
        let saved = graph.scopes[0].handle;
        let reserved = graph.publication.reserved.clone();
        let anchors = graph.publication.anchors.clone();
        let confirmed = graph
            .publication
            .confirmed
            .iter()
            .map(|(key, (_, name))| (*key, name.clone()))
            .collect::<HashMap<_, _>>();
        // Test-only access violates the private saved-frame invariant, exercising
        // the adapter's rejection without exposing a public handle escape hatch.
        let bytes = graph
            .engine
            .lock()
            .unwrap()
            .run(
                &pb::RunProgramRequest {
                    egraph_id: saved,
                    program: Some(pb::Program {
                        ..Default::default()
                    }),
                    profile: true,
                    include_run_reports: false,
                }
                .encode_to_vec(),
            )
            .unwrap();
        assert!(
            pb::RunProgramResponse::decode(bytes.as_slice())
                .unwrap()
                .error
                .is_none()
        );
        assert!(matches!(graph.pop(), Err(TypedError::Invalid(message))
            if message == "unrelated or stale scope return"));
        assert_eq!(graph.handle, active);
        assert_eq!(graph.scopes.len(), 1);
        assert_eq!(graph.scopes[0].handle, saved);
        assert_eq!(graph.publication.reserved, reserved);
        assert_eq!(graph.publication.anchors, anchors);
        assert_eq!(
            graph
                .publication
                .confirmed
                .iter()
                .map(|(key, (_, name))| (*key, name.clone()))
                .collect::<HashMap<_, _>>(),
            confirmed
        );
        assert!(graph.usable);
        graph.run_response(&group).unwrap();
    }

    #[test]
    fn typed_scope_recovers_uncertain_receipts_but_not_a_poisoned_mutex() {
        use super::super::ruleset;
        let group = ruleset(());
        let mut graph = EGraph::default();
        graph.run_response(&group).unwrap();
        graph.push().unwrap();
        let pending = graph.publication.prepare_run(&ruleset(()).0).unwrap();
        assert!(matches!(
            graph.accept_response(pending, &[0xff]),
            Err(TypedError::Decode(_))
        ));
        for error in [
            graph.push().unwrap_err(),
            graph.run_response(&group).unwrap_err(),
            graph.try_clone().err().expect("unusable cannot clone"),
        ] {
            assert!(matches!(error, TypedError::Invalid(message)
                if message == "session publication state is unknown"));
        }
        assert_eq!(graph.scopes.len(), 1);
        graph.pop().unwrap();
        assert!(graph.usable);
        graph.run_response(&group).unwrap();
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
        drop(graph); // Must not panic or implicitly return scopes.
    }

    #[test]
    fn typed_scope_failed_prefix_restores_logic_but_retains_native_statistics() {
        use super::super::{builtins::I64, rule, rule::Fact, ruleset};
        for preinstalled in [true, false] {
            let value = Expr::call(
                &Callable::constructor(
                    "Scope.Done",
                    vec![],
                    SortRef::equality("Scope"),
                    None,
                    false,
                ),
                vec![],
            );
            let group = ruleset(rule(Fact(value.clone()), I64::from(7)));
            let mut graph = EGraph::default();
            if preinstalled {
                graph.run_response(&group).unwrap();
            }
            graph.push().unwrap();
            let mut packer = graph.publication.prepare_run(&group.0).unwrap();
            let root = packer.intern(value.0.clone(), 0);
            packer.program.commands.insert(
                0,
                pb::Command {
                    kind: Some(pb::command::Kind::Action(pb::Action {
                        kind: Some(pb::action::Kind::Term(root)),
                        ..Default::default()
                    })),
                    ..Default::default()
                },
            );
            packer.program.commands.push(pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Panic("scoped failure after Run".into())),
                    ..Default::default()
                })),
                ..Default::default()
            });
            let Err(TypedError::Engine(error)) = graph.execute(packer, true) else {
                panic!("expected scoped execution failure after actual work")
            };
            assert_eq!(error.code, pb::ErrorCode::Panic as i32);
            assert_eq!(error.location.as_ref().unwrap().path, [2]);
            assert!(graph.usable, "ordinary error retains valid receipts");
            assert!(graph.check(Fact(value.clone())).unwrap());
            let before = graph.stats_response().unwrap();
            let Some(pb::command_output::Kind::Statistics(before_report)) = &before.outputs[0].kind
            else {
                panic!("missing scoped statistics")
            };
            assert!(!before_report.iterations.is_empty());
            assert_eq!(
                before_report
                    .num_matches_per_rule
                    .iter()
                    .map(|r| r.value)
                    .sum::<u64>(),
                1
            );
            graph.pop().unwrap();
            assert!(!graph.check(Fact(value)).unwrap());
            let after = graph.stats_response().unwrap();
            let Some(pb::command_output::Kind::Statistics(after_report)) = &after.outputs[0].kind
            else {
                panic!("missing restored statistics")
            };
            if preinstalled {
                assert_eq!(
                    after.outputs, before.outputs,
                    "every native field survives pop"
                );
                assert_eq!(after.rules, before.rules);
            } else {
                assert_eq!(
                    after_report.iterations.len(),
                    before_report.iterations.len()
                );
                assert_eq!(
                    after_report
                        .num_matches_per_rule
                        .iter()
                        .map(|r| (&r.native_name, r.value))
                        .collect::<Vec<_>>(),
                    before_report
                        .num_matches_per_rule
                        .iter()
                        .map(|r| (&r.native_name, r.value))
                        .collect::<Vec<_>>()
                );
                assert!(
                    after_report
                        .num_matches_per_rule
                        .iter()
                        .all(|r| r.rule.is_none() && r.direction.is_none())
                );
                assert!(after.rules.is_empty(), "no child-only attribution journal");
            }
            // Exact same-handle native getter, including all fields/attribution;
            // the two requests' own profiling times are separate measurements.
            let request = &graph.last_wire.as_ref().unwrap().0;
            let direct = graph.engine.lock().unwrap().run(request).unwrap();
            let direct = pb::RunProgramResponse::decode(direct.as_slice()).unwrap();
            assert!(direct.error.is_none());
            assert_eq!(after.outputs, direct.outputs);
            assert_eq!(after.rules, direct.rules);
            graph.run_response(&group).unwrap();
        }
    }

    #[test]
    fn typed_report_run_is_the_actual_decoded_response() {
        use super::super::{builtins::I64, rule, ruleset};
        let group = ruleset(rule((), I64::from(7)));
        let mut graph = EGraph::default();
        let mut detail_off = graph.try_clone().unwrap();
        let response = graph.run_response(&group).unwrap();
        let (input, output) = graph.last_wire.as_ref().unwrap();
        assert_eq!(
            pb::RunProgramResponse::decode(output.as_slice()).unwrap(),
            response
        );
        let request = pb::RunProgramRequest::decode(input.as_slice()).unwrap();
        assert!(request.profile);
        assert!(response.profile.as_ref().unwrap().complete);
        let [output] = response.outputs.as_slice() else {
            panic!("one requested Run output")
        };
        let Some(pb::command_output::Kind::Run(outcome)) = &output.kind else {
            panic!("missing Run outcome")
        };
        let report = output
            .run_report
            .as_ref()
            .expect("typed Run requests actual native detail");
        assert!(request.include_run_reports);
        assert_eq!(
            (report.updated, report.can_stop),
            (outcome.updated, outcome.can_stop)
        );
        assert!(!report.iterations.is_empty());
        assert_eq!(
            report
                .num_matches_per_rule
                .iter()
                .map(|row| row.value)
                .sum::<u64>(),
            1
        );
        for row in &report.num_matches_per_rule {
            let attribution =
                &response.rules[row.rule.expect("authored rule attribution") as usize];
            assert_eq!(attribution.rule, 0);
            assert!(attribution.children.is_empty());
            let Some(pb::ruleset_ref::Kind::Name(name)) = &attribution.root.as_ref().unwrap().kind
            else {
                panic!("named publication root")
            };
            assert_eq!(
                name,
                &graph.publication.confirmed.values().next().unwrap().1
            );
            assert_eq!(row.direction, Some(pb::NativeRuleDirection::Single as i32));
        }
        let packer = detail_off.publication.prepare_run(&group.0).unwrap();
        let off = detail_off.execute(packer, false).unwrap();
        assert_eq!(off.outputs[0].kind, output.kind);
        assert!(off.outputs[0].run_report.is_none());
        assert!(off.profile.as_ref().unwrap().complete);
        assert_eq!(
            off.profile
                .as_ref()
                .unwrap()
                .runs
                .iter()
                .flat_map(|run| &run.rules)
                .map(|rule| rule.matches)
                .collect::<Vec<_>>(),
            response
                .profile
                .as_ref()
                .unwrap()
                .runs
                .iter()
                .flat_map(|run| &run.rules)
                .map(|rule| rule.matches)
                .collect::<Vec<_>>()
        );
        let stats = detail_off.stats_response().unwrap();
        assert!(matches!(&stats.outputs[0].kind,
            Some(pb::command_output::Kind::Statistics(report)) if !report.iterations.is_empty()));
        let request =
            pb::RunProgramRequest::decode(detail_off.last_wire.as_ref().unwrap().0.as_slice())
                .unwrap();
        assert!(!request.include_run_reports);
        assert!(matches!(
            request.program.unwrap().commands[0].kind,
            Some(pb::command::Kind::Stats(_))
        ));
    }

    #[test]
    fn typed_report_stats_keeps_actual_failed_prefix_and_same_handle_fields() {
        use super::super::{builtins::I64, rule, ruleset};
        let group = ruleset(rule((), I64::from(7)));
        let value = Expr::call(
            &Callable::constructor(
                "Report.Done",
                vec![],
                SortRef::equality("Report"),
                None,
                false,
            ),
            vec![],
        );
        let mut graph = EGraph::default();
        let mut packer = graph.publication.prepare_run(&group.0).unwrap();
        let root = packer.intern(value.0.clone(), 0);
        packer.program.commands.insert(
            0,
            pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Term(root)),
                    ..Default::default()
                })),
                ..Default::default()
            },
        );
        packer.program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Panic("after actual Run".into())),
                ..Default::default()
            })),
            ..Default::default()
        });
        let Err(TypedError::Engine(error)) = graph.execute(packer, true) else {
            panic!("expected execution failure after prefix")
        };
        assert_eq!(error.code, pb::ErrorCode::Panic as i32);
        assert_eq!(error.location.as_ref().unwrap().path, [2]);
        let prefix =
            pb::RunProgramResponse::decode(graph.last_wire.as_ref().unwrap().1.as_slice()).unwrap();
        assert!(!prefix.profile.as_ref().unwrap().complete);
        assert!(
            !prefix.outputs[0]
                .run_report
                .as_ref()
                .unwrap()
                .iterations
                .is_empty()
        );
        assert!(graph.usable);
        assert_eq!(graph.publication.confirmed.len(), 1);
        assert!(graph.check(super::super::rule::Fact(value)).unwrap());
        let observed = graph.stats_response().unwrap();
        let (request, output) = graph.last_wire.as_ref().unwrap();
        assert_eq!(
            pb::RunProgramResponse::decode(output.as_slice()).unwrap(),
            observed
        );
        let request = pb::RunProgramRequest::decode(request.as_slice()).unwrap();
        assert!(request.profile);
        assert!(!request.include_run_reports);
        assert!(matches!(
            request.program.as_ref().unwrap().commands[0].kind,
            Some(pb::command::Kind::Stats(_))
        ));
        let Some(pb::command_output::Kind::Statistics(report)) = &observed.outputs[0].kind else {
            panic!("missing actual statistics")
        };
        assert!(!report.iterations.is_empty());
        assert_eq!(
            report
                .num_matches_per_rule
                .iter()
                .map(|row| row.value)
                .sum::<u64>(),
            1
        );
        // Repeat the exact request on the same handle: Stats performs no new
        // rule work. Request-profile timings are separate observations, whereas
        // every retained native report field and attribution must agree.
        let direct = graph
            .engine
            .lock()
            .unwrap()
            .run(&request.encode_to_vec())
            .unwrap();
        let direct = pb::RunProgramResponse::decode(direct.as_slice()).unwrap();
        assert_eq!(observed.outputs, direct.outputs);
        assert_eq!(observed.rules, direct.rules);
        assert!(direct.error.is_none());
        let recovered = graph.run_response(&group).unwrap();
        assert!(recovered.profile.unwrap().complete);

        // Decoder-only negative fixture: an unclassified native diagnostic key
        // is not made into an authored identity. This is not a producer claim.
        let mut unknown = observed;
        let Some(pb::command_output::Kind::Statistics(report)) = &mut unknown.outputs[0].kind
        else {
            unreachable!()
        };
        let row = &mut report.num_matches_per_rule[0];
        row.native_name = "unclassified-native-row".into();
        row.rule = None;
        row.direction = None;
        let accepted = graph
            .accept_response(Packer::default(), &unknown.encode_to_vec())
            .unwrap();
        assert_eq!(accepted, unknown);
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
            matches!(graph.stats_response(), Err(TypedError::Invalid(message)) if message == "byte engine mutex poisoned")
        );
        assert!(graph.last_wire.is_none());
    }

    #[test]
    fn publication_receipts_are_request_scoped_atomic_and_required() {
        use super::super::ruleset;
        let mut state = Publication::default();
        let old = state.prepare_run(&ruleset(()).0).unwrap();
        let old_name = old.program.rulesets[0].name.clone().unwrap();
        state
            .observe(
                &old,
                &pb::RunProgramResponse {
                    ruleset_publication: Some(pb::RulesetPublication {
                        names: vec![old_name],
                    }),
                    ..Default::default()
                },
            )
            .unwrap();
        let next = state.prepare_run(&ruleset(()).0).unwrap();
        let name = next.program.rulesets[0].name.clone().unwrap();
        for (receipt, error) in [
            (None, None),
            (Some(vec![name.clone(), name.clone()]), None),
            (Some(vec!["unsubmitted".into()]), None),
            (Some(vec![]), None),
            (
                Some(vec![]),
                Some(pb::Error {
                    code: pb::ErrorCode::Panic as i32,
                    message: "command failed".into(),
                    location: Some(pb::CommandLocation {
                        path: vec![0],
                        iterations: vec![],
                    }),
                    ..Default::default()
                }),
            ),
            (
                Some(vec![name.clone()]),
                Some(pb::Error {
                    code: pb::ErrorCode::InvalidProgram as i32,
                    message: "preparation failed".into(),
                    ..Default::default()
                }),
            ),
        ] {
            let response = pb::RunProgramResponse {
                ruleset_publication: receipt.map(|names| pb::RulesetPublication { names }),
                error,
                ..Default::default()
            };
            assert!(matches!(
                state.observe(&next, &response),
                Err(TypedError::Decode(_))
            ));
            assert_eq!(state.confirmed.len(), 1, "reject before promoting anything");
            assert_eq!(state.anchors.len(), 1, "old confirmations survive");
        }
        state
            .observe(
                &next,
                &pb::RunProgramResponse {
                    ruleset_publication: Some(pb::RulesetPublication { names: vec![name] }),
                    ..Default::default()
                },
            )
            .unwrap();
        assert_eq!(state.confirmed.len(), 2);
    }

    #[test]
    fn empty_group_first_naming_requires_its_own_confirmation() {
        use super::super::ruleset;
        let empty = ruleset(());
        let parent = ruleset(&empty);
        let mut state = Publication::default();
        let first = state.prepare_run(&parent.0).unwrap();
        let parent_name = first.program.rulesets[0].name.clone().unwrap();
        state
            .observe(
                &first,
                &pb::RunProgramResponse {
                    ruleset_publication: Some(pb::RulesetPublication {
                        names: vec![parent_name.clone()],
                    }),
                    ..Default::default()
                },
            )
            .unwrap();
        let naming = state.prepare_run(&empty.0).unwrap();
        let empty_name = naming.program.rulesets[0].name.clone().unwrap();
        assert_eq!(
            naming.program.rulesets.len(),
            2,
            "empty occurrence needs its parent anchor"
        );
        state
            .observe(
                &naming,
                &pb::RunProgramResponse {
                    ruleset_publication: Some(pb::RulesetPublication {
                        names: vec![parent_name.clone()],
                    }),
                    error: Some(pb::Error {
                        code: pb::ErrorCode::EvaluationFailed as i32,
                        message: "first naming did not complete".into(),
                        ..Default::default()
                    }),
                    ..Default::default()
                },
            )
            .unwrap();
        assert_eq!(state.confirmed.len(), 1);
        let next = state.prepare_run(&ruleset(&empty).0).unwrap();
        assert_eq!(next.program.rulesets.len(), 3);
        let empty_index = next
            .rulesets
            .iter()
            .position(|r| r.owner.as_ref().unwrap().id == empty.0.owner.as_ref().unwrap().id)
            .unwrap();
        assert!(
            next.program.rulesets[empty_index].name.is_none(),
            "a reservation is not publication"
        );
        for group in &next.program.rulesets {
            if let Some(pb::ruleset::Kind::Combined(children)) = &group.kind {
                assert_eq!(
                    children.rulesets[0].kind,
                    Some(pb::ruleset_ref::Kind::Index(empty_index as u32))
                );
            }
        }
        let retry = state.prepare_run(&empty.0).unwrap();
        assert_eq!(
            retry.program.rulesets[0].name.as_deref(),
            Some(empty_name.as_str())
        );
        state
            .observe(
                &retry,
                &pb::RunProgramResponse {
                    ruleset_publication: Some(pb::RulesetPublication {
                        names: vec![empty_name, parent_name],
                    }),
                    ..Default::default()
                },
            )
            .unwrap();
        assert_eq!(
            state.prepare_run(&empty.0).unwrap().program.rulesets.len(),
            1,
            "confirmed first naming is now a direct anchor"
        );
    }

    #[test]
    fn empty_child_first_naming_executes_and_becomes_a_direct_anchor() {
        use super::super::ruleset;
        let empty = ruleset(());
        let parent = ruleset(&empty);
        let empty_key = (
            empty.0.owner.as_ref().unwrap().id,
            Arena::Ruleset,
            empty.0.index,
        );
        let parent_key = (
            parent.0.owner.as_ref().unwrap().id,
            Arena::Ruleset,
            parent.0.index,
        );
        let mut graph = EGraph::default();
        let first = graph.run_response(&parent).unwrap();
        let parent_name = graph.publication.confirmed[&parent_key].1.clone();
        assert_eq!(
            first.ruleset_publication.unwrap().names,
            std::slice::from_ref(&parent_name)
        );
        assert_eq!(graph.publication.anchors[&empty_key], parent_key);
        let first_request =
            pb::RunProgramRequest::decode(graph.last_wire.as_ref().unwrap().0.as_slice()).unwrap();
        let first_program = first_request.program.unwrap();
        assert_eq!(first_program.rulesets.len(), 2);
        assert!(first_program.rulesets[1].name.is_none());

        let naming = graph.run_response(&empty).unwrap();
        let empty_name = graph.publication.confirmed[&empty_key].1.clone();
        let request =
            pb::RunProgramRequest::decode(graph.last_wire.as_ref().unwrap().0.as_slice()).unwrap();
        let program = request.program.unwrap();
        assert_eq!(program.rulesets.len(), 2);
        assert_eq!(
            program.rulesets[0].name.as_deref(),
            Some(empty_name.as_str())
        );
        assert!(
            matches!(&program.rulesets[0].kind, Some(pb::ruleset::Kind::Rules(r)) if r.rules.is_empty())
        );
        assert_eq!(
            program.rulesets[1].name.as_deref(),
            Some(parent_name.as_str())
        );
        assert!(
            matches!(&program.rulesets[1].kind, Some(pb::ruleset::Kind::Combined(c))
            if c.rulesets.len() == 1 && c.rulesets[0].kind == Some(pb::ruleset_ref::Kind::Index(0)))
        );
        assert_eq!(
            naming
                .ruleset_publication
                .unwrap()
                .names
                .into_iter()
                .collect::<HashSet<_>>(),
            HashSet::from([parent_name.clone(), empty_name.clone()])
        );
        assert_eq!(graph.publication.anchors[&empty_key], empty_key);
        assert_eq!(graph.publication.anchors[&parent_key], parent_key);
        assert!(Arc::ptr_eq(
            graph.publication.confirmed[&parent_key]
                .0
                .owner
                .as_ref()
                .unwrap(),
            parent.0.owner.as_ref().unwrap()
        ));

        let fresh_parent = ruleset(&empty);
        let response = graph.run_response(&fresh_parent).unwrap();
        let request =
            pb::RunProgramRequest::decode(graph.last_wire.as_ref().unwrap().0.as_slice()).unwrap();
        let program = request.program.unwrap();
        assert_eq!(
            program.rulesets.len(),
            2,
            "the old parent is no longer needed"
        );
        assert!(
            program
                .rulesets
                .iter()
                .all(|r| r.name.as_deref() != Some(parent_name.as_str()))
        );
        assert_eq!(
            program.rulesets[1].name.as_deref(),
            Some(empty_name.as_str())
        );
        assert!(
            matches!(&program.rulesets[0].kind, Some(pb::ruleset::Kind::Combined(c))
            if c.rulesets.len() == 1 && c.rulesets[0].kind == Some(pb::ruleset_ref::Kind::Index(1)))
        );
        assert_eq!(
            response
                .ruleset_publication
                .unwrap()
                .names
                .into_iter()
                .collect::<HashSet<_>>(),
            HashSet::from([program.rulesets[0].name.clone().unwrap(), empty_name])
        );
        assert_eq!(graph.publication.anchors[&empty_key], empty_key);
        assert_eq!(graph.publication.confirmed[&parent_key].1, parent_name);
    }

    #[test]
    fn anchor_only_packing_omits_unconfirmed_authored_descendant_names() {
        use super::super::{rule, ruleset};
        let shared = rule((), ());
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Rule as usize] = vec![Slot::External(shared.0.clone())];
        let named = Ruleset(
            publish(
                pb::Program {
                    rulesets: vec![pb::Ruleset {
                        name: Some("unfinished-child".into()),
                        kind: Some(pb::ruleset::Kind::Rules(pb::RuleList { rules: vec![0] })),
                        ..Default::default()
                    }],
                    ..Default::default()
                },
                slots,
                vec![],
                Arena::Ruleset,
                0,
            )
            .unwrap(),
            None,
        );
        let parent = ruleset(&named);
        let mut state = Publication::default();
        let first = state.prepare_run(&parent.0).unwrap();
        let parent_name = first.program.rulesets[0].name.clone().unwrap();
        state
            .observe(
                &first,
                &pb::RunProgramResponse {
                    ruleset_publication: Some(pb::RulesetPublication {
                        names: vec![parent_name.clone()],
                    }),
                    error: Some(pb::Error {
                        code: pb::ErrorCode::EvaluationFailed as i32,
                        message: "partial publication".into(),
                        ..Default::default()
                    }),
                    ..Default::default()
                },
            )
            .unwrap();
        let next = state.prepare_run(&ruleset(&shared).0).unwrap();
        assert_eq!(
            next.program.rules.len(),
            1,
            "one shared canonical occurrence"
        );
        assert_eq!(next.program.rulesets.len(), 3);
        assert!(
            next.program
                .rulesets
                .iter()
                .any(|r| r.name.as_deref() == Some(parent_name.as_str()))
        );
        assert!(
            !next
                .program
                .rulesets
                .iter()
                .any(|r| r.name.as_deref() == Some("unfinished-child"))
        );
        assert_eq!(next.program.commands.len(), 1, "never replay old commands");
        let retry = state.prepare_run(&named.0).unwrap();
        assert_eq!(
            retry.program.rulesets[0].name.as_deref(),
            Some("unfinished-child"),
            "explicitly requesting the child retries its first naming"
        );
    }

    #[test]
    fn rejected_candidates_never_anchor_later_shared_rules() {
        use super::super::{
            builtins::{F64, I64},
            rule, ruleset, var,
        };
        let shared = rule((), ());
        let bad = rule((), var::<I64>("unbound"));
        let rejected = ruleset((&shared, bad));
        let valid = ruleset(&shared);
        let mut state = Publication::default();
        let first = state.prepare_run(&rejected.0).unwrap();
        for code in [
            pb::ErrorCode::InvalidProgram,
            pb::ErrorCode::UnknownName,
            pb::ErrorCode::EvaluationFailed,
        ] {
            state
                .observe(
                    &first,
                    &pb::RunProgramResponse {
                        ruleset_publication: Some(pb::RulesetPublication { names: vec![] }),
                        error: Some(pb::Error {
                            code: code as i32,
                            message: "rejected".into(),
                            ..Default::default()
                        }),
                        ..Default::default()
                    },
                )
                .unwrap();
            let next = state.prepare_run(&valid.0).unwrap();
            assert_eq!(next.program.rulesets.len(), 1);
            assert_eq!(next.program.rules.len(), 1);
            assert!(
                next.program.nodes.is_empty(),
                "unrelated rejected closure omitted"
            );
            assert!(state.confirmed.is_empty());
        }
        let retry = state.prepare_run(&rejected.0).unwrap();
        assert_eq!(
            first.program.rulesets[0].name,
            retry.program.rulesets[0].name
        );
        let locally_rejected = ruleset((
            &shared,
            rule((var::<I64>("conflict"), var::<F64>("conflict")), ()),
        ));
        assert!(matches!(
            state.prepare_run(&locally_rejected.0),
            Err(TypedError::Invalid(_))
        ));
        assert_eq!(state.prepare_run(&valid.0).unwrap().program.rules.len(), 1);
        assert!(
            state.confirmed.is_empty(),
            "local preparation never adds anchors either"
        );
    }

    #[test]
    fn completed_definitions_are_confirmed_before_command_error_and_retry() {
        use super::super::{rule::Rule, ruleset};
        let constructor = Callable::constructor(
            "Published.Value",
            vec![],
            SortRef::equality("Published"),
            None,
            false,
        );
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Node as usize] = vec![Slot::External(Expr::call(&constructor, vec![]).0)];
        let group = ruleset(Rule(
            publish(
                pb::Program {
                    rules: vec![pb::Rule {
                        kind: Some(pb::rule::Kind::Rule(pb::RuleBody {
                            query: vec![],
                            head: vec![pb::Action {
                                kind: Some(pb::action::Kind::Term(0)),
                                ..Default::default()
                            }],
                        })),
                        eval_mode: pb::RuleEvalMode::Seminaive as i32,
                        ..Default::default()
                    }],
                    ..Default::default()
                },
                slots,
                vec![],
                Arena::Rule,
                0,
            )
            .unwrap(),
            None,
        ));
        let mut graph = EGraph::default();
        let mut request = graph.publication.prepare_run(&group.0).unwrap();
        request.program.commands.insert(
            0,
            pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Panic("after definitions".into())),
                    ..Default::default()
                })),
                ..Default::default()
            },
        );
        assert!(
            matches!(graph.execute(request, false), Err(TypedError::Engine(error))
            if error.code == pb::ErrorCode::Panic as i32)
        );
        assert_eq!(graph.publication.confirmed.len(), 1);
        assert_eq!(
            graph.declarations.len(),
            1,
            "completed constructor metadata survives too"
        );
        assert!(
            graph.usable,
            "ordinary engine errors do not poison the handle"
        );
        for expected in [1, 0] {
            let response = graph.run_response(&group).unwrap();
            let matches: u64 = response
                .profile
                .unwrap()
                .runs
                .iter()
                .flat_map(|run| &run.rules)
                .map(|rule| rule.matches.unwrap())
                .sum();
            assert_eq!(
                matches, expected,
                "command error must not reset or consume rule cursors"
            );
        }
    }

    #[test]
    fn fail_checks_keep_actual_bytes_receipts_and_recovery() {
        use super::super::ruleset;

        let constructor = Callable::constructor(
            "FailPublished.Value",
            vec![],
            SortRef::equality("FailPublished"),
            None,
            false,
        );
        let value = Expr::call(&constructor, vec![]);
        let group = ruleset(());
        for depth in [1, 2] {
            let mut graph = EGraph::default();
            let mut request = graph.publication.prepare_run(&group.0).unwrap();
            let name = request.program.rulesets[0].name.clone().unwrap();
            let root = request.intern(value.0.clone(), 0);
            let mut command = pb::Command {
                kind: Some(pb::command::Kind::Check(pb::Check { facts: vec![root] })),
                ..Default::default()
            };
            for _ in 0..depth {
                command = pb::Command {
                    kind: Some(pb::command::Kind::Fail(Box::new(command))),
                    ..Default::default()
                };
            }
            request.program.commands.insert(0, command);
            let result = graph.execute(request, false);
            let (input, output) = graph.last_wire.as_ref().unwrap();
            let request = pb::RunProgramRequest::decode(input.as_slice()).unwrap();
            let response = pb::RunProgramResponse::decode(output.as_slice()).unwrap();
            let program = request.program.unwrap();
            let mut command = &program.commands[0];
            for _ in 0..depth {
                let Some(pb::command::Kind::Fail(child)) = &command.kind else {
                    panic!("encoded request lost a Fail wrapper")
                };
                command = child;
            }
            assert_eq!(
                command.kind,
                Some(pb::command::Kind::Check(pb::Check { facts: vec![root] }))
            );
            assert!(matches!(
                &program.nodes[root as usize].kind,
                Some(pb::node::Kind::Call(call)) if call.func == "FailPublished.Value"
            ));
            if depth == 1 {
                assert_eq!(result.unwrap(), response);
                assert!(response.error.is_none());
            } else {
                let Err(TypedError::Engine(error)) = result else {
                    panic!("outer Fail must reject the successful inner Fail")
                };
                assert_eq!(response.error.as_ref(), Some(error.as_ref()));
                assert_eq!(error.code, pb::ErrorCode::EvaluationFailed as i32);
                assert_eq!(
                    error.location,
                    Some(pb::CommandLocation {
                        path: vec![0],
                        iterations: vec![],
                    })
                );
            }
            assert_eq!(
                response.ruleset_publication.unwrap().names.as_slice(),
                std::slice::from_ref(&name)
            );
            assert_eq!(graph.publication.confirmed.len(), 1);
            assert_eq!(graph.publication.confirmed.values().next().unwrap().1, name);
            assert!(graph.declarations.contains_key("FailPublished.Value"));
            assert!(graph.usable);

            let mut recovery = Packer::default();
            let root = recovery.intern(value.0.clone(), 0);
            recovery.program.commands = vec![
                pb::Command {
                    kind: Some(pb::command::Kind::Action(pb::Action {
                        kind: Some(pb::action::Kind::Term(root)),
                        ..Default::default()
                    })),
                    ..Default::default()
                },
                pb::Command {
                    kind: Some(pb::command::Kind::Check(pb::Check { facts: vec![root] })),
                    ..Default::default()
                },
            ];
            assert!(graph.execute(recovery, false).unwrap().error.is_none());
            assert!(graph.run_response(&group).unwrap().error.is_none());
        }
    }

    #[test]
    fn uncertain_response_blocks_later_engine_calls_and_clone() {
        use super::super::{builtins::I64, ruleset};
        for malformed in 0..4 {
            let group = ruleset(());
            let mut graph = EGraph::default();
            graph.run_response(&group).unwrap();
            let pending = graph.publication.prepare_run(&ruleset(()).0).unwrap();
            let name = pending.program.rulesets[0].name.clone().unwrap();
            // Inject only at the response boundary; this is not a claim that
            // the native producer emits malformed replies.
            let bytes = match malformed {
                0 => vec![0xff],
                1 => pb::RunProgramResponse::default().encode_to_vec(),
                2 | 3 => pb::RunProgramResponse {
                    ruleset_publication: Some(pb::RulesetPublication {
                        names: if malformed == 2 {
                            vec![name.clone(), name]
                        } else {
                            vec![]
                        },
                    }),
                    ..Default::default()
                }
                .encode_to_vec(),
                _ => unreachable!(),
            };
            assert!(matches!(
                graph.accept_response(pending, &bytes),
                Err(TypedError::Decode(_))
            ));
            assert_eq!(graph.publication.confirmed.len(), 1);
            // Invalidate the native handle: reaching the engine would return
            // an unknown-handle transport error instead of our state error.
            graph
                .engine
                .lock()
                .unwrap()
                .destroy(
                    &pb::DestroyEGraphRequest {
                        egraph_id: graph.handle,
                    }
                    .encode_to_vec(),
                )
                .unwrap();
            for error in [
                graph.register(()).unwrap_err(),
                graph.run_response(&group).unwrap_err(),
                graph.stats_response().unwrap_err(),
                graph.check(()).unwrap_err(),
                graph.extract(I64::from(0)).unwrap_err(),
                graph
                    .try_clone()
                    .err()
                    .expect("uncertain handles cannot clone"),
            ] {
                assert!(matches!(error, TypedError::Invalid(message)
                    if message == "session publication state is unknown"));
            }
        }
    }

    #[test]
    fn clone_owns_a_native_handle_and_independent_publication_maps() {
        use super::super::ruleset;
        let group = ruleset(());
        let mut graph = EGraph::default();
        graph.run_response(&group).unwrap();
        let engine = graph.engine.clone();
        let original_handle = graph.handle;
        let mut clone = graph.try_clone().unwrap();
        assert_ne!(clone.handle, original_handle);
        assert!(Arc::ptr_eq(&graph.engine, &clone.engine));
        assert_eq!(clone.publication.confirmed.len(), 1);
        let new_group = ruleset((&group, ruleset(())));
        clone.run_response(&new_group).unwrap();
        assert_eq!(graph.publication.confirmed.len(), 1);
        assert!(clone.publication.confirmed.len() > 1);
        assert_eq!(graph.publication.reserved.len(), 1);
        assert!(clone.publication.reserved.len() > 1);
        drop(graph);
        assert!(
            engine
                .lock()
                .unwrap()
                .clone_egraph(
                    &pb::CloneEGraphRequest {
                        egraph_id: original_handle
                    }
                    .encode_to_vec()
                )
                .is_err(),
            "dropping one wrapper destroys only its handle"
        );
        clone.run_response(&group).unwrap();
        let clone_handle = clone.handle;
        drop(clone);
        assert!(
            engine
                .lock()
                .unwrap()
                .clone_egraph(
                    &pb::CloneEGraphRequest {
                        egraph_id: clone_handle
                    }
                    .encode_to_vec()
                )
                .is_err()
        );
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
            let response = pb::RunProgramResponse {
                sorts: vec![pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
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
            let adopted = adopt(&response, 0, vec![]).unwrap();
            let mut packed = Packer::default();
            let root = packed.intern(adopted.0, 0);
            packed.finish().unwrap();
            assert_eq!(
                packed.program.nodes[root as usize].kind,
                response.nodes[0].kind
            );
            let mut wrong = response.clone();
            let Some(pb::sort::Kind::Family(sort)) = &mut wrong.sorts[0].kind else {
                unreachable!()
            };
            sort.name = "i64".into();
            assert!(adopt(&wrong, 0, vec![]).is_err());
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
                    adopt(&bad, 0, vec![]).is_err(),
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
            let response = graph.execute(packer, false).unwrap();
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
            let Some(pb::command_output::Kind::Extraction(extracted)) = &response.outputs[0].kind
            else {
                panic!()
            };
            let term = extracted.roots[0].variants[0].term;
            assert_eq!(
                response.nodes[term as usize].kind,
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(expected)
                }))
            );
            let adopted = adopt(&response, term, vec![]).unwrap();
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
        let response = pb::RunProgramResponse::decode(response.as_slice()).unwrap();
        let Some(pb::command_output::Kind::Extraction(extraction)) = &response.outputs[0].kind
        else {
            panic!()
        };
        let term = extraction.roots[0].variants[0].term;
        assert!(matches!(
            &response.nodes[term as usize].kind,
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
            kind: Some(pb::command::Kind::PrintFunction(pb::PrintFunction {
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
            profile: true,
            include_run_reports: false,
        }
        .encode_to_vec();
        let bytes = graph.engine.lock().unwrap().run(&request).unwrap();
        let response = pb::RunProgramResponse::decode(bytes.as_slice()).unwrap();
        let error = response.error.as_ref().unwrap();
        assert_eq!(error.code, pb::ErrorCode::EvaluationFailed as i32);
        assert_eq!(error.location.as_ref().unwrap().path, [4]);
        assert!(!response.profile.as_ref().unwrap().complete);
        assert_eq!(response.outputs.len(), 2);
        let Some(pb::command_output::Kind::Extraction(extraction)) = &response.outputs[0].kind
        else {
            panic!()
        };
        let extracted = Map::<I64, F64>::from_expression(
            adopt(&response, extraction.roots[0].variants[0].term, vec![]).unwrap(),
        );
        let Some(pb::command_output::Kind::PrintedFunction(table_result)) =
            &response.outputs[1].kind
        else {
            panic!()
        };
        assert_eq!(table_result.rows.len(), 1);
        let Some(pb::table_cell::Kind::Term(term)) =
            table_result.rows[0].output.as_ref().unwrap().kind
        else {
            panic!("expected available Map output")
        };
        let observed = Map::<I64, F64>::from_expression(adopt(&response, term, vec![]).unwrap());
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
                    profile: true,
                    include_run_reports: false,
                }
                .encode_to_vec(),
            )
            .unwrap();
        let after = pb::RunProgramResponse::decode(bytes.as_slice()).unwrap();
        assert!(after.error.is_none());
        let Some(pb::command_output::Kind::PrintedFunction(table)) = &after.outputs[0].kind else {
            panic!()
        };
        let Some(pb::table_cell::Kind::Term(term)) = table.rows[0].output.as_ref().unwrap().kind
        else {
            panic!("expected available Map output")
        };
        assert_eq!(adopt(&after, term, vec![]).unwrap(), *observed.expression());
        drop(graph);
        assert_eq!(EGraph::default().extract(&extracted).unwrap(), observed);
    }

    #[test]
    fn map_response_adoption_checks_ref_zero_missing_children_sorts_and_cycles() {
        use crate::typed::{
            EgglogValue,
            builtins::{F64, I64, Map},
        };
        let response = pb::RunProgramResponse {
            sorts: vec![
                pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "f64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "Map".into(),
                        args: vec![2, 0],
                    })),
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
        let value = Map::<I64, F64>::from_expression(adopt(&response, 2, vec![]).unwrap());
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
                .program
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
                let error = adopt(&malformed, 2, vec![]).unwrap_err();
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
                matches!(adopt(&wrong, 2, vec![]), Err(TypedError::Decode(s)) if s == "Map payload child sort mismatch")
            );
        }
        for kind in [
            pb::sort::Kind::Eq("Map".into()),
            pb::sort::Kind::Family(pb::HostSort {
                name: "Pair".into(),
                args: vec![2, 0],
            }),
            pb::sort::Kind::Family(pb::HostSort {
                name: "Map".into(),
                args: vec![2],
            }),
        ] {
            let mut wrong = response.clone();
            wrong.sorts[1].kind = Some(kind);
            assert!(adopt(&wrong, 2, vec![]).is_err());
        }
        let atom = SortRef::equality("A");
        let family = super::super::storage::builtin_catalog()
            .declaration("Map", DeclarationKind::HostSortFamily)
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
            matches!(adopt(&cycle, 2, vec![pack.0]), Err(TypedError::Decode(s)) if s == "cyclic extraction is not inert data")
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
        let response = pb::RunProgramResponse::decode(response.as_slice()).unwrap();
        let Some(pb::command_output::Kind::Extraction(extraction)) = &response.outputs[0].kind
        else {
            panic!()
        };
        let index = extraction.roots[0].variants[0].term;
        assert!(matches!(
            &response.nodes[index as usize].kind,
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
        let response = pb::RunProgramResponse {
            sorts: vec![
                pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "f64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "Pair".into(),
                        args: vec![2, 0],
                    })),
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
        let value = adopt(&response, 2, vec![]).unwrap();
        let [left, right] = value
            .pair_fields(&make, &I64::sort_ref(), &F64::sort_ref())
            .unwrap();
        assert_eq!(i64::try_from(&I64::from_expression(left)).unwrap(), 7);
        assert_eq!(f64::try_from(&F64::from_expression(right)).unwrap(), 1.5);
        assert_eq!(value.0.owner.as_ref().unwrap().program.nodes.len(), 3);
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
                let error = adopt(&malformed, 2, vec![]).unwrap_err();
                assert!(
                    matches!(error, TypedError::Decode(ref s) if s == if child.is_none() { "missing Pair child" } else { "invalid response node index" }),
                    "{error}"
                );
            }
        }
        let mut wrong = response.clone();
        wrong.nodes[0].sort_id = 0;
        assert!(
            matches!(adopt(&wrong, 2, vec![]), Err(TypedError::Decode(s)) if s == "Pair payload child sort mismatch")
        );
        for kind in [
            pb::sort::Kind::Eq("Pair".into()),
            pb::sort::Kind::Family(pb::HostSort {
                name: "Vec".into(),
                args: vec![2],
            }),
            pb::sort::Kind::Family(pb::HostSort {
                name: "Pair".into(),
                args: vec![2],
            }),
        ] {
            let mut malformed = response.clone();
            malformed.sorts[1].kind = Some(kind);
            assert!(adopt(&malformed, 2, vec![]).is_err());
        }
        let mut repeated = response.clone();
        repeated.sorts[1].kind = Some(pb::sort::Kind::Family(pb::HostSort {
            name: "Pair".into(),
            args: vec![2, 2],
        }));
        repeated.nodes[2].kind = Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Pair(pb::PairValue {
                first: Some(0),
                second: Some(0),
            })),
        }));
        let shared = adopt(&repeated, 2, vec![]).unwrap();
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
                .declaration("Pair", DeclarationKind::HostSortFamily)
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
            matches!(adopt(&cycle, 2, vec![pack.0]), Err(TypedError::Decode(s)) if s == "cyclic extraction is not inert data")
        );
    }

    #[test]
    fn maybe_response_adoption_checks_optional_zero_sorts_cycles_and_sharing() {
        use crate::typed::{
            EgglogValue,
            builtins::{I64, Maybe, Vec as EVec},
        };
        let response = pb::RunProgramResponse {
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
                        name: "Maybe".into(),
                        args: vec![0],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
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
        let value = Maybe::<I64>::from_expression(adopt(&response, 2, vec![]).unwrap());
        assert_eq!(Option::<I64>::try_from(&value).unwrap(), Some(I64::from(7)));
        assert_eq!(
            value
                .expression()
                .0
                .owner
                .as_ref()
                .unwrap()
                .program
                .nodes
                .len(),
            2
        );
        let repeated = EVec::<Maybe<I64>>::from_expression(adopt(&response, 3, vec![]).unwrap());
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
        let none = Maybe::<I64>::from_expression(adopt(&none, 2, vec![]).unwrap());
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
                    malformed.sorts[1].kind = Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "Vec".into(),
                        args: vec![0],
                    }))
                }
                4 => {
                    malformed.sorts[1].kind = Some(pb::sort::Kind::Family(pb::HostSort {
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
                adopt(&malformed, 2, vec![]).is_err(),
                "Maybe response negative {case}"
            );
        }
        let atom = SortRef::equality("A");
        let family = super::super::storage::builtin_catalog()
            .declaration("Maybe", DeclarationKind::HostSortFamily)
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
            matches!(adopt(&cycle, 2, vec![pack.0]), Err(TypedError::Decode(s)) if s == "cyclic extraction is not inert data")
        );
    }

    #[test]
    fn vec_response_adoption_checks_relocation_payloads_and_cycles() {
        use crate::typed::{EgglogValue, builtins::I64};
        let response = pb::RunProgramResponse {
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
        let value = adopt(&response, 0, vec![]).unwrap();
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
            matches!(adopt(&missing, 0, vec![]), Err(TypedError::Decode(s)) if s == "invalid response node index")
        );
        let mut wrong = response.clone();
        wrong.nodes[1].sort_id = 1;
        assert!(
            matches!(adopt(&wrong, 0, vec![]), Err(TypedError::Decode(s)) if s == "Vec payload element sort mismatch")
        );
        let mut cyclic_sort = response;
        let Some(pb::sort::Kind::Family(f)) = &mut cyclic_sort.sorts[1].kind else {
            panic!()
        };
        f.args[0] = 1;
        assert!(
            matches!(adopt(&cyclic_sort, 0, vec![]), Err(TypedError::Invalid(s)) if s == "cyclic concrete sort")
        );

        let atom = SortRef::equality("A");
        let family = super::super::storage::builtin_catalog()
            .declaration("Vec", DeclarationKind::HostSortFamily)
            .unwrap();
        let vector = SortRef::family(&family, vec![atom.clone()]).unwrap();
        let pack = Callable::constructor("Pack", vec![vector], atom, None, false);
        let cycle = pb::RunProgramResponse {
            sorts: vec![
                pb::Sort {
                    kind: Some(pb::sort::Kind::Eq("A".into())),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
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
            matches!(adopt(&cycle, 0, vec![pack.0]), Err(TypedError::Decode(s)) if s == "cyclic extraction is not inert data")
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
            let response = graph.execute(packer, false).unwrap();
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
                let declaration = request
                    .declarations
                    .iter()
                    .find(|d| {
                        matches!(&d.kind,
                    Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == provider)
                    })
                    .unwrap();
                if matches!(
                    provider,
                    "egglog.core.string.concat" | "egglog.core.bool.or"
                ) {
                    let rust = declaration
                        .bindings
                        .as_ref()
                        .unwrap()
                        .rust
                        .as_ref()
                        .unwrap();
                    assert_eq!(rust.views.last().unwrap().tail_repetitions, Some(2));
                    let python = declaration
                        .bindings
                        .as_ref()
                        .unwrap()
                        .python
                        .as_ref()
                        .unwrap();
                    assert_eq!(python.views.last().unwrap().tail_repetitions, Some(2));
                    if provider == "egglog.core.string.concat" {
                        assert_eq!(rust.views[0].tail_repetitions, None);
                    }
                }
            }
            let Some(pb::command_output::Kind::Extraction(extracted)) = &response.outputs[0].kind
            else {
                panic!()
            };
            let term = extracted.roots[0].variants[0].term;
            assert_eq!(
                response.nodes[term as usize].kind,
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(expected.clone())
                }))
            );
            let adopted = adopt(&response, term, vec![]).unwrap();
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
            malformed.nodes[term as usize].kind =
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(Value::I64(0)),
                }));
            assert!(
                adopt(&malformed, term, vec![]).is_err(),
                "wrong scalar payload for {provider}"
            );
            let sort = response.nodes[term as usize].sort_id;
            malformed = response;
            let Some(pb::sort::Kind::Family(family)) = &mut malformed.sorts[sort as usize].kind
            else {
                panic!()
            };
            family.name = "UnsupportedScalar".into();
            assert!(adopt(&malformed, term, vec![]).is_err());
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
        let mut response = pb::RunProgramResponse::decode(output.as_slice()).unwrap();
        let Some(pb::command_output::Kind::Extraction(extracted)) = &response.outputs[0].kind
        else {
            panic!()
        };
        let term = extracted.roots[0].variants[0].term;
        let declarations = graph.declarations.values().cloned().collect::<Vec<_>>();
        assert!(ensure_sort::<I64>(adopt(&response, term, declarations.clone()).unwrap()).is_ok());
        assert!(ensure_sort::<F64>(adopt(&response, term, declarations.clone()).unwrap()).is_err());
        response.nodes[term as usize].kind =
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::F64Bits(0)),
            }));
        assert!(
            adopt(&response, term, declarations.clone()).is_err(),
            "f64 payload in i64 sort"
        );
        let sort_id = response.nodes[term as usize].sort_id;
        let first = response.nodes.len() as u32;
        for value in [2, 3] {
            response.nodes.push(pb::Node {
                sort_id,
                kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::I64(value)),
                })),
                ..Default::default()
            });
        }
        response.nodes[term as usize].kind = Some(pb::node::Kind::Call(pb::Call {
            func: "egglog.core.i64.add".into(),
            args: vec![first, first + 1],
        }));
        let mut declarations = declarations;
        declarations.push(
            super::super::storage::builtin_catalog()
                .declaration("egglog.core.i64.add", DeclarationKind::Callable)
                .unwrap(),
        );
        let error = adopt(&response, term, declarations).unwrap_err();
        assert!(
            matches!(error, TypedError::Decode(ref message) if message == "extracted call is not a constructor"),
            "wrong rejection guard: {error}"
        );
    }

    fn response(args: Vec<u32>, child: bool) -> (pb::RunProgramResponse, Vec<Record>) {
        let sort = SortRef::equality("M");
        let pair = Callable::constructor(
            "Pair",
            vec![sort.clone(), sort.clone()],
            sort.clone(),
            None,
            false,
        );
        let leaf = Callable::constructor("Leaf", vec![], sort, None, false);
        let mut response = pb::RunProgramResponse {
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
            adopt(&r, 0, declarations).is_err(),
            "call-only cycle is not inert data"
        );
        let (r, declarations) = response(vec![1, 1], false);
        assert!(adopt(&r, 0, declarations).is_err(), "missing child");
        let (r, declarations) = response(vec![], false);
        assert!(adopt(&r, 0, declarations).is_err(), "wrong call arity");
        let (mut r, declarations) = response(vec![1, 1], true);
        r.sorts.push(pb::Sort {
            kind: Some(pb::sort::Kind::Eq("N".into())),
            ..Default::default()
        });
        r.nodes[1].sort_id = 1;
        assert!(
            adopt(&r, 0, declarations).is_err(),
            "wrong child/output sort"
        );
        let (mut r, declarations) = response(vec![1, 1], true);
        r.sorts.push(pb::Sort {
            kind: Some(pb::sort::Kind::Eq("N".into())),
            ..Default::default()
        });
        r.nodes[0].sort_id = 1;
        assert!(
            adopt(&r, 0, declarations).is_err(),
            "wrong root output sort"
        );
        let (r, declarations) = response(vec![1, 1], true);
        assert!(
            adopt(&r, 0, declarations).is_ok(),
            "shared finite child is valid"
        );
    }

    #[test]
    fn set_adoption_relocates_exact_slots_and_rejects_malformed_closures() {
        use crate::typed::{
            EgglogValue,
            builtins::{I64, Set},
        };
        let response = pb::RunProgramResponse {
            sorts: vec![
                pb::Sort {
                    kind: Some(pb::sort::Kind::Eq("Unused".into())),
                    ..Default::default()
                },
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
        let adopted = ensure_sort::<Set<I64>>(adopt(&response, 2, vec![]).unwrap()).unwrap();
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
                .program
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
                    let Some(pb::sort::Kind::Family(f)) = &mut malformed.sorts[2].kind else {
                        panic!()
                    };
                    f.name = "Vec".into();
                }
                2..=4 => {
                    let Some(pb::sort::Kind::Family(f)) = &mut malformed.sorts[2].kind else {
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
                adopt(&malformed, 2, vec![]).is_err(),
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
            matches!(adopt(&symbolic, 2, vec![add]), Err(TypedError::Decode(message)) if message == "extracted call is not a constructor")
        );

        let atom = SortRef::equality("SetCycle");
        let family = super::super::storage::builtin_catalog()
            .declaration("Set", DeclarationKind::HostSortFamily)
            .unwrap();
        let set = SortRef::family(&family, vec![atom.clone()]).unwrap();
        let pack = Callable::constructor("Pack", vec![set], atom, None, false);
        let cyclic = pb::RunProgramResponse {
            sorts: vec![
                pb::Sort {
                    kind: Some(pb::sort::Kind::Eq("SetCycle".into())),
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
            matches!(adopt(&cyclic, 0, vec![pack.0]), Err(TypedError::Decode(message)) if message == "cyclic extraction is not inert data")
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
                vec![],
                Arena::Sort,
                root.sort_id,
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
                Some(pb::sort::Kind::Family(f)) if f.name == "Unit" && f.args.is_empty()));
            let declaration = program
                .declarations
                .iter()
                .find(|d| {
                    matches!(&d.kind,
                Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == call.func)
                })
                .unwrap();
            let Some(pb::declaration::Kind::HostPrimitive(p)) = &declaration.kind else {
                panic!()
            };
            let Some(pb::host_primitive::Typing::Signature(s)) = &p.typing else {
                panic!()
            };
            assert_eq!(s.type_params.len(), 1);
            assert_eq!(s.inputs.len(), 2);
            assert!(s.varargs.is_empty());
            assert_eq!(s.inputs[0].sort, s.inputs[1].sort);
            assert_eq!(
                program.sorts[s.inputs[0].sort as usize].kind,
                Some(pb::sort::Kind::Var(0))
            );
            assert!(
                SortRef(sorts.resolve(Arena::Sort, s.output.unwrap()).unwrap()) == SortRef(sorts)
            );
            assert!(
                !program.declarations.iter().any(|d| matches!(&d.kind,
                Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.core.fn.apply")),
                "ordinary ne packs its reachable declarations, not the whole catalog"
            );
            let catalog = crate::typed::storage::builtin_catalog();
            let original = catalog.owner.as_ref().unwrap().program.declarations.iter().find(|d|
                matches!(&d.kind, Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == call.func)).unwrap();
            assert_eq!(declaration.bindings, original.bindings);
            let response = pb::RunProgramResponse::decode(output.as_slice()).unwrap();
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
        graph.run_response(ruleset(rewrite(&left, &right))).unwrap();
        observe(&mut graph, ne(&left, &right), false);
        observe(&mut graph, ne(&left_vec, &right_vec), false);
        assert_ne!(left, right);
        assert_ne!(left_vec, right_vec);
        observe(&mut graph, ne(I64::from(17), 23), true);

        // Corrupt bytes cannot turn failed checks into success or permit a
        // subsequent call on a session with unknown publication state.
        assert!(matches!(
            graph.accept_response(Packer::default(), &[0xff]),
            Err(TypedError::Decode(_))
        ));
        assert!(matches!(graph.check(ne(I64::from(17), 23)),
            Err(TypedError::Invalid(message)) if message == "session publication state is unknown"));
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
        let response = pb::RunProgramResponse::decode(output.as_slice()).unwrap();
        assert!(response.error.is_none());
        let term = response
            .outputs
            .iter()
            .find_map(|out| match &out.kind {
                Some(pb::command_output::Kind::Extraction(e)) => Some(e.roots[0].variants[0].term),
                _ => None,
            })
            .unwrap();
        let root = &response.nodes[term as usize];
        let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Set(items)),
        })) = &root.kind
        else {
            panic!()
        };
        assert_eq!(items.items.len(), 2);
        let Some(pb::sort::Kind::Family(family)) = &response.sorts[root.sort_id as usize].kind
        else {
            panic!()
        };
        assert_eq!(family.name, "Set");
        assert_eq!(family.args.len(), 1);
        for child in &items.items {
            assert_eq!(response.nodes[*child as usize].sort_id, family.args[0]);
        }
        let independently_adopted =
            ensure_sort::<Set<I64>>(adopt(&response, term, vec![]).unwrap()).unwrap();
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
        assert!(request.profile);
        assert!(
            matches!(&request.program.unwrap().nodes[root as usize].kind, Some(pb::node::Kind::Call(c)) if c.func == "ByteWitness.Leaf")
        );
        assert_eq!(
            pb::RunProgramResponse::decode(output.as_slice()).unwrap(),
            response
        );
        assert!(matches!(
            response.outputs[0].kind,
            Some(pb::command_output::Kind::Extraction(_))
        ));
    }

    #[test]
    fn explicit_ruleset_names_are_preserved_and_generated_names_do_not_capture() {
        let root = |name: Option<&str>| {
            Ruleset(
                publish(
                    pb::Program {
                        rulesets: vec![pb::Ruleset {
                            name: name.map(str::to_owned),
                            kind: Some(pb::ruleset::Kind::Rules(pb::RuleList { rules: vec![] })),
                            ..Default::default()
                        }],
                        ..Default::default()
                    },
                    std::array::from_fn(|_| vec![]),
                    vec![],
                    Arena::Ruleset,
                    0,
                )
                .unwrap(),
                None,
            )
        };
        let mut graph = EGraph::default();
        for explicit in ["chosen", "", "__typed_ruleset_3"] {
            graph.run_response(root(Some(explicit))).unwrap();
            let request =
                pb::RunProgramRequest::decode(graph.last_wire.as_ref().unwrap().0.as_slice())
                    .unwrap();
            let program = request.program.unwrap();
            assert_eq!(program.rulesets[0].name.as_deref(), Some(explicit));
            assert!(matches!(
                program.rulesets[0].kind,
                Some(pb::ruleset::Kind::Rules(_))
            ));
            let Some(pb::command::Kind::Run(run)) = &program.commands[0].kind else {
                panic!()
            };
            assert_eq!(
                run.ruleset.as_ref().unwrap().kind,
                Some(pb::ruleset_ref::Kind::Name(explicit.into()))
            );
        }
        graph.run_response(root(None)).unwrap();
        let request =
            pb::RunProgramRequest::decode(graph.last_wire.as_ref().unwrap().0.as_slice()).unwrap();
        assert_eq!(
            request.program.unwrap().rulesets[0].name.as_deref(),
            Some("__typed_ruleset_4")
        );
    }
}
