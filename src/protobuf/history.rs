//! The shared byte boundary owns audit retention, outside cloned native sessions.

use super::{Engine, TransportError, pb};
use pb::history_entry::{Outcome, Request};
use prost::Message;
use std::sync::{Arc, Mutex};

struct Exchange {
    sequence: u64,
    entry: Mutex<pb::HistoryEntry>,
}

struct Link {
    exchange: Arc<Exchange>,
    previous: Option<Arc<Link>>,
}

impl Drop for Link {
    fn drop(&mut self) {
        // Releasing a long uniquely owned audit must not recurse through it.
        while let Some(previous) = self.previous.take() {
            match Arc::try_unwrap(previous) {
                Ok(mut link) => self.previous = link.previous.take(),
                Err(_) => break,
            }
        }
    }
}

#[derive(Clone)]
pub(super) struct HistoryLog {
    initial_resources: pb::ConfigureEGraphResourcesResponse,
    head: Option<Arc<Link>>,
    pub(super) closed: bool,
}

impl HistoryLog {
    fn links(&self) -> Vec<Arc<Link>> {
        let mut links = vec![];
        let mut link = self.head.clone();
        while let Some(current) = link {
            link = current.previous.clone();
            links.push(current);
        }
        links.reverse();
        links
    }

    pub(super) fn merge(&mut self, other: &Self) {
        let left = self.links();
        let right = other.links();
        let (mut i, mut j) = (0, 0);
        let mut merged = Vec::with_capacity(left.len().max(right.len()));
        while i < left.len() || j < right.len() {
            let link = if j == right.len()
                || (i < left.len() && left[i].exchange.sequence <= right[j].exchange.sequence)
            {
                if j < right.len() && left[i].exchange.sequence == right[j].exchange.sequence {
                    j += 1;
                }
                let link = left[i].clone();
                i += 1;
                link
            } else {
                let link = right[j].clone();
                j += 1;
                link
            };
            merged.push(link);
        }
        // Normal scope returns already contain the saved exchanges in the
        // active chain. Adopt it instead of rebuilding retained prefix links.
        if merged.len() == right.len() {
            self.head = other.head.clone();
            return;
        }
        if merged.len() == left.len() {
            return;
        }
        let left_prefix = merged
            .iter()
            .zip(&left)
            .take_while(|(a, b)| a.exchange.sequence == b.exchange.sequence)
            .count();
        let right_prefix = merged
            .iter()
            .zip(&right)
            .take_while(|(a, b)| a.exchange.sequence == b.exchange.sequence)
            .count();
        let (prefix, base) = if left_prefix >= right_prefix {
            (left_prefix, &left)
        } else {
            (right_prefix, &right)
        };
        let mut head = prefix.checked_sub(1).map(|index| base[index].clone());
        for link in &merged[prefix..] {
            head = Some(Arc::new(Link {
                exchange: link.exchange.clone(),
                previous: head,
            }));
        }
        self.head = head;
    }
}

impl Engine {
    fn append_history(&mut self, handles: &[u64], request: Request) -> Arc<Exchange> {
        self.next_history = self
            .next_history
            .checked_add(1)
            .expect("history sequence space exhausted");
        let exchange = Arc::new(Exchange {
            sequence: self.next_history,
            // A native unwind leaves this truthful no-response outcome intact.
            entry: Mutex::new(pb::HistoryEntry {
                request: Some(request),
                outcome: Some(Outcome::Interrupted(pb::Unit {})),
            }),
        });
        for (index, handle) in handles.iter().enumerate() {
            if !handles[..index].contains(handle)
                && let Some(history) = self.histories.get_mut(handle)
            {
                history.head = Some(Arc::new(Link {
                    exchange: exchange.clone(),
                    previous: history.head.take(),
                }));
            }
        }
        exchange
    }

    // Capture only enabled histories, before native validation/normalization.
    // No callback or native operation runs while the exchange mutex is held.
    fn recorded<T: Clone, R: Message>(
        &mut self,
        handles: &[u64],
        request: T,
        record: fn(T) -> Request,
        operation: fn(&mut Self, T) -> Result<R, TransportError>,
        outcome: fn(R) -> Outcome,
    ) -> Result<Vec<u8>, TransportError> {
        let exchange = handles
            .iter()
            .any(|handle| self.histories.contains_key(handle))
            .then(|| self.append_history(handles, record(request.clone())));
        let result = operation(self, request);
        match result {
            Ok(response) => {
                let bytes = response.encode_to_vec();
                if let Some(exchange) = exchange {
                    exchange.entry.lock().unwrap().outcome = Some(outcome(response));
                }
                Ok(bytes)
            }
            Err(error) => {
                if let Some(exchange) = exchange {
                    exchange.entry.lock().unwrap().outcome =
                        Some(Outcome::TransportError(error.to_string()));
                }
                Err(error)
            }
        }
    }

    /// Create a handle; successful opt-in creation starts its structured audit.
    pub fn create(&mut self, bytes: &[u8]) -> Result<Vec<u8>, TransportError> {
        let request = pb::CreateEGraphRequest::decode(bytes)?;
        let original = request.record_history.then(|| request.clone());
        let response = self.create_request(request)?;
        if let Some(original) = original {
            let graph = &self.graphs[&response.egraph_id].graph;
            self.histories.insert(
                response.egraph_id,
                HistoryLog {
                    initial_resources: pb::ConfigureEGraphResourcesResponse {
                        threads: graph.num_threads() as u64,
                        no_decomp: graph.no_decomp,
                    },
                    head: None,
                    closed: false,
                },
            );
            let exchange = self.append_history(&[response.egraph_id], Request::Create(original));
            exchange.entry.lock().unwrap().outcome =
                Some(Outcome::CreateResponse(response.clone()));
        }
        Ok(response.encode_to_vec())
    }

    /// Clone native state, sharing recorded past with independent continuations.
    pub fn clone_egraph(&mut self, bytes: &[u8]) -> Result<Vec<u8>, TransportError> {
        let request = pb::CloneEGraphRequest::decode(bytes)?;
        self.recorded(
            &[request.egraph_id],
            request,
            Request::Clone,
            Self::clone_request,
            Outcome::CloneResponse,
        )
    }

    /// Release native state, retaining an enabled closed audit until Engine drop.
    pub fn destroy(&mut self, bytes: &[u8]) -> Result<Vec<u8>, TransportError> {
        let request = pb::DestroyEGraphRequest::decode(bytes)?;
        self.recorded(
            &[request.egraph_id],
            request,
            Request::Destroy,
            Self::destroy_request,
            Outcome::DestroyResponse,
        )
    }

    /// Restore a saved scope, joining both audits without rolling history back.
    pub fn return_to(&mut self, bytes: &[u8]) -> Result<Vec<u8>, TransportError> {
        let request = pb::ReturnToEGraphRequest::decode(bytes)?;
        self.recorded(
            &[request.active_id, request.saved_id],
            request,
            Request::ReturnTo,
            Self::return_request,
            Outcome::ReturnToResponse,
        )
    }

    /// Query/update resources without cloning logical state; record real outcomes.
    pub fn configure_resources(&mut self, bytes: &[u8]) -> Result<Vec<u8>, TransportError> {
        let request = pb::ConfigureEGraphResourcesRequest::decode(bytes)?;
        self.recorded(
            &[request.egraph_id],
            request,
            Request::ConfigureResources,
            Self::configure_request,
            Outcome::ConfigureResourcesResponse,
        )
    }

    /// Execute one original submission, retaining actual prefix outputs and errors.
    pub fn run(&mut self, bytes: &[u8]) -> Result<Vec<u8>, TransportError> {
        let request = pb::RunProgramRequest::decode(bytes)?;
        self.recorded(
            &[request.egraph_id],
            request,
            Request::RunProgram,
            Self::run_request,
            Outcome::RunProgramResponse,
        )
    }

    /// Export enabled history without recording this observation.
    pub fn get_history(&self, bytes: &[u8]) -> Result<Vec<u8>, TransportError> {
        let request = pb::GetHistoryRequest::decode(bytes)?;
        let history = self.histories.get(&request.egraph_id).ok_or_else(|| {
            TransportError(if self.graphs.contains_key(&request.egraph_id) {
                "history recording is disabled".into()
            } else {
                "unknown egraph_id".into()
            })
        })?;
        Ok(pb::GetHistoryResponse {
            entries: history
                .links()
                .into_iter()
                .map(|link| link.exchange.entry.lock().unwrap().clone())
                .collect(),
            initial_resources: Some(history.initial_resources),
            closed: history.closed,
        }
        .encode_to_vec())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create(engine: &mut Engine, recording: bool, mode: pb::ExecutionMode) -> u64 {
        let request = pb::CreateEGraphRequest {
            record_history: recording,
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
                ..Default::default()
            }),
            threads: Some(1),
            ..Default::default()
        };
        pb::CreateEGraphResponse::decode(
            engine.create(&request.encode_to_vec()).unwrap().as_slice(),
        )
        .unwrap()
        .egraph_id
    }

    fn empty_class(declare: bool) -> pb::Program {
        pb::Program {
            sorts: vec![pb::Sort {
                kind: Some(pb::sort::Kind::Eq("HistoryClass".into())),
                ..Default::default()
            }],
            declarations: if declare {
                vec![pb::Declaration {
                    kind: Some(pb::declaration::Kind::EqSort(pb::EqSort {
                        name: "HistoryClass".into(),
                        ..Default::default()
                    })),
                    ..Default::default()
                }]
            } else {
                vec![]
            },
            nodes: vec![pb::Node {
                kind: Some(pb::node::Kind::Union(pb::Union { members: vec![] })),
                ..Default::default()
            }],
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Term(0)),
                    ..Default::default()
                })),
                ..Default::default()
            }],
            ..Default::default()
        }
    }

    #[test]
    fn history_disabled_has_no_accumulating_log_or_sequence() {
        let mut engine = Engine::default();
        let parent = create(&mut engine, false, pb::ExecutionMode::Normal);
        for _ in 0..4 {
            engine
                .run(
                    &pb::RunProgramRequest {
                        egraph_id: parent,
                        program: Some(pb::Program::default()),
                        profile: true,
                        ..Default::default()
                    }
                    .encode_to_vec(),
                )
                .unwrap();
        }
        let child = pb::CloneEGraphResponse::decode(
            engine
                .clone_egraph(&pb::CloneEGraphRequest { egraph_id: parent }.encode_to_vec())
                .unwrap()
                .as_slice(),
        )
        .unwrap()
        .egraph_id;
        engine
            .return_to(
                &pb::ReturnToEGraphRequest {
                    active_id: child,
                    saved_id: parent,
                }
                .encode_to_vec(),
            )
            .unwrap();
        let error = engine
            .get_history(&pb::GetHistoryRequest { egraph_id: parent }.encode_to_vec())
            .unwrap_err();
        assert!(error.to_string().contains("disabled"));
        engine
            .destroy(&pb::DestroyEGraphRequest { egraph_id: parent }.encode_to_vec())
            .unwrap();
        assert!(engine.histories.is_empty());
        assert_eq!(engine.next_history, 0);
    }

    #[test]
    fn history_keeps_original_local_arenas_and_freeze_without_recursive_growth() {
        let mut engine = Engine::default();
        let id = create(&mut engine, true, pb::ExecutionMode::Normal);
        let mut originals = vec![];
        for declare in [true, false] {
            let request = pb::RunProgramRequest {
                egraph_id: id,
                program: Some(empty_class(declare)),
                profile: true,
                ..Default::default()
            };
            let response = pb::RunProgramResponse::decode(
                engine.run(&request.encode_to_vec()).unwrap().as_slice(),
            )
            .unwrap();
            assert_eq!(response.error, None);
            originals.push((request, response));
        }
        let getter = pb::GetHistoryRequest { egraph_id: id }.encode_to_vec();
        let before = engine.get_history(&getter).unwrap();
        assert_eq!(engine.get_history(&getter).unwrap(), before);
        let history = pb::GetHistoryResponse::decode(before.as_slice()).unwrap();
        assert_eq!(history.entries.len(), 3);
        assert_eq!(history.initial_resources.unwrap().threads, 1);
        for (entry, (request, response)) in history.entries[1..].iter().zip(originals) {
            assert_eq!(entry.request, Some(Request::RunProgram(request)));
            assert_eq!(entry.outcome, Some(Outcome::RunProgramResponse(response)));
        }
        let response = pb::RunProgramResponse::decode(
            engine
                .run(
                    &pb::RunProgramRequest {
                        egraph_id: id,
                        profile: true,
                        program: Some(pb::Program {
                            commands: vec![pb::Command {
                                kind: Some(pb::command::Kind::Freeze(pb::Freeze {})),
                                ..Default::default()
                            }],
                            ..Default::default()
                        }),
                        ..Default::default()
                    }
                    .encode_to_vec(),
                )
                .unwrap()
                .as_slice(),
        )
        .unwrap();
        let Some(pb::command_output::Kind::Snapshot(snapshot)) = &response.outputs[0].kind else {
            panic!("snapshot")
        };
        let program = snapshot.program.as_ref().unwrap();
        assert_eq!(program.nodes.iter().filter(|node| matches!(&node.kind, Some(pb::node::Kind::Union(union)) if union.members.is_empty())).count(), 2);
        let history =
            pb::GetHistoryResponse::decode(engine.get_history(&getter).unwrap().as_slice())
                .unwrap();
        assert_eq!(history.entries.len(), 4);
        assert_eq!(
            history.entries[3].outcome,
            Some(Outcome::RunProgramResponse(response))
        );
        assert_eq!(engine.histories[&id].links().len(), 4);
    }

    #[test]
    fn history_preserves_prefix_failures_preparation_errors_and_transport_errors() {
        let mut engine = Engine::default();
        let id = create(&mut engine, true, pb::ExecutionMode::Normal);
        let mut program = empty_class(true);
        program.nodes.push(program.nodes[0].clone());
        program.commands.extend([
            pb::Command {
                kind: Some(pb::command::Kind::PrintSize(pb::PrintSize::default())),
                ..Default::default()
            },
            pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Panic("stop before suffix".into())),
                    ..Default::default()
                })),
                ..Default::default()
            },
            pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Term(1)),
                    ..Default::default()
                })),
                ..Default::default()
            },
        ]);
        let original = pb::RunProgramRequest {
            egraph_id: id,
            program: Some(program),
            profile: true,
            ..Default::default()
        };
        let response = pb::RunProgramResponse::decode(
            engine.run(&original.encode_to_vec()).unwrap().as_slice(),
        )
        .unwrap();
        assert!(response.error.is_some());
        assert_eq!(response.outputs.len(), 1);
        let invalid = pb::RunProgramRequest {
            egraph_id: id,
            profile: true,
            program: Some(pb::Program {
                rules: vec![pb::Rule::default()],
                ..Default::default()
            }),
            ..Default::default()
        };
        let rejected = pb::RunProgramResponse::decode(
            engine.run(&invalid.encode_to_vec()).unwrap().as_slice(),
        )
        .unwrap();
        assert!(rejected.error.is_some());
        let resource = pb::ConfigureEGraphResourcesRequest {
            egraph_id: id,
            ..Default::default()
        };
        let error = engine
            .configure_resources(&resource.encode_to_vec())
            .unwrap_err();
        let history = pb::GetHistoryResponse::decode(
            engine
                .get_history(&pb::GetHistoryRequest { egraph_id: id }.encode_to_vec())
                .unwrap()
                .as_slice(),
        )
        .unwrap();
        assert_eq!(
            history.entries[1].request,
            Some(Request::RunProgram(original))
        );
        assert_eq!(
            history.entries[1].outcome,
            Some(Outcome::RunProgramResponse(response))
        );
        assert_eq!(
            history.entries[2].request,
            Some(Request::RunProgram(invalid))
        );
        assert_eq!(
            history.entries[2].outcome,
            Some(Outcome::RunProgramResponse(rejected))
        );
        assert_eq!(
            history.entries[3].outcome,
            Some(Outcome::TransportError(error.to_string()))
        );
        let snapshot = super::super::freeze::export(&engine.graphs[&id]).unwrap();
        assert_eq!(snapshot.program.unwrap().nodes.iter().filter(|node| matches!(&node.kind, Some(pb::node::Kind::Union(union)) if union.members.is_empty())).count(), 1);
    }

    #[test]
    fn history_clone_shares_past_and_return_joins_without_duplicate_prefix() {
        let mut engine = Engine::default();
        let parent = create(&mut engine, true, pb::ExecutionMode::Normal);
        let child = pb::CloneEGraphResponse::decode(
            engine
                .clone_egraph(&pb::CloneEGraphRequest { egraph_id: parent }.encode_to_vec())
                .unwrap()
                .as_slice(),
        )
        .unwrap()
        .egraph_id;
        assert!(Arc::ptr_eq(
            engine.histories[&parent].head.as_ref().unwrap(),
            engine.histories[&child].head.as_ref().unwrap()
        ));
        let query = pb::ConfigureEGraphResourcesRequest {
            egraph_id: parent,
            operation: Some(pb::configure_e_graph_resources_request::Operation::Query(
                pb::Unit {},
            )),
        };
        engine.configure_resources(&query.encode_to_vec()).unwrap();
        let run = pb::RunProgramRequest {
            egraph_id: child,
            program: Some(pb::Program::default()),
            profile: true,
            ..Default::default()
        };
        engine.run(&run.encode_to_vec()).unwrap();
        assert_eq!(engine.histories[&parent].links().len(), 3);
        assert_eq!(engine.histories[&child].links().len(), 3);
        engine
            .return_to(
                &pb::ReturnToEGraphRequest {
                    active_id: child,
                    saved_id: parent,
                }
                .encode_to_vec(),
            )
            .unwrap();
        let history = pb::GetHistoryResponse::decode(
            engine
                .get_history(&pb::GetHistoryRequest { egraph_id: parent }.encode_to_vec())
                .unwrap()
                .as_slice(),
        )
        .unwrap();
        assert_eq!(history.entries.len(), 5);
        assert_eq!(
            history.entries[2].request,
            Some(Request::ConfigureResources(query))
        );
        assert_eq!(history.entries[3].request, Some(Request::RunProgram(run)));
        assert!(matches!(
            &history.entries[4].outcome,
            Some(Outcome::ReturnToResponse(_))
        ));
        assert!(!history.closed);
        assert!(engine.histories[&child].closed);
        assert!(!engine.graphs.contains_key(&child));
        engine
            .destroy(&pb::DestroyEGraphRequest { egraph_id: parent }.encode_to_vec())
            .unwrap();
        assert!(!engine.graphs.contains_key(&parent));
        let closed = pb::GetHistoryResponse::decode(
            engine
                .get_history(&pb::GetHistoryRequest { egraph_id: parent }.encode_to_vec())
                .unwrap()
                .as_slice(),
        )
        .unwrap();
        assert!(closed.closed);
        assert_eq!(closed.entries.len(), 6);
        assert!(matches!(
            &closed.entries[5].outcome,
            Some(Outcome::DestroyResponse(_))
        ));
    }

    #[test]
    fn history_scope_returns_share_linear_retained_metadata() {
        let mut engine = Engine::default();
        let parent = create(&mut engine, true, pb::ExecutionMode::Normal);
        for _ in 0..32 {
            let child = pb::CloneEGraphResponse::decode(
                engine
                    .clone_egraph(&pb::CloneEGraphRequest { egraph_id: parent }.encode_to_vec())
                    .unwrap()
                    .as_slice(),
            )
            .unwrap()
            .egraph_id;
            engine
                .return_to(
                    &pb::ReturnToEGraphRequest {
                        active_id: child,
                        saved_id: parent,
                    }
                    .encode_to_vec(),
                )
                .unwrap();
        }
        let mut links = std::collections::HashSet::new();
        let mut exchanges = std::collections::HashSet::new();
        for history in engine.histories.values() {
            let mut link = history.head.as_ref();
            while let Some(current) = link {
                if !links.insert(Arc::as_ptr(current)) {
                    break;
                }
                exchanges.insert(Arc::as_ptr(&current.exchange));
                link = current.previous.as_ref();
            }
        }
        assert_eq!(exchanges.len(), 65);
        assert_eq!(links.len(), exchanges.len());
        assert_eq!(engine.histories[&parent].links().len(), 65);
    }

    #[test]
    fn history_keeps_actual_partial_installation_receipt() {
        use egglog::{ExecutionEvent, ExecutionOrigin, ast};
        let mut engine = Engine::default();
        let id = create(&mut engine, true, pb::ExecutionMode::Proofs);
        // Inject a real native trailing-maintenance failure, as in the existing
        // installation tests; authored Programs cannot name these private helpers.
        let session = engine.graphs.get_mut(&id).unwrap();
        let commands = session
            .graph
            .parse_program(None, "(sort HistoryForeign)")
            .unwrap();
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
        let mut poison = session
            .graph
            .parse_program(None, "(rule () ((panic \"history installation fault\")))")
            .unwrap();
        let ast::Command::Rule { rule } = &mut poison[0] else {
            unreachable!()
        };
        rule.ruleset = helpers.last().unwrap().clone();
        session.graph.run_program(poison).unwrap();
        let request = pb::RunProgramRequest {
            egraph_id: id,
            profile: true,
            program: Some(pb::Program {
                rulesets: ["history-first", "history-second"]
                    .into_iter()
                    .map(|name| pb::Ruleset {
                        name: Some(name.into()),
                        kind: Some(pb::ruleset::Kind::Rules(pb::RuleList::default())),
                        ..Default::default()
                    })
                    .collect(),
                ..Default::default()
            }),
            ..Default::default()
        };
        let response = pb::RunProgramResponse::decode(
            engine.run(&request.encode_to_vec()).unwrap().as_slice(),
        )
        .unwrap();
        assert!(response.error.is_some());
        assert_eq!(
            response.ruleset_publication.as_ref().unwrap().names,
            ["history-first"]
        );
        assert!(
            engine.graphs[&id]
                .definitions
                .rulesets
                .iter()
                .any(|set| set.name.as_deref() == Some("history-first"))
        );
        assert!(
            !engine.graphs[&id]
                .definitions
                .rulesets
                .iter()
                .any(|set| set.name.as_deref() == Some("history-second"))
        );
        let history = pb::GetHistoryResponse::decode(
            engine
                .get_history(&pb::GetHistoryRequest { egraph_id: id }.encode_to_vec())
                .unwrap()
                .as_slice(),
        )
        .unwrap();
        assert_eq!(
            history.entries[1].request,
            Some(Request::RunProgram(request))
        );
        assert_eq!(
            history.entries[1].outcome,
            Some(Outcome::RunProgramResponse(response))
        );
    }

    #[test]
    fn history_retains_interrupted_host_request_without_fabricated_response() {
        use super::super::cost_model::{
            CostModelContract, CostModelRuntime, ModelSort, NativeCostModel,
        };
        struct Unwind;
        impl NativeCostModel for Unwind {
            fn contract(&self) -> CostModelContract {
                let sort = || ModelSort {
                    sorts: vec![pb::Sort {
                        kind: Some(pb::sort::Kind::Family(pb::HostSort {
                            name: "i64".into(),
                            args: vec![],
                        })),
                        ..Default::default()
                    }],
                    root: 0,
                };
                CostModelContract {
                    annotation: sort(),
                    objective: sort(),
                    additive: false,
                }
            }
            fn start(&self, _: &pb::Program) -> Result<Arc<dyn CostModelRuntime>, egglog::Error> {
                panic!("host callback unwind")
            }
        }
        let mut engine = Engine::default();
        let id = create(&mut engine, true, pb::ExecutionMode::Normal);
        let model = engine.register_cost_model(id, Arc::new(Unwind)).unwrap();
        let request = pb::RunProgramRequest {
            egraph_id: id,
            profile: true,
            program: Some(pb::Program {
                sorts: vec![pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
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
                commands: vec![pb::Command {
                    kind: Some(pb::command::Kind::Extract(pb::Extract {
                        roots: vec![0],
                        variants: 1,
                        extractor: pb::Extractor::Tree.into(),
                        cost_model: model,
                    })),
                    ..Default::default()
                }],
                ..Default::default()
            }),
            ..Default::default()
        };
        let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            engine.run(&request.encode_to_vec())
        }));
        assert!(unwound.is_err());
        let history = pb::GetHistoryResponse::decode(
            engine
                .get_history(&pb::GetHistoryRequest { egraph_id: id }.encode_to_vec())
                .unwrap()
                .as_slice(),
        )
        .unwrap();
        assert_eq!(history.entries.len(), 2);
        assert_eq!(
            history.entries[1].request,
            Some(Request::RunProgram(request))
        );
        assert_eq!(
            history.entries[1].outcome,
            Some(Outcome::Interrupted(pb::Unit {}))
        );
    }
}
