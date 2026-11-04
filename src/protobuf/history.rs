//! Opt-in submitted inputs owned by live graphs, outside preparation clones.

use super::{Engine, TransportError, graph, pb, rules};
use prost::Message;
use std::collections::HashMap;
use std::sync::Arc;

// Resolve historic name selections against this request's post-setup values.
// A flattened history has one setup phase, so retaining live name references
// would otherwise retarget older commands after a later replacement.
pub(super) fn capture(
    mut program: pb::Program,
    registry: &rules::Registry,
) -> Result<pb::Program, String> {
    let mut bindings: HashMap<_, _> = program
        .rulesets
        .iter()
        .map(|binding| {
            (
                binding.name.clone(),
                binding.value.clone().expect("validated binding"),
            )
        })
        .collect();
    let names: Vec<_> = super::command_tree(&program.commands)
        .filter_map(|command| {
            if let Some(pb::command::Kind::Run(run)) = &command.kind {
                Some(run)
            } else {
                None
            }
        })
        .flat_map(|run| run.rulesets.iter())
        .filter_map(|selection| {
            if let Some(pb::ruleset_selection::Kind::Name(name)) = &selection.kind {
                Some(name.clone())
            } else {
                None
            }
        })
        .collect();
    let mut imported: HashMap<usize, pb::Rule> = HashMap::new();
    let mut files = HashMap::new();
    for name in names {
        if bindings.contains_key(&name) {
            continue;
        }
        let mut selected = vec![];
        for &index in registry.groups.get(&name).into_iter().flatten() {
            let rule = if let Some(rule) = imported.get(&index) {
                rule.clone()
            } else {
                let rule = graph::append_rule(
                    &mut program,
                    &registry.rules[index].candidate.record,
                    &mut files,
                )?;
                imported.insert(index, rule.clone());
                rule
            };
            selected.push(rule);
        }
        bindings.insert(name, pb::Ruleset { rules: selected });
    }
    let mut pending: Vec<_> = program.commands.iter_mut().collect();
    while let Some(command) = pending.pop() {
        match &mut command.kind {
            Some(pb::command::Kind::Run(run)) => {
                for selection in &mut run.rulesets {
                    if let Some(pb::ruleset_selection::Kind::Name(name)) = &selection.kind {
                        selection.kind =
                            Some(pb::ruleset_selection::Kind::Ruleset(bindings[name].clone()));
                    }
                }
            }
            Some(pb::command::Kind::Fail(child)) => pending.push(child),
            Some(pb::command::Kind::Loop(body)) => pending.extend(&mut body.body),
            _ => (),
        }
    }
    Ok(program)
}

struct Link {
    program: pb::Program,
    previous: Option<Arc<Link>>,
}

impl Drop for Link {
    fn drop(&mut self) {
        while let Some(previous) = self.previous.take() {
            match Arc::try_unwrap(previous) {
                Ok(mut link) => self.previous = link.previous.take(),
                Err(_) => break,
            }
        }
    }
}

#[derive(Clone, Default)]
pub(super) struct HistoryLog {
    head: Option<Arc<Link>>,
}

impl HistoryLog {
    pub(super) fn append(&mut self, program: pb::Program) {
        self.head = Some(Arc::new(Link {
            program,
            previous: self.head.take(),
        }));
    }

    fn export(&self) -> Result<pb::Program, String> {
        let mut links = vec![];
        let mut link = self.head.as_deref();
        while let Some(current) = link {
            links.push(&current.program);
            link = current.previous.as_deref();
        }
        let mut result = pb::Program::default();
        // Reconcile only definition metadata/closures, never the growing command
        // graph. Append each submitted data arena once after the header is built.
        for program in links.iter().rev() {
            crate::builtin::definitions::reconcile_declarations(program, &mut result)?;
        }
        for program in links.into_iter().rev() {
            let files = u32::try_from(result.files.len()).map_err(|_| "too many files")?;
            graph::append(&mut result, program, files)?;
        }
        let mut latest = HashMap::new();
        for (index, binding) in result.rulesets.iter().enumerate() {
            latest.insert(binding.name.clone(), index);
        }
        result.rulesets = result
            .rulesets
            .into_iter()
            .enumerate()
            .filter_map(|(index, binding)| (latest[&binding.name] == index).then_some(binding))
            .collect();
        Ok(result)
    }
}

impl Engine {
    /// Inspect the configured backend without allocating an e-graph handle.
    pub fn get_builtins(&mut self, bytes: &[u8]) -> Result<Vec<u8>, TransportError> {
        pb::GetBuiltinsRequest::decode(bytes)?;
        if self.builtins.is_none() {
            let mut graph = crate::new_experimental_egraph();
            graph.set_report_level(egglog_reports::ReportLevel::Off);
            if let Some(extension) = &self.extension {
                extension.initialize(&mut graph).map_err(TransportError)?;
            }
            self.builtins =
                Some(crate::builtin::configured_catalog(&graph).map_err(TransportError)?);
        }
        Ok(self.builtins.as_ref().unwrap().encode_to_vec())
    }

    /// Create a graph. Recording is off unless explicitly requested.
    pub fn create(&mut self, bytes: &[u8]) -> Result<Vec<u8>, TransportError> {
        let request = pb::CreateEGraphRequest::decode(bytes)?;
        let recording = request.record_history;
        let response = self.create_request(request)?;
        if recording {
            self.histories
                .insert(response.egraph_id, HistoryLog::default());
        }
        Ok(response.encode_to_vec())
    }

    /// Clone native state and share the immutable submitted-input prefix.
    pub fn clone_egraph(&mut self, bytes: &[u8]) -> Result<Vec<u8>, TransportError> {
        Ok(self
            .clone_request(pb::CloneEGraphRequest::decode(bytes)?)?
            .encode_to_vec())
    }

    /// Release the graph and its history.
    pub fn destroy(&mut self, bytes: &[u8]) -> Result<Vec<u8>, TransportError> {
        Ok(self
            .destroy_request(pb::DestroyEGraphRequest::decode(bytes)?)?
            .encode_to_vec())
    }

    /// Execute typed inputs. Preparation rejection does not enter history.
    pub fn run(&mut self, bytes: &[u8]) -> Result<Vec<Vec<u8>>, TransportError> {
        Ok(self
            .run_request(pb::RunProgramRequest::decode(bytes)?)?
            .into_iter()
            .map(|frame| frame.encode_to_vec())
            .collect())
    }

    /// Execute synchronously, delivering owned observations at safe command
    /// boundaries. The callback applies backpressure directly: no queue grows
    /// while it runs. Break cancels later commands without rolling effects back.
    /// A final completion/error chunk precedes successful stream completion.
    /// Its callback return value is ignored because execution has already ended.
    pub fn run_stream(
        &mut self,
        bytes: &[u8],
        emit: &mut dyn FnMut(pb::RunProgramResponse) -> std::ops::ControlFlow<()>,
    ) -> Result<(), TransportError> {
        self.run_request_stream(pb::RunProgramRequest::decode(bytes)?, emit)
    }

    /// Export the accumulated Program without recording this observation.
    pub fn get_history(&self, bytes: &[u8]) -> Result<Vec<u8>, TransportError> {
        let request = pb::GetHistoryRequest::decode(bytes)?;
        let history = self.histories.get(&request.egraph_id).ok_or_else(|| {
            TransportError(if self.graphs.contains_key(&request.egraph_id) {
                "history recording is disabled".into()
            } else {
                "unknown egraph_id".into()
            })
        })?;
        Ok(history.export().map_err(TransportError)?.encode_to_vec())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::protobuf::fixtures::Observed;

    fn recorded_engine() -> (Engine, u64) {
        let mut engine = Engine::default();
        let response = engine
            .create(
                &pb::CreateEGraphRequest {
                    record_history: true,
                    sorts: vec![pb::Sort {
                        kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
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
            .unwrap();
        (
            engine,
            pb::CreateEGraphResponse::decode(response.as_slice())
                .unwrap()
                .egraph_id,
        )
    }

    #[test]
    fn history_records_accepted_inputs_and_preserves_request_local_union_locations() {
        let (mut engine, id) = recorded_engine();
        let declaration = super::super::source::Source::new(None, "(sort E)")
            .unwrap()
            .next()
            .unwrap()
            .unwrap();
        engine
            .run(
                &pb::RunProgramRequest {
                    egraph_id: id,
                    program: Some(declaration),
                    diagnostics: false,
                }
                .encode_to_vec(),
            )
            .unwrap();
        let input = pb::Program {
            sorts: vec![pb::Sort {
                kind: Some(pb::sort::Kind::Eq("E".into())),
                ..Default::default()
            }],
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
        };
        for _ in 0..2 {
            let response = engine
                .run(
                    &pb::RunProgramRequest {
                        egraph_id: id,
                        program: Some(input.clone()),
                        diagnostics: false,
                    }
                    .encode_to_vec(),
                )
                .unwrap();
            assert_eq!(
                Observed::from_frames(
                    (response)
                        .iter()
                        .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap())
                )
                .error,
                None
            );
        }
        let before = engine.histories[&id].head.clone();
        let rejected = pb::Program {
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Term(99)),
                    ..Default::default()
                })),
                ..Default::default()
            }],
            ..Default::default()
        };
        let response = engine
            .run(
                &pb::RunProgramRequest {
                    egraph_id: id,
                    program: Some(rejected),
                    diagnostics: false,
                }
                .encode_to_vec(),
            )
            .unwrap();
        assert!(
            Observed::from_frames(
                (response)
                    .iter()
                    .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap())
            )
            .error
            .is_some()
        );
        assert!(Arc::ptr_eq(
            before.as_ref().unwrap(),
            engine.histories[&id].head.as_ref().unwrap()
        ));
        let failure = pb::Program {
            commands: ["stop", "unentered"]
                .into_iter()
                .map(|message| pb::Command {
                    kind: Some(pb::command::Kind::Action(pb::Action {
                        kind: Some(pb::action::Kind::Panic(message.into())),
                        ..Default::default()
                    })),
                    ..Default::default()
                })
                .collect(),
            ..Default::default()
        };
        let response = engine
            .run(
                &pb::RunProgramRequest {
                    egraph_id: id,
                    program: Some(failure),
                    diagnostics: false,
                }
                .encode_to_vec(),
            )
            .unwrap();
        assert!(
            Observed::from_frames(
                (response)
                    .iter()
                    .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap())
            )
            .error
            .is_some()
        );
        let bytes = engine
            .get_history(&pb::GetHistoryRequest { egraph_id: id }.encode_to_vec())
            .unwrap();
        let mut history = pb::Program::decode(bytes.as_slice()).unwrap();
        assert_eq!(history.commands.len(), 4);
        let roots: Vec<_> = history
            .commands
            .iter()
            .filter_map(|command| match &command.kind {
                Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Term(index)),
                    ..
                })) => Some(*index),
                _ => None,
            })
            .collect();
        assert_eq!(roots.len(), 2);
        assert_ne!(roots[0], roots[1]);
        assert!(history.declarations.is_empty());
        // Each accepted input retains its own self-declaring Eq arena root.
        assert_eq!(
            history
                .sorts
                .iter()
                .filter(|sort| matches!(&sort.kind, Some(pb::sort::Kind::Eq(name)) if name == "E"))
                .count(),
            4
        );
        engine.graphs[&id].prepare(&mut history).unwrap();
        assert_eq!(
            engine
                .get_history(&pb::GetHistoryRequest { egraph_id: id }.encode_to_vec())
                .unwrap(),
            bytes
        );
    }

    #[test]
    fn flattened_history_captures_names_before_later_binding_replacements() {
        let (mut engine, id) = recorded_engine();
        for text in [
            "(datatype E (N i64) (Goal i64) (Other i64)) (ruleset g) (rule ((N x)) ((Goal x)) :ruleset g) (N 1) (run g 1)",
            "(datatype E (N i64) (Goal i64) (Other i64)) (ruleset g) (rule ((N x)) ((Other x)) :ruleset g) (N 2) (run g 1) (check (Goal 1) (Other 2)) (fail (check (Goal 2)))",
        ] {
            for phase in super::super::source::Source::new(None, text).unwrap() {
                let frames = engine
                    .run(
                        &pb::RunProgramRequest {
                            egraph_id: id,
                            program: Some(phase.unwrap()),
                            diagnostics: false,
                        }
                        .encode_to_vec(),
                    )
                    .unwrap();
                let observed = Observed::from_frames(
                    frames
                        .iter()
                        .map(|frame| pb::RunProgramResponse::decode(frame.as_slice()).unwrap()),
                );
                assert_eq!(observed.error, None);
            }
        }
        let history = pb::Program::decode(
            engine
                .get_history(&pb::GetHistoryRequest { egraph_id: id }.encode_to_vec())
                .unwrap()
                .as_slice(),
        )
        .unwrap();
        assert_eq!(history.rulesets.len(), 1);
        assert!(
            super::super::command_tree(&history.commands)
                .filter_map(|command| {
                    if let Some(pb::command::Kind::Run(run)) = &command.kind {
                        Some(run)
                    } else {
                        None
                    }
                })
                .flat_map(|run| &run.rulesets)
                .all(|selection| matches!(
                    selection.kind,
                    Some(pb::ruleset_selection::Kind::Ruleset(_))
                ))
        );
        let (mut replay, fresh) = recorded_engine();
        let frames = replay
            .run(
                &pb::RunProgramRequest {
                    egraph_id: fresh,
                    program: Some(history),
                    diagnostics: false,
                }
                .encode_to_vec(),
            )
            .unwrap();
        assert_eq!(
            Observed::from_frames(
                frames
                    .iter()
                    .map(|frame| pb::RunProgramResponse::decode(frame.as_slice()).unwrap())
            )
            .error,
            None
        );
    }

    #[test]
    fn live_history_prefixes_share_and_release_with_clone_destroy_and_engine() {
        let (mut engine, id) = recorded_engine();
        engine
            .run(
                &pb::RunProgramRequest {
                    egraph_id: id,
                    program: Some(pb::Program::default()),
                    diagnostics: false,
                }
                .encode_to_vec(),
            )
            .unwrap();
        let prefix = Arc::downgrade(engine.histories[&id].head.as_ref().unwrap());
        for _ in 0..32 {
            let child = engine
                .clone_request(pb::CloneEGraphRequest { egraph_id: id })
                .unwrap()
                .egraph_id;
            assert!(Arc::ptr_eq(
                engine.histories[&id].head.as_ref().unwrap(),
                engine.histories[&child].head.as_ref().unwrap()
            ));
            engine
                .run(
                    &pb::RunProgramRequest {
                        egraph_id: child,
                        program: Some(pb::Program::default()),
                        diagnostics: false,
                    }
                    .encode_to_vec(),
                )
                .unwrap();
            let branch = Arc::downgrade(engine.histories[&child].head.as_ref().unwrap());
            engine
                .destroy_request(pb::DestroyEGraphRequest { egraph_id: child })
                .unwrap();
            assert!(branch.upgrade().is_none());
            assert_eq!(engine.histories.len(), 1);
            assert!(
                engine.histories[&id]
                    .head
                    .as_ref()
                    .unwrap()
                    .previous
                    .is_none()
            );
        }
        assert!(prefix.upgrade().is_some());
        let child = engine
            .clone_request(pb::CloneEGraphRequest { egraph_id: id })
            .unwrap()
            .egraph_id;
        engine
            .destroy_request(pb::DestroyEGraphRequest { egraph_id: id })
            .unwrap();
        assert!(
            engine
                .get_history(&pb::GetHistoryRequest { egraph_id: id }.encode_to_vec())
                .is_err()
        );
        assert!(
            engine
                .destroy_request(pb::DestroyEGraphRequest { egraph_id: id })
                .is_err()
        );
        assert_eq!(engine.histories.len(), 1);
        let history = engine
            .get_history(&pb::GetHistoryRequest { egraph_id: child }.encode_to_vec())
            .unwrap();
        assert_eq!(
            pb::Program::decode(history.as_slice()).unwrap(),
            pb::Program::default()
        );
        assert!(prefix.upgrade().is_some());
        drop(engine);
        assert!(prefix.upgrade().is_none());
    }
}
