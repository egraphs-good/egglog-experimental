#[path = "common/protobuf.rs"]
mod fixture;
use egglog_experimental::{
    proto as pb,
    protobuf::{Engine, source::Source},
};
use fixture::Observed;
use prost::Message;
use std::ops::ControlFlow;

fn create(engine: &mut Engine, recording: bool) -> u64 {
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
        record_history: recording,
        ..Default::default()
    };
    pb::CreateEGraphResponse::decode(engine.create(&request.encode_to_vec()).unwrap().as_slice())
        .unwrap()
        .egraph_id
}

fn submit(engine: &mut Engine, id: u64, program: pb::Program, diagnostics: bool) -> Observed {
    let bytes = engine
        .run(
            &pb::RunProgramRequest {
                egraph_id: id,
                program: Some(program),
                diagnostics,
            }
            .encode_to_vec(),
        )
        .unwrap();
    Observed::from_frames(
        bytes
            .iter()
            .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()),
    )
}

fn seed(engine: &mut Engine, id: u64) {
    let text = "(datatype E (N i64)) (ruleset step) (rule ((N x) (< x 3)) ((N (+ x 1))) :ruleset step) (N 0)";
    for program in Source::new(None, text).unwrap() {
        assert_eq!(submit(engine, id, program.unwrap(), false).error, None);
    }
}

fn loop_program() -> pb::Program {
    pb::Program {
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
        commands: vec![
            pb::Command {
                kind: Some(pb::command::Kind::Loop(pb::Loop {
                    max_iterations: Some(3),
                    body: vec![
                        pb::Command {
                            kind: Some(pb::command::Kind::Run(pb::Run {
                                groups: vec!["step".into()],
                                ..Default::default()
                            })),
                            ..Default::default()
                        },
                        pb::Command {
                            kind: Some(pb::command::Kind::Freeze(pb::Freeze {})),
                            ..Default::default()
                        },
                    ],
                    ..Default::default()
                })),
                ..Default::default()
            },
            pb::Command {
                kind: Some(pb::command::Kind::Extract(pb::Extract {
                    roots: vec![0],
                    variants: 1,
                    extractor: pb::Extractor::Tree.into(),
                    ..Default::default()
                })),
                ..Default::default()
            },
            pb::Command {
                kind: Some(pb::command::Kind::Extract(pb::Extract {
                    roots: vec![0],
                    variants: 1,
                    extractor: pb::Extractor::Tree.into(),
                    ..Default::default()
                })),
                ..Default::default()
            },
        ],
        ..Default::default()
    }
}

fn census(engine: &mut Engine, id: u64) -> u64 {
    let response = submit(
        engine,
        id,
        pb::Program {
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::PrintSize(pb::PrintSize {
                    tables: vec!["N".into()],
                })),
                ..Default::default()
            }],
            ..Default::default()
        },
        false,
    );
    assert_eq!(response.error, None);
    let Some(pb::command_output::Kind::Sizes(sizes)) = &response.output.outputs[0].kind else {
        panic!("sizes")
    };
    sizes.sizes[0].rows
}

#[test]
fn streaming_snapshots_cancel_before_next_iteration_and_preserve_live_prefix() {
    let mut engine = Engine::default();
    let id = create(&mut engine, true);
    seed(&mut engine, id);
    let mut snapshots = 0;
    let error = engine
        .run_stream(
            &pb::RunProgramRequest {
                egraph_id: id,
                program: Some(loop_program()),
                diagnostics: false,
            }
            .encode_to_vec(),
            &mut |chunk| {
                let Some(pb::run_program_response::Result::Output(chunk)) = chunk.result else {
                    panic!("unexpected error frame")
                };
                let Some(pb::command_output::Kind::Snapshot(snapshot)) = &chunk.outputs[0].kind
                else {
                    panic!("first snapshot")
                };
                assert!(snapshot.program.is_some());
                snapshots += 1;
                ControlFlow::Break(())
            },
        )
        .unwrap_err();
    assert!(error.to_string().contains("cancelled"));
    assert_eq!(snapshots, 1);
    // A buffered implementation delivering after execution would have four rows.
    assert_eq!(census(&mut engine, id), 2);
    let history = pb::Program::decode(
        engine
            .get_history(&pb::GetHistoryRequest { egraph_id: id }.encode_to_vec())
            .unwrap()
            .as_slice(),
    )
    .unwrap();
    assert!(
        history
            .commands
            .iter()
            .any(|command| matches!(command.kind, Some(pb::command::Kind::Loop(_))))
    );
    // The same live graph remains usable; no completed control was fabricated.
    let response = submit(&mut engine, id, loop_program(), false);
    assert_eq!(response.error, None);
    assert_eq!(census(&mut engine, id), 4);
}

#[test]
fn streamed_frames_are_local_ordered_and_match_buffered_execution_exactly() {
    let mut engine = Engine::default();
    let id = create(&mut engine, false);
    seed(&mut engine, id);
    let clone = pb::CloneEGraphResponse::decode(
        engine
            .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
            .unwrap()
            .as_slice(),
    )
    .unwrap()
    .egraph_id;
    let mut frames = vec![];
    engine
        .run_stream(
            &pb::RunProgramRequest {
                egraph_id: id,
                program: Some(loop_program()),
                diagnostics: false,
            }
            .encode_to_vec(),
            &mut |frame| {
                frames.push(frame);
                ControlFlow::Continue(())
            },
        )
        .unwrap();
    assert!(
        matches!(&frames.last().unwrap().result,Some(pb::run_program_response::Result::Output(output)) if output.outputs.is_empty())
    );
    let mut iterations = vec![];
    let mut terms = vec![];
    for frame in &frames {
        let Some(pb::run_program_response::Result::Output(output)) = &frame.result else {
            panic!("unexpected error frame")
        };
        for command in &output.outputs {
            match &command.kind {
                Some(pb::command_output::Kind::Snapshot(_)) => {
                    iterations.push(command.location.as_ref().unwrap().iterations.clone())
                }
                Some(pb::command_output::Kind::Extraction(extraction)) => {
                    let variant = &extraction.roots[0].variants[0];
                    assert!((variant.term as usize) < output.nodes.len());
                    assert!((variant.cost.unwrap() as usize) < output.nodes.len());
                    assert!(
                        output
                            .nodes
                            .iter()
                            .all(|node| (node.sort_id as usize) < output.sorts.len())
                    );
                    terms.push(variant.term);
                }
                _ => (),
            }
        }
    }
    assert_eq!(iterations, [vec![0], vec![1], vec![2]]);
    assert_eq!(terms.len(), 2);
    assert_eq!(
        terms[0], terms[1],
        "each extraction owns a fresh local arena"
    );
    let buffered = engine
        .run(
            &pb::RunProgramRequest {
                egraph_id: clone,
                program: Some(loop_program()),
                diagnostics: false,
            }
            .encode_to_vec(),
        )
        .unwrap();
    assert_eq!(
        buffered,
        frames
            .iter()
            .map(Message::encode_to_vec)
            .collect::<Vec<_>>()
    );
}

#[test]
fn default_off_diagnostics_explain_and_opt_in_preserve_control_and_data() {
    let mut engine = Engine::default();
    let id = create(&mut engine, false);
    seed(&mut engine, id);
    let clone = pb::CloneEGraphResponse::decode(
        engine
            .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
            .unwrap()
            .as_slice(),
    )
    .unwrap()
    .egraph_id;
    let explained = submit(
        &mut engine,
        id,
        pb::Program {
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Explain(pb::Explain {
                    groups: vec!["step".into()],
                })),
                ..Default::default()
            }],
            ..Default::default()
        },
        false,
    );
    assert_eq!(explained.error, None);
    let Some(pb::command_output::Kind::Diagnostic(plan)) = &explained.output.outputs[0].kind else {
        panic!("plan")
    };
    assert_eq!(plan.format, "application/vnd.egglog.query-plan+json");
    assert!(
        !serde_json::from_slice::<serde_json::Value>(&plan.content)
            .unwrap()
            .as_array()
            .unwrap()
            .is_empty()
    );
    assert_eq!(census(&mut engine, id), 1);
    let off = submit(&mut engine, id, loop_program(), false);
    let on = submit(&mut engine, clone, loop_program(), true);
    assert_eq!(off.error, None);
    assert_eq!(on.error, None);
    let off_result = off
        .output
        .outputs
        .iter()
        .find(|output| matches!(output.kind, Some(pb::command_output::Kind::Run(_))))
        .unwrap();
    let on_result = on
        .output
        .outputs
        .iter()
        .find(|output| matches!(output.kind, Some(pb::command_output::Kind::Run(_))))
        .unwrap();
    assert_eq!(off_result, on_result);
    assert!(
        matches!(&off_result.kind, Some(pb::command_output::Kind::Run(result)) if result.updated && !result.can_stop)
    );
    let Some(pb::command_output::Kind::Diagnostic(diagnostic)) = &on
        .output
        .outputs
        .iter()
        .find(|output| matches!(output.kind, Some(pb::command_output::Kind::Diagnostic(_))))
        .unwrap()
        .kind
    else {
        panic!("diagnostic")
    };
    let detail: serde_json::Value = serde_json::from_slice(&diagnostic.content).unwrap();
    assert!(detail.get("updated").is_none() && detail.get("can_stop").is_none());
    assert!(!detail["iterations"].as_array().unwrap().is_empty());
    for (handle, collected) in [(id, false), (clone, true)] {
        let stats = submit(
            &mut engine,
            handle,
            pb::Program {
                commands: vec![pb::Command {
                    kind: Some(pb::command::Kind::Stats(pb::Unit {})),
                    ..Default::default()
                }],
                ..Default::default()
            },
            false,
        );
        let Some(pb::command_output::Kind::Diagnostic(diagnostic)) = &stats.output.outputs[0].kind
        else {
            panic!("stats")
        };
        let detail: serde_json::Value = serde_json::from_slice(&diagnostic.content).unwrap();
        assert_eq!(
            !detail["iterations"].as_array().unwrap().is_empty(),
            collected
        );
        assert_eq!(
            !detail["num_matches_per_rule"]
                .as_object()
                .unwrap()
                .is_empty(),
            collected
        );
        assert_eq!(census(&mut engine, handle), 4);
    }
}

#[test]
fn later_loop_failure_keeps_delivered_observation_and_has_no_completed_result() {
    let mut engine = Engine::default();
    let id = create(&mut engine, false);
    seed(&mut engine, id);
    let mut program = loop_program();
    program.commands.truncate(1);
    let Some(pb::command::Kind::Loop(repeat)) = &mut program.commands[0].kind else {
        unreachable!()
    };
    repeat.body.push(pb::Command {
        kind: Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Panic("stop after snapshot".into())),
            ..Default::default()
        })),
        ..Default::default()
    });
    let mut observed = 0;
    let mut final_error = None;
    engine
        .run_stream(
            &pb::RunProgramRequest {
                egraph_id: id,
                program: Some(program),
                diagnostics: false,
            }
            .encode_to_vec(),
            &mut |chunk| {
                match chunk.result.expect("frame result") {
                    pb::run_program_response::Result::Output(output) => {
                        for command in output.outputs {
                            assert!(matches!(
                                command.kind,
                                Some(pb::command_output::Kind::Snapshot(_))
                            ));
                            observed += 1;
                        }
                    }
                    pb::run_program_response::Result::Error(error) => final_error = Some(error),
                }
                ControlFlow::Continue(())
            },
        )
        .unwrap();
    assert_eq!(observed, 1);
    let error = final_error.unwrap();
    assert_eq!(error.code, pb::ErrorCode::RuntimeFailure as i32);
    assert_eq!(error.location.unwrap().iterations, [0]);
    assert_eq!(census(&mut engine, id), 2);
}

#[test]
fn backoff_quiet_deferred_rounds_preserve_readiness_with_collection_off_and_on() {
    let mut engine = Engine::default();
    let id = create(&mut engine, false);
    for program in Source::new(None,
        "(relation R (i64)) (relation S (i64)) (ruleset copy) (rule ((R x)) ((S x)) :ruleset copy) (R 1) (R 2) (let-scheduler bo (back-off :match-limit 1 :ban-length 1))",
    ).unwrap() {
        assert_eq!(submit(&mut engine, id, program.unwrap(), false).error, None);
    }
    let clone = pb::CloneEGraphResponse::decode(
        engine
            .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
            .unwrap()
            .as_slice(),
    )
    .unwrap()
    .egraph_id;
    let mut traces = vec![];
    for (handle, diagnostics) in [(id, false), (clone, true)] {
        let mut flags = vec![];
        loop {
            let response = submit(
                &mut engine,
                handle,
                pb::Program {
                    commands: vec![pb::Command {
                        kind: Some(pb::command::Kind::Run(pb::Run {
                            groups: vec!["copy".into()],
                            scheduler: "bo".into(),
                        })),
                        ..Default::default()
                    }],
                    ..Default::default()
                },
                diagnostics,
            );
            assert_eq!(response.error, None);
            let Some(pb::command_output::Kind::Run(result)) = response.output.outputs[0].kind
            else {
                panic!("RunResult")
            };
            assert_eq!(
                response.output.outputs.len(),
                if diagnostics { 2 } else { 1 }
            );
            flags.push((result.updated, result.can_stop));
            if result.can_stop {
                break;
            }
            assert!(flags.len() < 10);
        }
        assert_eq!(
            flags[0],
            (false, false),
            "quiet is not ready while matches are deferred"
        );
        assert!(flags.iter().any(|(updated, _)| *updated));
        traces.push(flags);
    }
    assert_eq!(traces[0], traces[1]);
}

#[test]
fn cancellation_stops_before_authored_fail_and_cannot_turn_into_caught_success() {
    let mut engine = Engine::default();
    let id = create(&mut engine, false);
    seed(&mut engine, id);
    let mut program = loop_program();
    program.commands.truncate(1);
    let Some(pb::command::Kind::Loop(repeat)) = &mut program.commands[0].kind else {
        unreachable!()
    };
    repeat.body.push(pb::Command {
        kind: Some(pb::command::Kind::Fail(Box::new(pb::Command {
            kind: Some(pb::command::Kind::Loop(pb::Loop {
                max_iterations: Some(3),
                body: repeat.body.clone(),
                ..Default::default()
            })),
            ..Default::default()
        }))),
        ..Default::default()
    });
    let mut delivered = 0;
    let error = engine
        .run_stream(
            &pb::RunProgramRequest {
                egraph_id: id,
                program: Some(program),
                diagnostics: false,
            }
            .encode_to_vec(),
            &mut |chunk| {
                let Some(pb::run_program_response::Result::Output(output)) = chunk.result else {
                    panic!("unexpected error frame")
                };
                delivered += output.outputs.len();
                ControlFlow::Break(())
            },
        )
        .unwrap_err();
    assert!(error.to_string().contains("cancelled"));
    assert_eq!(delivered, 1);
    assert_eq!(census(&mut engine, id), 2);
}

#[test]
fn terminal_callback_break_preserves_actual_errors_and_completed_success() {
    let mut engine = Engine::default();
    let id = create(&mut engine, false);
    for (program, expected) in [
        (None, Some(pb::ErrorCode::InvalidProgram)),
        (
            Some(pb::Program {
                nodes: vec![pb::Node::default()],
                ..Default::default()
            }),
            Some(pb::ErrorCode::InvalidProgram),
        ),
        (
            Some(pb::Program {
                commands: vec![pb::Command {
                    kind: Some(pb::command::Kind::Action(pb::Action {
                        kind: Some(pb::action::Kind::Panic("original engine failure".into())),
                        ..Default::default()
                    })),
                    ..Default::default()
                }],
                ..Default::default()
            }),
            Some(pb::ErrorCode::RuntimeFailure),
        ),
        (Some(pb::Program::default()), None),
    ] {
        let mut delivered = 0;
        let mut actual = None;
        engine
            .run_stream(
                &pb::RunProgramRequest {
                    egraph_id: id,
                    program,
                    diagnostics: false,
                }
                .encode_to_vec(),
                &mut |chunk| {
                    delivered += 1;
                    actual = match chunk.result.expect("frame result") {
                        pb::run_program_response::Result::Output(output) => {
                            assert!(output.outputs.is_empty());
                            None
                        }
                        pb::run_program_response::Result::Error(error) => Some(error),
                    };
                    ControlFlow::Break(())
                },
            )
            .unwrap();
        assert_eq!(delivered, 1);
        assert_eq!(actual.map(|error| error.code), expected.map(i32::from));
    }
}

#[test]
fn decomposed_diagnostics_keep_actual_text_and_preserve_execution() {
    let mut engine = Engine::default();
    let id = create(&mut engine, false);
    let text = "(relation R (i64 i64)) (relation S (i64 i64)) (relation T (i64 i64)) (relation U (i64 i64)) (relation Out (i64 i64))
        (ruleset chain) (rule ((R a b) (S b c) (T c d) (U d a)) ((Out a d)) :ruleset chain)
        (R 1 2) (S 2 3) (T 3 4) (U 4 1)";
    for program in Source::new(None, text).unwrap() {
        assert_eq!(submit(&mut engine, id, program.unwrap(), false).error, None);
    }
    let clone = pb::CloneEGraphResponse::decode(
        engine
            .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
            .unwrap()
            .as_slice(),
    )
    .unwrap()
    .egraph_id;
    let request = pb::Program {
        commands: vec![pb::Command {
            kind: Some(pb::command::Kind::Run(pb::Run {
                groups: vec!["chain".into()],
                ..Default::default()
            })),
            ..Default::default()
        }],
        ..Default::default()
    };
    let off = submit(&mut engine, id, request.clone(), false);
    let on = submit(&mut engine, clone, request, true);
    assert_eq!(off.error, None);
    assert_eq!(on.error, None);
    assert_eq!(off.output.outputs[0], on.output.outputs[0]);
    let Some(pb::command_output::Kind::Diagnostic(document)) = &on.output.outputs[1].kind else {
        panic!("diagnostic")
    };
    let detail: serde_json::Value = serde_json::from_slice(&document.content).unwrap();
    let mut fallback = false;
    for iteration in detail["iterations"].as_array().unwrap() {
        for reports in iteration["rule_set_report"]["rule_reports"]
            .as_object()
            .unwrap()
            .values()
        {
            for report in reports.as_array().unwrap() {
                if let Some(text) = report["plan"]
                    .get("text")
                    .and_then(serde_json::Value::as_str)
                {
                    assert!(!text.is_empty() && text.contains("SymbolMap"));
                    assert!(
                        report["plan"].get("stages").is_none(),
                        "unavailable structured stages must not look empty"
                    );
                    fallback = true;
                }
            }
        }
    }
    assert!(
        fallback,
        "fixture must exercise the actual decomposed-plan presentation"
    );
    for handle in [id, clone] {
        let result = submit(
            &mut engine,
            handle,
            pb::Program {
                commands: vec![pb::Command {
                    kind: Some(pb::command::Kind::PrintSize(pb::PrintSize {
                        tables: vec!["Out".into()],
                    })),
                    ..Default::default()
                }],
                ..Default::default()
            },
            false,
        );
        let Some(pb::command_output::Kind::Sizes(sizes)) = &result.output.outputs[0].kind else {
            panic!("Out rows")
        };
        assert_eq!(sizes.sizes[0].rows, 1);
    }
}
