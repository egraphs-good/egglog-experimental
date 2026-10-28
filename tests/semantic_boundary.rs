use egglog_experimental::{
    proto as pb,
    protobuf::{
        Engine, NativeExtension,
        source::{Renderer, Source},
    },
};
use prost::Message;
use std::{ops::ControlFlow, sync::Arc};

fn create(engine: &mut Engine, recording: bool) -> u64 {
    let bytes = engine
        .create(
            &pb::CreateEGraphRequest {
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
            }
            .encode_to_vec(),
        )
        .unwrap();
    pb::CreateEGraphResponse::decode(bytes.as_slice())
        .unwrap()
        .egraph_id
}

fn run(engine: &mut Engine, id: u64, program: pb::Program) -> Vec<pb::RunProgramResponse> {
    engine
        .run(
            &pb::RunProgramRequest {
                egraph_id: id,
                program: Some(program),
                diagnostics: false,
            }
            .encode_to_vec(),
        )
        .unwrap()
        .into_iter()
        .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap())
        .collect()
}

fn source(engine: &mut Engine, id: u64, text: &str) -> Vec<pb::RunProgramResponse> {
    Source::new(Some("input.egg".into()), text)
        .unwrap()
        .flat_map(|program| run(engine, id, program.unwrap()))
        .collect()
}

#[test]
fn builtins_are_backend_wide_and_absent_from_user_state_and_history() {
    let mut engine = Engine::default();
    let before = engine.get_builtins(&[]).unwrap();
    let catalog = pb::BuiltinCatalog::decode(before.as_slice()).unwrap();
    assert!(catalog.primitives.len() > 100);
    assert!(catalog.primitive_sorts.len() > 10);
    assert!(
        catalog
            .sorts
            .iter()
            .any(|sort| matches!(sort.kind, Some(pb::sort::Kind::Var(_))))
    );
    let id = create(&mut engine, true);
    let mut frames = source(
        &mut engine,
        id,
        "(primitive inc (i64) i64 (+ _0 1)) (function f () i64 :merge (+ old new)) (set (f) (inc 2)) (check (= (f) 3))",
    );
    frames.extend(run(
        &mut engine,
        id,
        pb::Program {
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Freeze(pb::Freeze {})),
                ..Default::default()
            }],
            ..Default::default()
        },
    ));
    assert!(frames.iter().all(|frame| matches!(
        frame.result,
        Some(pb::run_program_response::Result::Output(_))
    )));
    let snapshot = frames
        .iter()
        .filter_map(|frame| match &frame.result {
            Some(pb::run_program_response::Result::Output(output)) => Some(output),
            _ => None,
        })
        .flat_map(|output| &output.outputs)
        .find_map(|output| match &output.kind {
            Some(pb::command_output::Kind::Snapshot(snapshot)) => Some(snapshot),
            _ => None,
        })
        .unwrap();
    let restored = snapshot.program.as_ref().unwrap();
    assert_eq!(restored.declarations.len(), 2);
    assert!(restored.declarations.iter().any(|declaration| matches!(&declaration.kind, Some(pb::declaration::Kind::UserDefinedPrimitive(primitive)) if primitive.name == "inc")));
    assert!(
        restored
            .sorts
            .iter()
            .all(|sort| !matches!(sort.kind, Some(pb::sort::Kind::Var(_))))
    );
    let history = pb::Program::decode(
        engine
            .get_history(&pb::GetHistoryRequest { egraph_id: id }.encode_to_vec())
            .unwrap()
            .as_slice(),
    )
    .unwrap();
    assert_eq!(history.declarations.len(), 2);
    assert!(
        history
            .sorts
            .iter()
            .all(|sort| !matches!(sort.kind, Some(pb::sort::Kind::Var(_))))
    );
    assert_eq!(engine.get_builtins(&[]).unwrap(), before);
    let fresh = create(&mut engine, false);
    assert!(
        run(&mut engine, fresh, restored.clone())
            .iter()
            .all(|frame| matches!(
                frame.result,
                Some(pb::run_program_response::Result::Output(_))
            ))
    );
}

struct ComputedProvider;
impl NativeExtension for ComputedProvider {
    fn initialize(&self, graph: &mut egglog_experimental::EGraph) -> Result<(), String> {
        graph
            .parse_and_run_program(None, "(primitive configured_inc (i64) i64 (+ _0 1))")
            .map_err(|error| error.to_string())?;
        Ok(())
    }
    fn lower_custom_value(
        &self,
        _graph: &egglog_experimental::EGraph,
        _sort: &egglog_experimental::ArcSort,
        _value: &pb::CustomValue,
        _span: Option<pb::Span>,
        _destination: &mut pb::Program,
    ) -> Result<pb::Call, String> {
        Err("no custom values".into())
    }
}

#[test]
fn configured_computed_implementation_is_an_ambient_signature_not_a_user_body() {
    let extension: Arc<dyn NativeExtension> = Arc::new(ComputedProvider);
    let mut engine = Engine::with_extension(extension.clone());
    let bytes = engine.get_builtins(&[]).unwrap();
    let catalog = pb::BuiltinCatalog::decode(bytes.as_slice()).unwrap();
    let primitive = catalog
        .primitives
        .iter()
        .find(|primitive| primitive.name == "configured_inc")
        .unwrap();
    assert!(primitive.signature.is_some());
    let id = create(&mut engine, false);
    let mut renderer = Renderer::with_extension(extension.clone()).unwrap();
    for program in
        Source::with_extension(None, "(check (= (configured_inc 2) 3))", extension).unwrap()
    {
        let program = program.unwrap();
        assert!(program.declarations.is_empty());
        renderer.render(&program).unwrap();
        for frame in run(&mut engine, id, program) {
            let Some(pb::run_program_response::Result::Output(output)) = frame.result else {
                panic!("{frame:?}")
            };
            for output in output.outputs {
                if let Some(pb::command_output::Kind::Snapshot(snapshot)) = output.kind {
                    assert!(snapshot.program.unwrap().declarations.is_empty());
                }
            }
        }
    }
    let frozen = run(
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
    assert!(frozen.iter().all(|frame| matches!(
        frame.result,
        Some(pb::run_program_response::Result::Output(_))
    )));
}

#[test]
fn stream_and_buffer_preserve_prefix_before_exclusive_terminal_error() {
    let program = pb::Program {
        files: vec![pb::SourceFile {
            name: "prefix.egg".into(),
            contents: Some("panic".into()),
        }],
        sorts: ["i64", "Unit"]
            .into_iter()
            .map(|name| pb::Sort {
                kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                    name: name.into(),
                    args: vec![],
                })),
                ..Default::default()
            })
            .collect(),
        nodes: [2, 3]
            .into_iter()
            .enumerate()
            .flat_map(|(index, value)| {
                [
                    pb::Node {
                        kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                            value: Some(pb::primitive_value::Value::I64(value)),
                        })),
                        ..Default::default()
                    },
                    pb::Node {
                        sort_id: 1,
                        kind: Some(pb::node::Kind::Call(pb::Call {
                            func: "Row".into(),
                            args: vec![2 * index as u32],
                        })),
                        ..Default::default()
                    },
                ]
            })
            .collect(),
        commands: vec![
            pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Term(1)),
                    ..Default::default()
                })),
                ..Default::default()
            },
            pb::Command {
                kind: Some(pb::command::Kind::TableSizes(pb::GetTableSizes {
                    tables: vec!["Row".into()],
                })),
                ..Default::default()
            },
            pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Panic("stop".into())),
                    span: Some(pb::Span {
                        file: 0,
                        start: 0,
                        end: 5,
                    }),
                })),
                ..Default::default()
            },
            pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Term(3)),
                    ..Default::default()
                })),
                ..Default::default()
            },
        ],
        ..Default::default()
    };
    let mut buffered = Engine::default();
    let id = create(&mut buffered, false);
    source(&mut buffered, id, "(relation Row (i64)) (Row 1)");
    let frames = run(&mut buffered, id, program.clone());
    assert!(
        matches!(&frames.last().unwrap().result,Some(pb::run_program_response::Result::Error(error)) if error.code == pb::ErrorCode::RuntimeFailure as i32 && error.location.is_some()),
        "{frames:?}"
    );
    assert!(frames.iter().take(frames.len()-1).any(|frame| matches!(&frame.result,Some(pb::run_program_response::Result::Output(output)) if output.outputs.iter().any(|output| matches!(&output.kind,Some(pb::command_output::Kind::Sizes(sizes)) if sizes.sizes[0].rows==2)))));
    let mut streamed = Engine::default();
    let other = create(&mut streamed, false);
    source(&mut streamed, other, "(relation Row (i64)) (Row 1)");
    let mut observed = vec![];
    streamed
        .run_stream(
            &pb::RunProgramRequest {
                egraph_id: other,
                program: Some(program),
                diagnostics: false,
            }
            .encode_to_vec(),
            &mut |frame| {
                observed.push(frame);
                ControlFlow::Continue(())
            },
        )
        .unwrap();
    assert_eq!(observed, frames);
    let terminal = frames.last().unwrap();
    let Some(pb::run_program_response::Result::Error(error)) = &terminal.result else {
        unreachable!()
    };
    let span = error.span.unwrap();
    assert_eq!(
        terminal.files[span.file as usize]
            .contents
            .as_deref()
            .unwrap()
            .get(span.start as usize..span.end as usize),
        Some("panic")
    );
    let rejected = source(&mut buffered, id, "(relation Row (i64)) (check (Row 3))");
    assert!(
        matches!(&rejected.last().unwrap().result,Some(pb::run_program_response::Result::Error(error)) if error.code==pb::ErrorCode::CheckFailed as i32)
    );

    assert!(
        source(
            &mut buffered,
            id,
            "(relation Row (i64)) (check (Row 1)) (check (Row 2))"
        )
        .iter()
        .all(|frame| matches!(
            frame.result,
            Some(pb::run_program_response::Result::Output(_))
        ))
    );
}

#[test]
fn capped_loops_stop_quiet_observers_in_native_text_wire_and_rendered_text() {
    for header in [
        "(repeat 3 (print-size Row))",
        "(repeat () (times 3) (body (print-size Row)))",
        "(saturate () (max-iterations 3) (body (print-size Row)))",
    ] {
        let text = format!("(relation Row (i64)) (Row 1) (run-schedule {header})");
        let mut native = egglog_experimental::new_experimental_egraph();
        let native_outputs = native.parse_and_run_program(None, &text).unwrap();
        assert_eq!(
            native_outputs
                .iter()
                .filter(|output| matches!(
                    output,
                    egglog_experimental::CommandOutput::PrintFunctionSize(1)
                ))
                .count(),
            1,
            "{header}"
        );
        let mut engine = Engine::default();
        let id = create(&mut engine, false);
        let mut renderer = Renderer::default();
        let mut rendered = String::new();
        let mut count = 0;
        for program in Source::new(None, &text).unwrap() {
            let program = program.unwrap();
            rendered.push_str(&renderer.render(&program).unwrap());
            for frame in run(&mut engine, id, program) {
                let Some(pb::run_program_response::Result::Output(output)) = frame.result else {
                    panic!("{frame:?}")
                };
                count += output
                    .outputs
                    .iter()
                    .filter(|output| {
                        matches!(output.kind, Some(pb::command_output::Kind::Sizes(_)))
                    })
                    .count();
            }
        }
        assert_eq!(count, 1, "{header}");
        let mut replay = egglog_experimental::new_experimental_egraph();
        let outputs = replay.parse_and_run_program(None, &rendered).unwrap();
        assert_eq!(
            outputs
                .iter()
                .filter(|output| matches!(
                    output,
                    egglog_experimental::CommandOutput::PrintFunctionSize(1)
                ))
                .count(),
            1,
            "{rendered}"
        );
    }
}

#[test]
fn source_application_is_intrinsic_and_first_class_application_has_a_body() {
    let mut engine = Engine::default();
    let id = create(&mut engine, true);
    let text = r#"
        (sort F (UnstableFn (i64) i64))
        (primitive inc (i64) i64 (+ _0 1))
        (function selected () F :merge old)
        (set (selected) (unstable-fn "inc"))
        (check (= (unstable-app (selected) 2) 3))
        (let adapted (unstable-fn "unstable-app" (selected)))
        (check (= adapted (unstable-fn "unstable-app" (selected))))
        (check (= (unstable-app adapted 3) 4))
        (extract adapted)
    "#;
    let mut renderer = Renderer::default();
    let mut application = false;
    let mut adapter = false;
    for program in Source::new(None, text).unwrap() {
        let program = program.unwrap();
        application |= program
            .nodes
            .iter()
            .any(|node| matches!(node.kind, Some(pb::node::Kind::Apply(_))));
        adapter |= program.declarations.iter().any(|declaration| matches!(&declaration.kind, Some(pb::declaration::Kind::UserDefinedPrimitive(primitive)) if primitive.name.starts_with("__egglog_application_")));
        for node in &program.nodes {
            let name = match &node.kind {
                Some(pb::node::Kind::Call(call)) => &call.func,
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::PartialCall(call)),
                })) => &call.func,
                _ => continue,
            };
            assert_ne!(name, "egglog.core.fn.apply");
            assert_ne!(name, "unstable-app");
        }
        renderer.render(&program).unwrap();
        let frames = run(&mut engine, id, program);
        assert!(
            frames.iter().all(|frame| matches!(
                frame.result,
                Some(pb::run_program_response::Result::Output(_))
            )),
            "{frames:?}"
        );
    }
    assert!(application);
    assert!(adapter);
    let frames = run(
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
    let snapshot = frames
        .iter()
        .find_map(|frame| match &frame.result {
            Some(pb::run_program_response::Result::Output(output)) => {
                output.outputs.iter().find_map(|output| match &output.kind {
                    Some(pb::command_output::Kind::Snapshot(snapshot)) => snapshot.program.as_ref(),
                    _ => None,
                })
            }
            _ => None,
        })
        .unwrap();
    let fresh = create(&mut engine, false);
    let replay = run(&mut engine, fresh, snapshot.clone());
    assert!(
        replay.iter().all(|frame| matches!(
            frame.result,
            Some(pb::run_program_response::Result::Output(_))
        )),
        "{replay:?}"
    );
}

#[test]
fn named_application_is_rejected_before_history_admission() {
    let mut engine = Engine::default();
    let id = create(&mut engine, true);
    let frames = run(
        &mut engine,
        id,
        pb::Program {
            nodes: vec![pb::Node {
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "egglog.core.fn.apply".into(),
                    ..Default::default()
                })),
                ..Default::default()
            }],
            ..Default::default()
        },
    );
    assert!(frames.iter().any(|frame| matches!(&frame.result, Some(pb::run_program_response::Result::Error(error)) if error.message.contains("requires Apply"))), "{frames:?}");
    let history = pb::Program::decode(
        engine
            .get_history(&pb::GetHistoryRequest { egraph_id: id }.encode_to_vec())
            .unwrap()
            .as_slice(),
    )
    .unwrap();
    assert!(history.nodes.is_empty());
    assert!(history.commands.is_empty());
}
