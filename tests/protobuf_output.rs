use egglog_experimental::{proto as pb, protobuf::Engine, protobuf::source::Source};
use prost::Message;
use std::ops::ControlFlow;

fn create(engine: &mut Engine) -> u64 {
    let bytes = engine
        .create(
            &pb::CreateEGraphRequest {
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
                record_history: true,
                threads: Some(1),
                ..Default::default()
            }
            .encode_to_vec(),
        )
        .unwrap();
    pb::CreateEGraphResponse::decode(bytes.as_slice())
        .unwrap()
        .egraph_id
}

fn submit(
    engine: &mut Engine,
    egraph_id: u64,
    program: pb::Program,
) -> Vec<pb::RunProgramResponse> {
    let mut frames = vec![];
    engine
        .run_stream(
            &pb::RunProgramRequest {
                egraph_id,
                program: Some(program),
                diagnostics: false,
            }
            .encode_to_vec(),
            &mut |frame| {
                frames.push(frame);
                ControlFlow::Continue(())
            },
        )
        .unwrap();
    frames
}

#[test]
fn streamed_snapshots_drop_sources_while_live_rules_and_input_history_keep_them() {
    let text = "(datatype E (N i64)) (ruleset boom) \
        (rule ((N e)) ((panic \"old-rule\")) :ruleset boom :name \"saved-label\") \
        (N 7) (extract (N 7)) (panic \"after export\")";
    let mut input = Source::new(Some("old.egg".into()), text)
        .unwrap()
        .next()
        .unwrap()
        .unwrap();
    input.rulesets[0].value.as_mut().unwrap().rules[0].doc = "rule docs".into();
    input.files.push(pb::SourceFile {
        name: "unused.egg".into(),
        contents: Some("unrelated".into()),
    });
    let panic = input.commands.pop().unwrap();
    input.commands.push(pb::Command {
        kind: Some(pb::command::Kind::Freeze(pb::Freeze {})),
        ..Default::default()
    });
    input.commands.push(panic);
    let original = input.clone();
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let frames = submit(&mut engine, id, input.clone());
    let mut snapshot = None;
    let mut extractions = 0;
    for frame in &frames {
        if let Some(pb::run_program_response::Result::Output(output)) = &frame.result {
            assert!(frame.files.is_empty());
            assert!(output.nodes.iter().all(|node| node.span.is_none()));
            assert!(output.sorts.iter().all(|sort| sort.span.is_none()));
            for observation in &output.outputs {
                match &observation.kind {
                    Some(pb::command_output::Kind::Extraction(_)) => extractions += 1,
                    Some(pb::command_output::Kind::Snapshot(saved)) => {
                        snapshot = saved.program.clone()
                    }
                    _ => (),
                }
            }
        }
    }
    assert_eq!(extractions, 1, "prefix was delivered before the error");
    let snapshot = snapshot.unwrap();
    assert!(snapshot.files.is_empty());
    assert!(snapshot.nodes.iter().all(|node| node.span.is_none()));
    assert!(snapshot.sorts.iter().all(|sort| sort.span.is_none()));
    assert!(
        snapshot
            .declarations
            .iter()
            .all(|declaration| declaration.span.is_none())
    );
    let rule = &snapshot
        .rulesets
        .iter()
        .find(|group| group.name == "boom")
        .unwrap()
        .value
        .as_ref()
        .unwrap()
        .rules[0];
    assert_eq!(rule.name.as_deref(), Some("saved-label"));
    assert_eq!(rule.doc, "rule docs");
    assert!(rule.span.is_none());
    let Some(pb::rule::Kind::Rule(body)) = &rule.kind else {
        panic!("rule")
    };
    assert!(body.head.iter().all(|action| action.span.is_none()));
    let terminal = frames.last().unwrap();
    let Some(pb::run_program_response::Result::Error(error)) = &terminal.result else {
        panic!("late panic")
    };
    let span = error.span.unwrap();
    assert_eq!(span.file, 0);
    assert_eq!(terminal.files, [input.files[0].clone()]);
    assert!(text[span.start as usize..span.end as usize].contains("after export"));
    assert_eq!(input, original);
    let bytes = engine
        .get_history(&pb::GetHistoryRequest { egraph_id: id }.encode_to_vec())
        .unwrap();
    let history = pb::Program::decode(bytes.as_slice()).unwrap();
    assert!(history.files.contains(&input.files[0]));
    assert!(
        history.rulesets[0].value.as_ref().unwrap().rules[0]
            .span
            .is_some()
    );

    let mut run = Source::new(Some("new.egg".into()), "(run-schedule boom)")
        .unwrap()
        .next()
        .unwrap()
        .unwrap();
    assert!(matches!(
        run.commands[0].kind,
        Some(pb::command::Kind::Run(_))
    ));
    run.files.insert(0, input.files[1].clone());
    run.commands[0].span.as_mut().unwrap().file = 1;
    let mut new_span = run.commands[0].span.unwrap();
    new_span.file = 0;
    let live = submit(&mut engine, id, run.clone()).pop().unwrap();
    let Some(pb::run_program_response::Result::Error(error)) = live.result else {
        panic!("saved panic")
    };
    let span = error.span.unwrap();
    assert_eq!(span.file, 0);
    assert_eq!(live.files, [input.files[0].clone()]);
    assert!(text[span.start as usize..span.end as usize].contains("old-rule"));
    for located in [true, false] {
        let restored = create(&mut engine);
        assert!(
            submit(&mut engine, restored, snapshot.clone())
                .iter()
                .all(|frame| frame.files.is_empty()
                    && matches!(
                        frame.result,
                        Some(pb::run_program_response::Result::Output(_))
                    ))
        );
        if !located {
            run.files.clear();
            run.commands[0].span = None;
        }
        let thawed = submit(&mut engine, restored, run.clone()).pop().unwrap();
        let Some(pb::run_program_response::Result::Error(error)) = thawed.result else {
            panic!("restored saved panic")
        };
        if located {
            assert_eq!(thawed.files, [run.files[1].clone()]);
            assert_eq!(error.span, Some(new_span));
        } else {
            assert!(thawed.files.is_empty());
            assert!(error.span.is_none());
        }
    }
}
