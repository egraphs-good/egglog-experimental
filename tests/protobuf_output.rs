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
fn streamed_snapshots_and_restored_rules_keep_independent_authored_error_context() {
    let text = "(datatype E (N i64)) (ruleset boom) \
        (rule ((N e)) ((panic \"old-rule\")) :ruleset boom :name \"saved-label\") \
        (N 7) (extract (N 7)) (panic \"after export\")";
    let mut input = Source::new(Some("old.egg".into()), text)
        .unwrap()
        .next()
        .unwrap()
        .unwrap();
    input.rulesets[0].value.as_mut().unwrap().rules[0].doc = "rule docs".into();
    let panic = input.commands.pop().unwrap();
    input.commands.push(pb::Command {
        kind: Some(pb::command::Kind::Freeze(pb::Freeze {})),
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
    let Some(pb::rule::Kind::Rule(body)) = &rule.kind else {
        panic!("rule")
    };
    assert!(
        matches!(body.actions[0].kind, Some(pb::action::Kind::Panic(ref message)) if message == "old-rule")
    );
    let terminal = frames.last().unwrap();
    let Some(pb::run_program_response::Result::Error(error)) = &terminal.result else {
        panic!("late panic")
    };
    let context = error.context.as_ref().unwrap();
    assert_eq!(context.commands, [input.commands.last().unwrap().clone()]);
    assert_eq!(error.site.as_ref().unwrap().path, [5, 0, 1]);
    assert_eq!(input, original);
    let bytes = engine
        .get_history(&pb::GetHistoryRequest { egraph_id: id }.encode_to_vec())
        .unwrap();
    let history = pb::Program::decode(bytes.as_slice()).unwrap();
    assert_eq!(
        history.rulesets[0].value.as_ref().unwrap().rules[0].doc,
        "rule docs"
    );
    assert_eq!(
        history.rulesets[0].value.as_ref().unwrap().rules[0]
            .name
            .as_deref(),
        Some("saved-label")
    );

    let run = Source::new(Some("new.egg".into()), "(run-schedule boom)")
        .unwrap()
        .next()
        .unwrap()
        .unwrap();
    assert!(matches!(
        run.commands[0].kind,
        Some(pb::command::Kind::Run(_))
    ));
    let live = submit(&mut engine, id, run.clone()).pop().unwrap();
    let Some(pb::run_program_response::Result::Error(error)) = live.result else {
        panic!("saved panic")
    };
    let context = error.context.as_ref().unwrap();
    let rule = &context.rulesets[0].value.as_ref().unwrap().rules[0];
    assert_eq!(rule.name.as_deref(), Some("saved-label"));
    assert_eq!(rule.doc, "rule docs");
    assert_eq!(error.site.as_ref().unwrap().path, [7, 0, 2, 1, 0, 1, 3, 0]);
    assert!(
        context
            .constructors
            .iter()
            .any(|constructor| constructor.name == input.constructors[0].name)
    );
    let restored = create(&mut engine);
    assert!(
        submit(&mut engine, restored, snapshot)
            .iter()
            .all(|frame| matches!(
                frame.result,
                Some(pb::run_program_response::Result::Output(_))
            ))
    );
    let thawed = submit(&mut engine, restored, run).pop().unwrap();
    let Some(pb::run_program_response::Result::Error(restored_error)) = thawed.result else {
        panic!("restored saved panic")
    };
    let restored_context = restored_error.context.unwrap();
    let restored_rule = &restored_context.rulesets[0].value.as_ref().unwrap().rules[0];
    assert_eq!(restored_rule.name, rule.name);
    assert_eq!(restored_rule.doc, rule.doc);
    assert_eq!(
        restored_error.site.as_ref().unwrap().path,
        error.site.as_ref().unwrap().path
    );
    assert_eq!(restored_error.location, error.location);
}
