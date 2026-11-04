//! Execution frames expose logical results, with source locations only on errors.
use super::{graph, pb};

/// Remove execution-result provenance without changing installed input metadata.
/// Every emitter, including partial and streamed output, uses this boundary.
pub(super) fn source_free_response(mut frame: pb::RunProgramResponse) -> pb::RunProgramResponse {
    let mut files = std::mem::take(&mut frame.files);
    match &mut frame.result {
        Some(pb::run_program_response::Result::Output(output)) => {
            for node in &mut output.nodes {
                node.span = None;
            }
            for sort in &mut output.sorts {
                sort.span = None;
            }
            for output in &mut output.outputs {
                if let Some(pb::command_output::Kind::Snapshot(snapshot)) = &mut output.kind
                    && let Some(program) = &mut snapshot.program
                {
                    source_free_program(program);
                }
            }
        }
        Some(pb::run_program_response::Result::Error(error)) => {
            let origin = error.span.take().and_then(|mut span| {
                let file = files.get(span.file as usize)?;
                if span.start > span.end
                    || file.contents.as_ref().is_some_and(|contents| {
                        !contents.is_char_boundary(span.start as usize)
                            || !contents.is_char_boundary(span.end as usize)
                    })
                {
                    return None;
                }
                let file = files.swap_remove(span.file as usize);
                span.file = 0;
                Some((span, file))
            });
            if let Some((span, file)) = origin {
                error.span = Some(span);
                frame.files.push(file);
            }
        }
        None => (),
    }
    frame
}

fn source_free_program(program: &mut pb::Program) {
    program.files.clear();
    // Deferred Lambda bodies use this same arena. Clearing every location also
    // covers unused saved code, shared children and cyclic reconstruction data.
    for node in &mut program.nodes {
        node.span = None;
    }
    for sort in &mut program.sorts {
        sort.span = None;
    }
    for declaration in &mut program.declarations {
        declaration.span = None;
    }
    for rule in graph::rules_mut(program) {
        rule.span = None;
        if let Some(pb::rule::Kind::Rule(body)) = &mut rule.kind {
            for action in &mut body.head {
                action.span = None;
            }
        }
    }
    let mut pending = program.commands.iter_mut().collect::<Vec<_>>();
    while let Some(command) = pending.pop() {
        command.span = None;
        match &mut command.kind {
            Some(pb::command::Kind::Action(action)) => action.span = None,
            Some(pb::command::Kind::Loop(body)) => pending.extend(&mut body.body),
            Some(pb::command::Kind::Fail(child)) => pending.push(child),
            _ => (),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn success_removes_sources_from_saved_code_and_nested_controls() {
        let mut program = super::super::source::Source::new(
            Some("saved.egg".into()),
            "(datatype E (C i64)) (ruleset g) \
             (rule ((C e)) ((C e)) :ruleset g :name \"authored label\") \
             (C 1) (run-schedule (repeat 0 (fail (run g))))",
        )
        .unwrap()
        .next()
        .unwrap()
        .unwrap();
        let span = program.sorts[0].span;
        let nominal = program
            .sorts
            .iter()
            .position(|sort| matches!(&sort.kind, Some(pb::sort::Kind::Eq(_))))
            .unwrap();
        program.sorts[nominal].doc = Some("sort documentation".into());
        program.declarations[0].doc = Some("constructor documentation".into());
        let Some(pb::declaration::Kind::Constructor(constructor)) =
            &mut program.declarations[0].kind
        else {
            panic!("constructor")
        };
        constructor.inputs[0].name = "e".into();
        for rule in graph::rules_mut(&mut program) {
            rule.doc = "rule documentation".into();
        }
        let scalar = program
            .sorts
            .iter()
            .position(|sort| {
                matches!(&sort.kind,
            Some(pb::sort::Kind::Primitive(value)) if value.name == "i64")
            })
            .unwrap() as u32;
        let function = program.sorts.len() as u32;
        program.sorts.push(pb::Sort {
            span,
            kind: Some(pb::sort::Kind::Func(pb::FuncSort {
                params: vec![scalar],
                result: scalar,
            })),
            ..Default::default()
        });
        let body = program.nodes.len() as u32;
        program.nodes.extend([
            pb::Node {
                span,
                sort_id: scalar,
                kind: Some(pb::node::Kind::Var("_0".into())),
            },
            pb::Node {
                span,
                sort_id: function,
                kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Lambda(pb::Lambda {
                        captures: vec![],
                        body,
                    })),
                })),
            },
        ]);
        let frame = source_free_response(pb::RunProgramResponse {
            files: program.files.clone(),
            result: Some(pb::run_program_response::Result::Output(
                pb::RunProgramOutput {
                    nodes: program.nodes.clone(),
                    sorts: program.sorts.clone(),
                    outputs: vec![pb::CommandOutput {
                        location: Some(pb::CommandLocation {
                            path: vec![2],
                            iterations: vec![],
                        }),
                        kind: Some(pb::command_output::Kind::Snapshot(pb::EGraphSnapshot {
                            program: Some(program.clone()),
                            ..Default::default()
                        })),
                    }],
                },
            )),
        });
        assert!(frame.files.is_empty());
        let Some(pb::run_program_response::Result::Output(output)) = frame.result else {
            panic!("success")
        };
        assert!(output.nodes.iter().all(|node| node.span.is_none()));
        assert!(output.sorts.iter().all(|sort| sort.span.is_none()));
        assert_eq!(output.outputs[0].location.as_ref().unwrap().path, [2]);
        let Some(pb::command_output::Kind::Snapshot(snapshot)) = &output.outputs[0].kind else {
            panic!("snapshot")
        };
        let clean = snapshot.program.as_ref().unwrap();
        assert!(clean.files.is_empty());
        assert!(clean.nodes.iter().all(|node| node.span.is_none()));
        assert!(clean.sorts.iter().all(|sort| sort.span.is_none()));
        assert!(
            clean
                .declarations
                .iter()
                .all(|declaration| declaration.span.is_none())
        );
        assert_eq!(clean.sorts[nominal].doc, program.sorts[nominal].doc);
        assert_eq!(clean.declarations[0].doc, program.declarations[0].doc);
        assert_eq!(clean.declarations[0].kind, program.declarations[0].kind);
        for (before, after) in program.nodes.iter().zip(&clean.nodes) {
            assert_eq!(before.kind, after.kind);
            assert_eq!(before.sort_id, after.sort_id);
        }
        let rules = graph::rules(clean).collect::<Vec<_>>();
        assert_eq!(rules.len(), 2);
        for rule in rules {
            assert!(rule.span.is_none());
            assert_eq!(rule.name.as_deref(), Some("authored label"));
            assert_eq!(rule.doc, "rule documentation");
            let Some(pb::rule::Kind::Rule(body)) = &rule.kind else {
                panic!("rule")
            };
            assert!(body.head.iter().all(|action| action.span.is_none()));
        }
        for command in super::super::command_tree(&clean.commands) {
            assert!(command.span.is_none());
            if let Some(pb::command::Kind::Action(action)) = &command.kind {
                assert!(action.span.is_none());
            }
        }
        assert!(super::super::command_tree(&clean.commands).any(|command|
            matches!(&command.kind, Some(pb::command::Kind::Loop(body)) if body.max_iterations == Some(0))));
        assert!(
            super::super::command_tree(&clean.commands)
                .any(|command| matches!(&command.kind, Some(pb::command::Kind::Fail(_))))
        );
        assert!(!program.files.is_empty());
        assert!(
            program.nodes[body as usize..]
                .iter()
                .all(|node| node.span.is_some())
        );
        assert!(
            program.rulesets[0].value.as_ref().unwrap().rules[0]
                .span
                .is_some()
        );
    }

    #[test]
    fn errors_retain_only_valid_referenced_sources_without_inventing_locations() {
        for (contents, position, valid) in [
            (Some("éabc"), Some((1, 2, 3)), true),
            (None, Some((1, u32::MAX, u32::MAX)), true),
            (Some("éabc"), None, false),
            (Some("éabc"), Some((9, 0, 1)), false),
            (Some("éabc"), Some((1, 4, 3)), false),
            (Some("éabc"), Some((1, 1, 2)), false),
            (Some("éabc"), Some((1, 2, 9)), false),
        ] {
            let selected = pb::SourceFile {
                name: "actual.egg".into(),
                contents: contents.map(str::to_owned),
            };
            let error = pb::Error {
                code: pb::ErrorCode::RuntimeFailure.into(),
                message: "actual failure".into(),
                span: position.map(|(file, start, end)| pb::Span { file, start, end }),
                location: Some(pb::CommandLocation {
                    path: vec![2, 1],
                    iterations: vec![3],
                }),
            };
            let frame = source_free_response(pb::RunProgramResponse {
                files: vec![
                    pb::SourceFile {
                        name: "unrelated.egg".into(),
                        contents: Some("other".into()),
                    },
                    selected.clone(),
                ],
                result: Some(pb::run_program_response::Result::Error(error.clone())),
            });
            let mut expected = error;
            expected.span = expected.span.filter(|_| valid).map(|mut span| {
                span.file = 0;
                span
            });
            assert_eq!(frame.files, if valid { vec![selected] } else { vec![] });
            assert_eq!(
                frame.result,
                Some(pb::run_program_response::Result::Error(expected))
            );
        }
    }
}
