use egglog_experimental::{new_experimental_egraph, protobuf::Engine};
use egglog_proto as pb;
use prost::Message;

fn fixture() -> pb::Program {
    use pb::{action, command, declaration, node, primitive_value, rule_decl, ruleset, sort};
    let int = |value| pb::Node {
        sort_id: 0,
        kind: Some(node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(primitive_value::Value::I64(value)),
        })),
        ..Default::default()
    };
    let call = |sort_id, func: &str, args| pb::Node {
        sort_id,
        kind: Some(node::Kind::Call(pb::Call {
            func: func.into(),
            args,
        })),
        ..Default::default()
    };
    let equality = |sort_id, members| pb::Node {
        sort_id,
        kind: Some(node::Kind::Union(pb::Union { members })),
        ..Default::default()
    };
    let set = |func: &str, value| pb::Command {
        kind: Some(command::Kind::Action(pb::Action {
            kind: Some(action::Kind::Set(pb::Set {
                target: Some(pb::Call {
                    func: func.into(),
                    args: vec![],
                }),
                value: Some(value),
            })),
            ..Default::default()
        })),
        ..Default::default()
    };
    let check = |facts| pb::Command {
        kind: Some(command::Kind::Check(pb::Check { facts })),
        ..Default::default()
    };
    pb::Program {
        ir_version: 1,
        sorts: vec![
            pb::Sort {
                kind: Some(sort::Kind::Family(pb::HostSort {
                    name: "i64".into(),
                    args: vec![],
                })),
                ..Default::default()
            },
            pb::Sort {
                kind: Some(sort::Kind::Eq("Math".into())),
                ..Default::default()
            },
        ],
        nodes: vec![
            int(10), // 0
            int(20), // 1
            int(30), // 2
            pb::Node {
                sort_id: 0,
                kind: Some(node::Kind::Var("new".into())),
                ..Default::default()
            }, // 3
            call(0, "current", vec![]), // 4
            call(0, "captured", vec![]), // 5
            call(1, "Num", vec![4]), // 6
            call(1, "Box", vec![6]), // 7
            pb::Node {
                sort_id: 1,
                kind: Some(node::Kind::Var("x".into())),
                ..Default::default()
            }, // 8
            call(1, "Box", vec![8]), // 9
            equality(0, vec![4, 1]), // 10
            equality(0, vec![5, 0]), // 11
            call(1, "Num", vec![1]), // 12
            equality(1, vec![7, 12]), // 13
        ],
        declarations: vec![
            pb::Declaration {
                kind: Some(declaration::Kind::EqSort(pb::EqSort {
                    name: "Math".into(),
                    ..Default::default()
                })),
                ..Default::default()
            },
            pb::Declaration {
                kind: Some(declaration::Kind::Constructor(pb::Constructor {
                    name: "Num".into(),
                    inputs: vec![pb::Arg {
                        sort: 0,
                        name: "n".into(),
                    }],
                    output: 1,
                    ..Default::default()
                })),
                ..Default::default()
            },
            pb::Declaration {
                kind: Some(declaration::Kind::Constructor(pb::Constructor {
                    name: "Box".into(),
                    inputs: vec![pb::Arg {
                        sort: 1,
                        name: "x".into(),
                    }],
                    output: 1,
                    ..Default::default()
                })),
                ..Default::default()
            },
            pb::Declaration {
                kind: Some(declaration::Kind::Function(pb::Function {
                    name: "current".into(),
                    output: 0,
                    merge: Some(3),
                    ..Default::default()
                })),
                ..Default::default()
            },
            pb::Declaration {
                kind: Some(declaration::Kind::Function(pb::Function {
                    name: "captured".into(),
                    output: 0,
                    ..Default::default()
                })),
                ..Default::default()
            },
        ],
        rules: vec![pb::RuleDecl {
            kind: Some(rule_decl::Kind::Rewrite(pb::Rewrite {
                lhs: 9,
                rhs: 8,
                ..Default::default()
            })),
            eval_mode: pb::RuleEvalMode::Seminaive.into(),
            name: Some("unbox".into()),
            ..Default::default()
        }],
        rulesets: vec![pb::Ruleset {
            name: Some("simplify".into()),
            kind: Some(ruleset::Kind::Rules(pb::RuleList { rules: vec![0] })),
            ..Default::default()
        }],
        commands: vec![
            set("current", 0),
            set("captured", 4),
            set("current", 1),
            check(vec![10, 11]),
            pb::Command {
                kind: Some(command::Kind::Action(pb::Action {
                    kind: Some(action::Kind::Term(7)),
                    ..Default::default()
                })),
                ..Default::default()
            },
            pb::Command {
                kind: Some(command::Kind::Run(pb::Run {
                    ruleset: Some(pb::RulesetRef {
                        kind: Some(pb::ruleset_ref::Kind::Index(0)),
                    }),
                    ..Default::default()
                })),
                ..Default::default()
            },
            check(vec![13]),
            pb::Command {
                kind: Some(command::Kind::Extract(pb::Extract {
                    roots: vec![7, 5, 7],
                    variants: 1,
                    extractor: pb::Extractor::Tree.into(),
                    ..Default::default()
                })),
                ..Default::default()
            },
            pb::Command {
                kind: Some(command::Kind::PrintFunction(pb::PrintFunction {
                    table: "current".into(),
                    max_rows: 10,
                })),
                ..Default::default()
            },
        ],
        ..Default::default()
    }
}

fn create(engine: &mut Engine) -> u64 {
    let request = pb::CreateEGraphRequest {
        sorts: fixture().sorts[..1].to_vec(),
        options: Some(pb::EGraphOptions { cost_sort: Some(0) }),
        ..Default::default()
    };
    let bytes = engine.create(&request.encode_to_vec()).unwrap();
    pb::CreateEGraphResponse::decode(bytes.as_slice())
        .unwrap()
        .egraph_id
}

fn run(engine: &mut Engine, egraph_id: u64, program: pb::Program) -> pb::RunProgramResponse {
    let bytes = engine
        .run(
            &pb::RunProgramRequest {
                egraph_id,
                program: Some(program),
                profile: true,
            }
            .encode_to_vec(),
        )
        .unwrap();
    pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()
}

fn value(response: &pb::RunProgramResponse, index: u32) -> String {
    match response.nodes[index as usize].kind.as_ref().unwrap() {
        pb::node::Kind::PrimitiveValue(value) => match value.value.as_ref().unwrap() {
            pb::primitive_value::Value::I64(n) => n.to_string(),
            other => panic!("unexpected value: {other:?}"),
        },
        pb::node::Kind::Call(call) => format!(
            "({} {})",
            call.func,
            call.args
                .iter()
                .map(|i| value(response, *i))
                .collect::<Vec<_>>()
                .join(" ")
        ),
        other => panic!("unexpected result node: {other:?}"),
    }
}

#[test]
fn decoded_program_matches_native_execution() {
    let mut native = new_experimental_egraph();
    let outputs = native
        .parse_and_run_program(
            None,
            r#"
        (datatype Math (Num i64) (Box Math))
        (function current () i64 :merge new)
        (function captured () i64 :no-merge)
        (ruleset simplify)
        (rewrite (Box x) x :ruleset simplify)
        (set (current) 10)
        (set (captured) (current))
        (set (current) 20)
        (check (= (current) 20) (= (captured) 10))
        (Box (Num (current)))
        (run simplify 1)
        (check (= (Box (Num 20)) (Num 20)))
        (extract (Box (Num (current))))
        (extract (captured))
    "#,
        )
        .unwrap();
    assert!(
        outputs
            .iter()
            .any(|out| out.to_string().contains("(Num 20)"))
    );

    let mut engine = Engine::default();
    let id = create(&mut engine);
    let response = run(&mut engine, id, fixture());
    assert_eq!(response.error, None);
    assert!(response.profile.as_ref().unwrap().complete);
    assert_eq!(response.outputs.len(), 3);
    assert_eq!(response.profile.as_ref().unwrap().runs.len(), 1);
    assert_eq!(response.profile.as_ref().unwrap().runs[0].invocations, 1);
    assert!(!response.profile.as_ref().unwrap().runs[0].rules.is_empty());
    let pb::command_output::Kind::Extraction(extracted) =
        response.outputs[1].kind.as_ref().unwrap()
    else {
        panic!("missing extraction")
    };
    assert_eq!(
        extracted
            .roots
            .iter()
            .map(|root| value(&response, root.variants[0].term))
            .collect::<Vec<_>>(),
        ["(Num 20)", "10", "(Num 20)"]
    );
    assert_eq!(
        extracted.roots[0].variants[0].term,
        extracted.roots[2].variants[0].term
    );
    let pb::command_output::Kind::PrintedFunction(table) =
        response.outputs[2].kind.as_ref().unwrap()
    else {
        panic!("missing table")
    };
    assert_eq!(table.rows.len(), 1);
    assert_eq!(value(&response, table.rows[0].output), "20");
}

#[test]
fn declared_node_sorts_are_checked_in_deferred_code() {
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut program = fixture();
    // Native inference would still accept `new` in the i64 merge body, but the
    // authored protobuf annotation incorrectly claims this variable is Math.
    program.nodes[3].sort_id = 1;
    let response = run(&mut engine, id, program);
    assert_eq!(
        response.error.unwrap().code,
        i32::from(pb::ErrorCode::InvalidProgram)
    );
    assert_eq!(run(&mut engine, id, fixture()).error, None);

    let id = create(&mut engine);
    let mut program = fixture();
    let rhs = program.nodes.len() as u32;
    program.nodes.push(pb::Node {
        sort_id: 0,
        kind: Some(pb::node::Kind::Var("x".into())),
        ..Default::default()
    });
    let Some(pb::rule_decl::Kind::Rewrite(rewrite)) = &mut program.rules[0].kind else {
        unreachable!()
    };
    rewrite.rhs = rhs;
    assert_eq!(
        run(&mut engine, id, program).error.unwrap().code,
        i32::from(pb::ErrorCode::InvalidProgram)
    );
}

#[test]
fn rule_head_annotations_cannot_be_retyped_by_native_inference() {
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut program = fixture();
    let variable = program.nodes.len() as u32;
    program.nodes.push(pb::Node {
        sort_id: 0,
        kind: Some(pb::node::Kind::Var("x".into())),
        ..Default::default()
    });
    let query = program.nodes.len() as u32;
    program.nodes.push(pb::Node {
        sort_id: 0,
        kind: Some(pb::node::Kind::Union(pb::Union {
            members: vec![4, variable],
        })),
        ..Default::default()
    });
    program.rules[0].kind = Some(pb::rule_decl::Kind::Rule(pb::Rule {
        query: vec![query],
        // Node 8 also spells x, but claims Math rather than the binder's i64.
        head: vec![pb::Action {
            kind: Some(pb::action::Kind::Set(pb::Set {
                target: Some(pb::Call {
                    func: "captured".into(),
                    args: vec![],
                }),
                value: Some(8),
            })),
            ..Default::default()
        }],
    }));
    assert_eq!(
        run(&mut engine, id, program).error.unwrap().code,
        i32::from(pb::ErrorCode::InvalidProgram)
    );
    assert_eq!(run(&mut engine, id, fixture()).error, None);
}

#[test]
fn creation_rejects_unresolved_sorts_and_profile_off_is_explicit() {
    let mut engine = Engine::default();
    let bad = pb::CreateEGraphRequest {
        sorts: fixture().sorts,
        options: Some(pb::EGraphOptions { cost_sort: Some(0) }),
        ..Default::default()
    };
    assert!(engine.create(&bad.encode_to_vec()).is_err());
    let id = create(&mut engine);
    let bytes = engine
        .run(
            &pb::RunProgramRequest {
                egraph_id: id,
                program: Some(fixture()),
                profile: false,
            }
            .encode_to_vec(),
        )
        .unwrap();
    let response = pb::RunProgramResponse::decode(bytes.as_slice()).unwrap();
    assert!(response.error.unwrap().message.contains("profile=false"));
    assert_eq!(response.profile, None);
    assert_eq!(run(&mut engine, id, fixture()).error, None);
}

#[test]
fn malformed_bytes_and_invalid_programs_do_not_mutate() {
    let mut engine = Engine::default();
    let id = create(&mut engine);
    assert!(engine.run(&[0xff]).is_err());
    let valid = pb::RunProgramRequest {
        egraph_id: id,
        program: Some(fixture()),
        profile: true,
    }
    .encode_to_vec();
    // A complete program prefix must not run if the last field is truncated.
    assert!(engine.run(&valid[..valid.len() - 1]).is_err());
    let mut program = fixture();
    program.nodes[0].sort_id = 999;
    let response = run(&mut engine, id, program);
    assert_eq!(
        response.error.unwrap().code,
        i32::from(pb::ErrorCode::InvalidProgram)
    );
    // Definitions from the rejected request must not have been installed.
    assert_eq!(run(&mut engine, id, fixture()).error, None);
}

#[test]
fn unavailable_extraction_is_distinct_from_failed_table_extraction() {
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut program = fixture();
    let Some(pb::declaration::Kind::Constructor(constructor)) = &mut program.declarations[1].kind
    else {
        unreachable!()
    };
    constructor.unextractable = true;
    program.commands.push(pb::Command {
        kind: Some(pb::command::Kind::PrintFunction(pb::PrintFunction {
            table: "Num".into(),
            max_rows: 0,
        })),
        ..Default::default()
    });
    program.commands.push(program.commands[0].clone());
    let response = run(&mut engine, id, program);
    assert_eq!(
        response.error.as_ref().unwrap().code,
        i32::from(pb::ErrorCode::ExtractionFailed)
    );
    assert_eq!(response.outputs.len(), 3);
    let Some(pb::command_output::Kind::Extraction(extract)) = &response.outputs[1].kind else {
        unreachable!()
    };
    assert!(extract.roots[0].variants.is_empty());
    assert_eq!(value(&response, extract.roots[1].variants[0].term), "10");
    assert!(extract.roots[2].variants.is_empty());
    assert!(!response.profile.unwrap().complete);
}

#[test]
fn panic_preserves_action_source_location() {
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut program = fixture();
    program.files.push(pb::SourceFile {
        name: "fixture.egg".into(),
        contents: Some("(panic \"stop\")".into()),
    });
    let action_span = pb::Span {
        file: 0,
        start: 0,
        end: 14,
    };
    program.commands.push(pb::Command {
        kind: Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Panic("stop".into())),
            span: Some(action_span),
        })),
        ..Default::default()
    });
    let response = run(&mut engine, id, program);
    let error = response.error.unwrap();
    assert_eq!(error.code, i32::from(pb::ErrorCode::Panic));
    assert_eq!(error.span, Some(action_span));
    assert_eq!(error.location.unwrap().path, [9]);
    assert_eq!(response.outputs.len(), 3);
}

#[test]
fn action_union_is_rejected_until_identity_is_preserved() {
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut program = fixture();
    program.commands.push(pb::Command {
        kind: Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Term(13)),
            ..Default::default()
        })),
        ..Default::default()
    });
    assert_eq!(
        run(&mut engine, id, program).error.unwrap().code,
        i32::from(pb::ErrorCode::InvalidProgram)
    );
    assert_eq!(run(&mut engine, id, fixture()).error, None);
}

#[test]
fn self_referencing_merge_is_rejected_before_native_installation() {
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut program = fixture();
    let merge = program.nodes.len() as u32;
    program.nodes.push(pb::Node {
        sort_id: 0,
        kind: Some(pb::node::Kind::Call(pb::Call {
            func: "recursive".into(),
            args: vec![],
        })),
        ..Default::default()
    });
    program.declarations.push(pb::Declaration {
        kind: Some(pb::declaration::Kind::Function(pb::Function {
            name: "recursive".into(),
            output: 0,
            merge: Some(merge),
            ..Default::default()
        })),
        ..Default::default()
    });
    assert_eq!(
        run(&mut engine, id, program).error.unwrap().code,
        i32::from(pb::ErrorCode::InvalidProgram)
    );
    assert_eq!(run(&mut engine, id, fixture()).error, None);
}

#[test]
fn invalid_function_subsumption_does_not_install_or_mutate() {
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut program = fixture();
    program.commands.push(pb::Command {
        kind: Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Subsume(pb::Call {
                func: "current".into(),
                args: vec![],
            })),
            ..Default::default()
        })),
        ..Default::default()
    });
    assert_eq!(
        run(&mut engine, id, program).error.unwrap().code,
        i32::from(pb::ErrorCode::InvalidProgram)
    );
    assert_eq!(run(&mut engine, id, fixture()).error, None);
}

#[test]
fn merge_constructor_declarations_are_order_independent() {
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut program = fixture();
    let old = program.nodes.len() as u32;
    program.nodes.push(pb::Node {
        sort_id: 1,
        kind: Some(pb::node::Kind::Var("old".into())),
        ..Default::default()
    });
    let new = program.nodes.len() as u32;
    program.nodes.push(pb::Node {
        sort_id: 1,
        kind: Some(pb::node::Kind::Var("new".into())),
        ..Default::default()
    });
    let merge = program.nodes.len() as u32;
    program.nodes.push(pb::Node {
        sort_id: 1,
        kind: Some(pb::node::Kind::Call(pb::Call {
            func: "Pair".into(),
            args: vec![old, new],
        })),
        ..Default::default()
    });
    program.declarations.push(pb::Declaration {
        kind: Some(pb::declaration::Kind::Function(pb::Function {
            name: "join".into(),
            output: 1,
            merge: Some(merge),
            ..Default::default()
        })),
        ..Default::default()
    });
    program.declarations.push(pb::Declaration {
        kind: Some(pb::declaration::Kind::Constructor(pb::Constructor {
            name: "Pair".into(),
            inputs: vec![
                pb::Arg {
                    sort: 1,
                    name: "left".into(),
                },
                pb::Arg {
                    sort: 1,
                    name: "right".into(),
                },
            ],
            output: 1,
            ..Default::default()
        })),
        ..Default::default()
    });
    assert_eq!(run(&mut engine, id, program).error, None);
}

#[test]
fn shared_syntax_expansion_has_a_bounded_failure() {
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut program = fixture();
    program.declarations.push(pb::Declaration {
        kind: Some(pb::declaration::Kind::Constructor(pb::Constructor {
            name: "Pair".into(),
            inputs: vec![
                pb::Arg {
                    sort: 1,
                    name: "left".into(),
                },
                pb::Arg {
                    sort: 1,
                    name: "right".into(),
                },
            ],
            output: 1,
            ..Default::default()
        })),
        ..Default::default()
    });
    let mut child = 12;
    for _ in 0..18 {
        let index = program.nodes.len() as u32;
        program.nodes.push(pb::Node {
            sort_id: 1,
            kind: Some(pb::node::Kind::Call(pb::Call {
                func: "Pair".into(),
                args: vec![child, child],
            })),
            ..Default::default()
        });
        child = index;
    }
    let response = run(&mut engine, id, program);
    assert_eq!(
        response.error.unwrap().code,
        i32::from(pb::ErrorCode::InvalidProgram)
    );
    assert_eq!(run(&mut engine, id, fixture()).error, None);
}

#[test]
fn unknown_observation_and_ruleset_names_have_structured_errors() {
    let mut engine = Engine::default();
    for kind in [
        pb::command::Kind::PrintFunction(pb::PrintFunction {
            table: "missing".into(),
            max_rows: 0,
        }),
        pb::command::Kind::Run(pb::Run {
            ruleset: Some(pb::RulesetRef {
                kind: Some(pb::ruleset_ref::Kind::Name("missing".into())),
            }),
            ..Default::default()
        }),
    ] {
        let id = create(&mut engine);
        let mut program = fixture();
        program.commands.push(pb::Command {
            kind: Some(kind),
            ..Default::default()
        });
        let response = run(&mut engine, id, program);
        let error = response.error.unwrap();
        assert_eq!(error.code, i32::from(pb::ErrorCode::UnknownName));
        assert!(error.location.is_none()); // rejected before command execution
        assert!(response.outputs.is_empty());
        assert_eq!(run(&mut engine, id, fixture()).error, None);
    }
}

#[test]
fn unused_subsuming_rewrite_still_requires_a_constructor_target() {
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut program = fixture();
    program.declarations.push(pb::Declaration {
        kind: Some(pb::declaration::Kind::Function(pb::Function {
            name: "f".into(),
            inputs: vec![pb::Arg {
                sort: 1,
                name: "x".into(),
            }],
            output: 1,
            ..Default::default()
        })),
        ..Default::default()
    });
    let lhs = program.nodes.len() as u32;
    program.nodes.push(pb::Node {
        sort_id: 1,
        kind: Some(pb::node::Kind::Call(pb::Call {
            func: "f".into(),
            args: vec![8],
        })),
        ..Default::default()
    });
    program.rules.push(pb::RuleDecl {
        kind: Some(pb::rule_decl::Kind::Rewrite(pb::Rewrite {
            lhs,
            rhs: 8,
            subsume: true,
            ..Default::default()
        })),
        eval_mode: pb::RuleEvalMode::Seminaive.into(),
        ..Default::default()
    });
    assert_eq!(
        run(&mut engine, id, program).error.unwrap().code,
        i32::from(pb::ErrorCode::InvalidProgram)
    );
    assert_eq!(run(&mut engine, id, fixture()).error, None);
}

#[test]
fn extraction_configuration_errors_are_classified_without_execution() {
    let mut engine = Engine::default();
    for (extractor, cost_model, expected) in [
        (
            pb::Extractor::Unspecified,
            "",
            pb::ErrorCode::InvalidProgram,
        ),
        (
            pb::Extractor::GreedyDag,
            "",
            pb::ErrorCode::ExtractionFailed,
        ),
        (pb::Extractor::Tree, "missing", pb::ErrorCode::UnknownName),
    ] {
        let id = create(&mut engine);
        let mut program = fixture();
        let Some(pb::command::Kind::Extract(extract)) = &mut program.commands[7].kind else {
            unreachable!()
        };
        extract.extractor = extractor.into();
        extract.cost_model = cost_model.into();
        assert_eq!(
            run(&mut engine, id, program).error.unwrap().code,
            i32::from(expected)
        );
        assert_eq!(run(&mut engine, id, fixture()).error, None);
    }
}

#[test]
fn failure_keeps_completed_outputs_and_effects_and_clone_is_independent() {
    let mut engine = Engine::default();
    let id = create(&mut engine);
    assert_eq!(run(&mut engine, id, fixture()).error, None);
    let clone = pb::CloneEGraphResponse::decode(
        engine
            .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
            .unwrap()
            .as_slice(),
    )
    .unwrap()
    .egraph_id;
    let mut program = fixture();
    program.declarations.clear();
    program.rules.clear();
    program.rulesets.clear();
    program.commands = vec![
        program.commands[8].clone(),
        program.commands[0].clone(),
        program.commands[3].clone(),
        program.commands[2].clone(),
    ];
    let response = run(&mut engine, id, program);
    let error = response.error.unwrap();
    assert_eq!(error.code, i32::from(pb::ErrorCode::CheckFailed));
    assert_eq!(error.location.unwrap().path, [2]);
    assert_eq!(response.outputs.len(), 1);
    assert!(!response.profile.unwrap().complete);

    let mut observe = fixture();
    observe.declarations.clear();
    observe.rules.clear();
    observe.rulesets.clear();
    observe.commands = vec![observe.commands[8].clone()];
    for (handle, expected) in [(id, "10"), (clone, "20")] {
        let response = run(&mut engine, handle, observe.clone());
        let pb::command_output::Kind::PrintedFunction(table) =
            response.outputs[0].kind.as_ref().unwrap()
        else {
            panic!("missing table")
        };
        assert_eq!(value(&response, table.rows[0].output), expected);
    }
    let destroyed = engine
        .destroy(&pb::DestroyEGraphRequest { egraph_id: clone }.encode_to_vec())
        .unwrap();
    pb::DestroyEGraphResponse::decode(destroyed.as_slice()).unwrap();
    assert!(
        engine
            .run(
                &pb::RunProgramRequest {
                    egraph_id: clone,
                    program: Some(observe),
                    profile: true
                }
                .encode_to_vec()
            )
            .is_err()
    );
}
