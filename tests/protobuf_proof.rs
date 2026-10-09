use egglog_experimental::proto as pb;
use egglog_experimental::protobuf::{
    Engine,
    source::{Renderer, Source},
};
use prost::Message;

fn create(engine: &mut Engine, mode: pb::ExecutionMode) -> u64 {
    let bytes = engine
        .create(
            &pb::CreateEGraphRequest {
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
                }),
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

fn run(engine: &mut Engine, id: u64, program: pb::Program) -> pb::RunProgramResponse {
    let bytes = engine
        .run(
            &pb::RunProgramRequest {
                egraph_id: id,
                program: Some(program),
                profile: true,
            }
            .encode_to_vec(),
        )
        .unwrap();
    let response = pb::RunProgramResponse::decode(bytes.as_slice()).unwrap();
    assert_eq!(response.encode_to_vec(), bytes);
    response
}

// Hand-authored wire IR, independent of the Source producer. N and Goal share
// an equality sort; only a rule derives Goal, avoiding fiat-only proof roots.
fn fixture() -> pb::Program {
    let int = |n| pb::Node {
        sort_id: 0,
        kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::I64(n)),
        })),
        ..Default::default()
    };
    let call = |name: &str, args| pb::Node {
        sort_id: 1,
        kind: Some(pb::node::Kind::Call(pb::Call {
            func: name.into(),
            args,
        })),
        ..Default::default()
    };
    let mut declarations = vec![pb::Declaration {
        kind: Some(pb::declaration::Kind::EqSort(pb::EqSort {
            name: "Num".into(),
            ..Default::default()
        })),
        ..Default::default()
    }];
    for name in ["N", "Goal", "Absent"] {
        declarations.push(pb::Declaration {
            kind: Some(pb::declaration::Kind::Constructor(pb::Constructor {
                name: name.into(),
                inputs: vec![pb::Arg {
                    name: "x".into(),
                    sort: 0,
                }],
                output: 1,
                ..Default::default()
            })),
            ..Default::default()
        });
    }
    pb::Program {
        ir_version: 1,
        sorts: vec![
            pb::Sort {
                kind: Some(pb::sort::Kind::Family(pb::HostSort {
                    name: "i64".into(),
                    args: vec![],
                })),
                ..Default::default()
            },
            pb::Sort {
                kind: Some(pb::sort::Kind::Eq("Num".into())),
                ..Default::default()
            },
        ],
        declarations,
        nodes: vec![
            int(1),
            pb::Node {
                sort_id: 0,
                kind: Some(pb::node::Kind::Var("x".into())),
                ..Default::default()
            },
            call("N", vec![0]),
            call("N", vec![1]),
            call("Goal", vec![1]),
            call("Goal", vec![0]),
            int(2),
            call("N", vec![6]),
            int(3),
            call("N", vec![8]),
        ],
        rules: vec![pb::RuleDecl {
            name: Some("derive".into()),
            eval_mode: pb::RuleEvalMode::Seminaive.into(),
            kind: Some(pb::rule_decl::Kind::Rule(pb::Rule {
                query: vec![3],
                head: vec![pb::Action {
                    kind: Some(pb::action::Kind::Term(4)),
                    ..Default::default()
                }],
            })),
            ..Default::default()
        }],
        rulesets: vec![pb::Ruleset {
            name: Some("rebuilding_ruleset".into()),
            kind: Some(pb::ruleset::Kind::Rules(pb::RuleList { rules: vec![0] })),
            ..Default::default()
        }],
        commands: vec![
            pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Term(2)),
                    ..Default::default()
                })),
                ..Default::default()
            },
            pb::Command {
                kind: Some(pb::command::Kind::Run(pb::Run {
                    ruleset: Some(pb::RulesetRef {
                        kind: Some(pb::ruleset_ref::Kind::Index(0)),
                    }),
                    ..Default::default()
                })),
                ..Default::default()
            },
            pb::Command {
                kind: Some(pb::command::Kind::Check(pb::Check { facts: vec![5] })),
                ..Default::default()
            },
            pb::Command {
                kind: Some(pb::command::Kind::Prove(pb::Prove { facts: vec![5] })),
                ..Default::default()
            },
            pb::Command {
                kind: Some(pb::command::Kind::ProveExists(pb::ProveExists {
                    constructor: "Goal".into(),
                })),
                ..Default::default()
            },
        ],
        ..Default::default()
    }
}

#[test]
fn all_modes_return_only_requested_outputs_and_exclusive_profiles() {
    for mode in [
        pb::ExecutionMode::Normal,
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ] {
        let mut engine = Engine::default();
        let id = create(&mut engine, mode);
        let mut program = fixture();
        // The wire namespaces may share a spelling, unlike native source.
        let Some(pb::declaration::Kind::Constructor(constructor)) =
            &mut program.declarations[1].kind
        else {
            unreachable!()
        };
        constructor.name = "Num".into();
        for node in &mut program.nodes {
            if let Some(pb::node::Kind::Call(call)) = &mut node.kind
                && call.func == "N"
            {
                call.func = "Num".into();
            }
        }
        let response = run(&mut engine, id, program);
        let profile = response.profile.as_ref().unwrap();
        assert_eq!(profile.runs.len(), 1);
        assert_eq!(profile.runs[0].command_path, [1]);
        assert_eq!(profile.runs[0].invocations, 1);
        assert!(profile.runs[0].search_and_apply_nanos.is_some());
        assert!(profile.runs[0].merge_nanos.is_some());
        assert!(profile.runs[0].rebuild_nanos.is_some());
        let Some(pb::command_output::Kind::Run(outcome)) = &response.outputs[0].kind else {
            panic!("requested run")
        };
        assert!(outcome.updated);
        assert!(!outcome.can_stop);
        let paths: Vec<_> = response
            .outputs
            .iter()
            .map(|output| output.location.as_ref().unwrap().path.clone())
            .collect();
        if matches!(
            mode,
            pb::ExecutionMode::Normal | pb::ExecutionMode::TermEncoding
        ) {
            assert_eq!(paths, [vec![1]]);
            let error = response.error.unwrap();
            assert_eq!(error.code, i32::from(pb::ErrorCode::ProofFailed));
            assert_eq!(
                error.proof_failure.unwrap().reason,
                i32::from(pb::ProofFailureReason::ProofsNotEnabled)
            );
            assert_eq!(error.location.unwrap().path, [3]);
            assert!(!profile.complete);
        } else {
            assert_eq!(response.error, None);
            assert!(profile.complete);
            assert_eq!(
                paths,
                if mode == pb::ExecutionMode::ProofTesting {
                    vec![vec![1], vec![2], vec![3], vec![4]]
                } else {
                    vec![vec![1], vec![3], vec![4]]
                }
            );
            for output in response.outputs.iter().skip(1) {
                let Some(pb::command_output::Kind::Proof(proof)) = &output.kind else {
                    panic!("proof only")
                };
                assert!(proof.root.is_some());
                assert!(!proof.proofs.is_empty());
                assert!(!proof.terms.is_empty());
            }
        }
        if mode != pb::ExecutionMode::Normal {
            assert!(response.rules.is_empty()); // no guessed transformed rule counts
            assert!(profile.runs[0].rules.is_empty());
            for index in [1, 3] {
                let site = Some(pb::MaintenanceSite {
                    target: Some(pb::maintenance_site::Target::Command(
                        pb::StaticCommandPath { path: vec![index] },
                    )),
                });
                let maintenance = profile.maintenance.iter().find(|m| m.site == site).unwrap();
                assert!(maintenance.invocations > 1);
                assert!(maintenance.search_and_apply_nanos.is_some());
            }
            assert!(profile.maintenance.iter().any(|m| matches!(
                m.site.as_ref().and_then(|s| s.target.as_ref()),
                Some(pb::maintenance_site::Target::Ruleset(0))
            )));
        }
    }
}

#[test]
fn proof_failure_preserves_owned_prefix_clone_mode_and_native_error_order() {
    for mode in [
        pb::ExecutionMode::Normal,
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ] {
        let mut engine = Engine::default();
        let id = create(&mut engine, mode);
        let mut setup = fixture();
        setup.commands.truncate(3);
        assert_eq!(run(&mut engine, id, setup).error, None);
        let cloned = engine
            .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
            .unwrap();
        let clone = pb::CloneEGraphResponse::decode(cloned.as_slice())
            .unwrap()
            .egraph_id;
        let mut program = fixture();
        program.declarations.clear();
        program.rules.clear();
        program.rulesets.clear();
        program.commands = vec![
            pb::Command {
                kind: Some(pb::command::Kind::ProveExists(pb::ProveExists {
                    constructor: "Goal".into(),
                })),
                ..Default::default()
            },
            pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Term(7)),
                    ..Default::default()
                })),
                ..Default::default()
            },
            pb::Command {
                kind: Some(pb::command::Kind::ProveExists(pb::ProveExists {
                    constructor: "Absent".into(),
                })),
                ..Default::default()
            },
            pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Term(9)),
                    ..Default::default()
                })),
                ..Default::default()
            },
        ];
        let proofs = matches!(
            mode,
            pb::ExecutionMode::Proofs | pb::ExecutionMode::ProofTesting
        );
        if !proofs {
            program.commands.remove(0);
        }
        let response = run(&mut engine, id, program.clone());
        let error = response.error.as_ref().unwrap();
        assert_eq!(error.code, i32::from(pb::ErrorCode::ProofFailed));
        let failure = error.proof_failure.as_ref().unwrap();
        assert_eq!(
            failure.reason,
            i32::from(pb::ProofFailureReason::QueryDidNotMatch)
        );
        assert_eq!(failure.constructor.as_deref(), Some("Absent"));
        assert_eq!(
            error.location.as_ref().unwrap().path,
            [if proofs { 2 } else { 1 }]
        );
        assert_eq!(response.outputs.len(), usize::from(proofs));
        for (handle, node, succeeds) in [(id, 7, true), (id, 9, false), (clone, 7, false)] {
            let mut check = program.clone();
            check.commands = vec![pb::Command {
                kind: Some(pb::command::Kind::Check(pb::Check { facts: vec![node] })),
                ..Default::default()
            }];
            assert_eq!(run(&mut engine, handle, check).error.is_none(), succeeds);
        }
        let mut proof = program;
        proof.commands = vec![fixture().commands[4].clone()];
        let copied = run(&mut engine, clone, proof);
        assert_eq!(copied.error.is_none(), proofs);
        if !proofs {
            assert_eq!(
                copied.error.unwrap().proof_failure.unwrap().reason,
                i32::from(pb::ProofFailureReason::ProofsNotEnabled)
            );
        }
        for handle in [id, clone] {
            engine
                .destroy(&pb::DestroyEGraphRequest { egraph_id: handle }.encode_to_vec())
                .unwrap();
        }
        let retained = pb::RunProgramResponse::decode(response.encode_to_vec().as_slice()).unwrap();
        assert_eq!(retained, response);
        if proofs {
            let Some(pb::command_output::Kind::Proof(proof)) = &retained.outputs[0].kind else {
                panic!("retained proof")
            };
            let root = &proof.proofs[proof.root.unwrap() as usize];
            assert_eq!(root.lhs, root.rhs);
        }
    }
}

#[test]
fn malformed_later_commands_unused_rules_and_encoded_observations_are_atomic_preparation() {
    for mode in [
        pb::ExecutionMode::Normal,
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ] {
        for invalid in 0..5 {
            if invalid >= 3 && mode == pb::ExecutionMode::Normal {
                continue;
            }
            let mut engine = Engine::default();
            let id = create(&mut engine, mode);
            let mut program = fixture();
            program.commands.truncate(1);
            match invalid {
                0 => program.commands.push(pb::Command {
                    kind: Some(pb::command::Kind::Prove(pb::Prove { facts: vec![999] })),
                    ..Default::default()
                }),
                1 => program.commands.push(pb::Command {
                    kind: Some(pb::command::Kind::ProveExists(pb::ProveExists {
                        constructor: "missing".into(),
                    })),
                    ..Default::default()
                }),
                2 => {
                    program.rulesets.clear();
                    let Some(pb::rule_decl::Kind::Rule(rule)) = &mut program.rules[0].kind else {
                        unreachable!()
                    };
                    rule.query.clear(); // x in the unused rule head is ungrounded
                }
                3 => program.commands.push(pb::Command {
                    kind: Some(pb::command::Kind::Extract(pb::Extract {
                        roots: vec![2],
                        variants: 1,
                        extractor: pb::Extractor::Tree.into(),
                        ..Default::default()
                    })),
                    ..Default::default()
                }),
                _ => program.commands.push(pb::Command {
                    kind: Some(pb::command::Kind::PrintFunction(pb::PrintFunction {
                        table: "N".into(),
                        max_rows: 0,
                    })),
                    ..Default::default()
                }),
            }
            let failed = run(&mut engine, id, program);
            assert!(failed.error.is_some());
            assert!(failed.outputs.is_empty());
            let profile = failed.profile.unwrap();
            assert!(!profile.complete);
            assert!(profile.runs.is_empty() && profile.maintenance.is_empty());
            // The same definitions still install, and the rejected action left no N(1).
            let mut retry = fixture();
            retry.commands = vec![pb::Command {
                kind: Some(pb::command::Kind::Check(pb::Check { facts: vec![2] })),
                ..Default::default()
            }];
            let retry = run(&mut engine, id, retry);
            let error = retry.error.unwrap();
            assert!(
                error.location.is_some(),
                "definitions must install: {error:?}"
            );
        }
    }
}

#[test]
fn source_and_renderer_keep_proof_commands_authored() {
    let source = "(datatype Num (N i64) (Goal i64)) (ruleset r) (rule ((N x)) ((Goal x)) :ruleset r :name \"derive\") (N 1) (run r 1) (check (Goal 1)) (prove (Goal 1)) (prove-exists Goal)";
    for mode in [pb::ExecutionMode::Proofs, pb::ExecutionMode::ProofTesting] {
        let mut engine = Engine::default();
        let id = create(&mut engine, mode);
        let graph = egglog_experimental::new_experimental_egraph().with_proofs_enabled();
        let mut native = if mode == pb::ExecutionMode::ProofTesting {
            graph.with_proof_testing()
        } else {
            graph
        };
        let mut renderer = Renderer::default();
        let mut kinds = vec![];
        let mut proofs = 0;
        for phase in Source::new(Some("proof.egg".into()), source).unwrap() {
            let phase = phase.unwrap();
            for command in &phase.commands {
                kinds.push(match &command.kind {
                    Some(pb::command::Kind::Prove(_)) => "prove",
                    Some(pb::command::Kind::ProveExists(_)) => "exists",
                    Some(pb::command::Kind::Check(_)) => "check",
                    Some(pb::command::Kind::Run(_)) => "run",
                    _ => "action",
                });
            }
            if phase
                .commands
                .iter()
                .any(|c| matches!(c.kind, Some(pb::command::Kind::Prove(_))))
            {
                assert!(phase.declarations.is_empty());
                assert!(phase.rulesets.is_empty());
                assert_eq!(phase.commands.len(), 1);
            }
            let text = renderer.render(&phase).unwrap();
            let mut requested = vec![];
            let commands = native.parse_program(None, &text).unwrap();
            native
                .run_program_observed(
                    commands,
                    &mut |_, origin, output| {
                        if origin == egglog::ExecutionOrigin::Requested {
                            match output {
                                egglog::CommandOutput::RunSchedule(_) => requested.push("run"),
                                egglog::CommandOutput::ProveExists { .. } => {
                                    requested.push("proof")
                                }
                                _ => (),
                            }
                        }
                    },
                    &mut |_, _| {},
                )
                .unwrap();
            let response = run(
                &mut engine,
                id,
                pb::Program::decode(phase.encode_to_vec().as_slice()).unwrap(),
            );
            assert_eq!(response.error, None, "{text}");
            let actual: Vec<_> = response
                .outputs
                .iter()
                .map(|o| match o.kind {
                    Some(pb::command_output::Kind::Run(_)) => "run",
                    Some(pb::command_output::Kind::Proof(_)) => {
                        proofs += 1;
                        "proof"
                    }
                    _ => panic!("unexpected output"),
                })
                .collect();
            assert_eq!(actual, requested);
        }
        assert_eq!(kinds, ["action", "run", "check", "prove", "exists"]);
        assert_eq!(
            proofs,
            if mode == pb::ExecutionMode::ProofTesting {
                3
            } else {
                2
            }
        );
    }
}

#[test]
fn encoded_authoring_builtins_resolve_scalar_and_result_only_calls() {
    let source = "(datatype Num (N i64) (Goal i64)) (sort V (Vec i64)) (constructor Keep (V) Num) (ruleset r) (rule ((N x)) ((Goal (+ x 1))) :ruleset r) (Keep (vec-empty)) (N 1) (run r 1) (check (Goal 2)) (prove (Goal 2))";
    for mode in [
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ] {
        let mut engine = Engine::default();
        let id = create(&mut engine, mode);
        for phase in Source::new(None, source).unwrap() {
            let phase = phase.unwrap();
            let proves = phase
                .commands
                .iter()
                .any(|c| matches!(c.kind, Some(pb::command::Kind::Prove(_))));
            let response = run(&mut engine, id, phase);
            if proves && mode == pb::ExecutionMode::TermEncoding {
                assert_eq!(
                    response.error.unwrap().proof_failure.unwrap().reason,
                    i32::from(pb::ProofFailureReason::ProofsNotEnabled)
                );
            } else {
                assert_eq!(response.error, None);
            }
        }
    }
}

#[test]
fn failed_authored_run_counts_entry_without_fabricated_metrics_or_result() {
    for mode in [
        pb::ExecutionMode::Normal,
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ] {
        let mut engine = Engine::default();
        let id = create(&mut engine, mode);
        let mut program = fixture();
        let limit = program.nodes.len() as u32;
        program.nodes.push(pb::Node {
            sort_id: 0,
            kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::I64(i64::MAX)),
            })),
            ..Default::default()
        });
        let overflow = program.nodes.len() as u32;
        program.nodes.push(pb::Node {
            sort_id: 0,
            kind: Some(pb::node::Kind::Call(pb::Call {
                func: "egglog.core.i64.add".into(),
                args: vec![1, limit],
            })),
            ..Default::default()
        });
        let goal = program.nodes.len() as u32;
        program.nodes.push(pb::Node {
            sort_id: 1,
            kind: Some(pb::node::Kind::Call(pb::Call {
                func: "Goal".into(),
                args: vec![overflow],
            })),
            ..Default::default()
        });
        let Some(pb::rule_decl::Kind::Rule(rule)) = &mut program.rules[0].kind else {
            unreachable!()
        };
        rule.head = vec![pb::Action {
            kind: Some(pb::action::Kind::Term(goal)),
            ..Default::default()
        }];
        program.commands.truncate(2);
        let response = run(&mut engine, id, program);
        let error = response.error.unwrap();
        assert_eq!(error.code, i32::from(pb::ErrorCode::EvaluationFailed));
        assert_eq!(error.location.unwrap().path, [1]);
        assert!(response.outputs.is_empty());
        let profile = response.profile.unwrap();
        assert!(!profile.complete);
        assert_eq!(profile.runs.len(), 1);
        let run = &profile.runs[0];
        assert_eq!(run.invocations, 1);
        assert_eq!(
            (
                run.search_and_apply_nanos,
                run.merge_nanos,
                run.rebuild_nanos
            ),
            (None, None, None)
        );
        assert!(run.rules.is_empty());
        for maintenance in profile.maintenance {
            // Independently successful inline/earlier maintenance is complete.
            assert!(maintenance.invocations > 0);
            assert!(maintenance.search_and_apply_nanos.is_some());
        }
        let response = engine
            .run(
                &pb::RunProgramRequest {
                    egraph_id: id,
                    program: Some(pb::Program {
                        ir_version: 1,
                        ..Default::default()
                    }),
                    profile: false,
                }
                .encode_to_vec(),
            )
            .unwrap();
        let response = pb::RunProgramResponse::decode(response.as_slice()).unwrap();
        assert_eq!(
            response.error.unwrap().code,
            i32::from(pb::ErrorCode::InvalidProgram)
        );
        assert!(response.profile.is_none());
    }
}
