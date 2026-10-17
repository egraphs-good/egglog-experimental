use egglog_experimental::proto as pb;
use egglog_experimental::protobuf::{
    Engine,
    source::{Renderer, Source},
};
use prost::Message;

#[test]
fn core_source_controls_keep_native_stopping_reports_and_modes() {
    use egglog::{ExecutionEvent, ExecutionOrigin, NativeLoopStop};
    for mode in [
        pb::ExecutionMode::Normal,
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ] {
        for (schedule, exact) in [
            ("(repeat 0 r)", true),
            ("(seq r)", true),
            ("(repeat 1 r)", false),
            ("(repeat 3 r)", false),
            ("(saturate r)", false),
            ("(repeat 3 (seq r (saturate r)))", false),
        ] {
            let setup = "(datatype Mark (Seed i64) (Goal i64)) (ruleset r) (rewrite (Seed x) (Goal x) :ruleset r :name \"derive\") (Seed 0)";
            let control = format!("(run-schedule {schedule})");
            let graph = egglog::EGraph::default();
            let mut native = match mode {
                pb::ExecutionMode::Normal => graph,
                pb::ExecutionMode::TermEncoding => graph.with_term_encoding_enabled(),
                pb::ExecutionMode::Proofs => graph.with_proofs_enabled(),
                _ => graph.with_proofs_enabled().with_proof_testing(),
            };
            native.parse_and_run_program(None, setup).unwrap();
            let commands = native.parse_program(None, &control).unwrap();
            let mut outcome = None;
            let mut runs = 0;
            let mut committed = 0;
            let mut whole_updated = None;
            native
                .run_program_observed(
                    commands,
                    &mut |_, origin, output| {
                        if origin == ExecutionOrigin::Requested
                            && let egglog::CommandOutput::RunSchedule(report) = output
                        {
                            committed += 1;
                            whole_updated = Some(report.updated);
                        }
                    },
                    &mut |_, event| match event {
                        ExecutionEvent::RunStarted {
                            origin: ExecutionOrigin::Requested,
                            ..
                        } => runs += 1,
                        ExecutionEvent::LoopFinished {
                            origin: ExecutionOrigin::Requested,
                            schedule: Some(site),
                            completed,
                            stop,
                            result,
                        } if site.path == [0] => {
                            // The actual Core parser's outer run-schedule Sequence
                            // is an envelope; its one child is the authored loop.
                            outcome =
                                Some((completed as u64, stop.unwrap(), result.unwrap().updated));
                        }
                        _ => (),
                    },
                )
                .unwrap();
            assert_eq!(committed, 1);
            let (iterations, stop, updated) = if schedule == "(seq r)" {
                // Native Sequence is one ordered pass, not an observed native
                // loop. Its whole-command report is the updated oracle.
                assert!(outcome.is_none());
                (1, NativeLoopStop::CountReached, whole_updated.unwrap())
            } else {
                outcome.unwrap_or_else(|| panic!("missing loop {mode:?}/{schedule}"))
            };
            let termination = if exact {
                pb::TerminationReason::CountReached
            } else if stop == NativeLoopStop::CountReached {
                pb::TerminationReason::IterationLimit
            } else {
                pb::TerminationReason::Saturated
            };
            let matches = native
                .get_overall_run_report()
                .num_matches_per_rule
                .get("derive")
                .copied()
                .unwrap_or(0) as u64;
            let check = if iterations == 0 {
                ""
            } else {
                "(check (= (Seed 0) (Goal 0)))"
            };
            native.parse_and_run_program(None, check).unwrap();
            let original = format!("{setup} {control} (print-stats) {check}");
            let mut renderer = Renderer::core();
            let mut rendered = String::new();
            for roundtrip in [false, true] {
                let source = if roundtrip {
                    rendered.clone()
                } else {
                    original.clone()
                };
                let mut engine = Engine::default();
                let id = create(&mut engine, mode);
                let mut loops = 0;
                let mut stats = 0;
                for phase in Source::new_core(Some("mode-loop.egg".into()), &source).unwrap() {
                    let phase = phase.unwrap();
                    if !roundtrip {
                        rendered.push_str(&renderer.render(&phase).unwrap());
                    }
                    let response = run(&mut engine, id, phase);
                    assert_eq!(
                        response.error, None,
                        "{mode:?}/{schedule}/reimport={roundtrip}"
                    );
                    for output in &response.outputs {
                        match &output.kind {
                            Some(pb::command_output::Kind::Loop(actual)) => {
                                loops += 1;
                                assert_eq!(
                                    (actual.iterations, actual.termination, actual.updated),
                                    (iterations, Some(termination.into()), updated)
                                );
                                assert_eq!(output.location.as_ref().unwrap().path, [0]);
                                assert_eq!(
                                    response
                                        .profile
                                        .as_ref()
                                        .unwrap()
                                        .runs
                                        .iter()
                                        .map(|run| run.invocations)
                                        .sum::<u64>(),
                                    runs
                                );
                            }
                            Some(pb::command_output::Kind::Statistics(report)) => {
                                stats += 1;
                                let count = report
                                    .num_matches_per_rule
                                    .iter()
                                    .filter(|row| {
                                        row.rule.is_some_and(|i| {
                                            response.rules[i as usize].name.as_deref()
                                                == Some("derive")
                                        })
                                    })
                                    .map(|row| row.value)
                                    .sum::<u64>();
                                assert_eq!(
                                    count, matches,
                                    "{mode:?}/{schedule}/reimport={roundtrip}"
                                );
                            }
                            _ => (),
                        }
                    }
                }
                assert_eq!((loops, stats), (1, 1));
            }
        }
    }
}

#[test]
fn core_source_failed_control_and_fail_wrappers_keep_prefixes_in_every_mode() {
    for mode in [
        pb::ExecutionMode::Normal,
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ] {
        for depth in 0..=2 {
            let control = format!(
                "{}(run-schedule (repeat 2 r)){}",
                "(fail ".repeat(depth),
                ")".repeat(depth)
            );
            let original = format!(
                "(datatype Num (N i64)) (ruleset r) (rule ((N x)) ((N (+ x 1))) :ruleset r :name \"derive\") (N 9223372036854775806) {control} (N 20)"
            );
            let graph = egglog::EGraph::default();
            let mut native = match mode {
                pb::ExecutionMode::Normal => graph,
                pb::ExecutionMode::TermEncoding => graph.with_term_encoding_enabled(),
                pb::ExecutionMode::Proofs => graph.with_proofs_enabled(),
                _ => graph.with_proofs_enabled().with_proof_testing(),
            };
            assert_eq!(
                native.parse_and_run_program(None, &original).is_ok(),
                depth == 1,
                "native {mode:?}/{depth}"
            );
            let native_matches = native
                .get_overall_run_report()
                .num_matches_per_rule
                .get("derive")
                .copied()
                .unwrap_or(0) as u64;
            native
                .parse_and_run_program(None, "(check (N 9223372036854775807))")
                .unwrap();
            assert_eq!(
                native.parse_and_run_program(None, "(check (N 20))").is_ok(),
                depth == 1
            );
            let mut renderer = Renderer::core();
            let mut rendered = String::new();
            for roundtrip in [false, true] {
                let text = if roundtrip {
                    rendered.clone()
                } else {
                    original.clone()
                };
                let mut engine = Engine::default();
                let id = create(&mut engine, mode);
                let mut failed = false;
                for phase in Source::new_core(Some("failed-loop.egg".into()), &text).unwrap() {
                    let phase = phase.unwrap();
                    if !roundtrip {
                        rendered.push_str(&renderer.render(&phase).unwrap());
                    }
                    let response = run(&mut engine, id, phase);
                    assert!(
                        response.outputs.is_empty(),
                        "failed or caught schedules have no completed outcome"
                    );
                    if let Some(error) = response.error {
                        failed = true;
                        assert_eq!(error.code, i32::from(pb::ErrorCode::EvaluationFailed));
                        assert!(error.span.is_some());
                        let location = error.location.unwrap();
                        assert_eq!(location.path, if depth == 0 { vec![0, 0] } else { vec![0] });
                        assert_eq!(
                            location.iterations,
                            if depth == 0 { vec![1] } else { vec![] }
                        );
                        assert!(!response.profile.unwrap().complete);
                        break; // Never advance source after a decoded error.
                    }
                }
                assert_eq!(failed, depth != 1, "{mode:?}/{depth}/reimport={roundtrip}");
                let read = run(
                    &mut engine,
                    id,
                    pb::Program {
                        ir_version: 1,
                        commands: vec![pb::Command {
                            kind: Some(pb::command::Kind::Stats(pb::Unit {})),
                            ..Default::default()
                        }],
                        ..Default::default()
                    },
                );
                assert_eq!(read.error, None);
                let Some(pb::command_output::Kind::Statistics(report)) = &read.outputs[0].kind
                else {
                    unreachable!()
                };
                let matches = report
                    .num_matches_per_rule
                    .iter()
                    .filter(|row| {
                        row.rule.is_some_and(|i| {
                            read.rules[i as usize].name.as_deref() == Some("derive")
                        })
                    })
                    .map(|row| row.value)
                    .sum::<u64>();
                assert_eq!(
                    matches, native_matches,
                    "failed whole schedule must not commit earlier leaf totals"
                );
                let table = run(
                    &mut engine,
                    id,
                    pb::Program {
                        ir_version: 1,
                        commands: vec![pb::Command {
                            kind: Some(pb::command::Kind::PrintFunction(pb::PrintFunction {
                                table: "N".into(),
                                max_rows: None,
                            })),
                            ..Default::default()
                        }],
                        ..Default::default()
                    },
                );
                if mode == pb::ExecutionMode::Normal {
                    assert_eq!(table.error, None);
                    let Some(pb::command_output::Kind::PrintedFunction(rows)) =
                        &table.outputs[0].kind
                    else {
                        unreachable!()
                    };
                    let mut values: Vec<_> = rows
                        .rows
                        .iter()
                        .map(|row| {
                            let Some(pb::table_cell::Kind::Term(term)) = row.args[0].kind else {
                                panic!("expected available i64 input")
                            };
                            match &table.nodes[term as usize].kind {
                                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                                    value: Some(pb::primitive_value::Value::I64(value)),
                                })) => *value,
                                other => panic!("unexpected cell {other:?}"),
                            }
                        })
                        .collect();
                    values.sort_unstable();
                    let mut expected = vec![i64::MAX - 1, i64::MAX];
                    if depth == 1 {
                        expected.insert(0, 20);
                    }
                    assert_eq!(values, expected, "{mode:?}/{depth}/reimport={roundtrip}");
                } else {
                    assert!(
                        table
                            .error
                            .unwrap()
                            .message
                            .contains("encoded-mode table observation")
                    );
                }
                let suffix = pb::Command {
                    kind: Some(pb::command::Kind::Check(pb::Check { facts: vec![3] })),
                    ..Default::default()
                };
                let checked = run(
                    &mut engine,
                    id,
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
                        nodes: [i64::MAX, 20]
                            .into_iter()
                            .map(|value| pb::Node {
                                sort_id: 0,
                                kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                                    value: Some(pb::primitive_value::Value::I64(value)),
                                })),
                                ..Default::default()
                            })
                            .chain([0, 1].into_iter().map(|arg| pb::Node {
                                sort_id: 1,
                                kind: Some(pb::node::Kind::Call(pb::Call {
                                    func: "N".into(),
                                    args: vec![arg],
                                })),
                                ..Default::default()
                            }))
                            .collect(),
                        commands: vec![
                            pb::Command {
                                kind: Some(pb::command::Kind::Check(pb::Check { facts: vec![2] })),
                                ..Default::default()
                            },
                            if depth == 1 {
                                suffix
                            } else {
                                pb::Command {
                                    kind: Some(pb::command::Kind::Fail(Box::new(suffix))),
                                    ..Default::default()
                                }
                            },
                        ],
                        ..Default::default()
                    },
                );
                assert_eq!(
                    checked.error, None,
                    "retained prefix/suffix {mode:?}/{depth}/reimport={roundtrip}"
                );
            }
        }
    }
}

#[test]
fn scope_return_restores_proof_state_and_can_prove_again() {
    for mode in [
        pb::ExecutionMode::Normal,
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ] {
        let mut engine = Engine::default();
        let saved = create(&mut engine, mode);
        let mut setup = fixture();
        setup.commands.truncate(1);
        assert_eq!(run(&mut engine, saved, setup).error, None);
        let active = pb::CloneEGraphResponse::decode(
            engine
                .clone_egraph(&pb::CloneEGraphRequest { egraph_id: saved }.encode_to_vec())
                .unwrap()
                .as_slice(),
        )
        .unwrap()
        .egraph_id;
        let proving = matches!(
            mode,
            pb::ExecutionMode::Proofs | pb::ExecutionMode::ProofTesting
        );
        let mut work = fixture();
        work.commands.remove(0);
        if !proving {
            work.commands.truncate(2);
        }
        let native = egglog_experimental::new_experimental_egraph();
        let mut native = match mode {
            pb::ExecutionMode::Normal => native,
            pb::ExecutionMode::TermEncoding => native.with_term_encoding_enabled(),
            pb::ExecutionMode::Proofs => native.with_proofs_enabled(),
            pb::ExecutionMode::ProofTesting => native.with_proofs_enabled().with_proof_testing(),
        };
        native.set_num_threads(1);
        native.parse_and_run_program(None, "(datatype Num (N i64) (Goal i64) (Absent i64)) (ruleset r) (rule ((N x)) ((Goal x)) :ruleset r :name \"derive\") (N 1)").unwrap();
        let native_work = if proving {
            "(run r 1) (check (Goal 1)) (prove (Goal 1)) (prove-exists Goal)"
        } else {
            "(run r 1) (check (Goal 1))"
        };
        native.push();
        native.parse_and_run_program(None, native_work).unwrap();
        native.pop().unwrap();
        native
            .parse_and_run_program(None, "(fail (check (Goal 1)))")
            .unwrap();
        let commands = native.parse_program(None, native_work).unwrap();
        let mut native_proofs = Vec::new();
        native
            .run_program_observed(
                commands,
                &mut |_, origin, output| {
                    if origin == egglog::ExecutionOrigin::Requested
                        && let egglog::CommandOutput::ProveExists {
                            proof_store,
                            proof_id,
                        } = output
                    {
                        native_proofs.push(match proof_store.get(proof_id).justification() {
                            egglog::proof::Justification::Rule { .. } => "rule",
                            egglog::proof::Justification::Fiat => "fiat",
                            other => panic!("unexpected native {mode:?} root: {other:?}"),
                        });
                    }
                },
                &mut |_, _| {},
            )
            .unwrap();
        let child = run(&mut engine, active, work.clone());
        assert_eq!(child.error, None, "child {mode:?}");
        if proving {
            assert!(child.outputs.iter().any(|output| matches!(&output.kind, Some(pb::command_output::Kind::Proof(proof)) if proof.root.is_some())));
        }
        engine
            .return_to(
                &pb::ReturnToEGraphRequest {
                    active_id: active,
                    saved_id: saved,
                }
                .encode_to_vec(),
            )
            .unwrap();
        let mut absent = fixture();
        absent.commands = vec![pb::Command {
            kind: Some(pb::command::Kind::Fail(Box::new(
                absent.commands[2].clone(),
            ))),
            ..Default::default()
        }];
        let restored = run(&mut engine, saved, absent);
        assert_eq!(
            restored.error, None,
            "scoped Goal must be absent after return in {mode:?}"
        );
        assert!(restored.outputs.is_empty());
        let after = run(&mut engine, saved, work);
        assert_eq!(after.error, None, "after return {mode:?}");
        if proving {
            let proofs: Vec<_> = after
                .outputs
                .iter()
                .filter_map(|output| match &output.kind {
                    Some(pb::command_output::Kind::Proof(proof)) => Some(proof),
                    _ => None,
                })
                .collect();
            assert!(!proofs.is_empty());
            assert!(proofs.iter().all(|proof| proof.root.is_some()
                && !proof.terms.is_empty()
                && !proof.proofs.is_empty()));
            // Native prove-exists may select a fiat witness from the same
            // equality sort. Compare actual requested native roots, not an
            // invented requirement that every output is rule-derived.
            let roots: Vec<_> = proofs
                .iter()
                .map(
                    |proof| match &proof.proofs[proof.root.unwrap() as usize].justification {
                        Some(pb::proof_step::Justification::Rule(_)) => "rule",
                        Some(pb::proof_step::Justification::Fiat(_)) => "fiat",
                        other => panic!("unexpected wire {mode:?} root: {other:?}"),
                    },
                )
                .collect();
            assert_eq!(
                roots, native_proofs,
                "requested roots after return {mode:?}"
            );
            assert!(
                proofs
                    .iter()
                    .any(|proof| proof.proofs.iter().any(|step| matches!(
                        step.justification,
                        Some(pb::proof_step::Justification::Rule(_))
                    ))),
                "mode={mode:?}"
            );
        }
    }
}

#[test]
fn recursive_fail_run_rendering_preserves_native_command_in_every_mode() {
    let source = "(ruleset r) (fail (fail (run r 1)))";
    for mode in [
        pb::ExecutionMode::Normal,
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ] {
        let native = egglog_experimental::new_experimental_egraph();
        let mut native = match mode {
            pb::ExecutionMode::Normal => native,
            pb::ExecutionMode::TermEncoding => native.with_term_encoding_enabled(),
            pb::ExecutionMode::Proofs => native.with_proofs_enabled(),
            pb::ExecutionMode::ProofTesting => native.with_proofs_enabled().with_proof_testing(),
        };
        let mut rendered = native.clone();
        native.parse_and_run_program(None, source).unwrap();

        let mut engine = Engine::default();
        let id = create(&mut engine, mode);
        let mut renderer = Renderer::default();
        let mut text = String::new();
        for phase in Source::new(None, source).unwrap() {
            let phase = phase.unwrap();
            text.push_str(&renderer.render(&phase).unwrap());
            let response = run(&mut engine, id, phase);
            assert_eq!(response.error, None, "original bytes {mode:?}");
            assert!(response.outputs.is_empty());
        }
        // Display's run-schedule spelling is shadowed by an experimental
        // UserDefined command. Re-export must retain a real native Run leaf,
        // including beneath Fail, before proof instrumentation sees it.
        let phases: Vec<_> = Source::new(None, &text)
            .unwrap()
            .map(|phase| phase.unwrap_or_else(|error| panic!("{mode:?}: {text}: {error}")))
            .collect();
        let [command] = phases.last().unwrap().commands.as_slice() else {
            panic!("expected one wrapped run");
        };
        let Some(pb::command::Kind::Fail(outer)) = &command.kind else {
            panic!("missing outer Fail");
        };
        let Some(pb::command::Kind::Fail(inner)) = &outer.kind else {
            panic!("missing inner Fail");
        };
        assert!(matches!(inner.kind, Some(pb::command::Kind::Run(_))));
        rendered.parse_and_run_program(None, &text).unwrap();
        let id = create(&mut engine, mode);
        for phase in phases {
            let response = run(&mut engine, id, phase);
            assert_eq!(response.error, None, "re-exported bytes {mode:?}");
            assert!(response.outputs.is_empty());
        }
    }
}

#[test]
fn recursive_fail_matches_native_checks_in_every_execution_mode() {
    for mode in [
        pb::ExecutionMode::Normal,
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ] {
        for (case, facts, expected) in [
            ("false", "(= 1 2)", true),
            ("true", "(= 1 1)", false),
            ("empty", "", false),
            (
                "ungrounded",
                "(= (+ x 1) 2)",
                mode != pb::ExecutionMode::ProofTesting,
            ),
            ("valid-get", "(= (set-get (set-of 1) 0) 1)", false),
            (
                "partial-get",
                "(= (set-get (set-of 1) 9) 0)",
                mode == pb::ExecutionMode::Normal,
            ),
            ("existing", "(M 5)", false),
            ("absent", "(M 40)", true),
            ("wrong-sort", "(= 1 \"x\")", false),
            ("unknown", "(missing-function)", false),
        ] {
            let setup = "(datatype Mark (M i64)) (sort IntSet (Set i64)) (M 5)";
            let tested = format!("(fail (check {facts}))");
            let preparation = matches!(case, "wrong-sort" | "unknown")
                || (case == "ungrounded" && mode == pb::ExecutionMode::ProofTesting)
                || (matches!(case, "valid-get" | "partial-get")
                    && mode != pb::ExecutionMode::Normal);
            let mut native = egglog_experimental::new_experimental_egraph();
            native = match mode {
                pb::ExecutionMode::Normal => native,
                pb::ExecutionMode::TermEncoding => native.with_term_encoding_enabled(),
                pb::ExecutionMode::Proofs => native.with_proofs_enabled(),
                pb::ExecutionMode::ProofTesting => {
                    native.with_proofs_enabled().with_proof_testing()
                }
            };
            native.parse_and_run_program(None, setup).unwrap();
            let plain_succeeds = matches!(case, "true" | "empty" | "existing")
                || (case == "valid-get" && mode == pb::ExecutionMode::Normal);
            let mut plain_native = native.clone();
            assert_eq!(
                plain_native
                    .parse_and_run_program(None, &format!("(M 10) (check {facts}) (M 20)"))
                    .is_ok(),
                plain_succeeds,
                "plain native {mode:?} {case}"
            );
            assert_eq!(
                native
                    .parse_and_run_program(None, &format!("(M 10) {tested} (M 20)"))
                    .is_ok(),
                expected,
                "native {mode:?} {case}"
            );
            native
                .parse_and_run_program(None, "(check (M 10))")
                .unwrap();
            assert_eq!(
                native.parse_and_run_program(None, "(check (M 20))").is_ok(),
                expected
            );
            let mut engine = Engine::default();
            let id = create(&mut engine, mode);
            let mut source =
                Source::new(Some("fail-modes.egg".into()), &format!("{setup} {tested}"))
                    .unwrap()
                    .peekable();
            let last = loop {
                let phase = source.next().unwrap();
                if source.peek().is_none() {
                    break phase;
                }
                assert_eq!(run(&mut engine, id, phase.unwrap()).error, None);
            };
            let mut phase = if matches!(case, "wrong-sort" | "unknown") {
                assert!(
                    last.is_err(),
                    "{mode:?} {case}: source typechecking must propagate"
                );
                // Independently test malformed bytes: Source correctly cannot
                // author these cases. Only expression records are mutated;
                // no substitute builtin metadata is introduced.
                let mut phase = Source::new(None, &format!("{setup} (fail (check (= 1 2)))"))
                    .unwrap()
                    .last()
                    .unwrap()
                    .unwrap();
                let Some(pb::command::Kind::Fail(child)) = &phase.commands[0].kind else {
                    unreachable!()
                };
                let Some(pb::command::Kind::Check(check)) = &child.kind else {
                    unreachable!()
                };
                let fact = check.facts[0] as usize;
                if case == "wrong-sort" {
                    let Some(pb::node::Kind::Union(union)) = &phase.nodes[fact].kind else {
                        unreachable!()
                    };
                    let right = union.members[1] as usize;
                    phase.nodes[right].sort_id = phase.sorts.len() as u32;
                    phase.sorts.push(pb::Sort {
                        kind: Some(pb::sort::Kind::Family(pb::HostSort {
                            name: "String".into(),
                            args: vec![],
                        })),
                        ..Default::default()
                    });
                    phase.nodes[right].kind =
                        Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                            value: Some(pb::primitive_value::Value::String("x".into())),
                        }));
                } else {
                    phase.nodes[fact].kind = Some(pb::node::Kind::Call(pb::Call {
                        func: "missing-function".into(),
                        args: vec![],
                    }));
                }
                phase
            } else {
                last.unwrap()
            };
            assert!(matches!(
                phase.commands[0].kind,
                Some(pb::command::Kind::Fail(_))
            ));
            let integer = phase.sorts.iter().position(|s| matches!(&s.kind, Some(pb::sort::Kind::Family(f)) if f.name == "i64" && f.args.is_empty())).unwrap() as u32;
            let mark = phase
                .sorts
                .iter()
                .position(|s| matches!(&s.kind, Some(pb::sort::Kind::Eq(name)) if name == "Mark"))
                .unwrap() as u32;
            for (position, value) in [(0, 10), (2, 20)] {
                let argument = phase.nodes.len() as u32;
                phase.nodes.push(pb::Node {
                    sort_id: integer,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::I64(value)),
                    })),
                    ..Default::default()
                });
                let call = phase.nodes.len() as u32;
                phase.nodes.push(pb::Node {
                    sort_id: mark,
                    kind: Some(pb::node::Kind::Call(pb::Call {
                        func: "M".into(),
                        args: vec![argument],
                    })),
                    ..Default::default()
                });
                phase.commands.insert(
                    position,
                    pb::Command {
                        kind: Some(pb::command::Kind::Action(pb::Action {
                            kind: Some(pb::action::Kind::Term(call)),
                            ..Default::default()
                        })),
                        ..Default::default()
                    },
                );
            }
            if !matches!(case, "wrong-sort" | "unknown") {
                let mut renderer = Renderer::default();
                let mut rendered = egglog_experimental::new_experimental_egraph();
                rendered = match mode {
                    pb::ExecutionMode::Normal => rendered,
                    pb::ExecutionMode::TermEncoding => rendered.with_term_encoding_enabled(),
                    pb::ExecutionMode::Proofs => rendered.with_proofs_enabled(),
                    pb::ExecutionMode::ProofTesting => {
                        rendered.with_proofs_enabled().with_proof_testing()
                    }
                };
                for setup_phase in Source::new(None, setup).unwrap() {
                    let text = renderer.render(&setup_phase.unwrap()).unwrap();
                    rendered.parse_and_run_program(None, &text).unwrap();
                }
                let text = renderer.render(&phase).unwrap();
                assert_eq!(
                    rendered.parse_and_run_program(None, &text).is_ok(),
                    expected,
                    "rendered {mode:?} {case}"
                );
            }
            let mut plain = phase.clone();
            let Some(pb::command::Kind::Fail(child)) = plain.commands[1].kind.take() else {
                unreachable!()
            };
            plain.commands[1] = *child;
            let plain_id = create(&mut engine, mode);
            for setup_phase in Source::new(None, setup).unwrap() {
                assert_eq!(run(&mut engine, plain_id, setup_phase.unwrap()).error, None);
            }
            let plain_response = run(&mut engine, plain_id, plain);
            assert_eq!(
                plain_response.error.is_none(),
                plain_succeeds,
                "plain byte {mode:?} {case}"
            );
            if let Some(error) = &plain_response.error {
                assert_eq!(error.location.is_none(), preparation);
                if let Some(location) = &error.location {
                    assert_eq!(location.path, [1]);
                }
                let code = if preparation {
                    pb::ErrorCode::InvalidProgram
                } else if case == "ungrounded" {
                    pb::ErrorCode::EvaluationFailed
                } else if mode == pb::ExecutionMode::ProofTesting {
                    pb::ErrorCode::ProofFailed
                } else {
                    pb::ErrorCode::CheckFailed
                };
                assert_eq!(error.code, i32::from(code), "plain byte {mode:?} {case}");
            }
            let response = run(&mut engine, id, phase);
            assert_eq!(
                response.error.is_none(),
                expected,
                "byte {mode:?} {case}: {:?}",
                response.error
            );
            assert!(
                response.outputs.is_empty(),
                "{mode:?} {case}: Fail leaked a requested output"
            );
            if let Some(error) = &response.error {
                assert_eq!(
                    error.location.is_none(),
                    preparation,
                    "{mode:?} {case}: {error:?}"
                );
                if let Some(location) = &error.location {
                    assert_eq!(location.path, [1]);
                }
                assert_eq!(
                    error.code,
                    i32::from(if preparation {
                        pb::ErrorCode::InvalidProgram
                    } else {
                        pb::ErrorCode::EvaluationFailed
                    })
                );
            }
            for (marker, present) in [(5, true), (10, !preparation), (20, expected)] {
                let read = Source::new(None, &format!("{setup} (check (M {marker}))"))
                    .unwrap()
                    .last()
                    .unwrap()
                    .unwrap();
                let response = run(&mut engine, id, read);
                assert_eq!(
                    response.error.is_none(),
                    present,
                    "{mode:?} {case}: marker {marker}"
                );
            }
            // A new request remains usable after either an expected failure,
            // unexpected success, or a rejected helper preparation.
            let mut recovery =
                Source::new(None, &format!("{setup} (M 30) (check (M 30))")).unwrap();
            recovery.next().unwrap().unwrap();
            recovery.next().unwrap().unwrap();
            recovery.next().unwrap().unwrap();
            for phase in recovery {
                assert_eq!(
                    run(&mut engine, id, phase.unwrap()).error,
                    None,
                    "recovery {mode:?} {case}"
                );
            }
        }
    }
}

#[test]
fn double_fail_suppresses_successful_proof_without_erasing_prior_output() {
    for mode in [pb::ExecutionMode::Proofs, pb::ExecutionMode::ProofTesting] {
        let source = "(datatype Mark (M i64) (Goal i64)) (rule ((M x)) ((Goal x))) (M 1) (run 1) (prove-exists Goal) (fail (fail (prove-exists Goal)))";
        let mut native = egglog_experimental::new_experimental_egraph().with_proofs_enabled();
        if mode == pb::ExecutionMode::ProofTesting {
            native = native.with_proof_testing();
        }
        native.parse_and_run_program(None, source).unwrap();
        let mut engine = Engine::default();
        let id = create(&mut engine, mode);
        let mut source = Source::new(Some("nested-proof.egg".into()), source).unwrap();
        for _ in 0..4 {
            assert_eq!(
                run(&mut engine, id, source.next().unwrap().unwrap()).error,
                None
            );
        }
        let mut program = source.next().unwrap().unwrap();
        let nested = source.next().unwrap().unwrap();
        // ProveExists has no node references; both phases own identical sorts
        // and source files, so retaining the authored wrapper needs no remap.
        assert_eq!(program.sorts, nested.sorts);
        assert_eq!(program.files, nested.files);
        program.commands.extend(nested.commands);
        let response = run(&mut engine, id, program);
        assert_eq!(response.error, None);
        assert_eq!(response.outputs.len(), 1);
        assert_eq!(response.outputs[0].location.as_ref().unwrap().path, [0]);
        assert!(matches!(
            response.outputs[0].kind,
            Some(pb::command_output::Kind::Proof(_))
        ));
    }
}

#[test]
fn binary_source_unions_keep_native_modes_and_checked_proof_attribution() {
    for (case, action) in [
        ("fiat", "(union (A) (B))"),
        (
            "constructors",
            "(rule ((A)) ((union (A) (B))) :name \"merge\") (run 1)",
        ),
        (
            "constructor_left",
            "(rule ((= x (A))) ((union (B) x)) :name \"merge\") (run 1)",
        ),
        (
            "constructor_right",
            "(rule ((= x (A))) ((union x (B))) :name \"merge\") (run 1)",
        ),
    ] {
        for mode in [
            pb::ExecutionMode::Normal,
            pb::ExecutionMode::TermEncoding,
            pb::ExecutionMode::Proofs,
            pb::ExecutionMode::ProofTesting,
        ] {
            let proving = matches!(
                mode,
                pb::ExecutionMode::Proofs | pb::ExecutionMode::ProofTesting
            );
            let source = format!(
                "(datatype E (A) (B)) (A) {action} (check (= (A) (B))) {}",
                if proving { "(prove (= (A) (B)))" } else { "" }
            );
            let graph = || {
                let graph = egglog_experimental::new_experimental_egraph();
                match mode {
                    pb::ExecutionMode::Normal => graph,
                    pb::ExecutionMode::TermEncoding => graph.with_term_encoding_enabled(),
                    pb::ExecutionMode::Proofs => graph.with_proofs_enabled(),
                    pb::ExecutionMode::ProofTesting => {
                        graph.with_proofs_enabled().with_proof_testing()
                    }
                }
            };
            graph().parse_and_run_program(None, &source).unwrap();
            let mut rendered = graph();
            let mut renderer = Renderer::default();
            let mut engine = Engine::default();
            let id = create(&mut engine, mode);
            let mut proofs = 0;
            for phase in Source::new(Some("binary-union.egg".into()), &source).unwrap() {
                let phase = pb::Program::decode(phase.unwrap().encode_to_vec().as_slice()).unwrap();
                let text = renderer.render(&phase).unwrap();
                let commands = rendered.parse_program(None, &text).unwrap();
                let mut requested = vec![];
                rendered
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
                let response = run(&mut engine, id, phase);
                assert_eq!(response.error, None, "{case} {mode:?}: {text}");
                let actual: Vec<_> = response
                    .outputs
                    .iter()
                    .map(|output| {
                        assert_eq!(output.location.as_ref().unwrap().path, [0]);
                        match &output.kind {
                            Some(pb::command_output::Kind::Run(_)) => "run",
                            Some(pb::command_output::Kind::Proof(proof)) => {
                                // Prove uses the existing native checker before export;
                                // decoded output must preserve the justification route.
                                assert!(proof.root.is_some());
                                assert!(!proof.terms.is_empty());
                                assert!(
                                    proof.proofs.iter().any(|step| match &step.justification {
                                        Some(pb::proof_step::Justification::Fiat(_)) =>
                                            case == "fiat",
                                        Some(pb::proof_step::Justification::Rule(rule)) =>
                                            case != "fiat" && rule.name.contains("_rule_0"),
                                        _ => false,
                                    }),
                                    "{case} {mode:?}: {proof:?}"
                                );
                                proofs += 1;
                                "proof"
                            }
                            _ => panic!("unexpected output"),
                        }
                    })
                    .collect();
                assert_eq!(actual, requested, "{case} {mode:?}");
            }
            assert_eq!(
                proofs,
                if mode == pb::ExecutionMode::ProofTesting {
                    2
                } else {
                    usize::from(proving)
                }
            );
        }
    }
}

#[test]
fn set_collapse_proof_and_get_validator_boundary_survive_bytes() {
    let collapse = r#"
        (sort Math) (constructor A () Math) (constructor B () Math)
        (sort MathSet (Set Math)) (constructor Holds (MathSet) Math)
        (Holds (set-of (A) (B))) (Holds (set-of (B)))
        (rewrite (A) (B)) (run 1)
        (prove (= (Holds (set-of (A) (B))) (Holds (set-of (B)))))
    "#;
    for mode in [pb::ExecutionMode::Proofs, pb::ExecutionMode::ProofTesting] {
        let mut engine = Engine::default();
        let id = create(&mut engine, mode);
        let mut proofs = 0;
        for phase in Source::new(None, collapse).unwrap() {
            let response = run(&mut engine, id, phase.unwrap());
            assert_eq!(response.error, None, "{mode:?}");
            proofs += response
                .outputs
                .iter()
                .filter(|o| matches!(o.kind, Some(pb::command_output::Kind::Proof(_))))
                .count();
        }
        assert_eq!(proofs, 1);
        let id = create(&mut engine, mode);
        let mut source = Source::new(None, "(sort S (Set i64)) (set-get (set-of 1) 0)").unwrap();
        assert_eq!(
            run(&mut engine, id, source.next().unwrap().unwrap()).error,
            None
        );
        let response = run(&mut engine, id, source.next().unwrap().unwrap());
        let error = response
            .error
            .expect("set-get still lacks a proof validator");
        assert!(
            error.message.contains("set-get") && error.message.contains("validator"),
            "{error:?}"
        );
    }
}

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
                include_run_reports: false,
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
fn shared_occurrences_resupply_name_and_clone_keep_native_proofs_and_cursors() {
    for mode in [
        pb::ExecutionMode::Normal,
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ] {
        let mut program = fixture();
        let mut ready = program.declarations[1].clone();
        let Some(pb::declaration::Kind::Constructor(c)) = &mut ready.kind else {
            unreachable!()
        };
        c.name = "Ready".into();
        program.declarations.push(ready);
        for arg in [1, 0, 6] {
            program.nodes.push(pb::Node {
                sort_id: 1,
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "Ready".into(),
                    args: vec![arg],
                })),
                ..Default::default()
            });
        }
        let Some(pb::rule_decl::Kind::Rule(rule)) = &mut program.rules[0].kind else {
            unreachable!()
        };
        rule.query.push(10);
        program.rulesets[0].name = None;
        program.rulesets.push(program.rulesets[0].clone());
        program.rulesets.push(pb::Ruleset {
            name: Some("parent".into()),
            kind: Some(pb::ruleset::Kind::Combined(pb::CombinedRuleset {
                rulesets: [0, 1, 0]
                    .into_iter()
                    .map(|i| pb::RulesetRef {
                        kind: Some(pb::ruleset_ref::Kind::Index(i)),
                    })
                    .collect(),
            })),
            ..Default::default()
        });
        program.files = vec![pb::SourceFile {
            name: "rule.egg".into(),
            contents: Some("derive".into()),
        }];
        program.rules[0].span = Some(pb::Span {
            file: 0,
            start: 0,
            end: 6,
        });
        let mut commands = vec![
            program.commands[0].clone(),
            pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Term(11)),
                    ..Default::default()
                })),
                ..Default::default()
            },
        ];
        for index in [0, 1, 2] {
            commands.push(pb::Command {
                kind: Some(pb::command::Kind::Run(pb::Run {
                    ruleset: Some(pb::RulesetRef {
                        kind: Some(pb::ruleset_ref::Kind::Index(index)),
                    }),
                    ..Default::default()
                })),
                ..Default::default()
            });
        }
        if matches!(
            mode,
            pb::ExecutionMode::Proofs | pb::ExecutionMode::ProofTesting
        ) {
            commands.extend_from_slice(&program.commands[3..]);
        }
        program.commands = commands;
        let mut engine = Engine::default();
        let id = create(&mut engine, mode);
        for iteration in 0..2 {
            let response = run(&mut engine, id, program.clone());
            assert_eq!(response.error, None, "{mode:?}, {iteration}");
            let outcomes: Vec<_> = response
                .outputs
                .iter()
                .filter_map(|o| match &o.kind {
                    Some(pb::command_output::Kind::Run(r)) => Some(r),
                    _ => None,
                })
                .collect();
            assert_eq!(outcomes.len(), 3);
            assert_eq!(
                outcomes.iter().map(|r| r.updated).collect::<Vec<_>>(),
                [iteration == 0, false, false]
            );
            let proofs: Vec<_> = response
                .outputs
                .iter()
                .filter_map(|o| match &o.kind {
                    Some(pb::command_output::Kind::Proof(p)) => Some(p),
                    _ => None,
                })
                .collect();
            assert_eq!(
                proofs.len(),
                if matches!(
                    mode,
                    pb::ExecutionMode::Proofs | pb::ExecutionMode::ProofTesting
                ) {
                    2
                } else {
                    0
                }
            );
            assert!(proofs.iter().all(|p| p.proofs.iter().any(|p| matches!(
                p.justification,
                Some(pb::proof_step::Justification::Rule(_))
            ))));
            if mode == pb::ExecutionMode::Normal {
                assert_eq!(
                    response
                        .profile
                        .unwrap()
                        .runs
                        .iter()
                        .map(|r| r.rules.iter().map(|r| r.matches.unwrap()).sum::<u64>())
                        .collect::<Vec<_>>(),
                    [u64::from(iteration == 0), 0, 0]
                );
            }
        }
        let cloned = engine
            .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
            .unwrap();
        let clone = pb::CloneEGraphResponse::decode(cloned.as_slice())
            .unwrap()
            .egraph_id;
        program.rulesets[0].name = Some("child".into());
        program.commands.clear();
        assert_eq!(run(&mut engine, clone, program.clone()).error, None);
        let mut name_only = pb::Program {
            ir_version: 1,
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Run(pb::Run {
                    ruleset: Some(pb::RulesetRef {
                        kind: Some(pb::ruleset_ref::Kind::Name("child".into())),
                    }),
                    ..Default::default()
                })),
                ..Default::default()
            }],
            ..Default::default()
        };
        assert_eq!(run(&mut engine, clone, name_only.clone()).error, None);
        assert_eq!(
            run(&mut engine, id, name_only.clone()).error.unwrap().code,
            i32::from(pb::ErrorCode::UnknownName)
        );
        let Some(pb::command::Kind::Run(r)) = &mut name_only.commands[0].kind else {
            unreachable!()
        };
        r.ruleset.as_mut().unwrap().kind = Some(pb::ruleset_ref::Kind::Name("parent".into()));
        program.rulesets.clear();
        program.rules.clear();
        program.files = vec![pb::SourceFile {
            name: "later.egg".into(),
            contents: None,
        }];
        program.commands = [7, 12]
            .into_iter()
            .map(|i| pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Term(i)),
                    ..Default::default()
                })),
                ..Default::default()
            })
            .chain(name_only.commands.clone())
            .collect();
        for target in [clone, id] {
            let response = run(&mut engine, target, program.clone());
            assert_eq!(response.error, None);
            let Some(pb::command_output::Kind::Run(outcome)) = &response.outputs[0].kind else {
                unreachable!()
            };
            assert!(
                outcome.updated,
                "clone cursor must not consume the other's new input"
            );
            if mode == pb::ExecutionMode::Normal {
                assert_eq!(response.rules.len(), 1);
                let span = response.rules[0].span.unwrap();
                assert_eq!(response.files[span.file as usize].name, "rule.egg");
                assert_eq!(span.file, 1);
                assert_eq!(response.profile.unwrap().runs[0].rules[0].matches, Some(1));
            }
        }
    }
}

#[test]
fn all_modes_return_only_requested_outputs_and_exclusive_profiles() {
    for (mode, include_run_reports) in [
        pb::ExecutionMode::Normal,
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ]
    .into_iter()
    .flat_map(|mode| [false, true].map(|include| (mode, include)))
    {
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
        let text = Renderer::default().render(&program).unwrap();
        let native = egglog_experimental::new_experimental_egraph();
        let mut native = match mode {
            pb::ExecutionMode::Normal => native,
            pb::ExecutionMode::TermEncoding => native.with_term_encoding_enabled(),
            pb::ExecutionMode::Proofs => native.with_proofs_enabled(),
            pb::ExecutionMode::ProofTesting => native.with_proofs_enabled().with_proof_testing(),
        };
        native.set_num_threads(1);
        let commands = native.parse_program(None, &text).unwrap();
        let mut native_reports = vec![];
        let mut leaves = vec![];
        let native_result = native.run_program_observed(
            commands,
            &mut |cause, origin, output| {
                if origin == egglog::ExecutionOrigin::Requested
                    && let egglog::CommandOutput::RunSchedule(report) = output
                {
                    native_reports.push((cause, report));
                }
            },
            &mut |cause, event| {
                if let egglog::ExecutionEvent::RunStarted { origin, .. } = event {
                    leaves.push((cause, origin));
                }
            },
        );
        assert_eq!(
            native_result.is_ok(),
            matches!(
                mode,
                pb::ExecutionMode::Proofs | pb::ExecutionMode::ProofTesting
            )
        );
        assert_eq!(native_reports.len(), 1);
        let (cause, native_report) = &native_reports[0];
        let native_leaves: Vec<_> = leaves.iter().filter(|(index, _)| index == cause).collect();
        let response = pb::RunProgramResponse::decode(
            engine
                .run(
                    &pb::RunProgramRequest {
                        egraph_id: id,
                        program: Some(program),
                        profile: true,
                        include_run_reports,
                    }
                    .encode_to_vec(),
                )
                .unwrap()
                .as_slice(),
        )
        .unwrap();
        let profile = response.profile.as_ref().unwrap();
        assert_eq!(profile.runs.len(), 1);
        assert_eq!(profile.runs[0].command_path, [1]);
        assert_eq!(profile.runs[0].invocations, 1);
        assert_eq!(
            native_leaves
                .iter()
                .filter(|(_, origin)| *origin == egglog::ExecutionOrigin::Requested)
                .count() as u64,
            profile.runs[0].invocations,
        );
        assert!(profile.runs[0].search_and_apply_nanos.is_some());
        assert!(profile.runs[0].merge_nanos.is_some());
        assert!(profile.runs[0].rebuild_nanos.is_some());
        let Some(pb::command_output::Kind::Run(outcome)) = &response.outputs[0].kind else {
            panic!("requested run")
        };
        assert!(outcome.updated);
        assert!(!outcome.can_stop);
        assert_eq!(
            response.outputs[0].run_report.is_some(),
            include_run_reports
        );
        if let Some(report) = &response.outputs[0].run_report {
            assert_eq!(
                (report.updated, report.can_stop),
                (outcome.updated, outcome.can_stop)
            );
            assert_eq!(
                report.iterations.len(),
                native_report.iterations.len(),
                "paired native history: mode={mode:?}"
            );
            assert_eq!(
                (report.updated, report.can_stop),
                (native_report.updated, native_report.can_stop)
            );
            // The requested native anchor includes its instrumented schedule's
            // complete history; one requested leaf need not mean one iteration.
            for (iteration, native) in report.iterations.iter().zip(&native_report.iterations) {
                let ruleset = iteration.rule_set_report.as_ref().unwrap();
                assert_eq!(ruleset.changed, native.rule_set_report.changed);
                let mut matches: Vec<_> = ruleset
                    .rule_reports
                    .iter()
                    .flat_map(|row| &row.reports)
                    .map(|report| report.num_matches)
                    .collect();
                let mut native_matches: Vec<_> = native
                    .rule_set_report
                    .rule_reports
                    .values()
                    .flatten()
                    .map(|report| report.num_matches as u64)
                    .collect();
                matches.sort_unstable();
                native_matches.sort_unstable();
                assert_eq!(
                    matches, native_matches,
                    "paired native iteration matches: mode={mode:?}"
                );
            }
        }
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
                assert!(output.run_report.is_none());
                let Some(pb::command_output::Kind::Proof(proof)) = &output.kind else {
                    panic!("proof only")
                };
                assert!(proof.root.is_some());
                assert!(!proof.proofs.is_empty());
                assert!(!proof.terms.is_empty());
            }
        }
        if mode != pb::ExecutionMode::Normal {
            if let Some(report) = &response.outputs[0].run_report {
                // Detail rows can retain a known authored occurrence even though
                // exclusive ProfileSummary deliberately omits transformed counts.
                assert_eq!(
                    response.rules,
                    [pb::RuleAttribution {
                        root: Some(pb::RulesetRef {
                            kind: Some(pb::ruleset_ref::Kind::Name("rebuilding_ruleset".into()))
                        }),
                        children: vec![],
                        rule: 0,
                        name: Some("derive".into()),
                        span: None,
                    }]
                );
                let mapped: Vec<_> = report
                    .num_matches_per_rule
                    .iter()
                    .filter(|row| row.rule.is_some())
                    .collect();
                let [authored] = mapped.as_slice() else {
                    panic!("expected one authored native count row")
                };
                assert_eq!(
                    authored.value,
                    native_report.num_matches_per_rule["derive"] as u64
                );
                for (name, rule, direction) in report
                    .num_matches_per_rule
                    .iter()
                    .map(|row| (&row.native_name, row.rule, row.direction))
                    .chain(
                        report
                            .search_and_apply_time_per_rule
                            .iter()
                            .map(|row| (&row.native_name, row.rule, row.direction)),
                    )
                    .chain(
                        report
                            .iterations
                            .iter()
                            .flat_map(|iteration| {
                                &iteration.rule_set_report.as_ref().unwrap().rule_reports
                            })
                            .map(|row| (&row.native_name, row.rule, row.direction)),
                    )
                {
                    assert_eq!(
                        (rule, direction),
                        if name == &authored.native_name {
                            (Some(0), Some(pb::NativeRuleDirection::Single.into()))
                        } else {
                            (None, None)
                        },
                        "helper attribution: {name}"
                    );
                }
            } else {
                assert!(response.rules.is_empty());
            }
            // No guessed transformed rule counts in the exclusive profile,
            // regardless of whether detailed reports were separately requested.
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
                        max_rows: None,
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
fn scalar_variadic_prove_and_prove_exists_keep_boundary_arities_and_requested_outputs() {
    for mode in [pb::ExecutionMode::Proofs, pb::ExecutionMode::ProofTesting] {
        for arity in [0, 1, 2, 5] {
            let strings = (0..arity).map(|i| format!("s{i}\0\n☃")).collect::<Vec<_>>();
            let string_args = strings
                .iter()
                .map(|s| egglog::ast::Literal::String(s.clone()).to_string())
                .collect::<Vec<_>>()
                .join(" ");
            let bool_args = (0..arity)
                .map(|i| (i == 1).to_string())
                .collect::<Vec<_>>()
                .join(" ");
            // Native prove-exists strips a single-premise rule wrapper. Two
            // independent facts keep a rule step in every returned witness.
            let source = format!(
                r#"
                (datatype Scalar (Seed) (Ready) (Text String) (Truth bool))
                (ruleset scalar)
                (rule ((Seed) (Ready)) ((Text (+ {string_args})) (Truth (or {bool_args}))) :ruleset scalar :name "derive-scalars")
                (Seed) (Ready) (run scalar 1)
                (prove (= (Text (+ {string_args})) (Text {})))
                (prove (= (Truth (or {bool_args})) (Truth {})))
                (prove-exists Text) (prove-exists Truth)
            "#,
                egglog::ast::Literal::String(strings.concat()),
                arity > 1
            );
            let mut engine = Engine::default();
            let id = create(&mut engine, mode);
            let graph = egglog_experimental::new_experimental_egraph().with_proofs_enabled();
            let mut native = if mode == pb::ExecutionMode::ProofTesting {
                graph.with_proof_testing()
            } else {
                graph
            };
            let mut renderer = Renderer::default();
            let mut proofs = 0;
            let mut seen_concat = false;
            let mut seen_or = false;
            let mut proof_commands = vec![];
            for phase in Source::new(Some("scalar-proof.egg".into()), &source).unwrap() {
                let phase = phase.unwrap();
                for node in &phase.nodes {
                    if let Some(pb::node::Kind::Call(call)) = &node.kind {
                        match call.func.as_str() {
                            "egglog.core.string.concat" => {
                                assert_eq!(call.args.len(), arity);
                                seen_concat = true;
                            }
                            "egglog.core.bool.or" => {
                                assert_eq!(call.args.len(), arity);
                                seen_or = true;
                            }
                            _ => (),
                        }
                    }
                }
                let expected = phase
                    .commands
                    .iter()
                    .enumerate()
                    .filter_map(|(index, command)| {
                        let kind = match command.kind {
                            Some(pb::command::Kind::Run(_)) => "run",
                            Some(pb::command::Kind::Prove(_)) => {
                                proof_commands.push("prove");
                                "proof"
                            }
                            Some(pb::command::Kind::ProveExists(_)) => {
                                proof_commands.push("exists");
                                "proof"
                            }
                            _ => return None,
                        };
                        Some((vec![index as u32], kind))
                    })
                    .collect::<Vec<_>>();
                let decoded = pb::Program::decode(phase.encode_to_vec().as_slice()).unwrap();
                assert_eq!(decoded, phase);
                let text = renderer.render(&decoded).unwrap();
                let commands = native.parse_program(None, &text).unwrap();
                let mut requested = vec![];
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
                let response = run(&mut engine, id, decoded);
                assert_eq!(response.error, None, "mode={mode:?}, arity={arity}: {text}");
                let actual = response
                    .outputs
                    .iter()
                    .map(|output| {
                        let kind = match &output.kind {
                            Some(pb::command_output::Kind::Run(_)) => "run",
                            Some(pb::command_output::Kind::Proof(proof)) => {
                                proofs += 1;
                                assert!(proof.root.is_some());
                                assert!(!proof.terms.is_empty());
                                assert!(
                                    proof.proofs.iter().any(|p| matches!(
                                        p.justification,
                                        Some(pb::proof_step::Justification::Rule(_))
                                    )),
                                    "mode={mode:?}, arity={arity}, commands={:?}, proof={proof:?}",
                                    phase.commands
                                );
                                "proof"
                            }
                            _ => panic!("unrequested output"),
                        };
                        (output.location.as_ref().unwrap().path.clone(), kind)
                    })
                    .collect::<Vec<_>>();
                assert_eq!(actual, expected);
                assert_eq!(
                    actual.iter().map(|(_, kind)| *kind).collect::<Vec<_>>(),
                    requested
                );
                if !expected.iter().any(|(_, kind)| *kind == "run") {
                    assert!(
                        response.profile.as_ref().unwrap().runs.is_empty(),
                        "internal proof helpers are not authored runs"
                    );
                }
            }
            assert!(seen_concat && seen_or);
            assert_eq!(proof_commands, ["prove", "prove", "exists", "exists"]);
            assert_eq!(proofs, 4);
        }
    }
}

#[test]
fn schedule_controls_match_native_counts_sites_and_stopping_in_every_mode() {
    use egglog::ast::{Command, RunConfig, Schedule};
    use egglog::{ExecutionEvent, ExecutionOrigin, NativeLoopStop, RepeatContinuation};
    for mode in [
        pb::ExecutionMode::Normal,
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ] {
        for case in 0..9 {
            let mut native = match mode {
                pb::ExecutionMode::Normal => egglog::EGraph::default(),
                pb::ExecutionMode::TermEncoding => {
                    egglog::EGraph::default().with_term_encoding_enabled()
                }
                pb::ExecutionMode::Proofs => egglog::EGraph::default().with_proofs_enabled(),
                _ => egglog::EGraph::default()
                    .with_proofs_enabled()
                    .with_proof_testing(),
            };
            native.parse_and_run_program(None, "(datatype Num (N i64) (Goal i64) (Absent i64)) (ruleset r) (rule ((N x)) ((Goal x)) :ruleset r) (N 1)").unwrap();
            let leaf = Schedule::Run(
                egglog::span!(),
                RunConfig {
                    ruleset: "r".into(),
                    until: None,
                },
            );
            let mut program = fixture();
            let run_leaf = program.commands[1].clone();
            let mut body = vec![run_leaf.clone()];
            let mut native_body = vec![leaf.clone()];
            if case == 5 {
                body.clear();
                native_body.clear();
            }
            if case == 6 {
                body = vec![
                    run_leaf.clone(),
                    pb::Command {
                        kind: Some(pb::command::Kind::Saturate(pb::Saturate {
                            body: vec![run_leaf],
                            ..Default::default()
                        })),
                        ..Default::default()
                    },
                ];
                native_body = vec![
                    leaf.clone(),
                    Schedule::Saturate(
                        egglog::span!(),
                        Box::new(Schedule::Sequence(egglog::span!(), vec![leaf])),
                    ),
                ];
            }
            if case == 8 {
                body = vec![pb::Command {
                    kind: Some(pb::command::Kind::Repeat(pb::Repeat {
                        times: Some(2),
                        body,
                        ..Default::default()
                    })),
                    ..Default::default()
                }];
                native_body = vec![Schedule::Repeat(
                    egglog::span!(),
                    2,
                    Box::new(Schedule::Sequence(egglog::span!(), native_body)),
                )];
            }
            let native_body = Box::new(Schedule::Sequence(egglog::span!(), native_body));
            let (kind, schedule) = match case {
                0 | 1 => (
                    pb::command::Kind::Repeat(pb::Repeat {
                        times: Some(case),
                        body,
                        ..Default::default()
                    }),
                    Schedule::Repeat(egglog::span!(), case as usize, native_body),
                ),
                2 | 3 => (
                    pb::command::Kind::Saturate(pb::Saturate {
                        max_iterations: Some(case - 1),
                        body,
                        ..Default::default()
                    }),
                    Schedule::Repeat(egglog::span!(), (case - 1) as usize, native_body),
                ),
                7 | 8 => (
                    pb::command::Kind::Repeat(pb::Repeat {
                        times: Some(3),
                        body,
                        ..Default::default()
                    }),
                    Schedule::Repeat(egglog::span!(), 3, native_body),
                ),
                _ => (
                    pb::command::Kind::Saturate(pb::Saturate {
                        body,
                        ..Default::default()
                    }),
                    Schedule::Saturate(egglog::span!(), native_body),
                ),
            };
            let mut expected = None;
            let mut expected_report = None;
            let mut native_runs = 0;
            native
                .run_program_observed_with_repeat_policy(
                    vec![Command::RunSchedule(schedule)],
                    &mut |_, origin, output| {
                        if origin == ExecutionOrigin::Requested
                            && let egglog::CommandOutput::RunSchedule(report) = output
                        {
                            expected_report = Some(report);
                        }
                    },
                    &mut |_, event| match event {
                        ExecutionEvent::RunStarted {
                            origin: ExecutionOrigin::Requested,
                            ..
                        } => native_runs += 1,
                        ExecutionEvent::LoopFinished {
                            schedule: Some(site),
                            completed,
                            stop,
                            result,
                            ..
                        } if site.path.is_empty() => {
                            expected = Some((completed, stop.unwrap(), result.unwrap().updated));
                        }
                        _ => (),
                    },
                    &|_, _| {
                        if case >= 7 {
                            RepeatContinuation::ExactCount
                        } else {
                            RepeatContinuation::CanStop
                        }
                    },
                )
                .unwrap();
            let (completed, stop, updated) = expected.unwrap();
            if case >= 7 {
                assert_eq!(completed, 3);
                assert_eq!(native_runs, if case == 7 { 3 } else { 6 });
            }
            let reason = if case <= 1 || case >= 7 {
                pb::TerminationReason::CountReached
            } else if stop == NativeLoopStop::CountReached {
                pb::TerminationReason::IterationLimit
            } else {
                pb::TerminationReason::Saturated
            };
            program.commands.truncate(1);
            program.commands.push(pb::Command {
                kind: Some(kind),
                ..Default::default()
            });
            let mut engine = Engine::default();
            let id = create(&mut engine, mode);
            let response = pb::RunProgramResponse::decode(
                engine
                    .run(
                        &pb::RunProgramRequest {
                            egraph_id: id,
                            program: Some(program.clone()),
                            profile: true,
                            include_run_reports: true,
                        }
                        .encode_to_vec(),
                    )
                    .unwrap()
                    .as_slice(),
            )
            .unwrap();
            assert_eq!(response.error, None, "mode {mode:?}, case {case}");
            assert_eq!(response.outputs.len(), 1, "no nested control outputs");
            let Some(pb::command_output::Kind::Loop(outcome)) = &response.outputs[0].kind else {
                panic!("{response:?}")
            };
            assert_eq!(
                (outcome.iterations, outcome.termination, outcome.updated),
                (completed as u64, Some(reason.into()), updated),
                "mode {mode:?}, case {case}"
            );
            let report = response.outputs[0].run_report.as_ref().unwrap();
            let expected_report = expected_report.unwrap();
            assert_eq!(report.updated, expected_report.updated);
            assert_eq!(report.can_stop, expected_report.can_stop);
            assert_eq!(report.iterations.len(), expected_report.iterations.len());
            let profile = response.profile.unwrap();
            assert_eq!(
                profile.runs.iter().map(|run| run.invocations).sum::<u64>(),
                native_runs
            );
            for run in &profile.runs {
                assert!(
                    run.command_path == [1, 0]
                        || case == 6 && run.command_path == [1, 1, 0]
                        || case == 8 && run.command_path == [1, 0, 0]
                );
            }
            assert_eq!(profile.runs.is_empty(), case == 0 || case == 5);
            // Composite source remains explicitly unrenderable, even though
            // the native and byte execution paths now accept this subtree.
            assert!(
                egglog_experimental::protobuf::source::Renderer::default()
                    .render(&program)
                    .is_err()
            );
        }
    }
}

#[test]
fn composite_reports_use_only_entered_exact_aliases() {
    for mode in [
        pb::ExecutionMode::Normal,
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ] {
        for entered_alias in [false, true] {
            let mut program = fixture();
            let indexed = program.commands[1].clone();
            let mut named = indexed.clone();
            let Some(pb::command::Kind::Run(run)) = &mut named.kind else {
                unreachable!()
            };
            run.ruleset = Some(pb::RulesetRef {
                kind: Some(pb::ruleset_ref::Kind::Name("rebuilding_ruleset".into())),
            });
            let second = if entered_alias {
                named
            } else {
                pb::Command {
                    kind: Some(pb::command::Kind::Repeat(pb::Repeat {
                        times: Some(0),
                        body: vec![named],
                        ..Default::default()
                    })),
                    ..Default::default()
                }
            };
            program.commands.truncate(1);
            program.commands.push(indexed.clone());
            program.commands.push(pb::Command {
                kind: Some(pb::command::Kind::Repeat(pb::Repeat {
                    times: Some(1),
                    body: vec![indexed, second],
                    ..Default::default()
                })),
                ..Default::default()
            });
            let mut engine = Engine::default();
            let id = create(&mut engine, mode);
            let response = pb::RunProgramResponse::decode(
                engine
                    .run(
                        &pb::RunProgramRequest {
                            egraph_id: id,
                            program: Some(program),
                            profile: true,
                            include_run_reports: true,
                        }
                        .encode_to_vec(),
                    )
                    .unwrap()
                    .as_slice(),
            )
            .unwrap();
            assert_eq!(response.error, None);
            let first = response.outputs[0].run_report.as_ref().unwrap();
            let physical = &first
                .search_and_apply_time_per_ruleset
                .iter()
                .find(|row| {
                    row.ruleset
                        .as_ref()
                        .and_then(|reference| reference.kind.as_ref())
                        == Some(&pb::ruleset_ref::Kind::Index(0))
                })
                .unwrap()
                .native_name;
            let report = response.outputs[1].run_report.as_ref().unwrap();
            let profile = response.profile.as_ref().unwrap();
            assert_eq!(profile.runs.len(), if entered_alias { 3 } else { 2 });
            let authored: Vec<_> = report
                .search_and_apply_time_per_ruleset
                .iter()
                .filter(|row| &row.native_name == physical)
                .collect();
            assert_eq!(authored.len(), 1, "{mode:?}: {report:?}");
            assert_eq!(
                authored[0].ruleset,
                (!entered_alias).then_some(pb::RulesetRef {
                    kind: Some(pb::ruleset_ref::Kind::Index(0))
                })
            );
        }
    }
}

#[test]
fn dead_schedule_bodies_still_reject_before_effects_in_every_mode() {
    for mode in [
        pb::ExecutionMode::Normal,
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ] {
        for case in [
            "action",
            "fail",
            "stats",
            "repeat-until",
            "missing",
            "until",
            "scheduler",
            "unknown",
            "span",
        ] {
            let mut program = fixture();
            let mut invalid = program.commands[1].clone();
            match case {
                "action" => invalid = program.commands[0].clone(),
                "fail" => {
                    invalid = pb::Command {
                        kind: Some(pb::command::Kind::Fail(Box::new(invalid))),
                        ..Default::default()
                    }
                }
                "stats" => invalid.kind = Some(pb::command::Kind::Stats(pb::Unit {})),
                "repeat-until" | "missing" => {
                    invalid.kind = Some(pb::command::Kind::Repeat(pb::Repeat {
                        times: (case == "repeat-until").then_some(2),
                        until: if case == "repeat-until" {
                            vec![2]
                        } else {
                            vec![]
                        },
                        ..Default::default()
                    }))
                }
                "until" => {
                    invalid.kind = Some(pb::command::Kind::Saturate(pb::Saturate {
                        until: vec![2],
                        ..Default::default()
                    }))
                }
                "span" => {
                    invalid.span = Some(pb::Span {
                        file: 999,
                        start: 0,
                        end: 1,
                    })
                }
                _ => {
                    let Some(pb::command::Kind::Run(run)) = &mut invalid.kind else {
                        unreachable!()
                    };
                    if case == "scheduler" {
                        run.scheduler = "custom".into();
                    } else {
                        run.ruleset = Some(pb::RulesetRef {
                            kind: Some(pb::ruleset_ref::Kind::Index(99)),
                        });
                    }
                }
            }
            program.commands.truncate(1);
            program.commands.push(pb::Command {
                kind: Some(pb::command::Kind::Repeat(pb::Repeat {
                    times: Some(0),
                    body: vec![invalid],
                    ..Default::default()
                })),
                ..Default::default()
            });
            let mut engine = Engine::default();
            let id = create(&mut engine, mode);
            let response = run(&mut engine, id, program.clone());
            assert!(
                response.error.as_ref().unwrap().location.is_none(),
                "{mode:?}/{case}: {response:?}"
            );
            assert!(response.outputs.is_empty());
            assert!(response.ruleset_publication.unwrap().names.is_empty());
            let profile = response.profile.unwrap();
            assert!(profile.runs.is_empty() && profile.maintenance.is_empty());
            assert!(
                Renderer::core().render(&program).is_err(),
                "dead Core source body {case}"
            );
            // A following independent check must not find the earlier authored
            // seed; a dead branch did not turn preparation into partial execution.
            program.commands = vec![pb::Command {
                kind: Some(pb::command::Kind::Check(pb::Check { facts: vec![2] })),
                ..Default::default()
            }];
            let checked = run(&mut engine, id, program);
            assert!(checked.error.is_some());
        }
    }
}

#[test]
fn repeated_leaf_failure_discards_incomplete_rule_totals() {
    use egglog::ast::{Command, RunConfig, Schedule};
    use egglog::{ExecutionEvent, ExecutionOrigin};

    for (mode, exact) in [
        pb::ExecutionMode::Normal,
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ]
    .into_iter()
    .flat_map(|mode| [false, true].map(|exact| (mode, exact)))
    {
        let mut native = match mode {
            pb::ExecutionMode::Normal => egglog::EGraph::default(),
            pb::ExecutionMode::TermEncoding => {
                egglog::EGraph::default().with_term_encoding_enabled()
            }
            pb::ExecutionMode::Proofs => egglog::EGraph::default().with_proofs_enabled(),
            _ => egglog::EGraph::default()
                .with_proofs_enabled()
                .with_proof_testing(),
        };
        native.parse_and_run_program(None, "(datatype Num (N i64)) (ruleset r) (rule ((N x)) ((N (+ x 1))) :ruleset r :name \"derive\") (N 9223372036854775806)").unwrap();
        let mut leaves = vec![];
        let error = native
            .run_program_observed(
                vec![Command::RunSchedule(Schedule::Repeat(
                    egglog::span!(),
                    2,
                    Box::new(Schedule::Run(
                        egglog::span!(),
                        RunConfig {
                            ruleset: "r".into(),
                            until: None,
                        },
                    )),
                ))],
                &mut |_, _, _| panic!("failed schedule must not produce output"),
                &mut |_, event| {
                    if let ExecutionEvent::RunFinished {
                        origin: ExecutionOrigin::Requested,
                        result,
                        ..
                    } = event
                    {
                        leaves.push(
                            result
                                .map(|report| report.num_matches_per_rule.values().sum::<usize>())
                                .ok(),
                        );
                    }
                },
            )
            .unwrap_err();
        assert!(
            matches!(error, egglog::Error::BackendError(_)),
            "{mode:?}: {error:?}"
        );
        assert_eq!(leaves, [Some(1), None], "{mode:?}");
        native
            .parse_and_run_program(None, "(check (N 9223372036854775807))")
            .unwrap();

        let mut program = fixture();
        program.nodes[0].kind = Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::I64(i64::MAX - 1)),
        }));
        let one = program.nodes.len() as u32;
        program.nodes.push(pb::Node {
            sort_id: 0,
            kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::I64(1)),
            })),
            ..Default::default()
        });
        let sum = program.nodes.len() as u32;
        program.nodes.push(pb::Node {
            sort_id: 0,
            kind: Some(pb::node::Kind::Call(pb::Call {
                func: "egglog.core.i64.add".into(),
                args: vec![1, one],
            })),
            ..Default::default()
        });
        program.nodes[4].kind = Some(pb::node::Kind::Call(pb::Call {
            func: "N".into(),
            args: vec![sum],
        }));
        program.commands.truncate(2);
        program.commands[1] = pb::Command {
            kind: Some(if exact {
                pb::command::Kind::Repeat(pb::Repeat {
                    times: Some(2),
                    body: vec![pb::Command {
                        kind: Some(pb::command::Kind::Repeat(pb::Repeat {
                            times: Some(1),
                            body: vec![program.commands[1].clone()],
                            ..Default::default()
                        })),
                        ..Default::default()
                    }],
                    ..Default::default()
                })
            } else {
                pb::command::Kind::Saturate(pb::Saturate {
                    max_iterations: Some(2),
                    body: vec![program.commands[1].clone()],
                    ..Default::default()
                })
            }),
            ..Default::default()
        };
        let mut engine = Engine::default();
        let id = create(&mut engine, mode);
        let response = run(&mut engine, id, program);
        let error = response.error.unwrap();
        assert_eq!(error.code, i32::from(pb::ErrorCode::EvaluationFailed));
        let location = error.location.unwrap();
        let path = if exact { vec![1, 0, 0] } else { vec![1, 0] };
        assert_eq!(location.path, path);
        assert_eq!(
            location.iterations,
            if exact { vec![1, 0] } else { vec![1] }
        );
        assert!(response.outputs.is_empty());
        let profile = response.profile.unwrap();
        assert!(!profile.complete);
        assert_eq!(profile.runs.len(), 1);
        let summary = &profile.runs[0];
        assert_eq!(summary.command_path, path);
        assert_eq!(summary.invocations, 2);
        assert_eq!(
            (
                summary.search_and_apply_nanos,
                summary.merge_nanos,
                summary.rebuild_nanos
            ),
            (None, None, None)
        );
        assert!(
            summary.rules.is_empty(),
            "partial earlier totals survived: {summary:?}"
        );
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
                    include_run_reports: false,
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
