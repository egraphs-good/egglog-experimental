use egglog_experimental::proto as pb;
use egglog_experimental::protobuf::{
    Engine,
    source::{Renderer, Source},
};
use prost::Message;

#[test]
fn source_receiving_mode_preserves_actual_global_proof_requests() {
    // Keep these small original Core fixtures local: dependency packages need
    // not ship their test directories, and no sibling checkout is required.
    let fixtures = [
        (
            "commute-collapse",
            r#"
(datatype Math
  (Add i64 i64)
  (Num i64))

;; Commutativity
(rule ((Add a b)) ((union (Add a b) (Add b a))) :name "rw1")

;; Constant folding with an extra condition, forcing commute first
(rule ((Add a b)
       (> a b))
      ((union (Add a b) (Num (+ a b)))) :name "rw2")

;; 2 + 3
(let start (Add 2 3))

(run 2)

;; 2 + 3 = 5 by
;; 2 + 3 = 3 + 2 (commute)
;; 3 + 2 = 5 (constant fold)
(prove (= (Add 2 3) (Num 5)))"#,
        ),
        (
            "eqsat-basic-proof",
            r#"(datatype Math
  (Num i64)
  (Var String)
  (Add Math Math)
  (Mul Math Math))

;; expr1 = 2 * (x + 3)
(let $expr1 (Mul (Num 2) (Add (Var "x") (Num 3))))
;; expr2 = 6 + 2 * x
(let $expr2 (Add (Num 6) (Mul (Num 2) (Var "x"))))

;; (rule ((= __root (Add a b)))
;;       ((union __root (Add b a)))
(rewrite (Add a b)
         (Add b a))
(rewrite (Mul a (Add b c))
         (Add (Mul a b) (Mul a c)))
(rewrite (Add (Num a) (Num b))
         (Num (+ a b)))
(rewrite (Mul (Num a) (Num b))
         (Num (* a b)))

(run 10)
(prove (= $expr1 $expr2))
"#,
        ),
    ];
    for mode in [pb::ExecutionMode::Proofs, pb::ExecutionMode::ProofTesting] {
        for (fixture, authored) in fixtures {
            let graph = egglog::EGraph::default().with_proofs_enabled();
            let mut native = if mode == pb::ExecutionMode::ProofTesting {
                graph.with_proof_testing()
            } else {
                graph
            };
            let native_outputs = native.parse_and_run_program(None, authored).unwrap();
            assert_eq!(
                native_outputs
                    .iter()
                    .filter(|output| matches!(output, egglog::CommandOutput::ProveExists { .. }))
                    .count(),
                1
            );
            let mut text = authored.to_owned();
            for replay in 0..2 {
                let mut source = Source::new_core(None, &text)
                    .unwrap()
                    .with_execution_mode(mode)
                    .unwrap();
                let mut renderer = Renderer::core();
                let mut rendered = String::new();
                let mut engine = Engine::default();
                let id = create(&mut engine, mode);
                let mut proofs = 0;
                while let Some(submission) = source.next_submission() {
                    let egglog_experimental::protobuf::source::Submission::Program(program) =
                        submission.unwrap()
                    else {
                        panic!("unexpected scope")
                    };
                    rendered.push_str(&renderer.render(&program).unwrap());
                    let response = run(&mut engine, id, program);
                    assert_eq!(response.error, None, "{fixture}/{mode:?}/replay{replay}");
                    assert!(response.profile.unwrap().complete);
                    for output in response.outputs {
                        if let Some(pb::command_output::Kind::Proof(proof)) = output.kind {
                            assert!(
                                proof
                                    .root
                                    .is_some_and(|root| root < proof.proofs.len() as u32)
                            );
                            assert!(!proof.terms.is_empty());
                            proofs += 1;
                        }
                    }
                }
                assert_eq!(proofs, 1, "{fixture}/{mode:?}/replay{replay}");
                text = rendered;
            }
        }
    }
}

#[test]
fn source_receiving_mode_preserves_native_global_boundaries() {
    for mode in [
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ] {
        for (case, tail) in [
            ("sizes", "(let $cap (N 1)) (print-size)"),
            ("explicit-size", "(let $cap (N 1)) (print-size $cap)"),
            (
                "explicit-function",
                "(let $cap (N 1)) (print-function $cap)",
            ),
            ("set", "(let $cap (N 1)) (set ($cap) (N 2))"),
            ("delete", "(let $cap (N 1)) (delete ($cap))"),
            ("repeated-let", "(let $cap (N 1)) (let $cap (N 2))"),
            ("failed-init", "(fail (let $cap (N (/ 1 0)))) (print-size)"),
            (
                "failed-init-function",
                "(fail (let $cap (N (/ 1 0)))) (print-function $cap)",
            ),
            ("failed-expression", "(fail (N (/ 1 0))) (print-size)"),
            ("ordinary-function", "(function f () E :no-merge)"),
            ("primitive-let", "(let $base 1)"),
            ("presort-alias", "(sort V (Vec i64)) (sort W (Vec i64))"),
            (
                "different-shapes",
                "(sort V (Vec i64)) (sort W (Vec String)) (datatype X (XV V) (XW W)) (XW (vec-of \"one\")) (print-size) (rule ((XW xs)) ((XV xs)))",
            ),
            (
                "sort-header",
                "(sort S) (constructor A () S) (let $s (A)) (check (= $s (A)))",
            ),
            ("aggregate-size", "(let $cap (N 1)) (N (get-size!))"),
            ("aggregate-nodes", "(let $cap (N 1)) (N (get-node-size!))"),
            (
                "scope",
                "(push 1) (let $cap (N 1)) (check (= $cap (N 1))) (pop 1) (print-size)",
            ),
        ] {
            let text = format!("(datatype E (N i64)) {tail}");
            let graph = egglog_experimental::new_experimental_egraph();
            let mut native = match mode {
                pb::ExecutionMode::TermEncoding => graph.with_term_encoding_enabled(),
                pb::ExecutionMode::Proofs => graph.with_proofs_enabled(),
                _ => graph.with_proofs_enabled().with_proof_testing(),
            };
            let commands = native.parse_program(None, &text).unwrap();
            let mut native_outputs = vec![];
            let mut native_result = Ok(());
            let mut native_boundary = None;
            for (position, mut command) in commands.into_iter().enumerate() {
                // Whole-action evaluation uses the existing native scoped
                // boundary, not legacy term encoding's last-instruction catch.
                if case == "failed-expression"
                    && let egglog::ast::Command::Fail(span, child) = command
                {
                    let egglog::ast::Command::Action(action) = *child else {
                        panic!("expected authored expression")
                    };
                    command = egglog::ast::Command::Fail(
                        span.clone(),
                        Box::new(egglog::ast::Command::ActionScope(
                            span,
                            egglog::ast::Actions::new(vec![action]),
                        )),
                    );
                }
                if let Err(error) =
                    native.run_program_with_outputs(vec![command], &mut native_outputs)
                {
                    native_boundary = Some(position);
                    native_result = Err(error);
                    break;
                }
            }
            let mut source = Source::new(None, &text)
                .unwrap()
                .with_execution_mode(mode)
                .unwrap();
            let mut engine = Engine::default();
            let mut id = create(&mut engine, mode);
            let mut saved = vec![];
            let mut byte_sizes = vec![];
            let mut byte_error = None;
            let mut byte_boundary = None;
            let mut position = 0;
            while let Some(submission) = source.next_submission() {
                use egglog_experimental::protobuf::source::Submission;
                let current_position = position;
                position += 1;
                match submission {
                    Err(error) => {
                        byte_error = Some(error.to_string());
                        byte_boundary = Some(current_position);
                        break;
                    }
                    Ok(Submission::Program(program)) => {
                        let response = run(&mut engine, id, program);
                        for output in response.outputs {
                            if let Some(pb::command_output::Kind::Sizes(sizes)) = output.kind {
                                byte_sizes.push(
                                    sizes
                                        .sizes
                                        .into_iter()
                                        .map(|row| (row.table, row.rows))
                                        .collect::<Vec<_>>(),
                                );
                            }
                        }
                        if let Some(error) = response.error {
                            byte_error = Some(error.message);
                            byte_boundary = Some(current_position);
                            break;
                        }
                    }
                    Ok(Submission::Push(count)) => {
                        for _ in 0..count {
                            let bytes = engine
                                .clone_egraph(
                                    &pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec(),
                                )
                                .unwrap();
                            saved.push(id);
                            id = pb::CloneEGraphResponse::decode(bytes.as_slice())
                                .unwrap()
                                .egraph_id;
                        }
                    }
                    Ok(Submission::Pop { count, .. }) => {
                        for _ in 0..count {
                            let parent = saved.pop().unwrap();
                            engine
                                .return_to(
                                    &pb::ReturnToEGraphRequest {
                                        active_id: id,
                                        saved_id: parent,
                                    }
                                    .encode_to_vec(),
                                )
                                .unwrap();
                            id = parent;
                        }
                    }
                    Ok(Submission::PrintFunction(_)) => {
                        panic!("mode-boundary fixture must not contain host file presentation")
                    }
                }
            }
            let native_sizes = native_outputs
                .into_iter()
                .filter_map(|output| match output {
                    egglog::CommandOutput::PrintAllFunctionsSize(rows) => Some(
                        rows.into_iter()
                            .map(|(name, rows)| (name, rows as u64))
                            .collect::<Vec<_>>(),
                    ),
                    egglog::CommandOutput::PrintFunctionSize(rows) => {
                        Some(vec![("$cap".into(), rows as u64)])
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            eprintln!(
                "{case}/{mode:?}: native={:?}; bytes={byte_error:?}; sizes={byte_sizes:?}",
                native_result.as_ref().err().map(ToString::to_string)
            );
            if matches!(case, "failed-init" | "failed-init-function") {
                // Preserve the legacy Core failure/prefix witness independently.
                // Source does not expose an authored binder as a Fail child.
                assert!(native_result.is_err(), "{case}/{mode:?}");
                assert_eq!(native_boundary, Some(1), "{case}/{mode:?}");
                assert_eq!(
                    byte_error.as_deref(),
                    Some("source Fail does not support authored let bindings"),
                    "{case}/{mode:?}"
                );
                assert_eq!(byte_boundary, Some(1), "{case}/{mode:?}");
                assert!(byte_sizes.is_empty());
                assert!(source.next_submission().is_none());
            } else {
                assert_eq!(
                    byte_error.is_some(),
                    native_result.is_err(),
                    "{case}/{mode:?}"
                );
                assert_eq!(byte_boundary, native_boundary, "{case}/{mode:?}");
                assert_eq!(byte_sizes, native_sizes, "{case}/{mode:?}");
                if case == "failed-expression" {
                    assert!(native_result.is_ok());
                    assert_eq!(byte_sizes, [vec![("N".into(), 0)]]);
                }
            }
            // Observe the surviving operand table after failure/recovery without
            // materializing a term or reading a hidden global by default.
            let egglog::CommandOutput::PrintFunctionSize(native_n) =
                native.print_size(Some("N")).unwrap()
            else {
                panic!("native N observation")
            };
            let response = run(
                &mut engine,
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
            );
            assert_eq!(response.error, None, "recovery {case}/{mode:?}");
            let Some(pb::command_output::Kind::Sizes(sizes)) = &response.outputs[0].kind else {
                panic!("wire N observation")
            };
            assert_eq!(
                sizes.sizes[0].rows, native_n as u64,
                "prefix {case}/{mode:?}"
            );
        }
    }
}

#[test]
fn source_receiving_modes_preserve_canonical_sort_alias_uses() {
    let text = r#"
        (sort V (Vec i64)) (sort W (Vec i64))
        (sort NestedV (Vec V)) (sort NestedW (Vec W))
        (datatype X (XV V) (XW W) (Nested NestedW) (Value))
        (function f (V) X :merge old)
        (XW (vec-of 2)) (XW (vec-of 1))
        (rule ((XW xs)) ((XV xs) (set (f xs) (Value))))
        (run 1)
        (check (XV (vec-of 2)) (XV (vec-of 1)) (= (f (vec-of 1)) (Value)))
        (Nested (vec-of (vec-of 1)))
        (check (Nested (vec-of (vec-of 1))))
        (print-size)
    "#;
    // Source compound sorts are structural. Its independent native reference
    // uses the one canonical sort, not native's intentionally distinct V/W.
    let canonical = r#"
        (sort V (Vec i64)) (sort NestedV (Vec V))
        (datatype X (XV V) (XW V) (Nested NestedV) (Value))
        (function f (V) X :merge old)
        (XW (vec-of 2)) (XW (vec-of 1))
        (rule ((XW xs)) ((XV xs) (set (f xs) (Value))))
        (run 1)
        (check (XV (vec-of 2)) (XV (vec-of 1)) (= (f (vec-of 1)) (Value)))
        (Nested (vec-of (vec-of 1)))
        (check (Nested (vec-of (vec-of 1))))
        (print-size)
    "#;
    for mode in [
        pb::ExecutionMode::Normal,
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ] {
        let graph = egglog_experimental::new_experimental_egraph();
        let mut native = match mode {
            pb::ExecutionMode::Normal => graph,
            pb::ExecutionMode::TermEncoding => graph.with_term_encoding_enabled(),
            pb::ExecutionMode::Proofs => graph.with_proofs_enabled(),
            _ => graph.with_proofs_enabled().with_proof_testing(),
        };
        let outputs = native
            .parse_and_run_program(None, canonical)
            .unwrap_or_else(|error| panic!("canonical native/{mode:?}: {error}"));
        let native_proofs = outputs
            .iter()
            .filter(|output| matches!(output, egglog::CommandOutput::ProveExists { .. }))
            .count();
        let native_sizes = outputs
            .into_iter()
            .find_map(|output| match output {
                egglog::CommandOutput::PrintAllFunctionsSize(rows) => Some(
                    rows.into_iter()
                        .map(|(name, rows)| (name, rows as u64))
                        .collect::<Vec<_>>(),
                ),
                _ => None,
            })
            .unwrap();
        let source = Source::new(None, text)
            .unwrap()
            .with_execution_mode(mode)
            .unwrap();
        let mut engine = Engine::default();
        let id = create(&mut engine, mode);
        let mut proofs = 0;
        let mut sizes = None;
        let mut aliases = (false, false);
        for phase in source {
            let phase = phase.unwrap();
            for sort in &phase.sorts {
                let names = sort
                    .egglog_aliases
                    .iter()
                    .map(|alias| alias.symbol.as_str())
                    .collect::<Vec<_>>();
                aliases.0 |= names == ["V", "W"];
                aliases.1 |= names == ["NestedV", "NestedW"];
            }
            let response = run(&mut engine, id, phase);
            assert_eq!(response.error, None, "canonical aliases/{mode:?}");
            for output in response.outputs {
                match output.kind {
                    Some(pb::command_output::Kind::Proof(proof)) => {
                        assert!(
                            proof
                                .root
                                .is_some_and(|root| root < proof.proofs.len() as u32)
                        );
                        proofs += 1;
                    }
                    Some(pb::command_output::Kind::Sizes(rows)) => {
                        sizes = Some(
                            rows.sizes
                                .into_iter()
                                .map(|row| (row.table, row.rows))
                                .collect::<Vec<_>>(),
                        );
                    }
                    _ => {}
                }
            }
        }
        assert!(aliases.0 && aliases.1, "canonical alias metadata/{mode:?}");
        assert_eq!(sizes.unwrap(), native_sizes, "canonical aliases/{mode:?}");
        assert_eq!(proofs, native_proofs, "canonical aliases/{mode:?}");
    }
}

#[test]
fn source_receiving_modes_preserve_typed_multi_vec_empty_context() {
    let header = "(sort V (Vec i64)) (sort NestedV (Vec V)) (datatype X (XV V) (XW V) (Nested NestedV) (Value)) (function f (V) X :merge old)";
    let canonical = format!("{header} (XW (vec-empty))");
    let text = "(sort V (Vec i64)) (sort W (Vec i64)) (sort NestedV (Vec V)) (sort NestedW (Vec W)) (datatype X (XV V) (XW W) (Nested NestedW) (Value)) (function f (V) X :merge old) (XW (vec-empty)) (check (XW xs) (= (vec-length xs) 0))";
    for mode in [
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ] {
        let graph = egglog_experimental::new_experimental_egraph();
        let mut native = match mode {
            pb::ExecutionMode::TermEncoding => graph.with_term_encoding_enabled(),
            pb::ExecutionMode::Proofs => graph.with_proofs_enabled(),
            _ => graph.with_proofs_enabled().with_proof_testing(),
        };
        let commands = native.parse_program(None, &canonical).unwrap();
        let mut native_failure = None;
        for (position, command) in commands.into_iter().enumerate() {
            if let Err(error) = native.run_program(vec![command]) {
                native_failure = Some((position, error.to_string()));
                break;
            }
        }
        let (position, message) = native_failure.expect("native ambiguity must remain visible");
        assert_eq!(position, 4, "native/{mode:?}");
        assert!(message.contains("Failed to infer a type for: @vec-empty"));
        assert!(matches!(
            native.print_size(Some("XW")).unwrap(),
            egglog::CommandOutput::PrintFunctionSize(0)
        ));

        // Legacy action instrumentation loses the enclosing XW type context
        // when it emits an isolated vec-empty Let. Typed wire actions retain
        // that context in a native ActionScope; compare independently against
        // the same native scoped boundary, not the erased legacy expression.
        let graph = egglog_experimental::new_experimental_egraph();
        let mut contextual = match mode {
            pb::ExecutionMode::TermEncoding => graph.with_term_encoding_enabled(),
            pb::ExecutionMode::Proofs => graph.with_proofs_enabled(),
            _ => graph.with_proofs_enabled().with_proof_testing(),
        };
        contextual.parse_and_run_program(None, header).unwrap();
        let egglog::ast::Command::Action(action) = contextual
            .parse_program(None, "(XW (vec-empty))")
            .unwrap()
            .remove(0)
        else {
            panic!("native contextual action")
        };
        contextual
            .run_program(vec![egglog::ast::Command::ActionScope(
                egglog::span!(),
                egglog::ast::GenericActions::new(vec![action]),
            )])
            .unwrap();
        contextual
            .parse_and_run_program(None, "(check (XW xs) (= (vec-length xs) 0))")
            .unwrap();
        assert!(matches!(
            contextual.print_size(Some("XW")).unwrap(),
            egglog::CommandOutput::PrintFunctionSize(1)
        ));
        let source = Source::new(None, text)
            .unwrap()
            .with_execution_mode(mode)
            .unwrap();
        let mut engine = Engine::default();
        let id = create(&mut engine, mode);
        for (position, phase) in source.enumerate() {
            let response = run(
                &mut engine,
                id,
                phase.expect("producer must preserve valid aliases"),
            );
            assert_eq!(response.error, None, "typed phase {position}/{mode:?}");
        }
        let response = run(
            &mut engine,
            id,
            pb::Program {
                commands: vec![pb::Command {
                    kind: Some(pb::command::Kind::PrintSize(pb::PrintSize {
                        tables: vec!["XW".into()],
                    })),
                    ..Default::default()
                }],
                ..Default::default()
            },
        );
        assert_eq!(response.error, None);
        let Some(pb::command_output::Kind::Sizes(sizes)) = &response.outputs[0].kind else {
            panic!("typed XW size")
        };
        assert_eq!(
            sizes.sizes[0].rows, 1,
            "contextual empty publication/{mode:?}"
        );
    }
}

#[test]
fn source_receiving_mode_aggregate_values_match_native_exactly() {
    // Capture both reads in inert i64 relation inputs before any observation.
    // Normal supports these primitives; encoded modes reject their missing
    // validators; the native-global test retains those rejection cases.
    let text = "(datatype E (N i64)) (let $cap (N 1)) (relation Observed (i64 i64)) (Observed (get-size!) (get-node-size!)) (print-function Observed)";
    let mut native = egglog_experimental::new_experimental_egraph();
    let mut native_values = vec![];
    for output in native.parse_and_run_program(None, text).unwrap() {
        if let egglog::CommandOutput::PrintFunction(_, dag, rows, _) = output {
            for (term, _) in rows {
                let egglog::Term::App(_, args) = dag.get(term) else {
                    panic!("native relation row must be an application")
                };
                native_values.push(
                    args.iter()
                        .map(|term| match dag.get(*term) {
                            egglog::Term::Lit(egglog::ast::Literal::Int(value)) => *value,
                            other => panic!("native size input must be i64: {other:?}"),
                        })
                        .collect::<Vec<_>>(),
                );
            }
        }
    }
    let source = Source::new(None, text)
        .unwrap()
        .with_execution_mode(pb::ExecutionMode::Normal)
        .unwrap();
    let mut engine = Engine::default();
    let id = create(&mut engine, pb::ExecutionMode::Normal);
    let mut byte_values = vec![];
    for phase in source {
        let response = run(&mut engine, id, phase.unwrap());
        assert_eq!(response.error, None);
        for output in &response.outputs {
            if let Some(pb::command_output::Kind::PrintedFunction(table)) = &output.kind {
                assert_eq!(table.table, "Observed");
                for row in &table.rows {
                    byte_values.push(
                        row.args
                            .iter()
                            .map(|cell| {
                                let Some(pb::table_cell::Kind::Term(term)) = &cell.kind else {
                                    panic!("encoded size input must be available")
                                };
                                match &response.nodes[*term as usize].kind {
                                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                                        value: Some(pb::primitive_value::Value::I64(value)),
                                    })) => *value,
                                    other => panic!("encoded size input must be i64: {other:?}"),
                                }
                            })
                            .collect::<Vec<_>>(),
                    );
                }
            }
        }
    }
    assert_eq!(native_values.len(), 1);
    assert_eq!(native_values[0].len(), 2);
    assert_eq!(
        byte_values, native_values,
        "exact captured aggregate values"
    );
}

#[test]
fn source_receiving_mode_is_fixed_before_first_submission_and_normal_stays_function_set() {
    let text = "(datatype E (N i64)) (let $cap (N 1))";
    let mut source = Source::new(None, text).unwrap();
    source.next_submission().unwrap().unwrap();
    assert!(
        source
            .with_execution_mode(pb::ExecutionMode::Proofs)
            .is_err()
    );
    let source = Source::new(None, text)
        .unwrap()
        .with_execution_mode(pb::ExecutionMode::Normal)
        .unwrap();
    assert!(
        source
            .with_execution_mode(pb::ExecutionMode::Proofs)
            .is_err()
    );
    let programs = Source::new(None, text)
        .unwrap()
        .with_execution_mode(pb::ExecutionMode::Normal)
        .unwrap()
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    assert!(programs.iter().flat_map(|program| &program.declarations).any(|declaration|
        matches!(&declaration.kind, Some(pb::declaration::Kind::Function(function))
            if function.name == "$cap" && function.inputs.is_empty() && function.merge.is_none())
    ));
    assert!(programs.iter().flat_map(|program| &program.commands).any(
        |command| matches!(&command.kind, Some(pb::command::Kind::Action(action))
            if matches!(&action.kind, Some(pb::action::Kind::Set(set))
                if set.target.as_ref().is_some_and(|target| target.func == "$cap")))
    ));
}

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
                {
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
                }
                let suffix = pb::Command {
                    kind: Some(pb::command::Kind::Check(pb::Check { facts: vec![3] })),
                    ..Default::default()
                };
                let checked = run(
                    &mut engine,
                    id,
                    pb::Program {
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

#[test]
fn logical_table_rows_match_native_views_in_every_mode() {
    use egglog_experimental::builtin::PortableEGraph;
    type ObservedRows = Vec<(Vec<(String, Option<String>)>, bool)>;

    fn sort_shape(sorts: &[pb::Sort], index: u32) -> String {
        match sorts[index as usize].kind.as_ref().unwrap() {
            pb::sort::Kind::Eq(name) => format!("Eq({name})"),
            pb::sort::Kind::Family(family) => format!(
                "{}({})",
                family.name,
                family
                    .args
                    .iter()
                    .map(|arg| sort_shape(sorts, *arg))
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            other => panic!("unexpected observation sort {other:?}"),
        }
    }

    fn wire_term(response: &pb::RunProgramResponse, index: u32) -> String {
        match response.nodes[index as usize].kind.as_ref().unwrap() {
            pb::node::Kind::Call(call) => format!(
                "({}{})",
                call.func,
                call.args
                    .iter()
                    .map(|arg| format!(" {}", wire_term(response, *arg)))
                    .collect::<String>()
            ),
            pb::node::Kind::PrimitiveValue(value) => match value.value.as_ref().unwrap() {
                pb::primitive_value::Value::I64(value) => value.to_string(),
                pb::primitive_value::Value::Unit(_) => "()".into(),
                pb::primitive_value::Value::Vec(values) => format!(
                    "(vec-of{})",
                    values
                        .items
                        .iter()
                        .map(|arg| format!(" {}", wire_term(response, *arg)))
                        .collect::<String>()
                ),
                other => panic!("unexpected observation value {other:?}"),
            },
            other => panic!("unexpected observation node {other:?}"),
        }
    }

    fn wire_rows(response: &pb::RunProgramResponse, table: &pb::PrintedFunction) -> ObservedRows {
        table
            .rows
            .iter()
            .map(|row| {
                let cells = row
                    .args
                    .iter()
                    .chain(row.output.iter())
                    .map(|cell| match cell.kind.unwrap() {
                        pb::table_cell::Kind::Term(term) => (
                            sort_shape(&response.sorts, response.nodes[term as usize].sort_id),
                            Some(wire_term(response, term)),
                        ),
                        pb::table_cell::Kind::UnavailableSort(sort) => {
                            (sort_shape(&response.sorts, sort), None)
                        }
                    })
                    .collect::<Vec<_>>();
                (cells, row.subsumed)
            })
            .collect()
    }

    // Each cell retains both its exact public type and representative, when
    // one exists. Compare scan order and flags without sorting/deduplicating.
    fn native_rows(
        graph: &egglog::EGraph,
        table: &str,
        relation: bool,
        limit: Option<u64>,
    ) -> ObservedRows {
        let mut rows = vec![];
        let input_sorts;
        let output_sort;
        if let Some((name, view)) = graph
            .functions_iter()
            .find(|(_, function)| function.term_constructor() == Some(table))
        {
            let (output, inputs) = view.func_type().input.split_last().unwrap();
            input_sorts = inputs.to_vec();
            output_sort = output.clone();
            graph
                .function_entries(name, |row| {
                    let (output, inputs) = row.inputs.split_last().unwrap();
                    rows.push((inputs.to_vec(), *output, row.subsumed));
                })
                .unwrap();
        } else {
            let function = graph.get_function(table).unwrap();
            input_sorts = function.func_type().input.clone();
            output_sort = function.func_type().output.clone();
            match graph.constructor_enodes(table, |row| {
                rows.push((row.children.to_vec(), row.eclass, row.subsumed))
            }) {
                Ok(()) => (),
                Err(egglog::Error::ApiError(egglog::ApiError::WrongSubtype { .. })) => {
                    graph
                        .function_entries(table, |row| {
                            rows.push((row.inputs.to_vec(), row.output, row.subsumed))
                        })
                        .unwrap();
                }
                Err(error) => panic!("native scan: {error}"),
            }
        }
        rows.truncate(limit.map_or(usize::MAX, |limit| limit as usize));
        rows.into_iter()
            .map(|(args, output, subsumed)| {
                let roots = args
                    .into_iter()
                    .zip(input_sorts.iter().cloned())
                    .map(|(value, sort)| (sort, value))
                    .chain((!relation).then(|| (output_sort.clone(), output)))
                    .collect::<Vec<_>>();
                let extracted = graph.extract_best(roots.clone()).unwrap();
                let mut cells = roots
                    .iter()
                    .zip(extracted.terms)
                    .map(|((sort, _), term)| {
                        let mut sorts = vec![];
                        let index = graph.export_sort(sort, &mut sorts).unwrap();
                        (
                            sort_shape(&sorts, index),
                            term.map(|term| extracted.termdag.to_string(term.term)),
                        )
                    })
                    .collect::<Vec<_>>();
                if relation {
                    cells.push(("Unit()".into(), Some("()".into())));
                }
                (cells, subsumed)
            })
            .collect()
    }

    let setup = "(sort E) (constructor Hidden () E :unextractable) \
        (constructor Visible () E) (constructor Row (i64) E) \
        (sort VI (Vec i64)) (constructor Container (VI E) E) \
        (relation Rel (i64 E VI)) (relation Empty (i64)) (relation Nullary ()) \
        (relation Gone (i64)) (Gone 9) (delete (Gone 9)) \
        (function f (E i64 E) E :merge new) \
        (function numbers (i64) VI :merge new) (function scalar () i64 :merge new) \
        (set (f (Hidden) 1 (Hidden)) (Visible)) \
        (set (f (Visible) 2 (Hidden)) (Hidden)) \
        (set (numbers 1) (vec-of 8 9)) (set (scalar) 10) (set (scalar) 20) \
        (Container (vec-of 3 4) (Visible)) (Row 3) (Row 4) \
        (subsume (Row 3)) (Rel 5 (Hidden) (vec-of 6 7)) (Nullary) \
        (let $cap (Visible))";
    let tables = [
        "f",
        "Hidden",
        "Row",
        "Container",
        "numbers",
        "scalar",
        "Rel",
        "Empty",
        "Nullary",
        "Gone",
        "$cap",
    ];
    for mode in [
        pb::ExecutionMode::Normal,
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ] {
        let graph = egglog_experimental::new_experimental_egraph();
        let mut native = match mode {
            pb::ExecutionMode::Normal => graph,
            pb::ExecutionMode::TermEncoding => graph.with_term_encoding_enabled(),
            pb::ExecutionMode::Proofs => graph.with_proofs_enabled(),
            _ => graph.with_proofs_enabled().with_proof_testing(),
        };
        for command in native.parse_program(None, setup).unwrap() {
            native
                .run_program(vec![command])
                .unwrap_or_else(|error| panic!("native setup/{mode:?}: {error}"));
        }
        let capture_dump = native
            .parse_and_run_program(None, "(print-function $cap)")
            .unwrap();
        let captures = capture_dump
            .iter()
            .filter_map(|output| match output {
                egglog::CommandOutput::PrintFunction(_, dag, rows, _) => Some((dag, rows)),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(
            captures.len(),
            1,
            "native explicit hidden capture dump/{mode:?}"
        );
        let (dag, capture) = captures[0];
        assert_eq!(capture.len(), 1);
        let capture_value = dag.to_string(capture[0].1);
        let mut engine = Engine::default();
        let id = create(&mut engine, mode);
        let mut text = setup.to_owned();
        for table in tables {
            for limit in [None, Some(0), Some(1)] {
                text.push_str(&format!(
                    " (print-function {table}{})",
                    limit.map(|n| format!(" {n}")).unwrap_or_default()
                ));
            }
        }
        // Observe live changes separately from immutable term-table history.
        let mutations = "(delete (Row 4)) (delete (Rel 5 (Hidden) (vec-of 6 7))) (Rel 6 (Visible) (vec-of 1 2)) (set (scalar) 30) (delete (numbers 1))";
        text.push_str(mutations);
        text.push_str(" (print-function Row) (print-function Rel) (print-function scalar) (print-function numbers)");
        let mut observations = 0;
        for phase in Source::new(None, &text)
            .unwrap()
            .with_execution_mode(mode)
            .unwrap()
        {
            let phase = phase.unwrap();
            let requests = phase
                .commands
                .iter()
                .filter_map(|command| match &command.kind {
                    Some(pb::command::Kind::PrintFunction(print)) => Some(print.clone()),
                    _ => None,
                })
                .collect::<Vec<_>>();
            if observations == tables.len() * 3 && !requests.is_empty() {
                // Advance the independent native state through the same
                // mutations once, before the first post-mutation observation.
                native.parse_and_run_program(None, mutations).unwrap();
            }
            let response = run(&mut engine, id, phase);
            assert_eq!(response.error, None, "{mode:?}");
            assert_eq!(response.outputs.len(), requests.len());
            for (output, request) in response.outputs.iter().zip(requests) {
                let Some(pb::command_output::Kind::PrintedFunction(table)) = &output.kind else {
                    panic!("table observation")
                };
                let actual = wire_rows(&response, table);
                assert_eq!(table.table, request.table);
                assert_eq!(
                    actual,
                    native_rows(
                        &native,
                        &table.table,
                        ["Rel", "Empty", "Nullary", "Gone"].contains(&table.table.as_str()),
                        request.max_rows
                    ),
                    "{mode:?}/{} limit {:?}",
                    table.table,
                    request.max_rows
                );
                if table.table == "$cap" && request.max_rows != Some(0) {
                    assert_eq!(actual[0].0, [("Eq(E)".into(), Some(capture_value.clone()))]);
                }
                assert!(
                    response.sorts.iter().all(
                        |sort| !matches!(&sort.kind, Some(pb::sort::Kind::Eq(name)) if name != "E")
                    ),
                    "private classes/witnesses must stay private"
                );
                observations += 1;
            }
        }
        assert_eq!(observations, tables.len() * 3 + 4);
        if mode != pb::ExecutionMode::Normal {
            // Raw native text dumps retained term-table history. This is an
            // explicit boundary, not a universal Source text dump parity claim.
            let history_dump = native
                .parse_and_run_program(None, "(print-function Row)")
                .unwrap();
            let histories = history_dump
                .iter()
                .filter_map(|output| match output {
                    egglog::CommandOutput::PrintFunction(_, _, rows, _) => Some(rows),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(histories.len(), 1, "native historical term dump/{mode:?}");
            let historical = histories[0];
            let live = native_rows(&native, "Row", false, None);
            assert_eq!(historical.len(), 2);
            assert_eq!(live.len(), 1);
            assert!(live[0].1, "the remaining Row(3) is subsumed");
        }

        // Encoded initialization can allocate its nullary row before failing.
        // Preserve that native prefix and exact unavailable public type. Stop
        // its Source stream at the error; observe with a fresh request.
        assert!(
            native
                .parse_and_run_program(None, "(let $bad (Row (/ 1 0)))")
                .is_err()
        );
        let expected = native_rows(&native, "$bad", false, None);
        let mut failed = false;
        for phase in Source::new(None, &format!("{setup} (let $bad (Row (/ 1 0)))"))
            .unwrap()
            .with_execution_mode(mode)
            .unwrap()
        {
            let response = run(&mut engine, id, phase.unwrap());
            if response.error.is_some() {
                failed = true;
                break;
            }
        }
        assert!(failed, "failed initializer/{mode:?}");
        let response = run(
            &mut engine,
            id,
            pb::Program {
                commands: vec![pb::Command {
                    kind: Some(pb::command::Kind::PrintFunction(pb::PrintFunction {
                        table: "$bad".into(),
                        max_rows: None,
                    })),
                    ..Default::default()
                }],
                ..Default::default()
            },
        );
        assert_eq!(response.error, None, "failed initializer table/{mode:?}");
        assert_eq!(response.outputs.len(), 1);
        let Some(pb::command_output::Kind::PrintedFunction(table)) = &response.outputs[0].kind
        else {
            panic!("failed initializer observation")
        };
        assert_eq!(
            wire_rows(&response, table),
            expected,
            "failed initializer prefix/{mode:?}"
        );
    }
}

#[test]
fn table_observation_keeps_completed_prefix_and_encoding_errors_are_not_unavailability() {
    use egglog_experimental::protobuf::NativeExtension;
    use std::sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    };

    #[derive(Default)]
    struct RejectEncoding {
        initializations: AtomicUsize,
        encodings: AtomicUsize,
    }
    impl NativeExtension for RejectEncoding {
        fn initialize(&self, _: &mut egglog::EGraph) -> Result<(), String> {
            self.initializations.fetch_add(1, Ordering::SeqCst);
            Ok(())
        }
        fn lower_custom_value(
            &self,
            _: &egglog::EGraph,
            _: &egglog::ArcSort,
            _: &pb::CustomValue,
            _: Option<pb::Span>,
            _: &mut pb::Program,
        ) -> Result<pb::Call, String> {
            Err("unused custom lowering".into())
        }
        fn encode_custom_value(
            &self,
            _: &egglog::ArcSort,
            _: &egglog::TermDag,
            _: egglog::TermId,
        ) -> Result<Option<pb::CustomValue>, String> {
            self.encodings.fetch_add(1, Ordering::SeqCst);
            Err("deliberate table encoding failure".into())
        }
    }
    for mode in [
        pb::ExecutionMode::Normal,
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ] {
        let mut engine = Engine::default();
        let id = create(&mut engine, mode);
        let mut program = fixture();
        program.commands.truncate(1);
        assert_eq!(run(&mut engine, id, program.clone()).error, None);
        program.commands = vec![
            pb::Command {
                kind: Some(pb::command::Kind::PrintFunction(pb::PrintFunction {
                    table: "N".into(),
                    max_rows: None,
                })),
                ..Default::default()
            },
            fixture().commands[2].clone(),
        ];
        let response = run(&mut engine, id, program);
        assert!(response.error.is_some());
        assert!(
            matches!(&response.outputs[..], [output] if matches!(&output.kind, Some(pb::command_output::Kind::PrintedFunction(table)) if table.rows.len() == 1))
        );

        let provider = Arc::new(RejectEncoding::default());
        let mut engine = Engine::with_extension(provider.clone());
        let id = create(&mut engine, mode);
        let initialized = provider.initializations.load(Ordering::SeqCst);
        let mut program = fixture();
        program.commands.truncate(1);
        assert_eq!(run(&mut engine, id, program.clone()).error, None);
        program.commands = vec![
            pb::Command {
                kind: Some(pb::command::Kind::PrintSize(pb::PrintSize {
                    tables: vec!["N".into()],
                })),
                ..Default::default()
            },
            pb::Command {
                kind: Some(pb::command::Kind::PrintFunction(pb::PrintFunction {
                    table: "N".into(),
                    max_rows: None,
                })),
                ..Default::default()
            },
        ];
        let response = run(&mut engine, id, program.clone());
        assert!(
            response
                .error
                .unwrap()
                .message
                .contains("deliberate table encoding failure")
        );
        assert!(
            matches!(&response.outputs[..], [output] if matches!(output.kind, Some(pb::command_output::Kind::Sizes(_))))
        );
        assert!(provider.encodings.load(Ordering::SeqCst) > 0);
        let encoded = provider.encodings.load(Ordering::SeqCst);
        program.commands.remove(0);
        let Some(pb::command::Kind::PrintFunction(print)) = &mut program.commands[0].kind else {
            unreachable!()
        };
        print.max_rows = Some(0);
        let response = run(&mut engine, id, program);
        assert_eq!(response.error, None);
        assert!(
            matches!(&response.outputs[..], [output] if matches!(&output.kind, Some(pb::command_output::Kind::PrintedFunction(table)) if table.rows.is_empty()))
        );
        assert!(response.nodes.is_empty() && response.sorts.is_empty());
        assert_eq!(provider.encodings.load(Ordering::SeqCst), encoded);
        assert_eq!(provider.initializations.load(Ordering::SeqCst), initialized);
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
                    ..Default::default()
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
        rules: vec![pb::Rule {
            name: Some("derive".into()),
            eval_mode: pb::RuleEvalMode::Seminaive.into(),
            kind: Some(pb::rule::Kind::Rule(pb::RuleBody {
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
        let Some(pb::rule::Kind::Rule(rule)) = &mut program.rules[0].kind else {
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
fn malformed_later_commands_unused_rules_and_observations_are_atomic_preparation() {
    for mode in [
        pb::ExecutionMode::Normal,
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ] {
        for invalid in 0..7 {
            if invalid == 3 && mode == pb::ExecutionMode::Normal {
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
                    let Some(pb::rule::Kind::Rule(rule)) = &mut program.rules[0].kind else {
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
                4 | 5 => {
                    if invalid == 5 {
                        program.declarations.push(pb::Declaration {
                            kind: Some(pb::declaration::Kind::Primitive(pb::Primitive {
                                name: "computed".into(),
                                inputs: vec![],
                                output: 0,
                                body: Some(0),
                            })),
                            ..Default::default()
                        });
                    }
                    program.commands.push(pb::Command {
                        kind: Some(pb::command::Kind::PrintFunction(pb::PrintFunction {
                            table: if invalid == 5 { "computed" } else { "missing" }.into(),
                            max_rows: Some(0),
                        })),
                        ..Default::default()
                    });
                }
                _ => {
                    program.declarations.push(pb::Declaration {
                        kind: Some(pb::declaration::Kind::Relation(pb::Relation {
                            name: "Predicate".into(),
                            inputs: vec![pb::Arg {
                                name: "x".into(),
                                sort: 0,
                            }],
                        })),
                        ..Default::default()
                    });
                    program.commands.push(pb::Command {
                        kind: Some(pb::command::Kind::Action(pb::Action {
                            kind: Some(pb::action::Kind::Subsume(pb::Call {
                                func: "Predicate".into(),
                                args: vec![0],
                            })),
                            ..Default::default()
                        })),
                        ..Default::default()
                    });
                }
            }
            let failed = run(&mut engine, id, program);
            assert!(failed.error.is_some());
            if invalid == 6 {
                assert!(
                    failed
                        .error
                        .as_ref()
                        .unwrap()
                        .message
                        .contains("relation rows cannot be Subsumed")
                );
            }
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
            if case == 0 {
                let outputs = native
                    .clone()
                    .parse_and_run_program(None, "(check (N 1))")
                    .unwrap();
                let proofs = outputs
                    .iter()
                    .filter(|output| matches!(output, egglog::CommandOutput::ProveExists { .. }))
                    .count();
                assert_eq!(proofs, usize::from(mode == pb::ExecutionMode::ProofTesting));
                assert!(outputs.iter().all(|output| matches!(
                    output,
                    egglog::CommandOutput::ProveExists { .. }
                        | egglog::CommandOutput::RunSchedule(_)
                )));
            }
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
            if case == 3 {
                let mut whole_body = program.clone();
                let Some(pb::command::Kind::Saturate(saturate)) = &mut whole_body.commands[1].kind
                else {
                    unreachable!()
                };
                saturate.body.push(saturate.body[0].clone());
                let rendered = Renderer::default().render(&whole_body).unwrap();
                assert!(
                    Source::new(None, &rendered)
                        .unwrap()
                        .all(|phase| phase.is_ok())
                );
            }
            // Exact Repeat and general Saturate are representable. Reparse text and
            // retain the independent native count/report oracle above.
            let mut replay_program = program.clone();
            replay_program.commands.push(pb::Command {
                kind: Some(pb::command::Kind::Check(pb::Check { facts: vec![2] })),
                ..Default::default()
            });
            let goal = pb::Command {
                kind: Some(pb::command::Kind::Check(pb::Check { facts: vec![5] })),
                ..Default::default()
            };
            replay_program.commands.push(if matches!(case, 0 | 5) {
                pb::Command {
                    kind: Some(pb::command::Kind::Fail(Box::new(goal))),
                    ..Default::default()
                }
            } else {
                goal
            });
            let rendered = Renderer::default().render(&replay_program).unwrap();
            let replay_id = create(&mut engine, mode);
            let mut loops = 0;
            let mut proofs = 0;
            let mut replay_runs = 0;
            for phase in Source::new(Some("rendered-control.egg".into()), &rendered).unwrap() {
                let phase = phase.unwrap();
                let check_phase = matches!(
                    phase.commands.as_slice(),
                    [pb::Command {
                        kind: Some(pb::command::Kind::Check(_)),
                        ..
                    }]
                );
                let replay = pb::RunProgramResponse::decode(
                    engine
                        .run(
                            &pb::RunProgramRequest {
                                egraph_id: replay_id,
                                program: Some(phase),
                                profile: true,
                                include_run_reports: true,
                            }
                            .encode_to_vec(),
                        )
                        .unwrap()
                        .as_slice(),
                )
                .unwrap();
                assert_eq!(replay.error, None, "{mode:?}/{case}: {rendered}");
                for output in &replay.outputs {
                    if let Some(pb::command_output::Kind::Proof(proof)) = &output.kind {
                        assert!(check_phase);
                        assert_eq!(mode, pb::ExecutionMode::ProofTesting);
                        assert!(!proof.terms.is_empty());
                        assert!((proof.root.unwrap() as usize) < proof.proofs.len());
                        assert!(output.run_report.is_none());
                        proofs += 1;
                        continue;
                    }
                    let Some(pb::command_output::Kind::Loop(outcome)) = &output.kind else {
                        panic!("unexpected replay output: {output:?}")
                    };
                    loops += 1;
                    assert_eq!(output.location.as_ref().unwrap().path, [0]);
                    assert_eq!(
                        (outcome.iterations, outcome.termination, outcome.updated),
                        (completed as u64, Some(reason.into()), updated)
                    );
                    let report = output.run_report.as_ref().unwrap();
                    assert_eq!(report.updated, expected_report.updated);
                    assert_eq!(report.can_stop, expected_report.can_stop);
                    assert_eq!(report.iterations.len(), expected_report.iterations.len());
                }
                let profile = replay.profile.unwrap();
                assert!(profile.complete);
                replay_runs += profile.runs.iter().map(|run| run.invocations).sum::<u64>();
                for run in &profile.runs {
                    assert!(
                        run.command_path == [0, 0]
                            || case == 6 && run.command_path == [0, 1, 0]
                            || case == 8 && run.command_path == [0, 0, 0]
                    );
                }
            }
            assert_eq!(loops, 1);
            assert_eq!(
                proofs,
                if mode == pb::ExecutionMode::ProofTesting {
                    if matches!(case, 0 | 5) { 1 } else { 2 }
                } else {
                    0
                },
                "{mode:?}/{case}"
            );
            assert_eq!(replay_runs, native_runs);
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
fn dead_schedule_bodies_are_validated_before_effects_in_every_mode() {
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
            let valid = matches!(case, "action" | "fail" | "repeat-until" | "until")
                || case == "stats" && mode == pb::ExecutionMode::Normal;
            if valid {
                assert_eq!(response.error, None, "{mode:?}/{case}: {response:?}");
                assert_eq!(response.outputs.len(), 1);
                let output = &response.outputs[0];
                assert_eq!(output.location.as_ref().unwrap().path, [1]);
                assert!(output.location.as_ref().unwrap().iterations.is_empty());
                assert!(output.run_report.is_none());
                let Some(pb::command_output::Kind::Loop(outcome)) = &output.kind else {
                    panic!("{mode:?}/{case}: {output:?}")
                };
                assert_eq!(
                    (outcome.iterations, outcome.termination, outcome.updated),
                    (0, Some(pb::TerminationReason::CountReached.into()), false)
                );
                assert_eq!(
                    response.ruleset_publication.as_ref().unwrap().names,
                    ["rebuilding_ruleset"]
                );
            } else {
                assert!(
                    response.error.as_ref().unwrap().location.is_none(),
                    "{mode:?}/{case}: {response:?}"
                );
                assert!(response.outputs.is_empty());
                assert!(
                    response
                        .ruleset_publication
                        .as_ref()
                        .unwrap()
                        .names
                        .is_empty()
                );
            }
            let profile = response.profile.unwrap();
            assert_eq!(profile.complete, valid);
            assert!(profile.runs.is_empty(), "{mode:?}/{case}: {profile:?}");
            if !valid || mode == pb::ExecutionMode::Normal {
                assert!(
                    profile.maintenance.is_empty(),
                    "{mode:?}/{case}: {profile:?}"
                );
            } else {
                // Native encoded normalization still surrounds the ruleset,
                // seed action and outer zero loop. No nested body is entered.
                use pb::maintenance_site::Target;
                assert_eq!(profile.maintenance.len(), 3, "{mode:?}/{case}: {profile:?}");
                for (maintenance, target) in profile.maintenance.iter().zip([
                    Target::Ruleset(0),
                    Target::Command(pb::StaticCommandPath { path: vec![0] }),
                    Target::Command(pb::StaticCommandPath { path: vec![1] }),
                ]) {
                    assert_eq!(maintenance.site.as_ref().unwrap().target, Some(target));
                    assert!(maintenance.invocations > 0);
                }
            }
            assert!(
                Renderer::core().render(&program).is_err(),
                "dead Core source body {case}"
            );
            // Valid dead controls retain the authored seed prefix, but neither
            // execute their bodies nor derive Goal. Invalid dead bodies reject
            // during preparation, before even that seed can have effects.
            program.commands = vec![pb::Command {
                kind: Some(pb::command::Kind::Check(pb::Check { facts: vec![2] })),
                ..Default::default()
            }];
            let checked = run(&mut engine, id, program.clone());
            assert_eq!(checked.error.is_none(), valid, "{mode:?}/{case}");
            program.commands = vec![pb::Command {
                kind: Some(pb::command::Kind::Check(pb::Check { facts: vec![5] })),
                ..Default::default()
            }];
            assert!(run(&mut engine, id, program).error.is_some());
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
        let Some(pb::rule::Kind::Rule(rule)) = &mut program.rules[0].kind else {
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
