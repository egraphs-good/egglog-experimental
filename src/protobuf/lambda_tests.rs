// The body uses x + captured (not a named forwarding form). Captures and
// body binders occupy distinct locations, and the function is also applied.
fn anonymous_arithmetic(captured: i64) -> pb::Program {
    use pb::{node::Kind as N, primitive_value::Value as V};
    pb::Program {
        sorts: vec![
            pb::Sort {
                kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                    name: "i64".into(),
                    args: vec![],
                })),
                ..Default::default()
            },
            pb::Sort {
                kind: Some(pb::sort::Kind::Func(pb::FuncSort {
                    params: vec![0],
                    result: 0,
                })),
                ..Default::default()
            },
        ],
        nodes: vec![
            pb::Node {
                sort_id: 0,
                kind: Some(N::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(V::I64(captured)),
                })),
                ..Default::default()
            },
            pb::Node {
                sort_id: 0,
                kind: Some(N::Var("_0".into())),
                ..Default::default()
            },
            pb::Node {
                sort_id: 0,
                kind: Some(N::Var("_1".into())),
                ..Default::default()
            },
            pb::Node {
                sort_id: 0,
                kind: Some(N::Call(pb::Call {
                    func: "egglog.core.i64.add".into(),
                    args: vec![2, 1],
                })),
                ..Default::default()
            },
            pb::Node {
                sort_id: 1,
                kind: Some(N::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(V::Lambda(pb::Lambda {
                        captures: vec![0],
                        body: 3,
                    })),
                })),
                ..Default::default()
            },
            pb::Node {
                sort_id: 0,
                kind: Some(N::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(V::I64(5)),
                })),
                ..Default::default()
            },
            pb::Node {
                sort_id: 0,
                kind: Some(N::Apply(pb::Apply {
                    function: Some(4),
                    args: vec![5],
                })),
                ..Default::default()
            },
        ],
        commands: vec![pb::Command {
            kind: Some(pb::command::Kind::Extract(pb::Extract {
                roots: vec![4, 6],
                variants: 1,
                extractor: pb::Extractor::Tree.into(),
                ..Default::default()
            })),
            ..Default::default()
        }],
        ..Default::default()
    }
}

#[test]
fn anonymous_lambda_executes_observes_and_restores_without_helper_names() {
    use pb::{node::Kind as N, primitive_value::Value as V};
    let (mut engine, id) = host_default_engine();
    let observed = run_host_default(&mut engine, id, anonymous_arithmetic(10));
    assert_eq!(observed.error, None);
    let output = observed.output;
    let Some(pb::command_output::Kind::Extraction(extract)) = &output.outputs[0].kind else {
        panic!("extraction")
    };
    let function = &output.nodes[extract.roots[0].variants[0].term as usize];
    let Some(N::PrimitiveValue(pb::PrimitiveValue {
        value: Some(V::Lambda(lambda)),
    })) = &function.kind
    else {
        panic!("anonymous data retains its body")
    };
    assert_eq!(lambda.captures.len(), 1);
    assert!(matches!(
        &output.nodes[lambda.captures[0] as usize].kind,
        Some(N::PrimitiveValue(pb::PrimitiveValue {
            value: Some(V::I64(10))
        }))
    ));
    assert!(
        matches!(&output.nodes[lambda.body as usize].kind, Some(N::Call(call)) if call.func == "egglog.core.i64.add")
    );
    assert!(matches!(
        &output.nodes[extract.roots[1].variants[0].term as usize].kind,
        Some(N::PrimitiveValue(pb::PrimitiveValue {
            value: Some(V::I64(15))
        }))
    ));
    assert!(!String::from_utf8_lossy(&output.encode_to_vec()).contains("__egglog_lambda"));
    let captured_node = lambda.captures[0];
    let mut replay = pb::Program {
        nodes: output.nodes,
        sorts: output.sorts,
        ..Default::default()
    };
    let value = replay.nodes.len() as u32;
    let int_sort = replay.nodes[captured_node as usize].sort_id;
    replay.nodes.push(pb::Node {
        sort_id: int_sort,
        kind: Some(N::PrimitiveValue(pb::PrimitiveValue {
            value: Some(V::I64(7)),
        })),
        ..Default::default()
    });
    let applied = replay.nodes.len() as u32;
    replay.nodes.push(pb::Node {
        sort_id: int_sort,
        kind: Some(N::Apply(pb::Apply {
            function: Some(extract.roots[0].variants[0].term),
            args: vec![value],
        })),
        ..Default::default()
    });
    replay.commands.push(pb::Command {
        kind: Some(pb::command::Kind::Extract(pb::Extract {
            roots: vec![applied],
            variants: 1,
            extractor: pb::Extractor::Tree.into(),
            ..Default::default()
        })),
        ..Default::default()
    });
    let (mut fresh, id) = host_default_engine();
    let observed = run_host_default(&mut fresh, id, replay);
    assert_eq!(observed.error, None);
    assert!(observed.output.nodes.iter().any(|node| matches!(
        &node.kind,
        Some(N::PrimitiveValue(pb::PrimitiveValue {
            value: Some(V::I64(17))
        }))
    )));
}

#[test]
fn anonymous_lambda_identity_excludes_environment_and_arena_metadata() {
    use pb::{node::Kind as N, primitive_value::Value as V};
    let (mut engine, id) = host_default_engine();
    let mut program = anonymous_arithmetic(10);
    program.declarations.push(pb::Declaration {
        kind: Some(pb::declaration::Kind::Function(pb::Function {
            name: "held".into(),
            inputs: vec![pb::Arg {
                name: "key".into(),
                sort: 0,
            }],
            output: 1,
            ..Default::default()
        })),
        ..Default::default()
    });
    program.commands = vec![pb::Command {
        kind: Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Set(pb::Set {
                target: Some(pb::Call {
                    func: "held".into(),
                    args: vec![5],
                }),
                value: Some(4),
            })),
            ..Default::default()
        })),
        ..Default::default()
    }];
    assert_eq!(
        run_host_default(&mut engine, id, program.clone()).error,
        None
    );
    let mut changed = program.clone();
    // The environment is 4+6 instead of literal 10; the code stays the same.
    changed.nodes[0].kind = Some(N::Call(pb::Call {
        func: "egglog.core.i64.add".into(),
        args: vec![7, 8],
    }));
    for value in [4, 6] {
        changed.nodes.push(pb::Node {
            sort_id: 0,
            kind: Some(N::PrimitiveValue(pb::PrimitiveValue {
                value: Some(V::I64(value)),
            })),
            ..Default::default()
        });
    }
    changed.files.push(pb::SourceFile {
        name: "other-author.egg".into(),
        contents: Some("lambda".into()),
    });
    changed.nodes[3].span = Some(pb::Span {
        file: 0,
        start: 0,
        end: 6,
    });
    // Duplicate a variable location used by the body, preserving typed syntax.
    changed.nodes.push(changed.nodes[2].clone());
    let last = changed.nodes.len() as u32 - 1;
    if let Some(N::Call(call)) = &mut changed.nodes[3].kind {
        call.args[0] = last;
    }
    assert_eq!(
        run_host_default(&mut engine, id, changed).error,
        None,
        "same code and evaluated environment must be the same native value"
    );
    let code_count = engine.graphs[&id]
        .definitions
        .declarations
        .iter()
        .filter(|d| matches!(d.kind, Some(pb::declaration::Kind::UserDefinedPrimitive(_))))
        .count();
    assert_eq!(code_count, 1);
    program.nodes[0].kind = Some(N::PrimitiveValue(pb::PrimitiveValue {
        value: Some(V::I64(11)),
    }));
    assert!(
        run_host_default(&mut engine, id, program).error.is_some(),
        "same code with a different environment is a different function value"
    );
    let snapshot = run_host_default(
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
    assert_eq!(snapshot.error, None);
    assert!(!String::from_utf8_lossy(&snapshot.output.encode_to_vec()).contains("__egglog_lambda"));
}
#[test]
fn anonymous_lambda_captures_now_and_defers_body_reads() {
    use pb::{node::Kind as N, primitive_value::Value as V};
    for deferred in [false, true] {
        let (mut engine, id) = host_default_engine();
        let mut program = inventory_fixture(
            "(sort F (UnstableFn (i64) i64)) (function cell () i64 :merge new) (function held () F :no-merge) (set (cell) 10)",
        );
        let mut code = anonymous_arithmetic(0);
        code.commands.clear();
        code.nodes[0].kind = Some(N::Call(pb::Call {
            func: "cell".into(),
            args: vec![],
        }));
        if deferred {
            code.nodes[4].kind = Some(N::PrimitiveValue(pb::PrimitiveValue {
                value: Some(V::Lambda(pb::Lambda {
                    captures: vec![],
                    body: 0,
                })),
            }));
        }
        let base = program.nodes.len() as u32;
        let files = program.files.len() as u32;
        graph::append(&mut program, &code, files).unwrap();
        let int = program.nodes[base as usize].sort_id;
        let function = program.nodes[base as usize + 4].sort_id;
        let twenty = program.nodes.len() as u32;
        program.nodes.push(pb::Node {
            sort_id: int,
            kind: Some(N::PrimitiveValue(pb::PrimitiveValue {
                value: Some(V::I64(20)),
            })),
            ..Default::default()
        });
        let held = program.nodes.len() as u32;
        program.nodes.push(pb::Node {
            sort_id: function,
            kind: Some(N::Call(pb::Call {
                func: "held".into(),
                args: vec![],
            })),
            ..Default::default()
        });
        let applied = program.nodes.len() as u32;
        program.nodes.push(pb::Node {
            sort_id: int,
            kind: Some(N::Apply(pb::Apply {
                function: Some(held),
                args: vec![base + 5],
            })),
            ..Default::default()
        });
        for (name, value) in [("held", base + 4), ("cell", twenty)] {
            program.commands.push(pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Set(pb::Set {
                        target: Some(pb::Call {
                            func: name.into(),
                            args: vec![],
                        }),
                        value: Some(value),
                    })),
                    ..Default::default()
                })),
                ..Default::default()
            });
        }
        program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Extract(pb::Extract {
                roots: vec![applied, base],
                variants: 1,
                extractor: pb::Extractor::Tree.into(),
                ..Default::default()
            })),
            ..Default::default()
        });
        let result = run_host_default(&mut engine, id, program);
        assert_eq!(result.error, None, "deferred={deferred}");
        let Some(pb::command_output::Kind::Extraction(extract)) = &result.output.outputs[0].kind
        else {
            panic!("extraction")
        };
        for (root, expected) in extract
            .roots
            .iter()
            .zip([if deferred { 20 } else { 15 }, 20])
        {
            assert!(
                matches!(&result.output.nodes[root.variants[0].term as usize].kind, Some(N::PrimitiveValue(pb::PrimitiveValue { value: Some(V::I64(value)) })) if *value == expected)
            );
        }
    }
}

#[test]
fn anonymous_lambda_nested_binders_and_clone_scopes_keep_code() {
    use pb::{node::Kind as N, primitive_value::Value as V};
    let (mut engine, id) = host_default_engine();
    let mut program = anonymous_arithmetic(10);
    program.sorts.push(pb::Sort {
        kind: Some(pb::sort::Kind::Func(pb::FuncSort {
            params: vec![0],
            result: 1,
        })),
        ..Default::default()
    });
    program.nodes[4].sort_id = 2;
    let y = program.nodes.len() as u32;
    program.nodes.push(pb::Node {
        sort_id: 0,
        kind: Some(N::Var("_2".into())),
        ..Default::default()
    });
    let xy = program.nodes.len() as u32;
    program.nodes.push(pb::Node {
        sort_id: 0,
        kind: Some(N::Call(pb::Call {
            func: "egglog.core.i64.add".into(),
            args: vec![2, y],
        })),
        ..Default::default()
    });
    let sum = program.nodes.len() as u32;
    program.nodes.push(pb::Node {
        sort_id: 0,
        kind: Some(N::Call(pb::Call {
            func: "egglog.core.i64.add".into(),
            args: vec![xy, 1],
        })),
        ..Default::default()
    });
    let inner = program.nodes.len() as u32;
    program.nodes.push(pb::Node {
        sort_id: 1,
        kind: Some(N::PrimitiveValue(pb::PrimitiveValue {
            value: Some(V::Lambda(pb::Lambda {
                captures: vec![1, 2],
                body: sum,
            })),
        })),
        ..Default::default()
    });
    if let Some(N::PrimitiveValue(pb::PrimitiveValue {
        value: Some(V::Lambda(lambda)),
    })) = &mut program.nodes[4].kind
    {
        lambda.body = inner;
    }
    program.nodes[6].sort_id = 1;
    let applied = program.nodes.len() as u32;
    program.nodes.push(pb::Node {
        sort_id: 0,
        kind: Some(N::Apply(pb::Apply {
            function: Some(6),
            args: vec![5],
        })),
        ..Default::default()
    });
    if let Some(pb::command::Kind::Extract(extract)) = &mut program.commands[0].kind {
        extract.roots = vec![4, 6, applied];
    }
    let result = run_host_default(&mut engine, id, program.clone());
    assert_eq!(result.error, None);
    assert!(result.output.nodes.iter().any(|node| matches!(
        &node.kind,
        Some(N::PrimitiveValue(pb::PrimitiveValue {
            value: Some(V::I64(20))
        }))
    )));
    assert!(!String::from_utf8_lossy(&result.output.encode_to_vec()).contains("__egglog_lambda"));
    let count = engine.graphs[&id].definitions.declarations.len();
    let child = engine
        .clone_request(pb::CloneEGraphRequest { egraph_id: id })
        .unwrap()
        .egraph_id;
    assert_eq!(run_host_default(&mut engine, child, program).error, None);
    assert_eq!(
        engine.graphs[&child].definitions.declarations.len(),
        count,
        "resupply reuses native code in a clone"
    );
    assert_eq!(engine.graphs[&id].definitions.declarations.len(), count);
    engine
        .destroy_request(pb::DestroyEGraphRequest { egraph_id: child })
        .unwrap();
    let result = run_host_default(&mut engine, id, anonymous_arithmetic(10));
    assert_eq!(
        result.error, None,
        "destroying a continuation keeps the parent registry"
    );
}

#[test]
fn anonymous_lambda_rejects_bad_binders_and_deferred_fresh_values_before_effects() {
    use pb::{node::Kind as N, primitive_value::Value as V};
    for invalid in ["binder", "sort", "union", "self"] {
        let (mut engine, id) = host_default_engine();
        let mut program = anonymous_arithmetic(10);
        match invalid {
            "binder" => program.nodes[1].kind = Some(N::Var("_2".into())),
            "sort" => program.nodes[1].sort_id = 1,
            "union" => program.nodes[3].kind = Some(N::Union(pb::Union { members: vec![] })),
            "self" => {
                if let Some(N::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(V::Lambda(lambda)),
                })) = &mut program.nodes[4].kind
                {
                    lambda.captures = vec![4];
                }
            }
            _ => unreachable!(),
        }
        let result = run_host_default(&mut engine, id, program);
        assert_eq!(
            result.error.unwrap().code,
            i32::from(pb::ErrorCode::InvalidProgram),
            "{invalid}"
        );
        assert_eq!(engine.graphs[&id].request, 0);
        assert!(engine.graphs[&id].definitions.declarations.is_empty());
    }
}

#[test]
fn anonymous_lambda_evaluates_failing_unused_captures_in_order() {
    use pb::{node::Kind as N, primitive_value::Value as V};
    let (mut engine, id) = host_default_engine();
    let mut program = inventory_fixture("(datatype Mark (M i64)) (M 1)");
    let mut code = anonymous_arithmetic(10);
    code.commands.clear();
    code.sorts.push(pb::Sort {
        kind: Some(pb::sort::Kind::Eq("Mark".into())),
        ..Default::default()
    });
    let zero = code.nodes.len() as u32;
    code.nodes.push(pb::Node {
        sort_id: 0,
        kind: Some(N::PrimitiveValue(pb::PrimitiveValue {
            value: Some(V::I64(0)),
        })),
        ..Default::default()
    });
    let failing = code.nodes.len() as u32;
    code.nodes.push(pb::Node {
        sort_id: 0,
        kind: Some(N::Call(pb::Call {
            func: "egglog.core.i64.div".into(),
            args: vec![0, zero],
        })),
        ..Default::default()
    });
    let later = code.nodes.len() as u32;
    code.nodes.push(pb::Node {
        sort_id: 2,
        kind: Some(N::Call(pb::Call {
            func: "M".into(),
            args: vec![5],
        })),
        ..Default::default()
    });
    if let Some(N::PrimitiveValue(pb::PrimitiveValue {
        value: Some(V::Lambda(lambda)),
    })) = &mut code.nodes[4].kind
    {
        lambda.captures = vec![failing, later];
        lambda.body = 5; // Both captures are unused; construction is still strict.
    }
    let base = program.nodes.len() as u32;
    let files = program.files.len() as u32;
    graph::append(&mut program, &code, files).unwrap();
    program.commands.push(pb::Command {
        kind: Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Term(base + 4)),
            ..Default::default()
        })),
        ..Default::default()
    });
    let result = run_host_default(&mut engine, id, program);
    assert_eq!(
        result.error.unwrap().code,
        i32::from(pb::ErrorCode::RuntimeFailure)
    );
    let graph = &engine.graphs[&id].graph;
    let mut values = vec![];
    graph
        .constructor_enodes(&native_name("call", "M"), |row| {
            values.push(graph.value_to_base::<i64>(row.children[0]))
        })
        .unwrap();
    assert_eq!(
        values,
        [1],
        "earlier effects survive and the later capture never executes"
    );
}

#[test]
fn anonymous_lambda_bodies_retain_native_context_admission() {
    use egglog::Context;
    for (body, expected) in [
        ("(+ 1 1)", [true, true, true, true]),
        ("(cell 1)", [false, true, false, true]),
        ("(Item 1)", [false, false, true, true]),
        ("(Item (cell 1))", [false, false, false, true]),
    ] {
        let (mut engine, id) = host_default_engine();
        let mut program = inventory_fixture(&format!(
            "(sort A) (constructor Item (i64) A)
             (function cell (i64) i64 :merge new) {body}"
        ));
        let Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Term(body)),
            ..
        })) = &program.commands.last().unwrap().kind
        else {
            panic!("body fixture")
        };
        let body = *body;
        let integer = program.sorts.iter().position(|sort| {
            matches!(&sort.kind, Some(pb::sort::Kind::Application(a)) if a.name == "i64")
        }).unwrap() as u32;
        let function = program.sorts.len() as u32;
        program.sorts.push(pb::Sort {
            kind: Some(pb::sort::Kind::Func(pb::FuncSort {
                params: vec![integer],
                result: program.nodes[body as usize].sort_id,
            })),
            ..Default::default()
        });
        program.nodes.push(pb::Node {
            sort_id: function,
            kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Lambda(pb::Lambda {
                    captures: vec![],
                    body,
                })),
            })),
            ..Default::default()
        });
        program.commands.clear();
        assert_eq!(run_host_default(&mut engine, id, program).error, None);
        let session = engine.graphs.get_mut(&id).unwrap();
        let helper = session
            .definitions
            .declarations
            .iter()
            .find_map(|d| {
                if let Some(pb::declaration::Kind::UserDefinedPrimitive(p)) = &d.kind {
                    Some(&p.name)
                } else {
                    None
                }
            })
            .unwrap();
        let primitives = session
            .graph
            .type_info()
            .get_prims(&native_name("call", helper))
            .unwrap();
        assert_eq!(primitives.len(), 1);
        let contexts = [Context::Pure, Context::Read, Context::Write, Context::Full]
            .map(|context| primitives[0].is_valid_in_context(context));
        assert_eq!(contexts, expected);
        assert_eq!(session.graph.get_size(&native_name("call", "Item")), 0);
        assert_eq!(session.graph.get_size(&native_name("call", "cell")), 0);
    }
}
