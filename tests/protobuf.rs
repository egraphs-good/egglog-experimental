use egglog_experimental::proto as pb;
use egglog_experimental::{new_experimental_egraph, protobuf::Engine};
use prost::Message;

#[test]
fn native_catalog_snapshot_is_deterministic_and_installs_as_bytes() {
    let first = new_experimental_egraph()
        .type_info()
        .builtin_catalog()
        .unwrap()
        .definitions;
    let second = new_experimental_egraph()
        .type_info()
        .builtin_catalog()
        .unwrap()
        .definitions;
    assert_eq!(first.encode_to_vec(), second.encode_to_vec());
    let family = first
        .declarations
        .iter()
        .find_map(|d| match &d.kind {
            Some(pb::declaration::Kind::HostSortFamily(f)) if f.name == "Vec" => Some(f),
            _ => None,
        })
        .unwrap();
    let binding = family.bindings.as_ref().expect("native Vec metadata");
    assert!(binding.python.is_none());
    assert_eq!(
        binding.rust.as_ref().unwrap().path,
        ["egglog_experimental", "typed", "builtins", "Vec"]
    );
    let mut engine = Engine::default();
    let id = create(&mut engine);
    for program in [first, second] {
        assert_eq!(run(&mut engine, id, program).error, None);
    }
}

fn constant_fixture(current_path: &[&str], constructor_path: &[&str]) -> pb::Program {
    let mut p = fixture();
    p.rules.clear();
    p.rulesets.clear();
    p.declarations.push(pb::Declaration {
        kind: Some(pb::declaration::Kind::Constructor(pb::Constructor {
            name: "Empty".into(),
            output: 1,
            ..Default::default()
        })),
        ..Default::default()
    });
    for (index, path) in [(3, current_path), (5, constructor_path)] {
        p.declarations[index].bindings = Some(pb::CallableBindings {
            python: Some(pb::PythonBindings {
                views: vec![pb::PythonCallable {
                    kind: pb::PythonCallKind::Constant.into(),
                    path: path.iter().map(|s| (*s).to_owned()).collect(),
                    ..Default::default()
                }],
            }),
            ..Default::default()
        });
    }
    p.nodes.push(pb::Node {
        sort_id: 1,
        kind: Some(pb::node::Kind::Call(pb::Call {
            func: "Empty".into(),
            args: vec![],
        })),
        ..Default::default()
    });
    let mut extraction = p.commands[7].clone();
    let Some(pb::command::Kind::Extract(e)) = &mut extraction.kind else {
        unreachable!()
    };
    e.roots = vec![4, p.nodes.len() as u32 - 1];
    p.commands.truncate(4); // Set current, capture, Set current, Check both values.
    p.commands.push(extraction);
    p
}

#[test]
fn constant_function_and_constructor_execute_as_bytes_and_resupply() {
    for (current_path, constructor_path) in [
        (&["test", "CURRENT"][..], &["test", "EMPTY"][..]),
        (&[""][..], &["example", ""][..]),
        (&["example", ""][..], &[""][..]),
    ] {
        let program = constant_fixture(current_path, constructor_path);
        let encoded = program.encode_to_vec();
        assert_eq!(pb::Program::decode(encoded.as_slice()).unwrap(), program);
        let mut engine = Engine::default();
        let id = create(&mut engine);
        let mut renderer = egglog_experimental::protobuf::source::Renderer::default();
        let mut native = new_experimental_egraph();
        for _ in 0..2 {
            let response = run(&mut engine, id, program.clone());
            assert_eq!(response.error, None);
            let Some(pb::command_output::Kind::Extraction(e)) = &response.outputs[0].kind else {
                panic!("extraction")
            };
            assert_eq!(value(&response, e.roots[0].variants[0].term), "20");
            assert!(
                matches!(&response.nodes[e.roots[1].variants[0].term as usize].kind, Some(pb::node::Kind::Call(c)) if c.func == "Empty" && c.args.is_empty())
            );
            let outputs = native
                .parse_and_run_program(None, &renderer.render(&program).unwrap())
                .unwrap();
            let egglog_experimental::CommandOutput::ExtractBest(dag, _, root) = &outputs[0] else {
                panic!("native extraction")
            };
            assert_eq!(dag.to_string(*root), "20");
            assert_eq!(outputs.len(), 2);
        }
        // Presentation survives byte ownership; rendering is executable semantics,
        // not a Python surface exporter or a retained native-AST execution path.
        assert_eq!(program.encode_to_vec(), encoded);
    }
}

#[test]
fn constant_metadata_conflicts_reject_before_writes_and_clone_keeps_prefix_state() {
    for (current_path, constructor_path) in [
        (&["test", "CURRENT"][..], &["test", "EMPTY"][..]),
        (&[""][..], &["example", ""][..]),
        (&["example", ""][..], &[""][..]),
    ] {
        let program = constant_fixture(current_path, constructor_path);
        let mut engine = Engine::default();
        let id = create(&mut engine);
        assert_eq!(run(&mut engine, id, program.clone()).error, None);
        let clone = pb::CloneEGraphResponse::decode(
            engine
                .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
                .unwrap()
                .as_slice(),
        )
        .unwrap()
        .egraph_id;
        let mut observation = program.clone();
        observation.commands = program.commands[3..].to_vec();
        for bad in 0..10 {
            let mut invalid = program.clone();
            let view = &mut invalid.declarations[3]
                .bindings
                .as_mut()
                .unwrap()
                .python
                .as_mut()
                .unwrap()
                .views[0];
            match bad {
                0 => view.path.clear(),
                1 => view.kind = pb::PythonCallKind::Function.into(), // Never reinterpret a constant as a function.
                2 => view.receiver = Some(0),
                3 => {
                    view.owner = Some(pb::BindingOwner {
                        kind: Some(pb::binding_owner::Kind::Sort(0)),
                    })
                }
                4 => view.params.push(pb::PythonParameter {
                    core_input: Some(0),
                    name: "x".into(),
                    ..Default::default()
                }),
                5 => view.kind = 99,
                6 | 7 => {
                    let Some(pb::declaration::Kind::Function(f)) =
                        &mut invalid.declarations[3].kind
                    else {
                        unreachable!()
                    };
                    if bad == 6 {
                        f.inputs.push(pb::Arg {
                            name: "x".into(),
                            sort: 0,
                        });
                    } else {
                        f.output = 1;
                    }
                }
                8 => view.path.insert(0, String::new()),
                9 => view.path.last_mut().unwrap().push_str("renamed"),
                _ => unreachable!(),
            }
            // The first action would write 10; preparation must fail before it runs.
            assert_eq!(
                run(&mut engine, id, invalid).error.unwrap().code,
                pb::ErrorCode::InvalidProgram as i32,
                "bad case {bad}"
            );
            assert_eq!(
                run(&mut engine, id, observation.clone()).error,
                None,
                "bad case {bad}"
            );
        }
        assert!(engine.run(&[0xff]).is_err());
        assert_eq!(run(&mut engine, id, observation.clone()).error, None);
        let mut runtime = program.clone();
        runtime.commands = vec![
            program.commands[0].clone(),
            pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Panic("after constant write".into())),
                    ..Default::default()
                })),
                ..Default::default()
            },
            program.commands[2].clone(),
        ];
        assert_eq!(
            run(&mut engine, id, runtime).error.unwrap().code,
            pb::ErrorCode::Panic as i32
        );
        assert_eq!(
            run(&mut engine, clone, observation.clone()).error,
            None,
            "clone remains at 20"
        );
        observation.commands.remove(0); // Extract the committed prefix, without the old 20 check.
        let response = run(&mut engine, id, observation);
        assert_eq!(response.error, None);
        let Some(pb::command_output::Kind::Extraction(e)) = &response.outputs[0].kind else {
            panic!("extraction")
        };
        assert_eq!(value(&response, e.roots[0].variants[0].term), "10");
    }
}

fn host_default_program(default_node: u32) -> pb::Program {
    let mut p = new_experimental_egraph()
        .type_info()
        .builtin_catalog()
        .unwrap()
        .definitions;
    let i64_sort = p.sorts.iter().position(|s| matches!(&s.kind, Some(pb::sort::Kind::Family(f)) if f.name == "i64" && f.args.is_empty())).unwrap() as u32;
    p.nodes = vec![
        pb::Node {
            sort_id: i64_sort,
            kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::I64(i64::MAX)),
            })),
            ..Default::default()
        },
        pb::Node {
            sort_id: i64_sort,
            kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::I64(1)),
            })),
            ..Default::default()
        },
        pb::Node {
            sort_id: i64_sort,
            kind: Some(pb::node::Kind::Call(pb::Call {
                func: "egglog.core.i64.add".into(),
                args: vec![0, 1],
            })),
            ..Default::default()
        },
        pb::Node {
            sort_id: i64_sort,
            kind: Some(pb::node::Kind::Call(pb::Call {
                func: "current".into(),
                args: vec![],
            })),
            ..Default::default()
        },
    ];
    p.declarations.push(pb::Declaration {
        kind: Some(pb::declaration::Kind::Function(pb::Function {
            name: "current".into(),
            inputs: vec![],
            output: i64_sort,
            merge: None,
        })),
        ..Default::default()
    });
    let get = p.declarations.iter_mut().find(|d| matches!(&d.kind, Some(pb::declaration::Kind::HostPrimitive(h)) if h.name == "egglog.core.vec.get")).unwrap();
    let Some(pb::declaration::Kind::HostPrimitive(h)) = &get.kind else {
        unreachable!()
    };
    let Some(pb::host_primitive::Typing::Signature(s)) = &h.typing else {
        unreachable!()
    };
    get.bindings.as_mut().unwrap().python = Some(pb::PythonBindings {
        views: vec![pb::PythonCallable {
            kind: pb::PythonCallKind::Method.into(),
            path: vec!["get".into()],
            owner: Some(pb::BindingOwner {
                kind: Some(pb::binding_owner::Kind::Sort(s.inputs[0].sort)),
            }),
            receiver: Some(0),
            params: vec![pb::PythonParameter {
                core_input: Some(1),
                name: "index".into(),
                default_expr: Some(default_node),
            }],
            ..Default::default()
        }],
    });
    p
}

#[test]
fn host_binding_default_keeps_builtin_callee_context_without_evaluation() {
    let mut engine = Engine::default();
    let id = create(&mut engine);
    // MAX + 1 would fail if evaluated. It remains a valid closed template.
    assert_eq!(run(&mut engine, id, host_default_program(2)).error, None);
    assert_eq!(run(&mut engine, id, host_default_program(2)).error, None);
    assert!(
        run(&mut engine, id, host_default_program(1))
            .error
            .is_some()
    );
}

#[test]
fn host_binding_default_keeps_user_callee_context_without_evaluation() {
    let mut engine = Engine::default();
    let id = create(&mut engine);
    assert_eq!(run(&mut engine, id, host_default_program(3)).error, None);
    let mut resend = host_default_program(3);
    resend
        .declarations
        .retain(|d| !matches!(d.kind, Some(pb::declaration::Kind::Function(_))));
    assert_eq!(
        run(&mut engine, id, resend).error,
        None,
        "default can refer to an ambient installed table"
    );
    assert!(
        run(&mut engine, id, host_default_program(1))
            .error
            .is_some()
    );
}

#[test]
fn wire_namespace_same_request_sort_and_constructor() {
    let mut p = fixture();
    p.sorts[1].kind = Some(pb::sort::Kind::Eq("Shared".into()));
    p.declarations = vec![
        pb::Declaration {
            kind: Some(pb::declaration::Kind::EqSort(pb::EqSort {
                name: "Shared".into(),
                ..Default::default()
            })),
            ..Default::default()
        },
        pb::Declaration {
            kind: Some(pb::declaration::Kind::Constructor(pb::Constructor {
                name: "Shared".into(),
                inputs: vec![pb::Arg {
                    sort: 0,
                    name: "value".into(),
                }],
                output: 1,
                ..Default::default()
            })),
            ..Default::default()
        },
    ];
    p.nodes.truncate(1);
    p.nodes.push(pb::Node {
        sort_id: 1,
        kind: Some(pb::node::Kind::Call(pb::Call {
            func: "Shared".into(),
            args: vec![0],
        })),
        ..Default::default()
    });
    p.rules.clear();
    p.rulesets.clear();
    p.commands = vec![pb::Command {
        kind: Some(pb::command::Kind::Extract(pb::Extract {
            roots: vec![1],
            variants: 1,
            extractor: pb::Extractor::Tree.into(),
            ..Default::default()
        })),
        ..Default::default()
    }];
    let mut engine = Engine::default();
    let id = create(&mut engine);
    p.commands.push(pb::Command {
        kind: Some(pb::command::Kind::PrintFunction(pb::PrintFunction {
            table: "Shared".into(),
            max_rows: 0,
        })),
        ..Default::default()
    });
    let mut renderer = egglog_experimental::protobuf::source::Renderer::default();
    let mut native = new_experimental_egraph();
    for _ in 0..2 {
        let response = run(&mut engine, id, p.clone());
        assert_eq!(response.error, None);
        assert!(
            response
                .sorts
                .iter()
                .any(|s| s.kind == Some(pb::sort::Kind::Eq("Shared".into())))
        );
        assert!(
            response
                .nodes
                .iter()
                .any(|n| matches!(&n.kind, Some(pb::node::Kind::Call(c)) if c.func == "Shared"))
        );
        assert!(response.outputs.iter().any(|o| matches!(&o.kind, Some(pb::command_output::Kind::PrintedFunction(f)) if f.table == "Shared" && f.rows.len() == 1)));
        native
            .parse_and_run_program(None, &renderer.render(&p).unwrap())
            .unwrap();
    }
}

fn check_cross_request_namespaces(sort_first: bool) {
    let sort = pb::Program {
        ir_version: 1,
        declarations: vec![pb::Declaration {
            kind: Some(pb::declaration::Kind::EqSort(pb::EqSort {
                name: "Shared".into(),
                ..Default::default()
            })),
            ..Default::default()
        }],
        ..Default::default()
    };
    let mut function = fixture();
    function.sorts.truncate(1);
    function.nodes.truncate(1);
    function.nodes.push(pb::Node {
        sort_id: 0,
        kind: Some(pb::node::Kind::Call(pb::Call {
            func: "Shared".into(),
            args: vec![],
        })),
        ..Default::default()
    });
    function.commands.truncate(1);
    let Some(pb::command::Kind::Action(pb::Action {
        kind: Some(pb::action::Kind::Set(set)),
        ..
    })) = &mut function.commands[0].kind
    else {
        unreachable!()
    };
    set.target.as_mut().unwrap().func = "Shared".into();
    function.commands.push(pb::Command {
        kind: Some(pb::command::Kind::Extract(pb::Extract {
            roots: vec![1],
            variants: 1,
            extractor: pb::Extractor::Tree.into(),
            ..Default::default()
        })),
        ..Default::default()
    });
    function.rules.clear();
    function.rulesets.clear();
    function.declarations = vec![pb::Declaration {
        kind: Some(pb::declaration::Kind::Function(pb::Function {
            name: "Shared".into(),
            inputs: vec![],
            output: 0,
            merge: None,
        })),
        ..Default::default()
    }];
    let phases = if sort_first {
        [sort, function]
    } else {
        [function, sort]
    };
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut renderer = egglog_experimental::protobuf::source::Renderer::default();
    let mut native = new_experimental_egraph();
    let mut clone = id;
    for phase in &phases {
        assert_eq!(run(&mut engine, id, phase.clone()).error, None);
        assert_eq!(run(&mut engine, clone, phase.clone()).error, None);
        native
            .parse_and_run_program(None, &renderer.render(phase).unwrap())
            .unwrap();
        let bytes = engine
            .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
            .unwrap();
        clone = pb::CloneEGraphResponse::decode(bytes.as_slice())
            .unwrap()
            .egraph_id;
    }
    for phase in &phases {
        assert_eq!(run(&mut engine, clone, phase.clone()).error, None);
        native
            .parse_and_run_program(None, &renderer.render(phase).unwrap())
            .unwrap();
    }
    let function = phases.iter().find(|p| !p.commands.is_empty()).unwrap();
    let mut conflict = function.clone();
    let Some(pb::declaration::Kind::Function(f)) = &mut conflict.declarations[0].kind else {
        unreachable!()
    };
    f.inputs.push(pb::Arg {
        name: "extra".into(),
        sort: 0,
    });
    conflict.nodes[0].kind = Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
        value: Some(pb::primitive_value::Value::I64(20)),
    }));
    assert!(run(&mut engine, clone, conflict.clone()).error.is_some());
    assert!(renderer.render(&conflict).is_err());
    let mut observation = function.clone();
    observation.declarations.clear();
    observation.commands.remove(0);
    let response = run(&mut engine, clone, observation.clone());
    assert_eq!(response.error, None);
    let Some(pb::command_output::Kind::Extraction(extracted)) = &response.outputs[0].kind else {
        unreachable!()
    };
    assert_eq!(value(&response, extracted.roots[0].variants[0].term), "10");
    native
        .parse_and_run_program(None, &renderer.render(&observation).unwrap())
        .unwrap();
}

#[test]
fn wire_namespace_sort_then_function() {
    check_cross_request_namespaces(true);
}

#[test]
fn wire_namespace_function_then_sort() {
    check_cross_request_namespaces(false);
}

#[test]
fn wire_namespace_host_aliases_unicode_and_nested_result_sorts() {
    let mut p = new_experimental_egraph()
        .type_info()
        .builtin_catalog()
        .unwrap()
        .definitions;
    let scalar = p
        .sorts
        .iter()
        .position(|s| matches!(&s.kind, Some(pb::sort::Kind::Family(f)) if f.name == "i64"))
        .unwrap() as u32;
    let eq = p.sorts.len() as u32;
    p.sorts.push(pb::Sort {
        kind: Some(pb::sort::Kind::Eq("Shared".into())),
        ..Default::default()
    });
    for child in [eq, eq + 1] {
        p.sorts.push(pb::Sort {
            kind: Some(pb::sort::Kind::Family(pb::HostSort {
                name: "Vec".into(),
                args: vec![child],
            })),
            ..Default::default()
        });
    }
    p.declarations.push(pb::Declaration {
        kind: Some(pb::declaration::Kind::EqSort(pb::EqSort {
            name: "Shared".into(),
            ..Default::default()
        })),
        ..Default::default()
    });
    p.nodes = vec![pb::Node {
        sort_id: scalar,
        kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::I64(10)),
        })),
        ..Default::default()
    }];
    let names = ["i64", "+", "é", "e\u{301}", "x) (panic \"injected\")"];
    let mut roots = vec![];
    for name in names {
        p.declarations.push(pb::Declaration {
            kind: Some(pb::declaration::Kind::Constructor(pb::Constructor {
                name: name.into(),
                inputs: vec![pb::Arg {
                    name: "x".into(),
                    sort: scalar,
                }],
                output: eq,
                ..Default::default()
            })),
            ..Default::default()
        });
        roots.push(p.nodes.len() as u32);
        p.nodes.push(pb::Node {
            sort_id: eq,
            kind: Some(pb::node::Kind::Call(pb::Call {
                func: name.into(),
                args: vec![0],
            })),
            ..Default::default()
        });
    }
    for (sort_id, child) in [(eq + 1, 1), (eq + 2, 6)] {
        p.nodes.push(pb::Node {
            sort_id,
            kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Vec(pb::ValueList {
                    items: vec![child],
                })),
            })),
            ..Default::default()
        });
    }
    roots.push(7);
    p.nodes.push(pb::Node {
        sort_id: scalar,
        kind: Some(pb::node::Kind::Call(pb::Call {
            func: "egglog.core.i64.add".into(),
            args: vec![0, 0],
        })),
        ..Default::default()
    });
    roots.push(8);
    p.commands = vec![pb::Command {
        kind: Some(pb::command::Kind::Extract(pb::Extract {
            roots,
            variants: 1,
            extractor: pb::Extractor::Tree.into(),
            ..Default::default()
        })),
        ..Default::default()
    }];
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let response = run(&mut engine, id, p.clone());
    assert_eq!(response.error, None);
    assert_eq!(
        response.sorts.len(),
        4,
        "logical sort interning includes nested Vec only once"
    );
    assert_eq!(
        response
            .sorts
            .iter()
            .filter(|s| s.kind == Some(pb::sort::Kind::Eq("Shared".into())))
            .count(),
        1
    );
    let calls: std::collections::HashSet<_> = response
        .nodes
        .iter()
        .filter_map(|n| match &n.kind {
            Some(pb::node::Kind::Call(c)) => Some(c.func.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(calls, names.into_iter().collect());
    assert!(response.nodes.iter().any(|n| matches!(
        &n.kind,
        Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::I64(20))
        }))
    )));
    let source = egglog_experimental::protobuf::source::Renderer::default()
        .render(&p)
        .unwrap();
    new_experimental_egraph()
        .parse_and_run_program(None, &source)
        .unwrap();

    // No wire call can address an installed table by guessing its native name.
    let mut invalid = p.clone();
    let Some(pb::node::Kind::Call(call)) = &mut invalid.nodes[1].kind else {
        unreachable!()
    };
    call.func = "__egglog_proto_call_693634".into();
    assert!(run(&mut engine, id, invalid).error.is_some());
    assert_eq!(run(&mut engine, id, p).error, None);
}

#[test]
fn wire_namespace_query_binders_do_not_rename_merge_variables() {
    let mut p = fixture();
    // The same node is native merge `old` and a rule-local variable.
    p.nodes[3].kind = Some(pb::node::Kind::Var("old".into()));
    let colliding = p.nodes.len() as u32;
    p.nodes.push(pb::Node {
        sort_id: 0,
        kind: Some(pb::node::Kind::Var(
            "__egglog_proto_call_63757272656e74".into(),
        )),
        ..Default::default()
    });
    let query = p.nodes.len() as u32;
    p.nodes.push(pb::Node {
        sort_id: 0,
        kind: Some(pb::node::Kind::Union(pb::Union {
            members: vec![3, 4, colliding],
        })),
        ..Default::default()
    });
    p.rules[0].kind = Some(pb::rule_decl::Kind::Rule(pb::Rule {
        query: vec![query],
        head: vec![pb::Action {
            kind: Some(pb::action::Kind::Set(pb::Set {
                target: Some(pb::Call {
                    func: "captured".into(),
                    args: vec![],
                }),
                value: Some(colliding),
            })),
            ..Default::default()
        }],
    }));
    p.commands = vec![
        p.commands[0].clone(),
        p.commands[2].clone(),
        p.commands[5].clone(),
        pb::Command {
            kind: Some(pb::command::Kind::Extract(pb::Extract {
                roots: vec![4, 5],
                variants: 1,
                extractor: pb::Extractor::Tree.into(),
                ..Default::default()
            })),
            ..Default::default()
        },
    ];
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let response = run(&mut engine, id, p.clone());
    assert_eq!(response.error, None);
    let Some(pb::command_output::Kind::Extraction(extracted)) =
        &response.outputs.last().unwrap().kind
    else {
        unreachable!()
    };
    for root in &extracted.roots {
        assert!(matches!(
            &response.nodes[root.variants[0].term as usize].kind,
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::I64(10))
            }))
        ));
    }
    let source = egglog_experimental::protobuf::source::Renderer::default()
        .render(&p)
        .unwrap();
    new_experimental_egraph()
        .parse_and_run_program(None, &source)
        .unwrap();
}

#[test]
fn compatible_declarations_resend_through_bytes_and_renderer() {
    use egglog_experimental::protobuf::source::Renderer;
    let mut program = fixture();
    program.commands.clear();
    program.rules.clear();
    program.rulesets.clear();
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut renderer = Renderer::default();
    let mut native = new_experimental_egraph();
    for _ in 0..2 {
        assert_eq!(run(&mut engine, id, program.clone()).error, None);
        native
            .parse_and_run_program(None, &renderer.render(&program).unwrap())
            .unwrap();
    }
}

#[test]
fn box_initializer_defaults_install_without_evaluation() {
    let mut program = fixture();
    program.commands.clear();
    program.rules.clear();
    program.rulesets.clear();
    let declaration = program
        .declarations
        .iter_mut()
        .find(|d| matches!(&d.kind, Some(pb::declaration::Kind::Constructor(c)) if c.name == "Num"))
        .unwrap();
    declaration.bindings = Some(pb::CallableBindings {
        python: Some(pb::PythonBindings {
            views: vec![pb::PythonCallable {
                kind: pb::PythonCallKind::Initializer.into(),
                owner: Some(pb::BindingOwner {
                    kind: Some(pb::binding_owner::Kind::Sort(1)),
                }),
                params: vec![pb::PythonParameter {
                    core_input: Some(0),
                    name: "value".into(),
                    default_expr: Some(4),
                }],
                ..Default::default()
            }],
        }),
        ..Default::default()
    });
    // The template reads current(), whose table has no row. Installation must
    // validate closed syntax/types without evaluating that read.
    let mut engine = Engine::default();
    let id = create(&mut engine);
    assert_eq!(run(&mut engine, id, program.clone()).error, None);
    assert_eq!(run(&mut engine, id, program.clone()).error, None);
    let constructor = program
        .declarations
        .iter_mut()
        .find(|d| d.bindings.is_some())
        .unwrap();
    constructor
        .bindings
        .as_mut()
        .unwrap()
        .python
        .as_mut()
        .unwrap()
        .views[0]
        .params[0]
        .default_expr = Some(3);
    assert!(
        run(&mut engine, id, program).error.is_some(),
        "merge variable new is not bound in a default"
    );
}

fn presentation_fixture() -> pb::Program {
    let mut p = fixture();
    p.commands.clear();
    p.rules.clear();
    p.rulesets.clear();
    p.nodes[0].kind = Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
        value: Some(pb::primitive_value::Value::I64(4)),
    }));
    for d in &mut p.declarations {
        match &mut d.kind {
            Some(pb::declaration::Kind::EqSort(s)) => {
                s.bindings = Some(pb::SortBindings {
                    python: Some(pb::TypeBinding {
                        path: vec!["test".into(), "Box".into()],
                        ..Default::default()
                    }),
                    ..Default::default()
                })
            }
            Some(pb::declaration::Kind::Constructor(c)) if c.name == "Num" => {
                d.bindings = Some(pb::CallableBindings {
                    python: Some(pb::PythonBindings {
                        views: vec![pb::PythonCallable {
                            kind: pb::PythonCallKind::Initializer.into(),
                            owner: Some(pb::BindingOwner {
                                kind: Some(pb::binding_owner::Kind::Sort(1)),
                            }),
                            params: vec![pb::PythonParameter {
                                core_input: Some(0),
                                name: "value".into(),
                                default_expr: Some(0),
                            }],
                            ..Default::default()
                        }],
                    }),
                    ..Default::default()
                })
            }
            _ => (),
        }
    }
    p
}

#[test]
fn presentation_freeze_obeys_clone_preparation_and_runtime_prefix_boundaries() {
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let presented = presentation_fixture();
    let mut absent = presented.clone();
    for d in &mut absent.declarations {
        d.bindings = None;
        if let Some(pb::declaration::Kind::EqSort(s)) = &mut d.kind {
            s.bindings = None;
        }
    }
    assert_eq!(run(&mut engine, id, absent.clone()).error, None);
    let clone = pb::CloneEGraphResponse::decode(
        engine
            .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
            .unwrap()
            .as_slice(),
    )
    .unwrap()
    .egraph_id;
    let mut runtime = presented.clone();
    runtime.commands = vec![
        fixture().commands[0].clone(),
        pb::Command {
            kind: Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Panic("after metadata and write".into())),
                ..Default::default()
            })),
            ..Default::default()
        },
    ];
    assert_eq!(
        run(&mut engine, id, runtime).error.unwrap().code,
        pb::ErrorCode::Panic as i32
    );
    let mut conflicting = presented.clone();
    for d in &mut conflicting.declarations {
        if let Some(b) = &mut d.bindings {
            b.python.as_mut().unwrap().views[0].params[0].default_expr = Some(1);
        }
    }
    conflicting.commands = vec![fixture().commands[2].clone()];
    assert!(run(&mut engine, id, conflicting.clone()).error.is_some());
    let mut observation = absent.clone();
    observation.commands = vec![pb::Command {
        kind: Some(pb::command::Kind::Extract(pb::Extract {
            roots: vec![4],
            variants: 1,
            extractor: pb::Extractor::Tree.into(),
            ..Default::default()
        })),
        ..Default::default()
    }];
    let response = run(&mut engine, id, observation);
    assert_eq!(response.error, None);
    let Some(pb::command_output::Kind::Extraction(result)) = &response.outputs[0].kind else {
        unreachable!()
    };
    assert_eq!(value(&response, result.roots[0].variants[0].term), "4");
    conflicting.commands.clear();
    assert_eq!(
        run(&mut engine, clone, conflicting.clone()).error,
        None,
        "clone had no first Python supply yet"
    );
    assert!(run(&mut engine, clone, presented.clone()).error.is_some());
    let fresh = create(&mut engine);
    assert_eq!(run(&mut engine, fresh, absent).error, None);
    let mut invalid = conflicting;
    invalid.commands = vec![pb::Command {
        kind: Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Set(pb::Set {
                target: Some(pb::Call {
                    func: "missing".into(),
                    args: vec![],
                }),
                value: Some(0),
            })),
            ..Default::default()
        })),
        ..Default::default()
    }];
    assert!(run(&mut engine, fresh, invalid).error.is_some());
    assert_eq!(
        run(&mut engine, fresh, presented).error,
        None,
        "preparation failure must not freeze metadata"
    );
}

#[test]
fn initializer_metadata_accepts_expanded_default_calls_and_rejects_semantic_resupply() {
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut program = presentation_fixture();
    let root = program.nodes.len() as u32;
    program.nodes.push(pb::Node {
        sort_id: 1,
        kind: Some(pb::node::Kind::Call(pb::Call {
            func: "Num".into(),
            args: vec![0],
        })),
        ..Default::default()
    });
    program.commands = vec![pb::Command {
        kind: Some(pb::command::Kind::Extract(pb::Extract {
            roots: vec![root],
            variants: 1,
            extractor: pb::Extractor::Tree.into(),
            ..Default::default()
        })),
        ..Default::default()
    }];
    let response = run(&mut engine, id, program.clone());
    assert_eq!(response.error, None);
    let Some(pb::command_output::Kind::Extraction(result)) = &response.outputs[0].kind else {
        unreachable!()
    };
    assert_eq!(
        value(&response, result.roots[0].variants[0].term),
        "(Num 4)"
    );
    for wrong in 0..5 {
        let mut changed = program.clone();
        let constructor = changed
            .declarations
            .iter_mut()
            .find_map(|d| match &mut d.kind {
                Some(pb::declaration::Kind::Constructor(c)) if c.name == "Num" => Some(c),
                _ => None,
            })
            .unwrap();
        match wrong {
            0 => constructor.cost = Some(0),
            1 => constructor.unextractable = true,
            2 => constructor.inputs[0].sort = 1,
            3 => constructor.output = 0,
            _ => {
                let function = changed
                    .declarations
                    .iter_mut()
                    .find_map(|d| match &mut d.kind {
                        Some(pb::declaration::Kind::Function(f)) if f.name == "current" => Some(f),
                        _ => None,
                    })
                    .unwrap();
                function.merge = None;
            }
        }
        assert!(
            run(&mut engine, id, changed).error.is_some(),
            "semantic change {wrong}"
        );
        assert_eq!(run(&mut engine, id, program.clone()).error, None);
    }
}

#[test]
fn source_vec_calls_execute_through_bytes() {
    use egglog_experimental::protobuf::source::{Renderer, Source};
    let text = r#"
        (sort V (Vec i64)) (sort W (Vec i64)) (sort Nested (Vec W))
        (function v () V :merge new) (function w () W :merge new)
        (function nested () Nested :merge new)
        (set (v) (vec-empty)) (set (w) (vec-of 3 4))
        (set (nested) (vec-of (w)))
        (check (= (vec-get (w) 1) 4))
        (extract (vec-get (vec-get (nested) 0) 1))
        (extract (v)) (extract (nested))
    "#;
    new_experimental_egraph()
        .parse_and_run_program(None, text)
        .unwrap();
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut results = vec![];
    let mut renderer = Renderer::default();
    let mut rendered = new_experimental_egraph();
    for program in Source::new(None, text).unwrap() {
        let program = pb::Program::decode(program.unwrap().encode_to_vec().as_slice()).unwrap();
        let source = renderer.render(&program).unwrap();
        rendered.parse_and_run_program(None, &source).unwrap();
        let response = run(&mut engine, id, program);
        assert_eq!(response.error, None);
        for output in &response.outputs {
            if let Some(pb::command_output::Kind::Extraction(result)) = &output.kind {
                results.push(value(&response, result.roots[0].variants[0].term));
                let reingest = pb::Program {
                    ir_version: 1,
                    sorts: response.sorts.clone(),
                    nodes: response.nodes.clone(),
                    commands: vec![pb::Command {
                        kind: Some(pb::command::Kind::Extract(pb::Extract {
                            roots: vec![result.roots[0].variants[0].term],
                            variants: 1,
                            extractor: pb::Extractor::Tree.into(),
                            ..Default::default()
                        })),
                        ..Default::default()
                    }],
                    ..Default::default()
                };
                assert_eq!(run(&mut engine, id, reingest.clone()).error, None);
                rendered
                    .parse_and_run_program(None, &renderer.render(&reingest).unwrap())
                    .unwrap();
            }
        }
    }
    assert_eq!(results, ["4", "[]", "[[3, 4]]"]);
}

#[test]
fn vec_empty_result_annotations_survive_multiple_shapes_and_rendering() {
    use egglog_experimental::protobuf::source::{Renderer, Source};
    let text = r#"(sort V (Vec i64)) (extract (vec-empty)) (sort S (Vec String))
        (function empty () V :merge new) (set (empty) (vec-empty)) (extract (empty))"#;
    let mut renderer = Renderer::default();
    let mut reparsed = new_experimental_egraph();
    let mut engine = Engine::default();
    let id = create(&mut engine);
    for (index, phase) in Source::new(None, text).unwrap().enumerate() {
        let mut program = phase.unwrap();
        if index == 5 {
            let Some(pb::command::Kind::Extract(extract)) = &program.commands[0].kind else {
                unreachable!()
            };
            program.nodes[extract.roots[0] as usize].kind = Some(pb::node::Kind::Call(pb::Call {
                func: "egglog.core.vec.empty".into(),
                args: vec![],
            }));
        }
        reparsed
            .parse_and_run_program(None, &renderer.render(&program).unwrap())
            .unwrap();
        let response = run(&mut engine, id, program.clone());
        assert_eq!(response.error, None);
        if index == 5 {
            let Some(pb::command_output::Kind::Extraction(result)) = &response.outputs[0].kind
            else {
                unreachable!()
            };
            assert_eq!(value(&response, result.roots[0].variants[0].term), "[]");
            let bytes = engine
                .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
                .unwrap();
            let clone = pb::CloneEGraphResponse::decode(bytes.as_slice())
                .unwrap()
                .egraph_id;
            assert!(program.declarations.is_empty());
            let last = program.sorts.len() as u32 - 1;
            program.sorts.reverse();
            for sort in &mut program.sorts {
                if let Some(pb::sort::Kind::Family(family)) = &mut sort.kind {
                    for index in &mut family.args {
                        *index = last - *index;
                    }
                }
            }
            for node in &mut program.nodes {
                node.sort_id = last - node.sort_id;
            }
            assert_eq!(run(&mut engine, clone, program.clone()).error, None);
            reparsed
                .parse_and_run_program(None, &renderer.render(&program).unwrap())
                .unwrap();
        }
    }
}

#[test]
fn vec_corrupt_annotations_and_private_names_reject_before_mutation() {
    use egglog_experimental::protobuf::source::Source;
    for corrupt in 0..9 {
        let text = "(sort V (Vec i64)) (function observed () i64 :merge new) (set (observed) 0) (set (observed) (vec-get (vec-of 7) 0)) (extract (observed))";
        let mut source = Source::new(None, text).unwrap();
        let mut engine = Engine::default();
        let id = create(&mut engine);
        for _ in 0..3 {
            assert_eq!(
                run(&mut engine, id, source.next().unwrap().unwrap()).error,
                None
            );
        }
        let mut program = source.next().unwrap().unwrap();
        let get = program.nodes.iter().position(|n| matches!(&n.kind, Some(pb::node::Kind::Call(c)) if c.func == "egglog.core.vec.get")).unwrap();
        let vec_sort = program.sorts.iter().position(|s| matches!(&s.kind, Some(pb::sort::Kind::Family(f)) if f.name == "Vec" && matches!(program.sorts[f.args[0] as usize].kind, Some(pb::sort::Kind::Family(_))))).unwrap();
        match corrupt {
            0 => {
                let Some(pb::node::Kind::Call(call)) = &mut program.nodes[get].kind else {
                    unreachable!()
                };
                call.func = "vec-get".into();
            }
            1 => program.nodes[get].sort_id = vec_sort as u32,
            2 | 8 => {
                let index = program.sorts.len() as u32;
                program.sorts.push(pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "f64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                });
                let literal = program
                    .nodes
                    .iter_mut()
                    .find(|n| {
                        matches!(
                            &n.kind,
                            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                                value: Some(pb::primitive_value::Value::I64(7))
                            }))
                        )
                    })
                    .unwrap();
                literal.sort_id = index;
                literal.kind = Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::F64Bits(7.0f64.to_bits())),
                }));
                if corrupt == 8 {
                    let node = program.nodes.iter_mut().find(|n| matches!(&n.kind, Some(pb::node::Kind::Call(c)) if c.func == "egglog.core.vec.of")).unwrap();
                    let Some(pb::node::Kind::Call(call)) = node.kind.take() else {
                        unreachable!()
                    };
                    node.kind = Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Vec(pb::ValueList {
                            items: call.args,
                        })),
                    }));
                }
            }
            3 => {
                let variable = program
                    .sorts
                    .iter_mut()
                    .find(|s| matches!(s.kind, Some(pb::sort::Kind::Var(_))))
                    .unwrap();
                variable.kind = Some(pb::sort::Kind::Var(1));
            }
            4 => {
                let Some(pb::sort::Kind::Family(f)) = &mut program.sorts[vec_sort].kind else {
                    unreachable!()
                };
                f.args[0] = vec_sort as u32;
            }
            5 => {
                let family = program
                    .declarations
                    .iter_mut()
                    .find_map(|d| match &mut d.kind {
                        Some(pb::declaration::Kind::HostSortFamily(f)) if f.name == "Vec" => {
                            Some(f)
                        }
                        _ => None,
                    })
                    .unwrap();
                family.arity = 2;
            }
            6 => program.declarations.push(pb::Declaration {
                kind: Some(pb::declaration::Kind::EqSort(pb::EqSort {
                    name: "__egglog_proto_vec_3_i64".into(),
                    ..Default::default()
                })),
                ..Default::default()
            }),
            7 => {
                let Some(pb::node::Kind::Call(call)) = &mut program.nodes[get].kind else {
                    unreachable!()
                };
                call.args.pop();
            }
            _ => unreachable!(),
        }
        assert!(
            run(&mut engine, id, program).error.is_some(),
            "corruption {corrupt}"
        );
        let response = run(&mut engine, id, source.next().unwrap().unwrap());
        assert_eq!(response.error, None);
        let Some(pb::command_output::Kind::Extraction(result)) = &response.outputs[0].kind else {
            unreachable!()
        };
        assert_eq!(value(&response, result.roots[0].variants[0].term), "0");
    }
}

#[test]
fn vec_lookup_failure_and_nominal_source_error_preserve_prefixes() {
    use egglog_experimental::protobuf::source::Source;
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let text = "(sort V (Vec i64)) (function observed () i64 :merge new) (set (observed) 4) (set (observed) (vec-get (vec-of 8) 3)) (extract (observed))";
    let mut source = Source::new(None, text).unwrap();
    for _ in 0..3 {
        assert_eq!(
            run(&mut engine, id, source.next().unwrap().unwrap()).error,
            None
        );
    }
    let failure = run(&mut engine, id, source.next().unwrap().unwrap());
    assert_eq!(
        failure.error.as_ref().unwrap().code,
        i32::from(pb::ErrorCode::EvaluationFailed)
    );
    assert_eq!(
        failure
            .error
            .as_ref()
            .unwrap()
            .location
            .as_ref()
            .unwrap()
            .path,
        [0]
    );
    let response = run(&mut engine, id, source.next().unwrap().unwrap());
    let Some(pb::command_output::Kind::Extraction(result)) = &response.outputs[0].kind else {
        unreachable!()
    };
    assert_eq!(value(&response, result.roots[0].variants[0].term), "4");

    let text = "(sort A (Vec i64)) (function a () A :merge new) (set (a) (vec-of 1)) (sort B (Vec i64)) (function b () B :merge new) (set (b) (vec-of 2)) (set (b) (a))";
    let mut source = Source::new(None, text).unwrap();
    let id = create(&mut engine);
    for _ in 0..6 {
        assert_eq!(
            run(&mut engine, id, source.next().unwrap().unwrap()).error,
            None
        );
    }
    assert!(
        source.next().unwrap().is_err(),
        "source nominal aliases must not become interchangeable"
    );
}

#[test]
fn source_scalar_builtin_definitions_select_distinct_overloads() {
    use egglog_experimental::protobuf::source::{Source, render};
    let text = "(extract (+ 1 2)) (extract (+ 1.0 2.0))";
    let mut native = new_experimental_egraph();
    native.parse_and_run_program(None, text).unwrap();
    let mut reparsed = new_experimental_egraph();
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut observed = vec![];
    let mut keys = vec![];
    for program in Source::new(None, text).unwrap() {
        let program = pb::Program::decode(program.unwrap().encode_to_vec().as_slice()).unwrap();
        let definitions = program
            .declarations
            .iter()
            .filter_map(|declaration| match &declaration.kind {
                Some(pb::declaration::Kind::HostPrimitive(primitive)) => {
                    Some(primitive.name.clone())
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(definitions.len(), 1);
        keys.extend(definitions);
        reparsed
            .parse_and_run_program(None, &render(&program).unwrap())
            .unwrap();
        let response = run(&mut engine, id, program);
        assert_eq!(response.error, None);
        let Some(pb::command_output::Kind::Extraction(result)) = &response.outputs[0].kind else {
            panic!("expected extraction")
        };
        observed.push(value(&response, result.roots[0].variants[0].term));
    }
    assert_eq!(keys, ["egglog.core.i64.add", "egglog.core.f64.add"]);
    assert_eq!(observed, ["3", "3.0"]);
}

#[test]
fn builtin_wire_identity_and_descriptor_errors_prevent_mutation() {
    use egglog_experimental::protobuf::source::Source;
    for corrupt in 0..7 {
        let mut engine = Engine::default();
        let id = create(&mut engine);
        let mut source = Source::new(None, "(function observed () i64 :merge new) (set (observed) 0) (set (observed) (+ 1 2)) (extract (observed))").unwrap();
        for _ in 0..2 {
            assert_eq!(
                run(&mut engine, id, source.next().unwrap().unwrap()).error,
                None
            );
        }
        let mut program = source.next().unwrap().unwrap();
        let index = program.nodes.iter().position(|node| matches!(&node.kind, Some(pb::node::Kind::Call(call)) if call.func == "egglog.core.i64.add")).unwrap();
        match corrupt {
            0 | 1 => {
                let Some(pb::node::Kind::Call(call)) = &mut program.nodes[index].kind else {
                    unreachable!()
                };
                call.func = if corrupt == 0 {
                    "egglog.core.f64.add"
                } else {
                    "missing.builtin"
                }
                .into();
            }
            2 => {
                let sort = program.sorts.len() as u32;
                program.sorts.push(pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "f64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                });
                program.nodes[index].sort_id = sort;
            }
            3 => {
                let declaration = program
                    .declarations
                    .iter_mut()
                    .find_map(|declaration| match &mut declaration.kind {
                        Some(pb::declaration::Kind::HostPrimitive(primitive)) => Some(primitive),
                        _ => None,
                    })
                    .unwrap();
                let Some(pb::host_primitive::Typing::Signature(signature)) =
                    &mut declaration.typing
                else {
                    unreachable!()
                };
                signature.inputs.pop();
            }
            4 => {
                let Some(pb::node::Kind::Call(call)) = &mut program.nodes[index].kind else {
                    unreachable!()
                };
                call.func = "+".into(); // Source aliases are not wire identities.
            }
            5 => {
                let declaration = program
                    .declarations
                    .iter_mut()
                    .find(|declaration| {
                        matches!(
                            &declaration.kind,
                            Some(pb::declaration::Kind::HostPrimitive(_))
                        )
                    })
                    .unwrap();
                declaration
                    .bindings
                    .as_mut()
                    .unwrap()
                    .egglog
                    .as_mut()
                    .unwrap()
                    .views[0]
                    .symbol = "wrong-alias".into();
            }
            6 => {
                let family = program
                    .declarations
                    .iter_mut()
                    .find_map(|declaration| match &mut declaration.kind {
                        Some(pb::declaration::Kind::HostSortFamily(family)) => Some(family),
                        _ => None,
                    })
                    .unwrap();
                family.arity = 1;
            }
            _ => unreachable!(),
        }
        assert!(run(&mut engine, id, program).error.is_some());
        let response = run(&mut engine, id, source.next().unwrap().unwrap());
        assert_eq!(response.error, None);
        let Some(pb::command_output::Kind::Extraction(result)) = &response.outputs[0].kind else {
            panic!("expected observation")
        };
        assert_eq!(value(&response, result.roots[0].variants[0].term), "0");
    }
}

#[test]
fn source_builtin_overflow_preserves_executed_prefix() {
    use egglog_experimental::protobuf::source::Source;
    let text = "(function observed () i64 :merge new) (set (observed) 4) (set (observed) (+ 9223372036854775807 1)) (set (observed) 9)";
    assert!(
        new_experimental_egraph()
            .parse_and_run_program(None, text)
            .is_err()
    );
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut source = Source::new(None, text).unwrap();
    for _ in 0..2 {
        assert_eq!(
            run(&mut engine, id, source.next().unwrap().unwrap()).error,
            None
        );
    }
    let failure = run(&mut engine, id, source.next().unwrap().unwrap());
    assert_eq!(
        failure.error.as_ref().unwrap().code,
        i32::from(pb::ErrorCode::EvaluationFailed)
    );
    assert_eq!(
        failure
            .error
            .as_ref()
            .unwrap()
            .location
            .as_ref()
            .unwrap()
            .path,
        [0]
    );
    let mut observation = source.next().unwrap().unwrap();
    let Some(pb::command::Kind::Action(pb::Action {
        kind: Some(pb::action::Kind::Set(set)),
        ..
    })) = &observation.commands[0].kind
    else {
        unreachable!()
    };
    let root = observation.nodes.len() as u32;
    observation.nodes.push(pb::Node {
        sort_id: 0,
        kind: Some(pb::node::Kind::Call(set.target.clone().unwrap())),
        ..Default::default()
    });
    observation.commands = vec![pb::Command {
        kind: Some(pb::command::Kind::Extract(pb::Extract {
            roots: vec![root],
            variants: 1,
            extractor: pb::Extractor::Tree.into(),
            ..Default::default()
        })),
        ..Default::default()
    }];
    let response = run(&mut engine, id, observation);
    assert_eq!(response.error, None);
    let Some(pb::command_output::Kind::Extraction(result)) = &response.outputs[0].kind else {
        panic!("expected observation")
    };
    assert_eq!(value(&response, result.roots[0].variants[0].term), "4");
}

#[test]
fn source_fixture_executes_and_renders_from_decoded_programs() {
    use egglog_experimental::protobuf::source::{Source, render};
    let source = r#"
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
    "#;
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut reparsed = new_experimental_egraph();
    let mut extracted = vec![];
    let mut native_extracted = vec![];
    let mut runs = 0;
    for program in Source::new(Some("source.egg".into()), source).unwrap() {
        let program = program.unwrap();
        let decoded = pb::Program::decode(program.encode_to_vec().as_slice()).unwrap();
        let rendered = render(&decoded).unwrap();
        for output in reparsed.parse_and_run_program(None, &rendered).unwrap() {
            if let egglog_experimental::CommandOutput::ExtractBest(dag, _, root) = output {
                native_extracted.push(dag.to_string(root));
            }
        }
        let response = run(&mut engine, id, decoded);
        assert_eq!(response.error, None);
        for output in &response.outputs {
            match output.kind.as_ref().unwrap() {
                pb::command_output::Kind::Extraction(result) => {
                    extracted.push(value(&response, result.roots[0].variants[0].term));
                }
                pb::command_output::Kind::Run(_) => runs += 1,
                _ => panic!("unexpected output"),
            }
        }
    }
    assert_eq!(runs, 1);
    assert_eq!(extracted, ["(Num 20)", "10"]);
    // Source uses private native symbols; byte responses retain logical keys.
    assert_eq!(native_extracted, ["(__egglog_proto_call_4e756d 20)", "10"]);
}

#[test]
fn source_captures_before_later_writes() {
    use egglog_experimental::protobuf::source::Source;
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut extracted = vec![];
    for program in Source::new(
        None,
        r#"
        (function f () i64 :merge new)
        (set (f) 0)
        (let $x (f))
        (set (f) 1)
        (check (= $x 0) (= (f) 1))
        (extract $x)
        (extract (f))
    "#,
    )
    .unwrap()
    {
        let response = run(&mut engine, id, program.unwrap());
        assert_eq!(response.error, None);
        for output in &response.outputs {
            if let Some(pb::command_output::Kind::Extraction(result)) = &output.kind {
                extracted.push(value(&response, result.roots[0].variants[0].term));
            }
        }
    }
    assert_eq!(extracted, ["0", "1"]);
}

#[test]
fn source_resolution_and_runtime_errors_preserve_only_executed_prefixes() {
    use egglog_experimental::protobuf::source::Source;
    let mut before_declaration =
        Source::new(None, "(set (late) 1) (function late () i64 :merge new)").unwrap();
    assert!(before_declaration.next().unwrap().is_err());
    assert!(before_declaration.next().is_none());
    for tail in ["(set (missing) 2)", "(check (= (f) 2))"] {
        let mut engine = Engine::default();
        let id = create(&mut engine);
        let mut source = Source::new(
            None,
            &format!("(function f () i64 :merge new) (set (f) 1) {tail} (set (f) 3)"),
        )
        .unwrap();
        let mut failed = false;
        for program in source.by_ref() {
            let Ok(program) = program else {
                failed = true;
                break;
            };
            let response = run(&mut engine, id, program);
            if response.error.is_some() {
                failed = true;
                break;
            }
        }
        assert!(failed);
        let mut observation = fixture();
        observation.declarations.clear();
        observation.rules.clear();
        observation.rulesets.clear();
        observation.sorts.truncate(1);
        observation.nodes = vec![pb::Node {
            sort_id: 0,
            kind: Some(pb::node::Kind::Call(pb::Call {
                func: "f".into(),
                args: vec![],
            })),
            ..Default::default()
        }];
        observation.commands = vec![pb::Command {
            kind: Some(pb::command::Kind::Extract(pb::Extract {
                roots: vec![0],
                variants: 1,
                extractor: pb::Extractor::Tree.into(),
                ..Default::default()
            })),
            ..Default::default()
        }];
        let response = run(&mut engine, id, observation);
        assert_eq!(response.error, None);
        let Some(pb::command_output::Kind::Extraction(result)) = &response.outputs[0].kind else {
            panic!("missing extraction")
        };
        assert_eq!(value(&response, result.roots[0].variants[0].term), "1");
    }
}

#[test]
fn source_byte_mutation_controls_execution() {
    use egglog_experimental::protobuf::source::{Source, render};
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut source = Source::new(
        None,
        "(function f () i64 :merge new) (set (f) 1) (extract (f))",
    )
    .unwrap();
    assert_eq!(
        run(&mut engine, id, source.next().unwrap().unwrap()).error,
        None
    );
    let program = source.next().unwrap().unwrap();
    let mut request = pb::RunProgramRequest {
        egraph_id: id,
        program: Some(program),
        profile: true,
    };
    let mut bytes = request.encode_to_vec();
    bytes.push(0x80);
    assert!(engine.run(&bytes).is_err());
    let observation = source.next().unwrap().unwrap();
    assert!(
        run(&mut engine, id, observation.clone()).error.is_some(),
        "malformed set must not create the row"
    );
    for node in &mut request.program.as_mut().unwrap().nodes {
        if let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::I64(value)),
        })) = &mut node.kind
        {
            *value = 7;
        }
    }
    assert!(
        render(request.program.as_ref().unwrap())
            .unwrap()
            .contains("7")
    );
    let response =
        pb::RunProgramResponse::decode(engine.run(&request.encode_to_vec()).unwrap().as_slice())
            .unwrap();
    assert_eq!(response.error, None);
    let response = run(&mut engine, id, observation);
    let Some(pb::command_output::Kind::Extraction(result)) = &response.outputs[0].kind else {
        panic!("missing extraction")
    };
    assert_eq!(value(&response, result.roots[0].variants[0].term), "7");
}

#[test]
fn source_native_hook_preserves_globals_without_executing_actions() {
    use egglog_experimental::ast::{GenericAction, GenericExpr, GenericFact, GenericNCommand};
    let mut graph = new_experimental_egraph();
    let commands = graph
        .parse_program(
            None,
            "(function f () i64 :no-merge) (let $x (f)) (check (= $x 0))",
        )
        .unwrap();
    let mut resolved = vec![];
    for command in commands {
        resolved.extend(graph.resolve_command_preserving_globals(command).unwrap());
    }
    assert!(
        graph.get_function("f").is_none(),
        "resolution must not install a runtime table"
    );
    let GenericNCommand::CoreAction(GenericAction::Let(_, binding, _)) = &resolved[1] else {
        panic!("global binding was lowered prematurely")
    };
    assert_eq!(binding.sort.name(), "i64");
    let GenericNCommand::Check(_, facts) = &resolved[2] else {
        panic!("expected check")
    };
    let GenericFact::Eq(_, GenericExpr::Var(_, reference), _) = &facts[0] else {
        panic!("global reference was lowered prematurely")
    };
    assert!(reference.is_global_ref);
    assert_eq!(reference.name, "$x");
}

#[test]
fn source_hook_refactor_preserves_native_proof_pipeline() {
    use egglog_experimental::{CommandOutput, EGraph};
    for mut graph in [EGraph::new_with_term_encoding(), EGraph::new_with_proofs()] {
        graph
            .parse_and_run_program(None, "(datatype E (Num i64)) (Num 2) (check (Num 2))")
            .unwrap();
        if graph.are_proofs_enabled() {
            let outputs = graph
                .parse_and_run_program(None, "(prove (Num 2))")
                .unwrap();
            assert!(
                outputs
                    .iter()
                    .any(|output| matches!(output, CommandOutput::ProveExists { .. }))
            );
        }
    }
}

#[test]
fn source_rejects_late_rule_growth_and_unimplemented_provenance() {
    use egglog_experimental::protobuf::source::Source;
    let mut source = Source::new(None, "(datatype M (Num i64) (Box M)) (ruleset r) (Box (Num 1)) (run r 1) (rewrite (Box x) x :ruleset r)").unwrap();
    for _ in 0..4 {
        assert!(source.next().unwrap().is_ok());
    }
    assert!(
        source
            .next()
            .unwrap()
            .unwrap_err()
            .to_string()
            .contains("after its first run")
    );
    assert!(source.next().is_none());
    for text in ["(relation R (i64))", "(primitive p (i64) i64 _0)"] {
        assert!(Source::new(None, text).unwrap().next().unwrap().is_err());
    }
}

#[test]
fn source_rejects_include_without_panicking() {
    use egglog_experimental::protobuf::source::Source;
    assert!(
        Source::new(None, "(include \"not-read.egg\")")
            .unwrap()
            .next()
            .unwrap()
            .is_err()
    );
}

#[test]
fn source_validates_each_rule_before_following_effects() {
    use egglog_experimental::protobuf::source::Source;
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut source = Source::new(
        None,
        r#"
        (datatype E (A))
        (function f (E) E :merge new)
        (function observed () i64 :merge new)
        (ruleset r)
        (rewrite (f x) x :ruleset r :subsume)
        (set (observed) 1)
        (run r 1)
    "#,
    )
    .unwrap();
    for _ in 0..4 {
        assert_eq!(
            run(&mut engine, id, source.next().unwrap().unwrap()).error,
            None
        );
    }
    let rule = source.next().unwrap().unwrap();
    assert!(
        run(&mut engine, id, rule).error.is_some(),
        "invalid rule must fail at its source position, not a future run"
    );
}

#[test]
fn source_keeps_native_rule_names_and_global_shadowing_checks() {
    use egglog_experimental::protobuf::source::Source;
    for (text, prefix_len) in [
        (
            r#"(datatype E (A) (B)) (ruleset r) (rule () ((A)) :ruleset r :name "dup") (rule () ((B)) :ruleset r :name "dup")"#,
            3,
        ),
        ("(let $x 0) (check (= x 1))", 1),
        (
            "(function f () i64 :no-merge) (set (f) 2) (check (= (f) f) (= f 2))",
            2,
        ),
    ] {
        let mut native = new_experimental_egraph();
        assert!(native.parse_and_run_program(None, text).is_err());
        let mut source = Source::new(None, text).unwrap();
        for _ in 0..prefix_len {
            assert!(source.next().unwrap().is_ok());
        }
        assert!(
            source.next().unwrap().is_err(),
            "native source rejection must survive: {text}"
        );
    }
}

#[test]
fn source_renderer_prevents_identifier_injection() {
    use egglog_experimental::protobuf::source::render;
    let injected = "f () i64 :merge new)\n(panic \"injected\")\n(function g";
    for target in 0..5 {
        let mut program = fixture();
        program.commands.truncate(1);
        match target {
            0 => {
                let Some(pb::declaration::Kind::Function(function)) =
                    &mut program.declarations[3].kind
                else {
                    panic!("expected function")
                };
                function.name = injected.into();
            }
            1 => program.sorts[1].kind = Some(pb::sort::Kind::Eq(injected.into())),
            2 => program.nodes[3].kind = Some(pb::node::Kind::Var(injected.into())),
            3 => program.rulesets[0].name = Some(injected.into()),
            4 => {
                let Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Set(set)),
                    ..
                })) = &mut program.commands[0].kind
                else {
                    panic!("expected set")
                };
                set.target.as_mut().unwrap().func = injected.into();
            }
            _ => unreachable!(),
        }
        if matches!(target, 2 | 3) {
            assert!(render(&program).is_err());
        } else {
            let source = render(&program).unwrap();
            assert!(!source.contains("(panic \"injected\")"));
            new_experimental_egraph()
                .parser
                .get_program_from_string(None, &source)
                .unwrap();
        }
    }
}

#[test]
fn source_global_fresh_name_collision_canary() {
    use egglog_experimental::protobuf::source::Source;
    // Core's test_fresh_name_collision_globals, also through protobuf. The
    // x/x1 hints used to mint the same name after ten intervening captures.
    let mut text = String::from(
        r#"
        (sort B)
        (constructor var (String) B)
        (constructor and2 (B B) B)
        (constructor or2 (B B) B)
        (let x (var "x"))
        (let y (var "y"))
    "#,
    );
    for i in 1..=10 {
        text.push_str(&format!("(let t{i} (or2 x y))\n"));
    }
    text.push_str(
        r#"(let x1 (var "x1")) (let out (and2 x x1)) (check (= out (and2 (var "x") x1)))"#,
    );
    new_experimental_egraph()
        .parse_and_run_program(None, &text)
        .unwrap();
    let mut engine = Engine::default();
    let id = create(&mut engine);
    for program in Source::new(None, &text).unwrap() {
        assert_eq!(run(&mut engine, id, program.unwrap()).error, None);
    }
}

#[test]
fn source_rule_locals_do_not_escape_into_later_declarations() {
    use egglog_experimental::protobuf::source::{Source, render};
    let text = r#"
        (datatype E (Num i64))
        (function observed () i64 :merge new)
        (let captured 7)
        (ruleset r)
        (rule ((= e (Num x)) (= x captured)) ((set (observed) x)) :ruleset r :name "keep")
        (function x () i64 :merge new)
        (function __proto_source_local_0_0 () i64 :merge new)
        (Num 7)
        (run r 1)
        (check (= (observed) 7))
        (extract (observed))
    "#;
    new_experimental_egraph()
        .parse_and_run_program(None, text)
        .unwrap();
    let mut rendered = new_experimental_egraph();
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut extracted = None;
    for program in Source::new(Some("locals.egg".into()), text).unwrap() {
        let program = pb::Program::decode(program.unwrap().encode_to_vec().as_slice()).unwrap();
        let response = run(&mut engine, id, program.clone());
        assert_eq!(response.error, None);
        rendered
            .parse_and_run_program(None, &render(&program).unwrap())
            .unwrap();
        if let Some(rule) = program.rules.first() {
            assert_eq!(rule.name.as_deref(), Some("keep"));
            assert!(rule.span.is_some());
        }
        for output in &response.outputs {
            if let Some(pb::command_output::Kind::Extraction(result)) = &output.kind {
                extracted = Some(value(&response, result.roots[0].variants[0].term));
            }
        }
    }
    assert_eq!(extracted.as_deref(), Some("7"));
}

#[test]
fn source_renderer_preserves_expression_action_grammar() {
    use egglog_experimental::protobuf::source::{Source, render};
    for name in ["panic", "include", "multi-extract"] {
        let mut engine = Engine::default();
        let id = create(&mut engine);
        let text = format!(
            "(function {name} (String) i64 :merge new) (set ({name} \"hello\") 1) (extract ({name} \"hello\"))"
        );
        let mut source = Source::new(None, &text).unwrap();
        let mut rendered = new_experimental_egraph();
        for _ in 0..2 {
            let program = source.next().unwrap().unwrap();
            rendered
                .parse_and_run_program(None, &render(&program).unwrap())
                .unwrap();
            assert_eq!(run(&mut engine, id, program).error, None);
        }
        let mut program = source.next().unwrap().unwrap();
        let Some(pb::command::Kind::Extract(extract)) = &program.commands[0].kind else {
            panic!("expected extract")
        };
        let action = pb::Action {
            kind: Some(pb::action::Kind::Term(extract.roots[0])),
            ..Default::default()
        };
        program.commands[0].kind = Some(pb::command::Kind::Action(action.clone()));
        let program = pb::Program::decode(program.encode_to_vec().as_slice()).unwrap();
        assert_eq!(run(&mut engine, id, program.clone()).error, None);
        rendered
            .parse_and_run_program(None, &render(&program).unwrap())
            .unwrap();

        // Native rule heads permit constructor calls, not custom-function
        // reads, so use a constructor to witness the same grammar boundary.
        let mut constructors = Source::new(
            None,
            &format!("(datatype E ({name} String)) (extract ({name} \"hello\"))"),
        )
        .unwrap();
        let rule_id = create(&mut engine);
        let declaration = constructors.next().unwrap().unwrap();
        let mut rendered_rule = new_experimental_egraph();
        rendered_rule
            .parse_and_run_program(None, &render(&declaration).unwrap())
            .unwrap();
        assert_eq!(run(&mut engine, rule_id, declaration).error, None);
        let mut rule_program = constructors.next().unwrap().unwrap();
        let Some(pb::command::Kind::Extract(extract)) = &rule_program.commands[0].kind else {
            panic!("expected constructor extract")
        };
        let action = pb::Action {
            kind: Some(pb::action::Kind::Term(extract.roots[0])),
            ..Default::default()
        };
        rule_program.commands.clear();
        rule_program.rules = vec![pb::RuleDecl {
            kind: Some(pb::rule_decl::Kind::Rule(pb::Rule {
                query: vec![],
                head: vec![action],
            })),
            eval_mode: pb::RuleEvalMode::Seminaive.into(),
            ..Default::default()
        }];
        rule_program.rulesets = vec![pb::Ruleset {
            name: Some("r".into()),
            kind: Some(pb::ruleset::Kind::Rules(pb::RuleList { rules: vec![0] })),
            ..Default::default()
        }];
        assert_eq!(run(&mut engine, rule_id, rule_program.clone()).error, None);
        rendered_rule
            .parse_and_run_program(None, &render(&rule_program).unwrap())
            .unwrap();
        rendered_rule
            .parse_and_run_program(None, "(run r 1)")
            .unwrap();
    }
}

#[test]
fn source_plain_rule_and_subsuming_rewrite_roundtrip() {
    use egglog_experimental::protobuf::source::{Source, render};
    for (text, expected) in [
        (
            r#"(datatype E (A i64)) (function f (i64) i64 :merge new)
            (rule ((A x)) ((set (f x) x)) :name "copy")
            (A 7) (run 1) (check (= (f 7) 7)) (extract (f 7))"#,
            "7",
        ),
        (
            r#"(datatype E (Num i64) (Box E)) (ruleset r)
            (rewrite (Box x) x :ruleset r :subsume)
            (Box (Num 1)) (run r 1) (extract (Box (Num 1)))"#,
            "(Num 1)",
        ),
    ] {
        let mut native = new_experimental_egraph();
        let mut engine = Engine::default();
        let id = create(&mut engine);
        let mut observed = None;
        for program in Source::new(None, text).unwrap() {
            let bytes = program.unwrap().encode_to_vec();
            let program = pb::Program::decode(bytes.as_slice()).unwrap();
            let outputs = native
                .parse_and_run_program(None, &render(&program).unwrap())
                .unwrap();
            let response = run(&mut engine, id, program);
            assert_eq!(response.error, None);
            for output in &response.outputs {
                if let Some(pb::command_output::Kind::Extraction(result)) = &output.kind {
                    observed = Some(value(&response, result.roots[0].variants[0].term));
                    let egglog_experimental::CommandOutput::ExtractBest(dag, _, root) = &outputs[0]
                    else {
                        panic!("expected rendered extraction")
                    };
                    assert_eq!(
                        dag.to_string(*root),
                        expected.replace("Num", "__egglog_proto_call_4e756d")
                    );
                }
            }
        }
        assert_eq!(observed.as_deref(), Some(expected));
    }
}

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
        options: Some(pb::EGraphOptions {
            cost_sort: Some(0),
            ..Default::default()
        }),
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
        pb::node::Kind::PrimitiveValue(primitive) => match primitive.value.as_ref().unwrap() {
            pb::primitive_value::Value::I64(n) => n.to_string(),
            pb::primitive_value::Value::F64Bits(bits) => format!("{:?}", f64::from_bits(*bits)),
            pb::primitive_value::Value::Vec(list) => format!(
                "[{}]",
                list.items
                    .iter()
                    .map(|i| value(response, *i))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
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
        options: Some(pb::EGraphOptions {
            cost_sort: Some(0),
            ..Default::default()
        }),
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
fn creation_threads_execute_and_preserve_clone_and_error_prefixes() {
    for threads in [0, 1, 2] {
        if cfg!(target_family = "wasm") && threads > 1 {
            continue;
        }
        let mut engine = Engine::default();
        let request = pb::CreateEGraphRequest {
            sorts: fixture().sorts[..1].to_vec(),
            options: Some(pb::EGraphOptions {
                cost_sort: Some(0),
                ..Default::default()
            }),
            threads: Some(threads),
            ..Default::default()
        };
        let bytes = engine.create(&request.encode_to_vec()).unwrap();
        let id = pb::CreateEGraphResponse::decode(bytes.as_slice())
            .unwrap()
            .egraph_id;
        assert_eq!(run(&mut engine, id, fixture()).error, None);
        let bytes = engine
            .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
            .unwrap();
        let clone = pb::CloneEGraphResponse::decode(bytes.as_slice())
            .unwrap()
            .egraph_id;
        let mut prefix = fixture();
        prefix.declarations.clear();
        prefix.rules.clear();
        prefix.rulesets.clear();
        prefix.commands = vec![
            prefix.commands[2].clone(),
            pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Panic("thread prefix".into())),
                    ..Default::default()
                })),
                ..Default::default()
            },
            prefix.commands[0].clone(),
        ];
        let Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Set(set)),
            ..
        })) = &mut prefix.commands[0].kind
        else {
            unreachable!()
        };
        set.value = Some(2); // current := 30, then panic, never current := 10.
        let failed = run(&mut engine, id, prefix.clone());
        assert_eq!(failed.error.unwrap().location.unwrap().path, [1]);
        prefix.commands = vec![pb::Command {
            kind: Some(pb::command::Kind::Extract(pb::Extract {
                roots: vec![4],
                variants: 1,
                extractor: pb::Extractor::Tree.into(),
                ..Default::default()
            })),
            ..Default::default()
        }];
        for (handle, expected) in [(id, "30"), (clone, "20")] {
            let response = run(&mut engine, handle, prefix.clone());
            assert_eq!(response.error, None);
            let Some(pb::command_output::Kind::Extraction(result)) = &response.outputs[0].kind
            else {
                unreachable!()
            };
            assert_eq!(value(&response, result.roots[0].variants[0].term), expected);
        }
    }
}

#[test]
fn resource_updates_preserve_program_prefix_and_clone_isolation() {
    use pb::configure_e_graph_resources_request::Operation;
    let mut engine = Engine::default();
    let id = create(&mut engine);
    assert_eq!(run(&mut engine, id, fixture()).error, None);
    let selected = if cfg!(target_family = "wasm") { 1 } else { 2 };
    let bytes = engine
        .configure_resources(
            &pb::ConfigureEGraphResourcesRequest {
                egraph_id: id,
                operation: Some(Operation::Threads(selected)),
            }
            .encode_to_vec(),
        )
        .unwrap();
    assert_eq!(
        pb::ConfigureEGraphResourcesResponse::decode(bytes.as_slice())
            .unwrap()
            .threads,
        u64::from(selected)
    );
    let bytes = engine
        .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
        .unwrap();
    let clone = pb::CloneEGraphResponse::decode(bytes.as_slice())
        .unwrap()
        .egraph_id;
    for (handle, operation, expected) in [
        (clone, Operation::Query(pb::Unit {}), selected),
        (clone, Operation::Threads(1), 1),
        (id, Operation::Query(pb::Unit {}), selected),
    ] {
        let bytes = engine
            .configure_resources(
                &pb::ConfigureEGraphResourcesRequest {
                    egraph_id: handle,
                    operation: Some(operation),
                }
                .encode_to_vec(),
            )
            .unwrap();
        assert_eq!(
            pb::ConfigureEGraphResourcesResponse::decode(bytes.as_slice())
                .unwrap()
                .threads,
            u64::from(expected)
        );
    }

    let mut prefix = fixture();
    prefix.declarations.clear();
    prefix.rules.clear();
    prefix.rulesets.clear();
    prefix.commands = vec![
        prefix.commands[0].clone(),
        pb::Command {
            kind: Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Panic("resource prefix".into())),
                ..Default::default()
            })),
            ..Default::default()
        },
    ];
    let Some(pb::command::Kind::Action(pb::Action {
        kind: Some(pb::action::Kind::Set(set)),
        ..
    })) = &mut prefix.commands[0].kind
    else {
        unreachable!()
    };
    set.value = Some(2);
    assert_eq!(
        run(&mut engine, id, prefix.clone())
            .error
            .unwrap()
            .location
            .unwrap()
            .path,
        [1]
    );
    let bytes = engine
        .configure_resources(
            &pb::ConfigureEGraphResourcesRequest {
                egraph_id: id,
                operation: Some(Operation::Threads(0)),
            }
            .encode_to_vec(),
        )
        .unwrap();
    let actual = pb::ConfigureEGraphResourcesResponse::decode(bytes.as_slice())
        .unwrap()
        .threads;
    assert!(actual >= 1);
    // A failed update and an inert query cannot alter the completed write.
    assert!(
        engine
            .configure_resources(
                &pb::ConfigureEGraphResourcesRequest {
                    egraph_id: id,
                    operation: None
                }
                .encode_to_vec()
            )
            .is_err()
    );
    let bytes = engine
        .configure_resources(
            &pb::ConfigureEGraphResourcesRequest {
                egraph_id: id,
                operation: Some(Operation::Query(pb::Unit {})),
            }
            .encode_to_vec(),
        )
        .unwrap();
    assert_eq!(
        pb::ConfigureEGraphResourcesResponse::decode(bytes.as_slice())
            .unwrap()
            .threads,
        actual
    );
    prefix.commands = vec![pb::Command {
        kind: Some(pb::command::Kind::Extract(pb::Extract {
            roots: vec![4],
            variants: 1,
            extractor: pb::Extractor::Tree.into(),
            ..Default::default()
        })),
        ..Default::default()
    }];
    for (handle, expected) in [(id, "30"), (clone, "20")] {
        let response = run(&mut engine, handle, prefix.clone());
        assert_eq!(response.error, None);
        let Some(pb::command_output::Kind::Extraction(result)) = &response.outputs[0].kind else {
            unreachable!()
        };
        assert_eq!(value(&response, result.roots[0].variants[0].term), expected);
    }
}

#[test]
fn unsupported_proof_commands_reject_preparation_before_any_action() {
    for proof in [
        pb::command::Kind::Prove(pb::Prove { facts: vec![] }),
        pb::command::Kind::ProveExists(pb::ProveExists {
            constructor: "Num".into(),
        }),
    ] {
        let mut engine = Engine::default();
        let id = create(&mut engine);
        assert_eq!(run(&mut engine, id, fixture()).error, None);
        let mut program = fixture();
        program.declarations.clear();
        program.rules.clear();
        program.rulesets.clear();
        program.commands = vec![
            program.commands[0].clone(),
            pb::Command {
                kind: Some(proof),
                ..Default::default()
            },
        ];
        let response = run(&mut engine, id, program.clone());
        assert_eq!(
            response.error.unwrap().code,
            i32::from(pb::ErrorCode::InvalidProgram)
        );
        assert!(response.outputs.is_empty());
        program.commands = vec![pb::Command {
            kind: Some(pb::command::Kind::Extract(pb::Extract {
                roots: vec![4],
                variants: 1,
                extractor: pb::Extractor::Tree.into(),
                ..Default::default()
            })),
            ..Default::default()
        }];
        let observed = run(&mut engine, id, program);
        assert_eq!(observed.error, None);
        let Some(pb::command_output::Kind::Extraction(result)) = &observed.outputs[0].kind else {
            unreachable!()
        };
        assert_eq!(value(&observed, result.roots[0].variants[0].term), "20");
    }
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
