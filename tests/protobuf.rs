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
    assert_eq!(
        binding.python.as_ref().unwrap().path,
        ["egglog", "builtins", "Vec"]
    );
    assert_eq!(
        pb::Program::decode(first.encode_to_vec().as_slice()).unwrap(),
        first
    );
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

#[test]
fn declaration_doc_presence_survives_bytes_without_changing_execution_or_resupply() {
    let mut encodings = vec![];
    for first in [None, Some(""), Some(" docs\n")] {
        let mut program = constant_fixture(&["test", "CURRENT"], &["test", "EMPTY"]);
        for declaration in &mut program.declarations {
            declaration.doc = first.map(str::to_owned);
        }
        let encoded = program.encode_to_vec();
        let decoded = pb::Program::decode(encoded.as_slice()).unwrap();
        assert_eq!(decoded, program);
        assert!(
            decoded
                .declarations
                .iter()
                .all(|d| d.doc.as_deref() == first)
        );
        encodings.push(encoded);
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
        let mut renderer = egglog_experimental::protobuf::source::Renderer::default();
        let mut native = new_experimental_egraph();
        native
            .parse_and_run_program(None, &renderer.render(&program).unwrap())
            .unwrap();
        for later in [None, Some(""), Some("other")] {
            let mut resupply = program.clone();
            for declaration in &mut resupply.declarations {
                declaration.doc = later.map(str::to_owned);
            }
            for handle in [id, clone] {
                let response = run(&mut engine, handle, resupply.clone());
                assert_eq!(response.error, None);
                let Some(pb::command_output::Kind::Extraction(result)) = &response.outputs[0].kind
                else {
                    unreachable!()
                };
                assert_eq!(value(&response, result.roots[0].variants[0].term), "20");
            }
            native
                .parse_and_run_program(None, &renderer.render(&resupply).unwrap())
                .unwrap();
            let Some(pb::declaration::Kind::Constructor(constructor)) =
                &mut resupply.declarations[1].kind
            else {
                unreachable!()
            };
            constructor.unextractable = true;
            resupply.commands = vec![program.commands[0].clone()]; // Would write current=10.
            assert!(run(&mut engine, id, resupply.clone()).error.is_some());
            assert!(renderer.render(&resupply).is_err());
        }
        let mut observation = program;
        observation.declarations.clear();
        observation.commands = vec![observation.commands.last().unwrap().clone()];
        let response = run(&mut engine, id, observation);
        assert_eq!(response.error, None);
        let Some(pb::command_output::Kind::Extraction(result)) = &response.outputs[0].kind else {
            unreachable!()
        };
        assert_eq!(value(&response, result.roots[0].variants[0].term), "20");
    }
    assert!(
        encodings[0] != encodings[1]
            && encodings[1] != encodings[2]
            && encodings[0] != encodings[2]
    );
    // This is byte transport/resupply behavior, not a Freeze or text-doc exporter.
}

#[test]
fn repeated_tail_descriptors_preserve_width_and_reject_incompatible_providers_before_writes() {
    let mut native = new_experimental_egraph();
    let mut canonical = constant_fixture(&["test", "CURRENT"], &["test", "EMPTY"]);
    native
        .type_info()
        .export_builtin_definition("egglog.core.vec.of", &mut canonical)
        .unwrap();
    let mut engine = Engine::default();
    let id = create(&mut engine);
    assert_eq!(run(&mut engine, id, canonical.clone()).error, None);
    let mut renderer = egglog_experimental::protobuf::source::Renderer::default();
    renderer.render(&canonical).unwrap();
    for width in [0, 2, 3] {
        let mut conflicting = canonical.clone();
        let primitive = conflicting
            .declarations
            .iter_mut()
            .find_map(|d| match &mut d.kind {
                Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.core.vec.of" => {
                    Some(p)
                }
                _ => None,
            })
            .unwrap();
        let Some(pb::host_primitive::Typing::Signature(signature)) = &mut primitive.typing else {
            unreachable!()
        };
        assert_eq!(signature.varargs.len(), 1);
        signature.varargs = vec![signature.varargs[0].clone(); width];
        conflicting.commands = vec![canonical.commands[0].clone()]; // Must not write current=10.
        let decoded = pb::Program::decode(conflicting.encode_to_vec().as_slice()).unwrap();
        assert_eq!(
            decoded, conflicting,
            "repeated equal patterns must not collapse"
        );
        assert!(run(&mut engine, id, decoded).error.is_some());
        assert!(renderer.render(&conflicting).is_err());
    }
    let mut observation = canonical.clone();
    observation.declarations.clear();
    observation.commands = vec![observation.commands.last().unwrap().clone()];
    let response = run(&mut engine, id, observation);
    assert_eq!(response.error, None);
    let Some(pb::command_output::Kind::Extraction(result)) = &response.outputs[0].kind else {
        unreachable!()
    };
    assert_eq!(value(&response, result.roots[0].variants[0].term), "20");
    assert_eq!(run(&mut engine, id, canonical).error, None);
    // The registered Vec provider has width1. Wider groups transport faithfully
    // but cannot replace its signature; no Map execution is claimed here.
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

fn pair_fixture() -> pb::Program {
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
                kind: Some(pb::sort::Kind::Family(pb::HostSort {
                    name: "String".into(),
                    args: vec![],
                })),
                ..Default::default()
            },
            pb::Sort {
                kind: Some(pb::sort::Kind::Family(pb::HostSort {
                    name: "Pair".into(),
                    args: vec![0, 1],
                })),
                ..Default::default()
            },
        ],
        declarations: vec![pb::Declaration {
            kind: Some(pb::declaration::Kind::HostSortFamily(pb::HostSortFamily {
                name: "Pair".into(),
                arity: 2,
                bindings: None,
            })),
            ..Default::default()
        }],
        nodes: vec![
            pb::Node {
                sort_id: 0,
                kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::I64(1)),
                })),
                ..Default::default()
            },
            pb::Node {
                sort_id: 1,
                kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::String("x".into())),
                })),
                ..Default::default()
            },
            pb::Node {
                sort_id: 2,
                kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Pair(pb::PairValue {
                        first: Some(0),
                        second: Some(1),
                    })),
                })),
                ..Default::default()
            },
        ],
        commands: vec![pb::Command {
            kind: Some(pb::command::Kind::Extract(pb::Extract {
                roots: vec![2],
                variants: 1,
                extractor: pb::Extractor::Tree.into(),
                ..Default::default()
            })),
            ..Default::default()
        }],
        ..Default::default()
    }
}

fn map_fixture() -> pb::Program {
    let mut p = pair_fixture();
    let Some(pb::sort::Kind::Family(f)) = &mut p.sorts[2].kind else {
        unreachable!()
    };
    f.name = "Map".into();
    let Some(pb::declaration::Kind::HostSortFamily(f)) = &mut p.declarations[0].kind else {
        unreachable!()
    };
    f.name = "Map".into();
    p.nodes.extend([
        pb::Node {
            sort_id: 1,
            kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::String("last".into())),
            })),
            ..Default::default()
        },
        pb::Node {
            sort_id: 0,
            kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::I64(2)),
            })),
            ..Default::default()
        },
    ]);
    p.nodes[2].kind = Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
        value: Some(pb::primitive_value::Value::Map(pb::MapValue {
            entries: vec![
                pb::MapEntry {
                    key: Some(0),
                    value: Some(1),
                },
                pb::MapEntry {
                    key: Some(4),
                    value: Some(1),
                },
                pb::MapEntry {
                    key: Some(0),
                    value: Some(3),
                },
            ],
        })),
    }));
    p
}

#[test]
fn map_value_bytes_extract_reingest_and_render() {
    use egglog_experimental::protobuf::source::Renderer;
    let mut program = map_fixture();
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut renderer = Renderer::default();
    let mut native = new_experimental_egraph();
    for _ in 0..2 {
        for key in ["empty", "of", "get", "insert"] {
            native
                .type_info()
                .export_builtin_definition(&format!("egglog.core.map.{key}"), &mut program)
                .unwrap();
        }
        let decoded = pb::Program::decode(program.encode_to_vec().as_slice()).unwrap();
        assert_eq!(decoded, program);
        let response = run(&mut engine, id, decoded);
        assert_eq!(response.error, None);
        let Some(pb::command_output::Kind::Extraction(result)) = &response.outputs[0].kind else {
            panic!("extraction")
        };
        let root = result.roots[0].variants[0].term;
        let node = &response.nodes[root as usize];
        let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Map(map)),
        })) = &node.kind
        else {
            panic!("MapValue, not symbolic Call")
        };
        assert_eq!(map.entries.len(), 2);
        let mut observed = map
            .entries
            .iter()
            .map(|entry| {
                (
                    value(&response, entry.key.unwrap()),
                    value(&response, entry.value.unwrap()),
                )
            })
            .collect::<Vec<_>>();
        observed.sort();
        assert_eq!(
            observed,
            [
                ("1".into(), "\"last\"".into()),
                ("2".into(), "\"x\"".into())
            ]
        );
        let Some(pb::sort::Kind::Family(family)) = &response.sorts[node.sort_id as usize].kind
        else {
            panic!("Map sort")
        };
        assert_eq!(family.name, "Map");
        for entry in &map.entries {
            assert_eq!(
                response.nodes[entry.key.unwrap() as usize].sort_id,
                family.args[0]
            );
            assert_eq!(
                response.nodes[entry.value.unwrap() as usize].sort_id,
                family.args[1]
            );
        }
        native
            .parse_and_run_program(None, &renderer.render(&program).unwrap())
            .unwrap();
        program = pb::Program {
            ir_version: 1,
            sorts: response.sorts,
            nodes: response.nodes,
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Extract(pb::Extract {
                    roots: vec![root],
                    variants: 1,
                    extractor: pb::Extractor::Tree.into(),
                    ..Default::default()
                })),
                ..Default::default()
            }],
            ..Default::default()
        };
    }
    let mut empty = map_fixture();
    let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
        value: Some(pb::primitive_value::Value::Map(map)),
    })) = &mut empty.nodes[2].kind
    else {
        unreachable!()
    };
    map.entries.clear();
    let response = run(&mut engine, id, empty.clone());
    assert_eq!(response.error, None);
    assert!(response.nodes.iter().any(|n| matches!(&n.kind,
        Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Map(map)),
        })) if map.entries.is_empty())));
    native
        .parse_and_run_program(None, &renderer.render(&empty).unwrap())
        .unwrap();
}

#[test]
fn map_flat_and_computed_source_calls_execute_through_bytes() {
    use egglog_experimental::protobuf::source::{Renderer, Source};
    let text = r#"
        (sort M (Map i64 String))
        (function m () M :merge new)
        (set (m) (map-of 1 "first" 2 "two" 1 "last"))
        (check (= (map-get (m) 1) "last"))
        (sort P (Pair i64 String)) (sort V (Vec P))
        (function entries () V :merge new)
        (set (entries) (vec-of (pair 3 "three")))
        (set (m) (map-from-pairs (entries)))
        (check (= (map-get (m) 3) "three"))
        (set (m) (map-insert (m) 3 "updated"))
        (check (= (map-get (m) 3) "updated"))
        (set (m) (map-of))
        (check (= (m) (map-empty)))
    "#;
    new_experimental_egraph()
        .parse_and_run_program(None, text)
        .unwrap();
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut renderer = Renderer::default();
    let mut native = new_experimental_egraph();
    let mut final_arena_map_calls = 0;
    for phase in Source::new(None, text).unwrap() {
        let program = pb::Program::decode(phase.unwrap().encode_to_vec().as_slice()).unwrap();
        // Source retains a cumulative node arena, so count only the latest
        // arena rather than interpreting indices across different Programs.
        final_arena_map_calls = 0;
        for node in &program.nodes {
            if let Some(pb::node::Kind::Call(call)) = &node.kind {
                assert!(!matches!(call.func.as_str(), "map-of" | "map-from-pairs"));
                if call.func == "egglog.core.map.of" {
                    assert_eq!(call.args.len(), 1);
                    final_arena_map_calls += 1;
                }
            }
        }
        assert_eq!(run(&mut engine, id, program.clone()).error, None);
        native
            .parse_and_run_program(None, &renderer.render(&program).unwrap())
            .unwrap();
    }
    assert_eq!(final_arena_map_calls, 3);
}

#[test]
fn unused_map_payloads_reject_before_earlier_writes_and_zero_refs_are_values() {
    use egglog_experimental::protobuf::source::{Renderer, Source};
    let phases = Source::new(
        None,
        "(function observed () i64 :merge new) (set (observed) 0) (check (= (observed) 0))",
    )
    .unwrap()
    .collect::<Result<Vec<_>, _>>()
    .unwrap();
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut renderer = Renderer::default();
    for p in &phases[..2] {
        assert_eq!(run(&mut engine, id, p.clone()).error, None);
        renderer.render(p).unwrap();
    }
    for bad in 0..20 {
        let mut invalid = map_fixture();
        // The entire Map is unused, including its first overwritten entry.
        invalid.commands = vec![pb::Command {
            kind: Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Set(pb::Set {
                    target: Some(pb::Call {
                        func: "observed".into(),
                        args: vec![],
                    }),
                    value: Some(0),
                })),
                ..Default::default()
            })),
            ..Default::default()
        }];
        match bad {
            0..=5 => {
                let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Map(map)),
                })) = &mut invalid.nodes[2].kind
                else {
                    unreachable!()
                };
                match bad {
                    0 => map.entries[0].key = None,
                    1 => map.entries[0].value = None,
                    2 => map.entries[0].key = Some(999),
                    3 => map.entries[0].value = Some(999),
                    4 => map.entries[0].key = Some(1),
                    _ => map.entries[0].value = Some(0),
                }
            }
            6 => invalid.nodes[2].sort_id = 0,
            7..=9 => {
                let Some(pb::sort::Kind::Family(f)) = &mut invalid.sorts[2].kind else {
                    unreachable!()
                };
                match bad {
                    7 => {
                        f.args.pop();
                    }
                    8 => f.args.reverse(),
                    _ => f.args[0] = 2,
                }
            }
            10 => {
                invalid.nodes[0].kind = Some(pb::node::Kind::Call(pb::Call {
                    func: "egglog.core.i64.add".into(),
                    args: vec![0, 0],
                }))
            }
            11 => {
                invalid.nodes[1].kind = Some(pb::node::Kind::Union(pb::Union {
                    members: vec![1, 1],
                }))
            }
            12 => {
                let Some(pb::declaration::Kind::HostSortFamily(f)) =
                    &mut invalid.declarations[0].kind
                else {
                    unreachable!()
                };
                f.arity = 1;
            }
            13 | 14 => {
                invalid.nodes[2].kind = Some(pb::node::Kind::Call(pb::Call {
                    func: if bad == 13 {
                        "map-of"
                    } else {
                        "egglog.core.map.of"
                    }
                    .into(),
                    args: vec![0, 1],
                }))
            }
            15 => invalid.sorts[2].kind = Some(pb::sort::Kind::Eq("Map".into())),
            _ => {
                new_experimental_egraph()
                    .type_info()
                    .export_builtin_definition("egglog.core.map.of", &mut invalid)
                    .unwrap();
                let declaration = invalid.declarations.last_mut().unwrap();
                let Some(pb::declaration::Kind::HostPrimitive(p)) = &mut declaration.kind else {
                    unreachable!()
                };
                let Some(pb::host_primitive::Typing::Signature(s)) = &mut p.typing else {
                    unreachable!()
                };
                match bad {
                    16 => s.inputs[0].sort = s.output.unwrap(),
                    17 => s.output = Some(s.inputs[0].sort),
                    18 => {
                        s.type_params.pop();
                    }
                    _ => {
                        declaration
                            .bindings
                            .as_mut()
                            .unwrap()
                            .python
                            .as_mut()
                            .unwrap()
                            .views[0]
                            .owner = Some(pb::BindingOwner {
                            kind: Some(pb::binding_owner::Kind::Sort(s.inputs[0].sort)),
                        });
                    }
                }
            }
        }
        let response = run(&mut engine, id, invalid.clone());
        assert_eq!(
            response.error.unwrap().code,
            pb::ErrorCode::InvalidProgram as i32,
            "bad {bad}"
        );
        assert!(response.outputs.is_empty());
        assert!(renderer.render(&invalid).is_err(), "bad {bad}");
        assert_eq!(run(&mut engine, id, phases[2].clone()).error, None);
    }
    let mut zero = map_fixture();
    let Some(pb::sort::Kind::Family(f)) = &mut zero.sorts[2].kind else {
        unreachable!()
    };
    f.args = vec![0, 0];
    zero.nodes[2].kind = Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
        value: Some(pb::primitive_value::Value::Map(pb::MapValue {
            entries: vec![pb::MapEntry {
                key: Some(0),
                value: Some(0),
            }],
        })),
    }));
    let decoded = pb::Program::decode(zero.encode_to_vec().as_slice()).unwrap();
    assert_eq!(decoded, zero);
    let response = run(&mut engine, id, decoded);
    assert_eq!(response.error, None);
    let Some(pb::command_output::Kind::Extraction(e)) = &response.outputs[0].kind else {
        unreachable!()
    };
    let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
        value: Some(pb::primitive_value::Value::Map(map)),
    })) = &response.nodes[e.roots[0].variants[0].term as usize].kind
    else {
        unreachable!()
    };
    assert_eq!(
        map.entries[0].key, map.entries[0].value,
        "typed term cache preserves repeated child"
    );
}

#[test]
fn nested_map_source_keeps_nominal_and_same_head_user_provenance() {
    use egglog_experimental::protobuf::source::{Renderer, Source};
    let text = r#"
        (sort Map) (constructor Key () Map)
        (sort M (Map Map i64)) (sort P (Pair M M)) (sort V (Vec P))
        (function stored () V :merge new)
        (set (stored) (vec-of (pair (map-of (Key) 7) (map-of (Key) 7))))
        (extract (stored))
    "#;
    new_experimental_egraph()
        .parse_and_run_program(None, text)
        .unwrap();
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut renderer = Renderer::default();
    let mut native = new_experimental_egraph();
    let mut map_data = false;
    let mut user_call = false;
    let mut table_data = false;
    let mut observation = pb::Program::default();
    for phase in Source::new(None, text).unwrap() {
        let program = phase.unwrap();
        observation = program.clone();
        let response = run(&mut engine, id, program.clone());
        assert_eq!(response.error, None);
        native
            .parse_and_run_program(None, &renderer.render(&program).unwrap())
            .unwrap();
        for (index, node) in response.nodes.iter().enumerate() {
            match &node.kind {
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Map(map)),
                })) => {
                    let Some(pb::sort::Kind::Family(f)) =
                        &response.sorts[node.sort_id as usize].kind
                    else {
                        unreachable!()
                    };
                    assert_eq!(f.name, "Map");
                    assert_eq!(
                        response.sorts[f.args[0] as usize].kind,
                        Some(pb::sort::Kind::Eq("Map".into()))
                    );
                    assert_eq!(value(&response, map.entries[0].key.unwrap()), "(Key)");
                    map_data = true;
                }
                Some(pb::node::Kind::Call(call)) if call.func == "map-of" => {
                    assert_eq!(
                        response.sorts[node.sort_id as usize].kind,
                        Some(pb::sort::Kind::Eq("Map".into()))
                    );
                    user_call = true;
                }
                _ => continue,
            }
            let reingest = pb::Program {
                ir_version: 1,
                sorts: response.sorts.clone(),
                nodes: response.nodes.clone(),
                commands: vec![pb::Command {
                    kind: Some(pb::command::Kind::Extract(pb::Extract {
                        roots: vec![index as u32],
                        variants: 1,
                        extractor: pb::Extractor::Tree.into(),
                        ..Default::default()
                    })),
                    ..Default::default()
                }],
                ..Default::default()
            };
            assert_eq!(run(&mut engine, id, reingest.clone()).error, None);
            native
                .parse_and_run_program(None, &renderer.render(&reingest).unwrap())
                .unwrap();
        }
        table_data |= response
            .outputs
            .iter()
            .any(|o| matches!(o.kind, Some(pb::command_output::Kind::PrintedFunction(_))))
            && response.nodes.iter().any(|n| {
                matches!(
                    n.kind,
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Map(_))
                    }))
                )
            });
    }
    observation.commands = vec![pb::Command {
        kind: Some(pb::command::Kind::PrintFunction(pb::PrintFunction {
            table: "stored".into(),
            max_rows: 10,
        })),
        ..Default::default()
    }];
    let table = run(&mut engine, id, observation.clone());
    assert_eq!(table.error, None);
    table_data |= table.nodes.iter().any(|n| {
        matches!(
            n.kind,
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Map(_))
            }))
        )
    });
    native
        .parse_and_run_program(None, &renderer.render(&observation).unwrap())
        .unwrap();
    // Native registration reserves its alias; the wire namespace projection
    // still admits a distinct authored constructor with the same spelling.
    for spelling in ["map-of", "map-from-pairs"] {
        let mut user = map_fixture();
        user.sorts.push(pb::Sort {
            kind: Some(pb::sort::Kind::Eq("Map".into())),
            ..Default::default()
        });
        user.declarations.push(pb::Declaration {
            kind: Some(pb::declaration::Kind::Constructor(pb::Constructor {
                name: spelling.into(),
                inputs: vec![pb::Arg {
                    name: "n".into(),
                    sort: 0,
                }],
                output: 3,
                ..Default::default()
            })),
            ..Default::default()
        });
        user.nodes.push(pb::Node {
            sort_id: 3,
            kind: Some(pb::node::Kind::Call(pb::Call {
                func: spelling.into(),
                args: vec![0],
            })),
            ..Default::default()
        });
        let Some(pb::command::Kind::Extract(e)) = &mut user.commands[0].kind else {
            unreachable!()
        };
        e.roots.push(5);
        let response = run(&mut engine, id, user.clone());
        assert_eq!(response.error, None);
        let Some(pb::command_output::Kind::Extraction(e)) = &response.outputs[0].kind else {
            unreachable!()
        };
        let node = &response.nodes[e.roots[1].variants[0].term as usize];
        assert!(matches!(&node.kind, Some(pb::node::Kind::Call(c)) if c.func == spelling));
        assert_eq!(
            response.sorts[node.sort_id as usize].kind,
            Some(pb::sort::Kind::Eq("Map".into()))
        );
        native
            .parse_and_run_program(None, &renderer.render(&user).unwrap())
            .unwrap();
        user_call = true;
    }
    assert!(map_data && user_call && table_data);
}

#[test]
fn pair_value_bytes_extract_reingest_and_render() {
    use egglog_experimental::protobuf::source::Renderer;
    let mut program = pair_fixture();
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut renderer = Renderer::default();
    let mut native = new_experimental_egraph();
    for _ in 0..2 {
        // Reattach the authoritative views to both authored and returned arenas.
        // The second pass exercises signature/owner relocation around result sorts.
        for key in ["make", "first", "second"] {
            native
                .type_info()
                .export_builtin_definition(&format!("egglog.core.pair.{key}"), &mut program)
                .unwrap();
        }
        let decoded = pb::Program::decode(program.encode_to_vec().as_slice()).unwrap();
        assert_eq!(decoded, program);
        let response = run(&mut engine, id, decoded);
        assert_eq!(response.error, None);
        let Some(pb::command_output::Kind::Extraction(result)) = &response.outputs[0].kind else {
            panic!("extraction")
        };
        let root = result.roots[0].variants[0].term;
        let node = &response.nodes[root as usize];
        let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Pair(pair)),
        })) = &node.kind
        else {
            panic!("PairValue, not a symbolic Call")
        };
        let Some(pb::sort::Kind::Family(family)) = &response.sorts[node.sort_id as usize].kind
        else {
            panic!("Pair family")
        };
        assert_eq!(family.name, "Pair");
        assert_eq!(family.args.len(), 2);
        assert_eq!(
            response.nodes[pair.first.unwrap() as usize].sort_id,
            family.args[0]
        );
        assert_eq!(
            response.nodes[pair.second.unwrap() as usize].sort_id,
            family.args[1]
        );
        assert_eq!(value(&response, root), "(pair 1 \"x\")");
        native
            .parse_and_run_program(None, &renderer.render(&program).unwrap())
            .unwrap();
        program = pb::Program {
            ir_version: 1,
            sorts: response.sorts,
            nodes: response.nodes,
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Extract(pb::Extract {
                    roots: vec![root],
                    variants: 1,
                    extractor: pb::Extractor::Tree.into(),
                    ..Default::default()
                })),
                ..Default::default()
            }],
            ..Default::default()
        };
    }
}

#[test]
fn pair_source_calls_execute_through_bytes() {
    use egglog_experimental::protobuf::source::{Renderer, Source};
    let text = r#"
        (sort P (Pair i64 String)) (sort Q (Pair i64 String)) (sort R (Pair String i64))
        (function p () P :merge new) (function q () Q :merge new) (function r () R :merge new)
        (set (p) (pair 1 "x"))
        (set (q) (pair 2 "y")) (set (r) (pair "z" 3))
        (check (= (pair-first (p)) 1) (= (pair-second (p)) "x"))
        (check (= (pair-first (q)) 2) (= (pair-second (r)) 3))
        (extract (pair-first (p))) (extract (pair-second (p))) (extract (p))
    "#;
    new_experimental_egraph()
        .parse_and_run_program(None, text)
        .unwrap();
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut renderer = Renderer::default();
    let mut native = new_experimental_egraph();
    let mut keys = std::collections::BTreeSet::new();
    let mut results = vec![];
    for phase in Source::new(None, text).unwrap() {
        let program = pb::Program::decode(phase.unwrap().encode_to_vec().as_slice()).unwrap();
        for declaration in &program.declarations {
            if let Some(pb::declaration::Kind::HostPrimitive(p)) = &declaration.kind
                && p.name.starts_with("egglog.core.pair.")
            {
                let bindings = declaration.bindings.as_ref().unwrap();
                assert!(bindings.python.is_some() && bindings.rust.is_some());
                let mut expected = program.clone();
                native
                    .type_info()
                    .export_builtin_definition(&p.name, &mut expected)
                    .unwrap();
                assert_eq!(program, expected, "source must retain exact native views");
            }
        }
        for node in &program.nodes {
            if let Some(pb::node::Kind::Call(call)) = &node.kind {
                assert!(!matches!(
                    call.func.as_str(),
                    "pair" | "pair-first" | "pair-second"
                ));
                if call.func.starts_with("egglog.core.pair.") {
                    keys.insert(call.func.clone());
                }
            }
        }
        let response = run(&mut engine, id, program.clone());
        assert_eq!(response.error, None);
        native
            .parse_and_run_program(None, &renderer.render(&program).unwrap())
            .unwrap();
        for output in &response.outputs {
            if let Some(pb::command_output::Kind::Extraction(result)) = &output.kind {
                results.push(value(&response, result.roots[0].variants[0].term));
            }
        }
    }
    assert_eq!(
        keys.into_iter().collect::<Vec<_>>(),
        [
            "egglog.core.pair.first",
            "egglog.core.pair.make",
            "egglog.core.pair.second"
        ]
    );
    assert_eq!(results, ["1", "\"x\"", "(pair 1 \"x\")"]);
}

#[test]
fn pair_presentations_resupply_and_clone_freeze_before_writes() {
    use egglog_experimental::protobuf::source::Renderer;
    let mut provider = new_experimental_egraph();
    let mut program = constant_fixture(&["test", "CURRENT"], &["test", "EMPTY"]);
    for key in ["make", "first", "second"] {
        provider
            .type_info()
            .export_builtin_definition(&format!("egglog.core.pair.{key}"), &mut program)
            .unwrap();
    }
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut renderer = Renderer::default();
    for _ in 0..2 {
        assert_eq!(run(&mut engine, id, program.clone()).error, None);
        provider
            .parse_and_run_program(None, &renderer.render(&program).unwrap())
            .unwrap();
    }
    let clone = pb::CloneEGraphResponse::decode(
        engine
            .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
            .unwrap()
            .as_slice(),
    )
    .unwrap()
    .egraph_id;
    for conflict in 0..4 {
        let mut changed = program.clone();
        changed.commands.truncate(1); // Would change current=20 back to10.
        for declaration in &mut changed.declarations {
            if conflict < 2 {
                if let Some(pb::declaration::Kind::HostSortFamily(f)) = &mut declaration.kind
                    && f.name == "Pair"
                {
                    let b = f.bindings.as_mut().unwrap();
                    let binding = if conflict == 0 {
                        &mut b.python
                    } else {
                        &mut b.rust
                    };
                    *binding.as_mut().unwrap().path.last_mut().unwrap() = "OtherPair".into();
                }
            } else if matches!(&declaration.kind, Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.core.pair.first")
            {
                let b = declaration.bindings.as_mut().unwrap();
                if conflict == 2 {
                    b.python.as_mut().unwrap().views[0].path[0] = "other_left".into();
                } else {
                    b.rust.as_mut().unwrap().views[0]
                        .receiver
                        .as_mut()
                        .unwrap()
                        .borrowed = false;
                }
            }
        }
        assert!(renderer.render(&changed).is_err());
        for handle in [id, clone] {
            let response = run(&mut engine, handle, changed.clone());
            assert_eq!(
                response.error.unwrap().code,
                pb::ErrorCode::InvalidProgram as i32
            );
            assert!(response.outputs.is_empty());
        }
    }
    program.declarations.clear();
    program.commands = vec![program.commands.last().unwrap().clone()];
    for handle in [id, clone] {
        let response = run(&mut engine, handle, program.clone());
        assert_eq!(response.error, None);
        let Some(pb::command_output::Kind::Extraction(extraction)) = &response.outputs[0].kind
        else {
            unreachable!()
        };
        assert_eq!(value(&response, extraction.roots[0].variants[0].term), "20");
    }
}

#[test]
fn pair_invalid_payloads_and_annotations_reject_before_mutation() {
    use egglog_experimental::protobuf::source::{Renderer, Source};
    let phases = Source::new(
        None,
        "(function observed () i64 :merge new) (set (observed) 0) (check (= (observed) 0))",
    )
    .unwrap()
    .collect::<Result<Vec<_>, _>>()
    .unwrap();
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut renderer = Renderer::default();
    for program in &phases[..2] {
        assert_eq!(run(&mut engine, id, program.clone()).error, None);
        renderer.render(program).unwrap();
    }
    for bad in 0..14 {
        let mut invalid = pair_fixture();
        invalid.commands.insert(
            0,
            pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Set(pb::Set {
                        target: Some(pb::Call {
                            func: "observed".into(),
                            args: vec![],
                        }),
                        value: Some(0),
                    })),
                    ..Default::default()
                })),
                ..Default::default()
            },
        );
        match bad {
            0..=3 => {
                let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Pair(pair)),
                })) = &mut invalid.nodes[2].kind
                else {
                    unreachable!()
                };
                match bad {
                    0 => pair.first = None,
                    1 => pair.second = None,
                    2 => pair.first = Some(999),
                    _ => std::mem::swap(&mut pair.first, &mut pair.second),
                }
            }
            4 => invalid.nodes[2].sort_id = 0,
            5 | 6 | 12 => {
                let Some(pb::sort::Kind::Family(f)) = &mut invalid.sorts[2].kind else {
                    unreachable!()
                };
                match bad {
                    5 => {
                        f.args.pop();
                    }
                    6 => f.args.reverse(),
                    _ => f.args[0] = 2,
                }
            }
            7 => {
                invalid.nodes[0].kind = Some(pb::node::Kind::Call(pb::Call {
                    func: "egglog.core.i64.add".into(),
                    args: vec![0, 0],
                }))
            }
            8 => {
                let mut unused = invalid.nodes[2].clone();
                let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Pair(pair)),
                })) = &mut unused.kind
                else {
                    unreachable!()
                };
                pair.second = Some(999);
                invalid.nodes.push(unused);
            }
            9..=11 => {
                invalid.nodes[2].kind = Some(pb::node::Kind::Call(pb::Call {
                    func: match bad {
                        9 => "egglog.core.pair.missing",
                        10 => "pair",
                        _ => "egglog.core.pair.make",
                    }
                    .into(),
                    args: if bad == 11 { vec![1, 0] } else { vec![0, 1] },
                }))
            }
            _ => invalid.nodes[0].kind = Some(pb::node::Kind::Var("unbound".into())),
        }
        assert!(
            run(&mut engine, id, invalid.clone()).error.is_some(),
            "bad {bad}"
        );
        assert!(renderer.render(&invalid).is_err(), "render bad {bad}");
        assert_eq!(
            run(&mut engine, id, phases[2].clone()).error,
            None,
            "mutation after bad {bad}"
        );
    }
    assert!(engine.run(&[0xff]).is_err());
    assert_eq!(run(&mut engine, id, phases[2].clone()).error, None);
    assert_eq!(run(&mut engine, id, pair_fixture()).error, None);
    renderer.render(&pair_fixture()).unwrap();
}

#[test]
fn pair_nested_values_rebuild_and_keep_user_constructor_provenance() {
    use egglog_experimental::protobuf::source::{Renderer, Source};
    let text = r#"
        (datatype N (A) (B))
        (sort P (Pair N i64)) (sort V (Vec P)) (sort Nested (Pair P V))
        (function p () P :merge new) (function n () Nested :merge new)
        (set (p) (pair (A) 7)) (set (n) (pair (p) (vec-of (p))))
        (rewrite (A) (B)) (run 1)
        (check (= (pair-first (p)) (B)))
        (check (= (pair-second (vec-get (pair-second (n)) 0)) 7))
        (extract (n))
    "#;
    new_experimental_egraph()
        .parse_and_run_program(None, text)
        .unwrap();
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut renderer = Renderer::default();
    let mut native = new_experimental_egraph();
    let mut observation = pb::Program::default();
    for phase in Source::new(None, text).unwrap() {
        let program = pb::Program::decode(phase.unwrap().encode_to_vec().as_slice()).unwrap();
        let response = run(&mut engine, id, program.clone());
        assert_eq!(response.error, None);
        native
            .parse_and_run_program(None, &renderer.render(&program).unwrap())
            .unwrap();
        if let Some(pb::command_output::Kind::Extraction(result)) =
            response.outputs.first().and_then(|o| o.kind.as_ref())
        {
            let root = result.roots[0].variants[0].term;
            assert!(
                response
                    .sorts
                    .iter()
                    .any(|s| matches!(&s.kind, Some(pb::sort::Kind::Eq(name)) if name == "N"))
            );
            let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Pair(pair)),
            })) = &response.nodes[root as usize].kind
            else {
                panic!("nested Pair")
            };
            let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Vec(vec)),
            })) = &response.nodes[pair.second.unwrap() as usize].kind
            else {
                panic!("nested Vec")
            };
            assert_eq!(
                pair.first,
                Some(vec.items[0]),
                "typed term cache preserves shared children"
            );
            observation = program;
        }
    }
    observation.commands = vec![pb::Command {
        kind: Some(pb::command::Kind::PrintFunction(pb::PrintFunction {
            table: "n".into(),
            max_rows: 10,
        })),
        ..Default::default()
    }];
    let table = run(&mut engine, id, observation.clone());
    assert_eq!(table.error, None);
    assert!(matches!(
        table.outputs[0].kind,
        Some(pb::command_output::Kind::PrintedFunction(_))
    ));
    assert!(table.nodes.iter().any(|n| matches!(
        &n.kind,
        Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Pair(_))
        }))
    )));
    native
        .parse_and_run_program(None, &renderer.render(&observation).unwrap())
        .unwrap();

    let mut user = pair_fixture();
    user.sorts.push(pb::Sort {
        kind: Some(pb::sort::Kind::Eq("Pair".into())),
        ..Default::default()
    });
    user.declarations.extend([
        pb::Declaration {
            kind: Some(pb::declaration::Kind::EqSort(pb::EqSort {
                name: "Pair".into(),
                bindings: None,
            })),
            ..Default::default()
        },
        pb::Declaration {
            kind: Some(pb::declaration::Kind::Constructor(pb::Constructor {
                name: "pair".into(),
                inputs: vec![
                    pb::Arg {
                        name: "first".into(),
                        sort: 0,
                    },
                    pb::Arg {
                        name: "second".into(),
                        sort: 1,
                    },
                ],
                output: 3,
                ..Default::default()
            })),
            ..Default::default()
        },
    ]);
    user.nodes.push(pb::Node {
        sort_id: 3,
        kind: Some(pb::node::Kind::Call(pb::Call {
            func: "pair".into(),
            args: vec![0, 1],
        })),
        ..Default::default()
    });
    let Some(pb::command::Kind::Extract(e)) = &mut user.commands[0].kind else {
        unreachable!()
    };
    e.roots.push(3);
    let response = run(&mut engine, id, user.clone());
    assert_eq!(response.error, None);
    let Some(pb::command_output::Kind::Extraction(e)) = &response.outputs[0].kind else {
        panic!("extraction")
    };
    assert!(
        matches!(&response.nodes[e.roots[1].variants[0].term as usize].kind, Some(pb::node::Kind::Call(c)) if c.func == "pair")
    );
    assert_eq!(
        response.sorts[response.nodes[e.roots[1].variants[0].term as usize].sort_id as usize].kind,
        Some(pb::sort::Kind::Eq("Pair".into()))
    );
    native
        .parse_and_run_program(None, &renderer.render(&user).unwrap())
        .unwrap();
}

#[test]
fn nominal_pair_source_preserves_names_through_bytes_and_rendering() {
    use egglog_experimental::protobuf::source::{Renderer, Source};
    let text = r#"
        (sort Pair) (constructor P () Pair)
        (sort Real (Pair Pair i64))
        (function stored () Real :merge new)
        (set (stored) (pair (P) 7))
        (check (= (pair-first (stored)) (P)) (= (pair-second (stored)) 7))
        (extract (P)) (extract (stored))
    "#;
    new_experimental_egraph()
        .parse_and_run_program(None, text)
        .unwrap();
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut renderer = Renderer::default();
    let mut reparsed = new_experimental_egraph();
    let mut values = vec![];
    let mut nominal_declared = false;
    for phase in Source::new(None, text).unwrap() {
        let program = pb::Program::decode(phase.unwrap().encode_to_vec().as_slice()).unwrap();
        nominal_declared |= program.declarations.iter().any(|d| {
            matches!(
            &d.kind, Some(pb::declaration::Kind::EqSort(s)) if s.name == "Pair")
        });
        let response = run(&mut engine, id, program.clone());
        assert_eq!(response.error, None);
        reparsed
            .parse_and_run_program(None, &renderer.render(&program).unwrap())
            .unwrap();
        for output in &response.outputs {
            if let Some(pb::command_output::Kind::Extraction(e)) = &output.kind {
                let root = e.roots[0].variants[0].term;
                values.push(value(&response, root));
                assert!(
                    response
                        .sorts
                        .iter()
                        .any(|s| s.kind == Some(pb::sort::Kind::Eq("Pair".into())))
                );
                if let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Pair(pair)),
                })) = &response.nodes[root as usize].kind
                {
                    let Some(pb::sort::Kind::Family(f)) =
                        &response.sorts[response.nodes[root as usize].sort_id as usize].kind
                    else {
                        unreachable!()
                    };
                    assert_eq!(f.name, "Pair");
                    assert_eq!(
                        response.sorts[f.args[0] as usize].kind,
                        Some(pb::sort::Kind::Eq("Pair".into()))
                    );
                    assert!(
                        matches!(&response.nodes[pair.first.unwrap() as usize].kind, Some(pb::node::Kind::Call(c)) if c.func == "P")
                    );
                }
                let reingest = pb::Program {
                    ir_version: 1,
                    sorts: response.sorts.clone(),
                    nodes: response.nodes.clone(),
                    commands: vec![pb::Command {
                        kind: Some(pb::command::Kind::Extract(pb::Extract {
                            roots: vec![root],
                            variants: 1,
                            extractor: pb::Extractor::Tree.into(),
                            ..Default::default()
                        })),
                        ..Default::default()
                    }],
                    ..Default::default()
                };
                assert_eq!(run(&mut engine, id, reingest.clone()).error, None);
                reparsed
                    .parse_and_run_program(None, &renderer.render(&reingest).unwrap())
                    .unwrap();
            }
        }
    }
    assert!(nominal_declared);
    assert_eq!(values, ["(P)", "(pair (P) 7)"]);
}

fn nominal_pair_fixture() -> pb::Program {
    let mut p = pair_fixture();
    p.sorts[1].kind = Some(pb::sort::Kind::Eq("Pair".into()));
    let Some(pb::sort::Kind::Family(f)) = &mut p.sorts[2].kind else {
        unreachable!()
    };
    f.args = vec![1, 0];
    p.declarations.extend([
        pb::Declaration {
            kind: Some(pb::declaration::Kind::EqSort(pb::EqSort {
                name: "Pair".into(),
                bindings: Some(pb::SortBindings {
                    python: Some(pb::TypeBinding {
                        path: vec!["test".into(), "NominalPair".into()],
                        ..Default::default()
                    }),
                    ..Default::default()
                }),
            })),
            ..Default::default()
        },
        pb::Declaration {
            kind: Some(pb::declaration::Kind::Constructor(pb::Constructor {
                name: "Pair".into(),
                output: 1,
                ..Default::default()
            })),
            ..Default::default()
        },
        pb::Declaration {
            kind: Some(pb::declaration::Kind::Function(pb::Function {
                name: "stored".into(),
                output: 2,
                merge: Some(3),
                ..Default::default()
            })),
            ..Default::default()
        },
    ]);
    p.nodes[1].kind = Some(pb::node::Kind::Call(pb::Call {
        func: "Pair".into(),
        args: vec![],
    }));
    p.nodes[2].kind = Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
        value: Some(pb::primitive_value::Value::Pair(pb::PairValue {
            first: Some(1),
            second: Some(0),
        })),
    }));
    p.nodes.extend([
        pb::Node {
            sort_id: 2,
            kind: Some(pb::node::Kind::Var("new".into())),
            ..Default::default()
        },
        pb::Node {
            sort_id: 2,
            kind: Some(pb::node::Kind::Call(pb::Call {
                func: "stored".into(),
                args: vec![],
            })),
            ..Default::default()
        },
    ]);
    let Some(pb::command::Kind::Extract(e)) = &mut p.commands[0].kind else {
        unreachable!()
    };
    e.roots = vec![1, 4];
    p.commands.insert(
        0,
        pb::Command {
            kind: Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Set(pb::Set {
                    target: Some(pb::Call {
                        func: "stored".into(),
                        args: vec![],
                    }),
                    value: Some(2),
                })),
                ..Default::default()
            })),
            ..Default::default()
        },
    );
    p.commands.push(pb::Command {
        kind: Some(pb::command::Kind::PrintFunction(pb::PrintFunction {
            table: "stored".into(),
            max_rows: 10,
        })),
        ..Default::default()
    });
    p
}

#[test]
fn nominal_pair_resupply_orders_clone_conflicts_and_prefixes() {
    use egglog_experimental::protobuf::source::Renderer;
    for explicit in [false, true] {
        for reverse in [false, true] {
            let mut program = nominal_pair_fixture();
            if !explicit {
                program.declarations.remove(0);
            }
            if reverse {
                program.declarations.reverse();
                let Some(pb::command::Kind::Extract(e)) = &mut program.commands[1].kind else {
                    unreachable!()
                };
                e.roots.reverse();
            }
            let mut engine = Engine::default();
            let id = create(&mut engine);
            let mut renderer = Renderer::default();
            let mut reparsed = new_experimental_egraph();
            // Exercise both incremental sort arrival orders, then complete
            // resupply; ambient family availability never supplies the EqSort.
            for d in program.declarations.iter().filter(|d| {
                matches!(
                    d.kind,
                    Some(
                        pb::declaration::Kind::EqSort(_) | pb::declaration::Kind::HostSortFamily(_)
                    )
                )
            }) {
                let phase = pb::Program {
                    ir_version: 1,
                    declarations: vec![d.clone()],
                    ..Default::default()
                };
                assert_eq!(run(&mut engine, id, phase.clone()).error, None);
                reparsed
                    .parse_and_run_program(None, &renderer.render(&phase).unwrap())
                    .unwrap();
            }
            for _ in 0..2 {
                let response = run(&mut engine, id, program.clone());
                assert_eq!(response.error, None);
                let Some(pb::command_output::Kind::Extraction(e)) = &response.outputs[0].kind
                else {
                    unreachable!()
                };
                let expected = if reverse {
                    ["(pair (Pair) 1)", "(Pair)"]
                } else {
                    ["(Pair)", "(pair (Pair) 1)"]
                };
                assert_eq!(
                    e.roots
                        .iter()
                        .map(|r| value(&response, r.variants[0].term))
                        .collect::<Vec<_>>(),
                    expected
                );
                let Some(pb::command_output::Kind::PrintedFunction(table)) =
                    &response.outputs[1].kind
                else {
                    unreachable!()
                };
                assert_eq!(table.table, "stored");
                assert_eq!(table.rows.len(), 1);
                assert_eq!(value(&response, table.rows[0].output), "(pair (Pair) 1)");
                reparsed
                    .parse_and_run_program(None, &renderer.render(&program).unwrap())
                    .unwrap();
            }
            let clone = pb::CloneEGraphResponse::decode(
                engine
                    .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
                    .unwrap()
                    .as_slice(),
            )
            .unwrap()
            .egraph_id;
            let mut observation = program.clone();
            observation.commands.remove(0);
            for bad in 0..4 {
                let mut conflict = nominal_pair_fixture();
                conflict.nodes[0].kind = Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::I64(99)),
                }));
                match bad {
                    0 => {
                        let Some(pb::declaration::Kind::HostSortFamily(f)) =
                            &mut conflict.declarations[0].kind
                        else {
                            unreachable!()
                        };
                        f.arity = 1;
                    }
                    1 => {
                        let Some(pb::declaration::Kind::EqSort(eq)) =
                            &mut conflict.declarations[1].kind
                        else {
                            unreachable!()
                        };
                        eq.bindings.as_mut().unwrap().python.as_mut().unwrap().path[1] =
                            "Changed".into();
                    }
                    2 => {
                        let Some(pb::declaration::Kind::Constructor(c)) =
                            &mut conflict.declarations[2].kind
                        else {
                            unreachable!()
                        };
                        c.unextractable = true;
                    }
                    _ => {
                        let Some(pb::declaration::Kind::Function(f)) =
                            &mut conflict.declarations[3].kind
                        else {
                            unreachable!()
                        };
                        f.merge = None;
                    }
                }
                assert!(run(&mut engine, id, conflict.clone()).error.is_some());
                assert!(renderer.render(&conflict).is_err());
                let response = run(&mut engine, id, observation.clone());
                assert_eq!(response.error, None);
                let Some(pb::command_output::Kind::PrintedFunction(table)) =
                    &response.outputs[1].kind
                else {
                    unreachable!()
                };
                assert_eq!(value(&response, table.rows[0].output), "(pair (Pair) 1)");
            }
            program.nodes[0].kind = Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::I64(2)),
            }));
            program.commands.insert(
                1,
                pb::Command {
                    kind: Some(pb::command::Kind::Action(pb::Action {
                        kind: Some(pb::action::Kind::Panic("after nominal Pair write".into())),
                        ..Default::default()
                    })),
                    ..Default::default()
                },
            );
            assert_eq!(
                run(&mut engine, id, program).error.unwrap().code,
                pb::ErrorCode::Panic as i32
            );
            for (handle, expected) in [(id, "(pair (Pair) 2)"), (clone, "(pair (Pair) 1)")] {
                let response = run(&mut engine, handle, observation.clone());
                assert_eq!(response.error, None);
                let Some(pb::command_output::Kind::PrintedFunction(table)) =
                    &response.outputs[1].kind
                else {
                    unreachable!()
                };
                assert_eq!(value(&response, table.rows[0].output), expected);
            }
        }
    }
}

#[test]
fn nominal_pair_wrong_kind_names_reject_before_earlier_writes() {
    use egglog_experimental::protobuf::source::{Renderer, Source};
    let phases = Source::new(None,
        "(sort OnlyNominal) (function observed () i64 :merge new) (set (observed) 0) (check (= (observed) 0))")
        .unwrap().collect::<Result<Vec<_>, _>>().unwrap();
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut renderer = Renderer::default();
    for phase in &phases[..3] {
        assert_eq!(run(&mut engine, id, phase.clone()).error, None);
        renderer.render(phase).unwrap();
    }
    for bad in 0..4 {
        let mut invalid = phases[2].clone();
        let literal = invalid
            .nodes
            .iter_mut()
            .find(|n| {
                matches!(
                    n.kind,
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::I64(_))
                    }))
                )
            })
            .unwrap();
        literal.kind = Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::I64(99)),
        }));
        let expected = match bad {
            0 | 1 => {
                invalid.sorts.push(pb::Sort {
                    kind: Some(pb::sort::Kind::Eq(
                        if bad == 0 { "Pair" } else { "i64" }.into(),
                    )),
                    ..Default::default()
                });
                "unknown sort"
            }
            2 => {
                invalid.declarations.push(pb::Declaration {
                    kind: Some(pb::declaration::Kind::HostSortFamily(pb::HostSortFamily {
                        name: "OnlyNominal".into(),
                        arity: 0,
                        bindings: None,
                    })),
                    ..Default::default()
                });
                "unknown host sort family OnlyNominal"
            }
            _ => {
                invalid.sorts.push(pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "OnlyNominal".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                });
                // This family is outside the admitted codec slice; distinguish
                // the unsupported-family gate from the provider lookup above.
                "only equality, scalar, Vec, Pair and Map sorts are supported yet"
            }
        };
        let response = run(&mut engine, id, invalid.clone());
        let error = response.error.unwrap();
        assert_eq!(error.code, pb::ErrorCode::InvalidProgram as i32);
        assert!(
            error.message.contains(expected),
            "bad {bad}: {}",
            error.message
        );
        assert!(response.outputs.is_empty());
        let render_error = renderer.render(&invalid).unwrap_err();
        assert!(render_error.to_string().contains(expected));
        assert_eq!(run(&mut engine, id, phases[3].clone()).error, None);
    }
}

#[test]
fn pair_value_queries_require_grounded_children() {
    use egglog_experimental::protobuf::source::{Renderer, Source};
    let text = r#"
        (sort P (Pair i64 String)) (datatype Box (N i64))
        (function stored () P :no-merge) (function observed () i64 :merge new)
        (set (stored) (pair 7 "x")) (set (observed) 0) (N 7)
        (rule ((N x) (= (stored) (pair x "x"))) ((set (observed) x)))
        (run 1) (check (= (observed) 7))
    "#;
    new_experimental_egraph()
        .parse_and_run_program(None, text)
        .unwrap();
    let observation = Source::new(
        None,
        "(function observed () i64 :merge new) (check (= (observed) 0))",
    )
    .unwrap()
    .last()
    .unwrap()
    .unwrap();
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut renderer = Renderer::default();
    let mut checked_ungrounded = false;
    for phase in Source::new(None, text).unwrap() {
        let mut program = phase.unwrap();
        if !program.rules.is_empty() {
            for node in &mut program.nodes {
                if let Some(pb::node::Kind::Call(call)) = &node.kind
                    && call.func == "egglog.core.pair.make"
                {
                    node.kind = Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Pair(pb::PairValue {
                            first: Some(call.args[0]),
                            second: Some(call.args[1]),
                        })),
                    }));
                }
            }
            if !checked_ungrounded {
                let mut ungrounded = program.clone();
                let Some(pb::rule_decl::Kind::Rule(rule)) = &mut ungrounded.rules[0].kind else {
                    unreachable!()
                };
                assert_eq!(rule.query.len(), 2);
                rule.query.remove(0); // Remove the constructor fact that binds x.
                ungrounded.rulesets = vec![pb::Ruleset {
                    name: Some("pair-grounding-probe".into()),
                    kind: Some(pb::ruleset::Kind::Rules(pb::RuleList { rules: vec![0] })),
                    ..Default::default()
                }];
                let response = run(&mut engine, id, ungrounded.clone());
                assert!(
                    response.error.is_some(),
                    "Pair payload must not inverse-match its child variable"
                );
                assert!(renderer.render(&ungrounded).is_err());
                assert_eq!(run(&mut engine, id, observation.clone()).error, None);
                checked_ungrounded = true;
            }
        }
        assert_eq!(run(&mut engine, id, program.clone()).error, None);
        renderer.render(&program).unwrap();
    }
}

#[test]
fn map_value_queries_require_grounded_children() {
    use egglog_experimental::protobuf::source::{Renderer, Source};
    let text = r#"
        (sort M (Map i64 String)) (datatype Box (N i64))
        (function stored () M :no-merge) (function observed () i64 :merge new)
        (set (stored) (map-of 7 "x")) (set (observed) 0) (N 7)
        (rule ((N x) (= (stored) (map-of x "x"))) ((set (observed) x)))
        (run 1) (check (= (observed) 7))
    "#;
    new_experimental_egraph()
        .parse_and_run_program(None, text)
        .unwrap();
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut renderer = Renderer::default();
    let mut checked_ungrounded = false;
    for phase in Source::new(None, text).unwrap() {
        let mut program = phase.unwrap();
        if !program.rules.is_empty() {
            for index in 0..program.nodes.len() {
                if let Some(pb::node::Kind::Call(call)) = &program.nodes[index].kind
                    && call.func == "egglog.core.map.of"
                {
                    let Some(pb::node::Kind::Call(vector)) =
                        &program.nodes[call.args[0] as usize].kind
                    else {
                        unreachable!()
                    };
                    let entries = vector
                        .args
                        .iter()
                        .map(|pair| {
                            let Some(pb::node::Kind::Call(pair)) =
                                &program.nodes[*pair as usize].kind
                            else {
                                unreachable!()
                            };
                            pb::MapEntry {
                                key: Some(pair.args[0]),
                                value: Some(pair.args[1]),
                            }
                        })
                        .collect();
                    program.nodes[index].kind =
                        Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                            value: Some(pb::primitive_value::Value::Map(pb::MapValue { entries })),
                        }));
                }
            }
            if !checked_ungrounded {
                let mut ungrounded = program.clone();
                let Some(pb::rule_decl::Kind::Rule(rule)) = &mut ungrounded.rules[0].kind else {
                    unreachable!()
                };
                assert_eq!(rule.query.len(), 2);
                rule.query.remove(0);
                ungrounded.rulesets = vec![pb::Ruleset {
                    name: Some("map-grounding-probe".into()),
                    kind: Some(pb::ruleset::Kind::Rules(pb::RuleList { rules: vec![0] })),
                    ..Default::default()
                }];
                assert!(run(&mut engine, id, ungrounded.clone()).error.is_some());
                assert!(renderer.render(&ungrounded).is_err());
                checked_ungrounded = true;
            }
        }
        assert_eq!(run(&mut engine, id, program.clone()).error, None);
        renderer.render(&program).unwrap();
    }
    assert!(checked_ungrounded);
}

#[test]
fn pair_defaults_and_runtime_prefixes_survive_resupply_and_clone() {
    use egglog_experimental::protobuf::source::Renderer;
    let mut program = pair_fixture();
    program.nodes.push(pb::Node {
        sort_id: 2,
        kind: Some(pb::node::Kind::Var("new".into())),
        ..Default::default()
    });
    program.declarations.extend([
        pb::Declaration {
            kind: Some(pb::declaration::Kind::Function(pb::Function {
                name: "stored".into(),
                inputs: vec![],
                output: 2,
                merge: Some(3),
            })),
            ..Default::default()
        },
        pb::Declaration {
            kind: Some(pb::declaration::Kind::Function(pb::Function {
                name: "take_pair".into(),
                inputs: vec![pb::Arg {
                    name: "p".into(),
                    sort: 2,
                }],
                output: 0,
                merge: None,
            })),
            bindings: Some(pb::CallableBindings {
                python: Some(pb::PythonBindings {
                    views: vec![pb::PythonCallable {
                        kind: pb::PythonCallKind::Function.into(),
                        path: vec!["test".into(), "take_pair".into()],
                        params: vec![pb::PythonParameter {
                            core_input: Some(0),
                            name: "p".into(),
                            default_expr: Some(2),
                        }],
                        ..Default::default()
                    }],
                }),
                ..Default::default()
            }),
            ..Default::default()
        },
    ]);
    let write = pb::Command {
        kind: Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Set(pb::Set {
                target: Some(pb::Call {
                    func: "stored".into(),
                    args: vec![],
                }),
                value: Some(2),
            })),
            ..Default::default()
        })),
        ..Default::default()
    };
    program.commands.insert(0, write);
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut renderer = Renderer::default();
    for _ in 0..3 {
        assert_eq!(run(&mut engine, id, program.clone()).error, None);
        renderer.render(&program).unwrap();
    }
    let clone = pb::CloneEGraphResponse::decode(
        engine
            .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
            .unwrap()
            .as_slice(),
    )
    .unwrap()
    .egraph_id;
    let mut conflict = program.clone();
    conflict.nodes[0].kind = Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
        value: Some(pb::primitive_value::Value::I64(99)),
    }));
    assert!(run(&mut engine, id, conflict.clone()).error.is_some());
    assert!(renderer.render(&conflict).is_err());
    program.declarations.clear();
    program.nodes[0].kind = Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
        value: Some(pb::primitive_value::Value::I64(2)),
    }));
    program.commands.insert(
        1,
        pb::Command {
            kind: Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Panic("after Pair write".into())),
                ..Default::default()
            })),
            ..Default::default()
        },
    );
    let response = run(&mut engine, id, program.clone());
    assert_eq!(response.error.unwrap().code, pb::ErrorCode::Panic as i32);
    program.nodes = vec![pb::Node {
        sort_id: 2,
        kind: Some(pb::node::Kind::Call(pb::Call {
            func: "stored".into(),
            args: vec![],
        })),
        ..Default::default()
    }];
    program.commands = vec![pb::Command {
        kind: Some(pb::command::Kind::Extract(pb::Extract {
            roots: vec![0],
            variants: 1,
            extractor: pb::Extractor::Tree.into(),
            ..Default::default()
        })),
        ..Default::default()
    }];
    for (handle, expected) in [(id, "(pair 2 \"x\")"), (clone, "(pair 1 \"x\")")] {
        let response = run(&mut engine, handle, program.clone());
        assert_eq!(response.error, None);
        let Some(pb::command_output::Kind::Extraction(e)) = &response.outputs[0].kind else {
            unreachable!()
        };
        assert_eq!(value(&response, e.roots[0].variants[0].term), expected);
    }
}

#[test]
fn pair_payload_children_evaluate_first_then_second() {
    let mut program = pair_fixture();
    for (name, output) in [("left", 0), ("right", 1)] {
        program.declarations.push(pb::Declaration {
            kind: Some(pb::declaration::Kind::Function(pb::Function {
                name: name.into(),
                inputs: vec![],
                output,
                merge: None,
            })),
            ..Default::default()
        });
        program.nodes[output as usize].kind = Some(pb::node::Kind::Call(pb::Call {
            func: name.into(),
            args: vec![],
        }));
    }
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut errors = vec![];
    for root in [0, 1, 2] {
        program.commands = vec![pb::Command {
            kind: Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Term(root)),
                ..Default::default()
            })),
            ..Default::default()
        }];
        errors.push(run(&mut engine, id, program.clone()).error.unwrap());
    }
    assert_ne!(
        errors[0].message, errors[1].message,
        "the two missing reads must distinguish order"
    );
    assert_eq!(
        errors[2].message, errors[0].message,
        "the Pair fails at its first child"
    );
    program.nodes.push(pb::Node {
        sort_id: 0,
        kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::I64(8)),
        })),
        ..Default::default()
    });
    program.commands.insert(
        0,
        pb::Command {
            kind: Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Set(pb::Set {
                    target: Some(pb::Call {
                        func: "left".into(),
                        args: vec![],
                    }),
                    value: Some(3),
                })),
                ..Default::default()
            })),
            ..Default::default()
        },
    );
    assert_eq!(
        run(&mut engine, id, program.clone()).error.unwrap().message,
        errors[1].message
    );
    program.commands = vec![pb::Command {
        kind: Some(pb::command::Kind::Extract(pb::Extract {
            roots: vec![0],
            variants: 1,
            extractor: pb::Extractor::Tree.into(),
            ..Default::default()
        })),
        ..Default::default()
    }];
    let response = run(&mut engine, id, program);
    assert_eq!(response.error, None);
    let Some(pb::command_output::Kind::Extraction(e)) = &response.outputs[0].kind else {
        unreachable!()
    };
    assert_eq!(
        value(&response, e.roots[0].variants[0].term),
        "8",
        "earlier Set survives the second-child failure"
    );
}

#[test]
fn map_payload_visits_overwritten_entries_in_order_and_keeps_runtime_prefix() {
    let mut program = map_fixture();
    let Some(pb::sort::Kind::Family(f)) = &mut program.sorts[2].kind else {
        unreachable!()
    };
    f.args = vec![0, 0];
    let reads = ["key0", "value0", "key1", "value1"];
    program.nodes = reads
        .iter()
        .map(|name| pb::Node {
            sort_id: 0,
            kind: Some(pb::node::Kind::Call(pb::Call {
                func: (*name).into(),
                args: vec![],
            })),
            ..Default::default()
        })
        .collect();
    for name in reads {
        program.declarations.push(pb::Declaration {
            kind: Some(pb::declaration::Kind::Function(pb::Function {
                name: name.into(),
                output: 0,
                ..Default::default()
            })),
            ..Default::default()
        });
    }
    program.nodes.push(pb::Node {
        sort_id: 2,
        kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Map(pb::MapValue {
                entries: vec![
                    pb::MapEntry {
                        key: Some(0),
                        value: Some(1),
                    },
                    pb::MapEntry {
                        key: Some(2),
                        value: Some(3),
                    },
                ],
            })),
        })),
        ..Default::default()
    });
    program.nodes.push(pb::Node {
        sort_id: 0,
        kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::I64(7)),
        })),
        ..Default::default()
    });
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut errors = vec![];
    for root in 0..4 {
        program.commands = vec![pb::Command {
            kind: Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Term(root)),
                ..Default::default()
            })),
            ..Default::default()
        }];
        errors.push(run(&mut engine, id, program.clone()).error.unwrap().message);
    }
    assert_eq!(
        errors
            .iter()
            .collect::<std::collections::HashSet<_>>()
            .len(),
        4
    );
    for (position, expected) in errors.iter().enumerate() {
        program.commands = (0..position)
            .map(|i| pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Set(pb::Set {
                        target: Some(pb::Call {
                            func: reads[i].into(),
                            args: vec![],
                        }),
                        value: Some(5),
                    })),
                    ..Default::default()
                })),
                ..Default::default()
            })
            .collect();
        program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Term(4)),
                ..Default::default()
            })),
            ..Default::default()
        });
        let response = run(&mut engine, id, program.clone());
        assert_eq!(
            &response.error.unwrap().message,
            expected,
            "position {position}"
        );
    }
    // The last failure happened after key0/value0/key1 were written. A Map
    // duplicate does not suppress its overwritten first value's evaluation.
    program.commands = vec![pb::Command {
        kind: Some(pb::command::Kind::Extract(pb::Extract {
            roots: vec![0, 1, 2],
            variants: 1,
            extractor: pb::Extractor::Tree.into(),
            ..Default::default()
        })),
        ..Default::default()
    }];
    let response = run(&mut engine, id, program);
    assert_eq!(response.error, None);
    let Some(pb::command_output::Kind::Extraction(e)) = &response.outputs[0].kind else {
        unreachable!()
    };
    assert!(
        e.roots
            .iter()
            .all(|r| value(&response, r.variants[0].term) == "7")
    );
}

#[test]
fn map_defaults_clone_and_missing_key_preserve_canonical_records_and_prefix() {
    use egglog_experimental::protobuf::source::Renderer;
    let mut program = map_fixture();
    program.nodes.extend([
        pb::Node {
            sort_id: 2,
            kind: Some(pb::node::Kind::Var("new".into())),
            ..Default::default()
        },
        pb::Node {
            sort_id: 2,
            kind: Some(pb::node::Kind::Call(pb::Call {
                func: "stored".into(),
                args: vec![],
            })),
            ..Default::default()
        },
        pb::Node {
            sort_id: 0,
            kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::I64(999)),
            })),
            ..Default::default()
        },
        pb::Node {
            sort_id: 1,
            kind: Some(pb::node::Kind::Call(pb::Call {
                func: "egglog.core.map.get".into(),
                args: vec![6, 7],
            })),
            ..Default::default()
        },
    ]);
    program.declarations.extend([
        pb::Declaration {
            kind: Some(pb::declaration::Kind::Function(pb::Function {
                name: "stored".into(),
                output: 2,
                merge: Some(5),
                ..Default::default()
            })),
            ..Default::default()
        },
        pb::Declaration {
            kind: Some(pb::declaration::Kind::Function(pb::Function {
                name: "take_map".into(),
                inputs: vec![pb::Arg {
                    name: "map".into(),
                    sort: 2,
                }],
                output: 0,
                merge: None,
            })),
            bindings: Some(pb::CallableBindings {
                python: Some(pb::PythonBindings {
                    views: vec![pb::PythonCallable {
                        kind: pb::PythonCallKind::Function.into(),
                        path: vec!["test".into(), "take_map".into()],
                        params: vec![pb::PythonParameter {
                            core_input: Some(0),
                            name: "map".into(),
                            default_expr: Some(2),
                        }],
                        ..Default::default()
                    }],
                }),
                ..Default::default()
            }),
            ..Default::default()
        },
    ]);
    let write = pb::Command {
        kind: Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Set(pb::Set {
                target: Some(pb::Call {
                    func: "stored".into(),
                    args: vec![],
                }),
                value: Some(2),
            })),
            ..Default::default()
        })),
        ..Default::default()
    };
    program.commands.insert(0, write);
    let canonical = program.clone();
    let mut engine = Engine::default();
    let id = create(&mut engine);
    let mut renderer = Renderer::default();
    let mut native = new_experimental_egraph();
    for _ in 0..3 {
        assert_eq!(run(&mut engine, id, program.clone()).error, None);
        native
            .parse_and_run_program(None, &renderer.render(&program).unwrap())
            .unwrap();
        assert_eq!(program, canonical);
    }
    let clone = pb::CloneEGraphResponse::decode(
        engine
            .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
            .unwrap()
            .as_slice(),
    )
    .unwrap()
    .egraph_id;
    let mut changed = program.clone();
    changed.nodes[3].kind = Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
        value: Some(pb::primitive_value::Value::String("updated".into())),
    }));
    for handle in [id, clone] {
        assert_eq!(
            run(&mut engine, handle, changed.clone())
                .error
                .unwrap()
                .code,
            pb::ErrorCode::InvalidProgram as i32
        );
    }
    assert!(renderer.render(&changed).is_err());
    changed.declarations.clear();
    changed.commands.push(pb::Command {
        kind: Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Term(8)),
            ..Default::default()
        })),
        ..Default::default()
    });
    let response = run(&mut engine, id, changed.clone());
    assert_eq!(
        response.error.unwrap().code,
        pb::ErrorCode::EvaluationFailed as i32
    );
    assert_eq!(
        response.outputs.len(),
        1,
        "completed extraction survives failed lookup"
    );
    assert!(
        native
            .parse_and_run_program(None, &renderer.render(&changed).unwrap())
            .is_err()
    );
    program.declarations.clear();
    program.commands = vec![pb::Command {
        kind: Some(pb::command::Kind::PrintFunction(pb::PrintFunction {
            table: "stored".into(),
            max_rows: 10,
        })),
        ..Default::default()
    }];
    for (handle, expected) in [(id, "\"updated\""), (clone, "\"last\"")] {
        let response = run(&mut engine, handle, program.clone());
        assert_eq!(response.error, None);
        let Some(pb::command_output::Kind::PrintedFunction(table)) = &response.outputs[0].kind
        else {
            unreachable!()
        };
        let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Map(map)),
        })) = &response.nodes[table.rows[0].output as usize].kind
        else {
            unreachable!()
        };
        let entry = map
            .entries
            .iter()
            .find(|e| value(&response, e.key.unwrap()) == "1")
            .unwrap();
        assert_eq!(value(&response, entry.value.unwrap()), expected);
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
fn map_source_errors_preserve_only_previously_submitted_phases() {
    use egglog_experimental::protobuf::source::Source;
    for failing_value in ["(map-of 1)", "(map-of 1 (- 2 1))"] {
        let text = format!(
            "(sort M (Map i64 i64)) (function stored () M :merge new)
             (set (stored) (map-of 1 7)) (set (stored) {failing_value})
             (set (stored) (map-of 1 99))"
        );
        let mut engine = Engine::default();
        let id = create(&mut engine);
        let mut source = Source::new(None, &text).unwrap();
        for _ in 0..3 {
            assert_eq!(
                run(&mut engine, id, source.next().unwrap().unwrap()).error,
                None
            );
        }
        let failure = source.next().unwrap().unwrap_err();
        assert!(!failure.to_string().is_empty());
        assert!(
            source.next().is_none(),
            "discard the failed source phase and its suffix"
        );
        let observation = Source::new(
            None,
            "(sort M (Map i64 i64)) (function stored () M :merge new)
             (check (= (map-get (stored) 1) 7))",
        )
        .unwrap()
        .last()
        .unwrap()
        .unwrap();
        assert_eq!(run(&mut engine, id, observation).error, None);
    }
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
            pb::primitive_value::Value::String(s) => format!("{s:?}"),
            pb::primitive_value::Value::Pair(pair) => format!(
                "(pair {} {})",
                value(response, pair.first.unwrap()),
                value(response, pair.second.unwrap())
            ),
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
        pb::node::Kind::Call(call) if call.args.is_empty() => format!("({})", call.func),
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
