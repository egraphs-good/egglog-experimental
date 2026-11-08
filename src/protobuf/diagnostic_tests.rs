#[test]
fn authored_error_retains_installed_rule_and_closed_declarations_across_clone() {
    for mode in [
        pb::ExecutionMode::Normal,
        pb::ExecutionMode::TermEncoding,
        pb::ExecutionMode::Proofs,
        pb::ExecutionMode::ProofTesting,
    ] {
        let (mut engine, id) = host_default_engine();
        let session = engine.graphs.get_mut(&id).unwrap();
        let graph = std::mem::take(&mut session.graph);
        session.graph = match mode {
            pb::ExecutionMode::Normal => graph,
            pb::ExecutionMode::TermEncoding => graph.with_term_encoding_enabled(),
            pb::ExecutionMode::Proofs => graph.with_proofs_enabled(),
            pb::ExecutionMode::ProofTesting => graph.with_proofs_enabled().with_proof_testing(),
        };
        session.mode = mode;
        let setup = inventory_fixture(
            "(sort V (Vec i64)) (sort E) (constructor N (i64) E :cost 7) \
             (constructor Out (i64) E :cost 8) (constructor Unrelated () E) \
             (ruleset g) (rule ((N x)) ((Out (vec-get (vec-of x) 4))) \
             :ruleset g :name \"bad-setter\") (N 1)",
        );
        assert_eq!(run_host_default(&mut engine, id, setup).error, None);
        let child = engine
            .clone_request(pb::CloneEGraphRequest { egraph_id: id })
            .unwrap()
            .egraph_id;
        let response = run_host_default(
            &mut engine,
            child,
            pb::Program {
                commands: vec![pb::Command {
                    kind: Some(pb::command::Kind::Run(pb::Run {
                        rulesets: vec![pb::RulesetSelection {
                            kind: Some(pb::ruleset_selection::Kind::Name("g".into())),
                        }],
                        ..Default::default()
                    })),
                }],
                ..Default::default()
            },
        );
        let error = response.error.expect("escaping primitive failure");
        assert_eq!(error.code, pb::ErrorCode::RuntimeFailure as i32, "{mode:?}");
        assert_eq!(error.location.as_ref().unwrap().path, [0]);
        let context = error.context.as_ref().expect("owned installed rule");
        assert!(context.commands.is_empty());
        let rule = graph::rules(context).next().unwrap();
        assert_eq!(rule.name.as_deref(), Some("bad-setter"));
        assert_eq!(
            context
                .constructors
                .iter()
                .map(|d| d.name.as_str())
                .collect::<HashSet<_>>(),
            HashSet::from(["N", "Out"])
        );
        assert!(context.constructors.iter().all(|d| d.cost.is_some()));
        // Declaration-cost roots precede rule roots in the response, so this
        // assertion also checks that the exact failure node was relocated.
        let site = error.site.as_ref().expect("authored site");
        assert_eq!(site.path, [7, 0, 2, 1, 0, 1, 3, 0], "{mode:?}");
        assert!(
            matches!(&context.nodes[site.node_id.expect("exact primitive") as usize].kind,
            Some(pb::node::Kind::Call(call)) if call.func == "egglog.core.vec.get")
        );
        assert!(!error.message.contains("__protobuf_"), "{}", error.message);
        source::Renderer::default()
            .render(context)
            .expect("context renders without request/history");
    }
}

#[test]
fn authored_error_merge_failures_own_the_declaration() {
    for explicit_merge in [false, true] {
        let (mut engine, id) = host_default_engine();
        let merge = if explicit_merge {
            " :merge (vec-get (vec-of old) new)"
        } else {
            " :no-merge"
        };
        let setup = inventory_fixture(&format!(
            "(sort V (Vec i64)) (datatype E (N i64)) (function score (E) i64{merge}) \
             (set (score (N 1)) 1) (set (score (N 2)) 7)"
        ));
        assert_eq!(run_host_default(&mut engine, id, setup).error, None);
        let response = run_host_default(
            &mut engine,
            id,
            inventory_fixture("(datatype E (N i64)) (union (N 1) (N 2))"),
        );
        let error = response.error.expect("rebuild collision fails");
        let context = error.context.as_ref().expect("owned merge declaration");
        let function = &context.functions[0];
        assert_eq!(function.name, "score");
        assert_eq!(function.merge.is_some(), explicit_merge);
        assert_eq!(error.site.as_ref().unwrap().path, [8, 0]);
        assert_eq!(
            error.site.as_ref().unwrap().node_id.is_some(),
            explicit_merge
        );
        assert_eq!(error.location.as_ref().unwrap().path, [0]);
        assert!(graph::rules(context).next().is_none());
    }
}

#[test]
fn authored_error_shared_nodes_keep_the_action_occurrence() {
    let program = inventory_fixture(
        "(sort V (Vec i64)) (datatype E (N i64)) (ruleset g) \
         (rule ((N x)) ((N (vec-get (vec-of x) 4)) (N (vec-get (vec-of x) 4))) :ruleset g)",
    );
    let rule = graph::rules(&program).next().unwrap().clone();
    let mut fragment = pb::Program {
        rulesets: vec![pb::RulesetBinding {
            name: String::new(),
            value: Some(pb::Ruleset { rules: vec![rule] }),
        }],
        ..Default::default()
    };
    let Some(pb::rule::Kind::Rule(body)) =
        &mut fragment.rulesets[0].value.as_mut().unwrap().rules[0].kind
    else {
        unreachable!()
    };
    body.actions[1] = body.actions[0].clone();
    let root = action_roots(&body.actions[0]).unwrap()[0];
    let mut origins = AuthoredOrigins::fragment(&program, fragment, vec![7, 0, 2, 1, 0, 1, 3, 0]);
    let first = authored_span(Some(root), &origins);
    *origins.path.last_mut().unwrap() = 1;
    let second = authored_span(Some(root), &origins);
    let (ast::Span::External(first), ast::Span::External(second)) = (first, second) else {
        panic!("authored tokens")
    };
    let first = first.0.downcast_ref::<AuthoredSite>().unwrap();
    let second = second.0.downcast_ref::<AuthoredSite>().unwrap();
    assert!(Arc::ptr_eq(&first.context, &second.context));
    assert_eq!(first.site.node_id, second.site.node_id);
    assert_ne!(first.site.path, second.site.path);
}

#[test]
fn authored_error_closure_preserves_cycles_and_recursive_declarations() {
    let source = pb::Program {
        sorts: vec![pb::Sort {
            kind: Some(pb::sort::Kind::Eq("E".into())),
            ..Default::default()
        }],
        nodes: vec![
            pb::Node {
                sort_id: 0,
                kind: Some(pb::node::Kind::Eq(pb::Eq {
                    members: vec![0, 1],
                })),
            },
            pb::Node {
                sort_id: 0,
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "a".into(),
                    args: vec![],
                })),
            },
            pb::Node {
                sort_id: 0,
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "b".into(),
                    args: vec![],
                })),
            },
            pb::Node {
                sort_id: 0,
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "a".into(),
                    args: vec![],
                })),
            },
        ],
        user_defined_primitives: vec![
            pb::UserDefinedPrimitive {
                name: "a".into(),
                output: 0,
                body: Some(2),
                ..Default::default()
            },
            pb::UserDefinedPrimitive {
                name: "b".into(),
                output: 0,
                body: Some(3),
                ..Default::default()
            },
            pb::UserDefinedPrimitive {
                name: "unrelated".into(),
                output: 0,
                body: Some(2),
                ..Default::default()
            },
        ],
        ..Default::default()
    };
    let (owner, _) = graph::compact(
        &source,
        pb::Program {
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Term(0)),
                })),
            }],
            ..Default::default()
        },
    )
    .unwrap();
    assert!(
        owner.user_defined_primitives.is_empty(),
        "declaration closure is deferred"
    );
    let (context, nodes) = graph::error_context(&owner, &source).unwrap();
    assert_eq!(
        context
            .user_defined_primitives
            .iter()
            .map(|d| d.name.as_str())
            .collect::<Vec<_>>(),
        ["a", "b"]
    );
    let pb::command::Kind::Action(action) = context.commands[0].kind.as_ref().unwrap() else {
        unreachable!()
    };
    let pb::action::Kind::Term(root) = action.kind.as_ref().unwrap() else {
        unreachable!()
    };
    let pb::node::Kind::Eq(group) = context.nodes[*root as usize].kind.as_ref().unwrap() else {
        unreachable!()
    };
    assert_eq!(group.members[0], *root);
    assert_eq!(nodes[&0], *root);
    assert_eq!(context.nodes.len(), 4);
}

#[test]
fn authored_error_through_lambda_keeps_authored_primitive_definition() {
    let (mut engine, id) = host_default_engine();
    let mut program = anonymous_arithmetic(0);
    let Some(pb::node::Kind::Call(call)) = &mut program.nodes[3].kind else {
        unreachable!()
    };
    call.func = "egglog.core.i64.div".into();
    program
        .user_defined_primitives
        .push(pb::UserDefinedPrimitive {
            name: "compute".into(),
            output: 0,
            body: Some(6),
            ..Default::default()
        });
    let call = program.nodes.len() as u32;
    program.nodes.push(pb::Node {
        sort_id: 0,
        kind: Some(pb::node::Kind::Call(pb::Call {
            func: "compute".into(),
            args: vec![],
        })),
    });
    program.commands = vec![pb::Command {
        kind: Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Term(call)),
        })),
    }];
    let error = run_host_default(&mut engine, id, program)
        .error
        .expect("escaping deferred division");
    let context = error.context.as_ref().expect("authored caller context");
    assert_eq!(
        context
            .user_defined_primitives
            .iter()
            .map(|d| d.name.as_str())
            .collect::<Vec<_>>(),
        ["compute"]
    );
    assert!(context.nodes.iter().any(|node| matches!(
        node.kind,
        Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Lambda(_))
        }))
    )));
    assert!(!String::from_utf8_lossy(&context.encode_to_vec()).contains("__egglog_lambda"));
    if let Some(node) = error.site.as_ref().unwrap().node_id {
        assert!((node as usize) < context.nodes.len());
    }
}

#[test]
fn authored_error_named_commands_close_exact_keys_and_preserve_aliases() {
    let definitions = pb::Program {
        sorts: vec![pb::Sort {
            kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
                name: "i64".into(),
                args: vec![],
            })),
            ..Default::default()
        }],
        nodes: vec![
            pb::Node {
                sort_id: 0,
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "merge-value".into(),
                    args: vec![],
                })),
            },
            pb::Node {
                sort_id: 0,
                kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::I64(7)),
                })),
            },
        ],
        functions: vec![
            pb::Function {
                name: "current".into(),
                output: 0,
                merge: Some(0),
                ..Default::default()
            },
            pb::Function {
                name: "other".into(),
                output: 0,
                table_name: Some(pb::function::TableName::PublicAlias("current".into())),
                ..Default::default()
            },
        ],
        user_defined_primitives: vec![pb::UserDefinedPrimitive {
            name: "merge-value".into(),
            output: 0,
            body: Some(1),
            ..Default::default()
        }],
        ..Default::default()
    };
    for kind in [
        pb::command::Kind::TableSizes(pb::GetTableSizes {
            tables: vec!["current".into(), "missing".into()],
        }),
        pb::command::Kind::TableRows(pb::GetTableRows {
            table: "current".into(),
            max_rows: None,
        }),
        pb::command::Kind::TableStats(pb::GetTableStats {
            tables: vec!["current".into(), "missing".into()],
        }),
    ] {
        let owner = pb::Program {
            commands: vec![pb::Command { kind: Some(kind) }],
            ..Default::default()
        };
        let (context, _) = graph::error_context(&owner, &definitions).unwrap();
        assert_eq!(
            context
                .functions
                .iter()
                .map(|d| d.name.as_str())
                .collect::<Vec<_>>(),
            ["current"]
        );
        assert_eq!(context.functions[0].table_name, None);
        assert_eq!(context.user_defined_primitives[0].name, "merge-value");
        assert_eq!(context.nodes.len(), 2);
    }
    let owner = pb::Program {
        commands: vec![pb::Command {
            kind: Some(pb::command::Kind::TableRows(pb::GetTableRows {
                table: "other".into(),
                max_rows: None,
            })),
        }],
        ..Default::default()
    };
    let (context, _) = graph::error_context(&owner, &definitions).unwrap();
    assert_eq!(
        context.functions[0].table_name,
        definitions.functions[1].table_name
    );
    assert!(context.user_defined_primitives.is_empty());
    let mut constructors = definitions.clone();
    constructors.sorts.push(pb::Sort {
        kind: Some(pb::sort::Kind::Eq("E".into())),
        ..Default::default()
    });
    constructors.constructors.push(pb::Constructor {
        name: "Thing".into(),
        output: 1,
        cost: Some(1),
        ..Default::default()
    });
    let owner = pb::Program {
        commands: vec![pb::Command {
            kind: Some(pb::command::Kind::ProveExists(pb::ProveExists {
                constructor: "Thing".into(),
            })),
        }],
        ..Default::default()
    };
    let (context, _) = graph::error_context(&owner, &constructors).unwrap();
    assert_eq!(context.constructors[0].name, "Thing");
    assert!(context.constructors[0].cost.is_some());
    assert!(context.functions.is_empty());
    let (mut engine, id) = host_default_engine();
    assert_eq!(
        run_host_default(
            &mut engine,
            id,
            inventory_fixture("(function current () i64 :merge old)")
        )
        .error,
        None
    );
    let error = run_host_default(
        &mut engine,
        id,
        pb::Program {
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::TableSizes(pb::GetTableSizes {
                    tables: vec!["current".into(), "missing".into()],
                })),
            }],
            ..Default::default()
        },
    )
    .error
    .expect("unknown second table");
    assert_eq!(error.context.as_ref().unwrap().functions[0].name, "current");
    assert_eq!(error.site.as_ref().unwrap().path, [5, 0]);
}
