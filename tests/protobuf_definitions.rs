use egglog_experimental::{builtin::definitions::reconcile_declarations, proto as pb};

fn relation_definition_fixture(reversed: bool) -> pb::Program {
    let list = pb::Sort {
        kind: Some(pb::sort::Kind::Eq("IList".into())),
        ..Default::default()
    };
    let number = pb::Sort {
        kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
            name: "i64".into(),
            args: vec![],
        })),
        ..Default::default()
    };
    let (sorts, list_sort, number_sort) = if reversed {
        (vec![number, list], 1, 0)
    } else {
        (vec![list, number], 0, 1)
    };
    pb::Program {
        sorts,
        nodes: vec![pb::Node {
            sort_id: number_sort,
            kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::I64(7)),
            })),
        }],
        relations: vec![pb::Relation {
            name: "ordered_inputs".into(),
            inputs: vec![list_sort, number_sort],
            ..Default::default()
        }],
        ..Default::default()
    }
}

#[test]
fn relation_definitions_reconcile_and_relocate_input_only_records() {
    let source = relation_definition_fixture(false);
    let mut destination = pb::Program::default();
    reconcile_declarations(&source, &mut destination)
        .expect("canonical input-only Relation must participate in declaration reconciliation");
    let installed = destination.clone();
    let relocated = relation_definition_fixture(true);
    reconcile_declarations(&relocated, &mut destination).unwrap();
    assert_eq!(
        destination, installed,
        "compatible resupply must not grow the closure"
    );
    let relations = &destination.relations;
    assert_eq!(relations.len(), 1);
    let relation = &relations[0];
    assert_eq!(relation.name, "ordered_inputs");
    assert!(matches!(
        &destination.sorts[relation.inputs[0] as usize].kind,
        Some(pb::sort::Kind::Eq(name)) if name == "IList"
    ));
    assert!(matches!(
        &destination.sorts[relation.inputs[1] as usize].kind,
        Some(pb::sort::Kind::Primitive(family)) if family.name == "i64" && family.args.is_empty()
    ));
    assert!(
        destination.nodes.is_empty(),
        "unused expression data is not a semantic declaration dependency"
    );
    assert_eq!(
        destination.relations.len(),
        1,
        "no synthetic Function/Constructor output carrier"
    );
    assert!(destination.constructors.is_empty());
    assert!(destination.functions.is_empty());
    assert!(destination.user_defined_primitives.is_empty());
}

#[test]
fn relation_definitions_kind_signature_and_reference_conflicts_are_atomic() {
    let source = relation_definition_fixture(false);
    let mut destination = pb::Program::default();
    reconcile_declarations(&source, &mut destination).unwrap();
    for case in [
        "arity",
        "order",
        "unknown-sort",
        "function",
        "constructor",
        "empty-name",
    ] {
        let mut conflicting = source.clone();
        let relation = &mut conflicting.relations[0];
        match case {
            "arity" => {
                relation.inputs.pop();
            }
            "order" => relation.inputs.swap(0, 1),
            "unknown-sort" => relation.inputs[0] = 99,
            "empty-name" => relation.name.clear(),
            "function" => {
                conflicting.functions.push(pb::Function {
                    name: relation.name.clone(),
                    inputs: relation.inputs.clone(),
                    output: 1,
                    ..Default::default()
                });
                conflicting.relations.clear();
            }
            "constructor" => {
                conflicting.constructors.push(pb::Constructor {
                    name: relation.name.clone(),
                    inputs: relation.inputs.clone(),
                    output: 0,
                    ..Default::default()
                });
                conflicting.relations.clear();
            }
            _ => unreachable!(),
        }
        let before = destination.clone();
        assert!(
            reconcile_declarations(&conflicting, &mut destination).is_err(),
            "{case}"
        );
        assert_eq!(
            destination, before,
            "{case}: rejected metadata must not partially publish"
        );
    }
}

#[test]
fn compiler_sort_aliases_share_types_without_registering_native_instances() {
    let mut graph = egglog::EGraph::default();
    graph
        .parse_and_run_program(None, "(sort A (Vec i64))")
        .unwrap();
    graph
        .bind_source_sort_alias("Z", "A", egglog::span!())
        .unwrap();
    assert_eq!(graph.type_info().get_sort_by_name("Z").unwrap().name(), "A");
    assert_eq!(
        graph
            .type_info()
            .get_arcsorts_by(|sort| sort.name() == "A")
            .len(),
        1
    );
    let command = graph
        .parse_program(None, "(function same (Z) A :merge new)")
        .unwrap()
        .remove(0);
    graph.resolve_command_preserving_globals(command).unwrap();
    graph.parse_and_run_program(None, "(push)").unwrap();
    graph
        .bind_source_sort_alias("Scoped", "A", egglog::span!())
        .unwrap();
    graph.parse_and_run_program(None, "(pop)").unwrap();
    assert!(graph.type_info().get_sort_by_name("Scoped").is_none());
    graph
        .bind_source_sort_alias("Scoped", "A", egglog::span!())
        .unwrap();
    assert!(
        graph
            .bind_source_sort_alias("Z", "A", egglog::span!())
            .is_err()
    );
    assert!(
        graph
            .bind_source_sort_alias("same", "A", egglog::span!())
            .is_err()
    );
    assert!(
        graph
            .bind_source_sort_alias("Missing", "unknown", egglog::span!())
            .is_err()
    );
    graph.parse_and_run_program(None, "(sort Nominal)").unwrap();
    assert!(
        graph
            .bind_source_sort_alias("Other", "Nominal", egglog::span!())
            .is_err()
    );
    assert!(graph.parse_and_run_program(None, "(sort Z)").is_err());
    assert!(
        graph
            .parse_and_run_program(None, "(function Z () i64 :merge new)")
            .is_err()
    );
    graph
        .parse_and_run_program(None, "(sort B (Vec i64))")
        .unwrap();
    assert_eq!(graph.type_info().get_sort_by_name("B").unwrap().name(), "B");
    assert_eq!(
        graph
            .type_info()
            .get_arcsorts_by(|sort| matches!(sort.name(), "A" | "B"))
            .len(),
        2
    );
}

#[test]
fn documentation_presence_is_retained_but_not_semantic_identity() {
    for first in [None, Some(""), Some(" docs\n")] {
        let mut source = box_definition();
        source.relations.push(pb::Relation {
            name: "seen".into(),
            inputs: vec![0],
            ..Default::default()
        });
        source
            .user_defined_primitives
            .push(pb::UserDefinedPrimitive {
                name: "saved".into(),
                output: 0,
                body: Some(0),
                ..Default::default()
            });
        source.relations[0].doc = first.map(str::to_owned);
        source.user_defined_primitives[0].doc = first.map(str::to_owned);
        source.constructors[0].doc = first.map(str::to_owned);
        source.functions[0].doc = first.map(str::to_owned);
        source.sorts[1].doc = first.map(str::to_owned);
        let mut destination = pb::Program::default();
        reconcile_declarations(&source, &mut destination).unwrap();
        let installed = destination.clone();
        assert!(
            destination.constructors[0].doc.as_deref() == first
                && destination.functions[0].doc.as_deref() == first
                && destination.relations[0].doc.as_deref() == first
                && destination.user_defined_primitives[0].doc.as_deref() == first
        );
        assert_eq!(
            destination
                .sorts
                .iter()
                .find(|sort| matches!(&sort.kind, Some(pb::sort::Kind::Eq(name)) if name == "Box"))
                .unwrap()
                .doc
                .as_deref(),
            first,
        );
        for later in [None, Some(""), Some("other")] {
            let mut resupply = source.clone();
            resupply.constructors[0].doc = later.map(str::to_owned);
            resupply.functions[0].doc = later.map(str::to_owned);
            resupply.relations[0].doc = later.map(str::to_owned);
            resupply.user_defined_primitives[0].doc = later.map(str::to_owned);
            resupply.sorts[1].doc = later.map(str::to_owned);
            let mut independent = destination.clone();
            reconcile_declarations(&resupply, &mut independent).unwrap();
            assert_eq!(
                independent, installed,
                "resupply retains first-record diagnostics"
            );
            assert_eq!(destination, installed);
            let c = &mut resupply.constructors[0];
            c.unextractable = true;
            assert!(reconcile_declarations(&resupply, &mut independent).is_err());
            assert_eq!(independent, installed);
            let c = &mut resupply.constructors[0];
            c.unextractable = false;
            reconcile_declarations(&resupply, &mut independent).unwrap();
            assert_eq!(independent, installed);
        }
    }
}

fn box_definition() -> pb::Program {
    pb::Program {
        sorts: vec![
            pb::Sort {
                kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
                    name: "i64".into(),
                    args: vec![],
                })),
                ..Default::default()
            },
            pb::Sort {
                kind: Some(pb::sort::Kind::Eq("Box".into())),
                ..Default::default()
            },
        ],
        nodes: vec![
            pb::Node {
                sort_id: 0,
                kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::I64(4)),
                })),
            },
            pb::Node {
                sort_id: 0,
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "current".into(),
                    args: vec![],
                })),
            },
            pb::Node {
                sort_id: 0,
                kind: Some(pb::node::Kind::Var("new".into())),
            },
        ],
        constructors: vec![pb::Constructor {
            name: "Box".into(),
            inputs: vec![0],
            output: 1,
            ..Default::default()
        }],
        functions: vec![pb::Function {
            name: "current".into(),
            inputs: vec![],
            output: 0,
            hidden: false,
            merge: Some(2),
            ..Default::default()
        }],
        ..Default::default()
    }
}

#[test]
fn declaration_closures_relocate_and_resupply_structurally() {
    let source = box_definition();
    let mut destination = pb::Program::default();
    assert_eq!(
        reconcile_declarations(&source, &mut destination).unwrap(),
        [true, true]
    );
    let installed = destination.clone();
    let mut permuted = source.clone();
    permuted.sorts.reverse();
    permuted.nodes.reverse();
    for n in &mut permuted.nodes {
        n.sort_id = 1 - n.sort_id;
    }
    let c = &mut permuted.constructors[0];
    c.inputs[0] = 1;
    c.output = 0;
    let f = &mut permuted.functions[0];
    f.output = 1;
    f.merge = Some(0);
    permuted.constructors.reverse();
    permuted.functions.reverse();
    assert_eq!(
        reconcile_declarations(&permuted, &mut destination).unwrap(),
        [false, false]
    );
    assert_eq!(
        destination, installed,
        "compatible resupply must not retain unreachable template copies"
    );
    let before = destination.clone();
    let f = &mut permuted.functions[0];
    f.merge = None;
    assert!(reconcile_declarations(&permuted, &mut destination).is_err());
    assert_eq!(destination, before);
}

#[test]
fn flat_callable_lists_share_one_namespace_and_coalesce_compatible_duplicates() {
    let base = box_definition();
    let mut sources = std::array::from_fn::<_, 4, _>(|_| pb::Program {
        sorts: base.sorts.clone(),
        nodes: base.nodes.clone(),
        ..Default::default()
    });
    let input = 0;
    sources[0].constructors = vec![
        pb::Constructor {
            name: "shared".into(),
            inputs: vec![input],
            output: 1,
            ..Default::default()
        };
        2
    ];
    sources[1].functions = vec![
        pb::Function {
            name: "shared".into(),
            inputs: vec![input],
            output: 0,
            ..Default::default()
        };
        2
    ];
    sources[2].relations = vec![
        pb::Relation {
            name: "shared".into(),
            inputs: vec![input],
            ..Default::default()
        };
        2
    ];
    sources[3].user_defined_primitives = vec![
        pb::UserDefinedPrimitive {
            name: "shared".into(),
            inputs: vec![input],
            output: 0,
            body: Some(0),
            ..Default::default()
        };
        2
    ];
    for (kind, source) in sources.iter().enumerate() {
        let mut destination = pb::Program::default();
        assert_eq!(
            reconcile_declarations(source, &mut destination).unwrap(),
            [true, false]
        );
        let installed = destination.clone();
        for (other, candidate) in sources.iter().enumerate() {
            let result = reconcile_declarations(candidate, &mut destination);
            if kind == other {
                assert_eq!(result.unwrap(), [false, false]);
            } else {
                assert!(
                    result
                        .unwrap_err()
                        .contains("conflicting declaration shared")
                );
            }
            assert_eq!(destination, installed, "kind {kind}, candidate {other}");
        }
    }
}
