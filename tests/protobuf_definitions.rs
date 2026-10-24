use egglog_experimental::{builtin::definitions::reconcile_declarations, proto as pb};

fn relation_definition_fixture(reversed: bool) -> pb::Program {
    let list = pb::Sort {
        kind: Some(pb::sort::Kind::Eq("IList".into())),
        ..Default::default()
    };
    let number = pb::Sort {
        kind: Some(pb::sort::Kind::Application(pb::SortApplication {
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
            ..Default::default()
        }],
        declarations: vec![
            pb::Declaration {
                kind: Some(pb::declaration::Kind::EqSort(pb::EqSort {
                    name: "IList".into(),
                })),
                ..Default::default()
            },
            pb::Declaration {
                kind: Some(pb::declaration::Kind::Relation(pb::Relation {
                    name: "ordered_inputs".into(),
                    inputs: vec![
                        pb::Arg {
                            sort: list_sort,
                            name: "list".into(),
                        },
                        pb::Arg {
                            sort: number_sort,
                            name: "index".into(),
                        },
                    ],
                })),
                ..Default::default()
            },
        ],
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
    let mut relocated = relation_definition_fixture(true);
    let Some(pb::declaration::Kind::Relation(relation)) = &mut relocated.declarations[1].kind
    else {
        unreachable!()
    };
    relation.inputs[0].name = "renamed_list".into();
    relation.inputs[1].name = "renamed_index".into();
    reconcile_declarations(&relocated, &mut destination).unwrap();
    assert_eq!(
        destination, installed,
        "compatible resupply must not grow the closure"
    );
    let relations = destination
        .declarations
        .iter()
        .filter_map(|declaration| match &declaration.kind {
            Some(pb::declaration::Kind::Relation(relation)) => Some(relation),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(relations.len(), 1);
    let relation = relations[0];
    assert_eq!(relation.name, "ordered_inputs");
    assert!(matches!(
        &destination.sorts[relation.inputs[0].sort as usize].kind,
        Some(pb::sort::Kind::Eq(name)) if name == "IList"
    ));
    assert!(matches!(
        &destination.sorts[relation.inputs[1].sort as usize].kind,
        Some(pb::sort::Kind::Application(family)) if family.name == "i64" && family.args.is_empty()
    ));
    assert!(
        destination.nodes.is_empty(),
        "unused expression data is not a semantic declaration dependency"
    );
    assert_eq!(
        destination.declarations.len(),
        2,
        "no synthetic Function/Constructor output carrier"
    );
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
        let Some(pb::declaration::Kind::Relation(relation)) = &mut conflicting.declarations[1].kind
        else {
            unreachable!()
        };
        match case {
            "arity" => {
                relation.inputs.pop();
            }
            "order" => relation.inputs.swap(0, 1),
            "unknown-sort" => relation.inputs[0].sort = 99,
            "empty-name" => relation.name.clear(),
            "function" => {
                conflicting.declarations[1].kind =
                    Some(pb::declaration::Kind::Function(pb::Function {
                        name: relation.name.clone(),
                        inputs: relation.inputs.clone(),
                        output: 1,
                        ..Default::default()
                    }));
            }
            "constructor" => {
                conflicting.declarations[1].kind =
                    Some(pb::declaration::Kind::Constructor(pb::Constructor {
                        name: relation.name.clone(),
                        inputs: relation.inputs.clone(),
                        output: 0,
                        ..Default::default()
                    }));
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
        for d in &mut source.declarations {
            d.doc = first.map(str::to_owned);
        }
        let mut destination = pb::Program::default();
        reconcile_declarations(&source, &mut destination).unwrap();
        let installed = destination.clone();
        assert!(
            destination
                .declarations
                .iter()
                .all(|d| d.doc.as_deref() == first)
        );
        for later in [None, Some(""), Some("other")] {
            let mut resupply = source.clone();
            for d in &mut resupply.declarations {
                d.doc = later.map(str::to_owned);
            }
            let mut independent = destination.clone();
            reconcile_declarations(&resupply, &mut independent).unwrap();
            assert_eq!(
                independent, installed,
                "resupply retains first-record diagnostics"
            );
            assert_eq!(destination, installed);
            let Some(pb::declaration::Kind::Constructor(c)) = &mut resupply.declarations[1].kind
            else {
                unreachable!()
            };
            c.unextractable = true;
            assert!(reconcile_declarations(&resupply, &mut independent).is_err());
            assert_eq!(independent, installed);
            let Some(pb::declaration::Kind::Constructor(c)) = &mut resupply.declarations[1].kind
            else {
                unreachable!()
            };
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
                kind: Some(pb::sort::Kind::Application(pb::SortApplication {
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
                ..Default::default()
            },
            pb::Node {
                sort_id: 0,
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "current".into(),
                    args: vec![],
                })),
                ..Default::default()
            },
            pb::Node {
                sort_id: 0,
                kind: Some(pb::node::Kind::Var("new".into())),
                ..Default::default()
            },
        ],
        declarations: vec![
            pb::Declaration {
                kind: Some(pb::declaration::Kind::EqSort(pb::EqSort {
                    name: "Box".into(),
                })),
                ..Default::default()
            },
            pb::Declaration {
                kind: Some(pb::declaration::Kind::Constructor(pb::Constructor {
                    name: "Box".into(),
                    inputs: vec![pb::Arg {
                        sort: 0,
                        name: "value".into(),
                    }],
                    output: 1,
                    ..Default::default()
                })),
                ..Default::default()
            },
            pb::Declaration {
                kind: Some(pb::declaration::Kind::Function(pb::Function {
                    name: "current".into(),
                    inputs: vec![],
                    output: 0,
                    hidden: false,
                    merge: Some(2),
                })),
                ..Default::default()
            },
        ],
        ..Default::default()
    }
}

#[test]
fn declaration_closures_relocate_and_resupply_structurally() {
    let source = box_definition();
    let mut destination = pb::Program::default();
    assert_eq!(
        reconcile_declarations(&source, &mut destination).unwrap(),
        [true, true, true]
    );
    let installed = destination.clone();
    let mut permuted = source.clone();
    permuted.sorts.reverse();
    permuted.nodes.reverse();
    for n in &mut permuted.nodes {
        n.sort_id = 1 - n.sort_id;
    }
    let Some(pb::declaration::Kind::Constructor(c)) = &mut permuted.declarations[1].kind else {
        unreachable!()
    };
    c.inputs[0].sort = 1;
    c.inputs[0].name = "diagnostic alpha rename".into();
    c.output = 0;
    let Some(pb::declaration::Kind::Function(f)) = &mut permuted.declarations[2].kind else {
        unreachable!()
    };
    f.output = 1;
    f.merge = Some(0);
    permuted.declarations.reverse();
    assert_eq!(
        reconcile_declarations(&permuted, &mut destination).unwrap(),
        [false, false, false]
    );
    assert_eq!(
        destination, installed,
        "compatible resupply must not retain unreachable template copies"
    );
    let before = destination.clone();
    let Some(pb::declaration::Kind::Function(f)) = &mut permuted.declarations[0].kind else {
        unreachable!()
    };
    f.merge = None;
    assert!(reconcile_declarations(&permuted, &mut destination).is_err());
    assert_eq!(destination, before);
}
