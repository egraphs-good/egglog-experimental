//! Inert state export into the existing reconstruction Program.
use super::*;
use std::hash::Hash;

// A read-only execution view keeps snapshot export independent of Session's
// ownership, so the same exporter can observe a live loop without cloning it.
#[derive(Clone, Copy)]
pub(super) struct View<'a> {
    pub graph: &'a EGraph,
    pub names: &'a NativeNames,
    pub definitions: &'a pb::Program,
    pub lambdas: &'a lambda::Registry,
    pub mode: pb::ExecutionMode,
    pub extension: Option<&'a Arc<dyn NativeExtension>>,
}

// The only retained graph is the generated Program. These maps assign wire
// locations to native values; the queue closes container edges iteratively.
struct Export<'a, K, F> {
    session: View<'a>,
    program: pb::Program,
    classes: HashMap<K, u32>,
    canonical: F,
    values: HashMap<(String, Value), u32>,
    pending: Vec<(ArcSort, Value, u32)>,
}

impl<K: Eq + Hash, F: Fn(&ArcSort, Value) -> K> Export<'_, K, F> {
    fn sort(&mut self, sort: &ArcSort) -> Result<u32, egglog::Error> {
        let mut sorts = vec![];
        let root = self
            .session
            .graph
            .export_sort(sort, &mut sorts)
            .map_err(egglog::Error::BackendError)?;
        for sort in &mut sorts {
            if let Some(pb::sort::Kind::Eq(name)) = &mut sort.kind {
                let logical = self.session.names.sorts.get(name).ok_or_else(|| {
                    egglog::Error::BackendError(format!(
                        "Freeze cannot export unregistered native sort {name}"
                    ))
                })?;
                *name = logical.clone();
            }
        }
        crate::builtin::import_sort(&sorts, root, &mut self.program.sorts)
            .map_err(egglog::Error::BackendError)
    }

    fn append(&mut self, node: pb::Node) -> Result<u32, egglog::Error> {
        let index = u32::try_from(self.program.nodes.len())
            .map_err(|_| egglog::Error::BackendError("Freeze node arena exceeds u32".into()))?;
        self.program.nodes.push(node);
        Ok(index)
    }

    fn value(&mut self, sort: &ArcSort, value: Value) -> Result<u32, egglog::Error> {
        if sort.is_eq_sort() {
            return self
                .classes
                .get(&(self.canonical)(sort, value))
                .copied()
                .ok_or_else(|| {
                    egglog::Error::BackendError(format!(
                        "Freeze value is absent from {} class inventory",
                        sort.name()
                    ))
                });
        }
        let key = (sort.name().to_owned(), value);
        if let Some(index) = self.values.get(&key) {
            return Ok(*index);
        }
        let sort_id = self.sort(sort)?;
        let index = self.append(pb::Node {
            sort_id,
            ..Default::default()
        })?;
        self.values.insert(key, index);
        self.pending.push((sort.clone(), value, index));
        Ok(index)
    }

    fn close_values(&mut self) -> Result<(), egglog::Error> {
        use pb::primitive_value::Value as V;
        while let Some((sort, value, index)) = self.pending.pop() {
            let custom = self
                .session
                .extension
                .map(|extension| {
                    extension.encode_observed_custom_value(self.session.graph, &sort, value)
                })
                .transpose()
                .map_err(egglog::Error::BackendError)?
                .flatten();
            let payload = if let Some(custom) = custom {
                // Extension inspection is inert; no unknown reconstruction is
                // invoked just to discover whether a value has a codec.
                if !custom.args.is_empty() {
                    return Err(egglog::Error::BackendError(
                        "observed custom values currently require a leaf codec".into(),
                    ));
                }
                V::Custom(custom)
            } else if sort.is_container_sort() {
                use std::any::TypeId;
                let actual = sort.value_type();
                let family = self.program.sorts
                    [self.program.nodes[index as usize].sort_id as usize]
                    .kind
                    .as_ref();
                match family {
                    Some(pb::sort::Kind::Func(_))
                        if actual == Some(TypeId::of::<egglog::sort::FunctionContainer>())
                            && sort.clone().as_arc_any().is::<egglog::sort::FunctionSort>() => {}
                    Some(pb::sort::Kind::Primitive(_)) => {
                        value::container_kind(
                            &sort,
                            &self.program.sorts
                                [self.program.nodes[index as usize].sort_id as usize],
                        )
                        .map_err(egglog::Error::BackendError)?;
                    }
                    _ => {
                        return Err(egglog::Error::BackendError(format!(
                            "Freeze has no inert container codec for {}",
                            sort.name()
                        )));
                    }
                }
                let native_children = self.session.graph.container_inner_values(&sort, value);
                let children = native_children
                    .iter()
                    .map(|(sort, value)| self.value(sort, *value))
                    .collect::<Result<Vec<_>, _>>()?;
                let family = self.program.sorts
                    [self.program.nodes[index as usize].sort_id as usize]
                    .kind
                    .as_ref();
                match family {
                    Some(pb::sort::Kind::Func(_))
                        if actual == Some(TypeId::of::<egglog::sort::FunctionContainer>()) =>
                    {
                        let name = self
                            .session
                            .graph
                            .export_function_value_target(&sort, value)
                            .map_err(egglog::Error::BackendError)?;
                        let name = self.session.names.callables.get(&name).unwrap_or(&name);
                        self.session
                            .lambdas
                            .observe(name, &children, &mut self.program)
                            .map_err(egglog::Error::BackendError)?
                            .and_then(|value| value.value)
                            .unwrap_or_else(|| {
                                V::PartialCall(pb::Call {
                                    func: name.clone(),
                                    args: children,
                                })
                            })
                    }
                    Some(pb::sort::Kind::Primitive(_)) => value::container_payload(
                        &sort,
                        &self.program.sorts[self.program.nodes[index as usize].sort_id as usize],
                        &children,
                        &self.program.nodes,
                    )
                    .map_err(egglog::Error::BackendError)?,
                    _ => {
                        return Err(egglog::Error::BackendError(format!(
                            "Freeze has no inert container codec for {}",
                            sort.name()
                        )));
                    }
                }
            } else {
                let family = match &self.program.sorts
                    [self.program.nodes[index as usize].sort_id as usize]
                    .kind
                {
                    Some(pb::sort::Kind::Primitive(family)) if family.args.is_empty() => family,
                    _ => {
                        return Err(egglog::Error::BackendError(
                            "Freeze scalar has a non-leaf sort".into(),
                        ));
                    }
                };
                if !self
                    .session
                    .graph
                    .get_sort_by_name(&family.name)
                    .is_some_and(|registered| {
                        registered.clone().as_arc_any().as_ref().type_id()
                            == sort.clone().as_arc_any().as_ref().type_id()
                    })
                {
                    return Err(egglog::Error::BackendError(format!(
                        "Freeze has no inert value codec for {}",
                        sort.name()
                    )));
                }
                let scalar =
                    value::Scalar::reflect(self.session.graph, &sort, value).ok_or_else(|| {
                        egglog::Error::BackendError(format!(
                            "Freeze has no inert value codec for {}",
                            sort.name()
                        ))
                    })?;
                let encoded = scalar.encode().map_err(egglog::Error::BackendError)?;
                value::Scalar::decode(Some(&family.name), &encoded)
                    .map_err(egglog::Error::BackendError)?;
                encoded.value.expect("scalar codec supplies a value")
            };
            self.program.nodes[index as usize].kind =
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(payload),
                }));
        }
        Ok(())
    }
}

pub(super) fn export(
    session: View<'_>,
    registry: &rules::Registry,
) -> Result<pb::EGraphSnapshot, egglog::Error> {
    let mut observation = observation(session, &[])?;
    let mut sorts = Vec::new();
    let cost_sort = session
        .graph
        .export_sort(session.graph.get_sort_by_name("i64").unwrap(), &mut sorts)
        .map_err(egglog::Error::BackendError)?;
    let cost_sort = crate::builtin::import_sort(&sorts, cost_sort, &mut observation.program.sorts)
        .map_err(egglog::Error::BackendError)?;
    registry
        .reconstruct(&mut observation.program)
        .map_err(egglog::Error::BackendError)?;
    Ok(pb::EGraphSnapshot {
        options: Some(pb::EGraphOptions {
            cost_sort: Some(cost_sort),
            execution_mode: session.mode.into(),
            seminaive: Some(session.graph.seminaive),
        }),
        program: Some(observation.program),
    })
}

pub(super) fn observation(
    session: View<'_>,
    roots: &[(ArcSort, Value)],
) -> Result<cost_model::Observation, egglog::Error> {
    if session.mode != pb::ExecutionMode::Normal {
        return Err(egglog::Error::BackendError(
            "Freeze currently requires normal execution mode".into(),
        ));
    }
    // Builtins are a backend environment, not graph state. The session retains
    // every installed user body, including dependencies and exact diagnostics.
    let definitions = session
        .lambdas
        .export_definitions(session.definitions)
        .map_err(egglog::Error::BackendError)?;
    let mut export = Export {
        session,
        program: definitions,
        classes: HashMap::new(),
        canonical: |sort: &ArcSort, value| session.graph.value_to_class_id(sort, value).to_string(),
        values: HashMap::new(),
        pending: vec![],
    };
    export.program.commands.clear();
    let tables_to_export: Vec<_> = declarations(&export.program)
        .filter_map(|declaration| match declaration {
            Declaration::Constructor(c) => Some((c.name.clone(), false, true)),
            Declaration::Function(f) => Some((f.name.clone(), false, false)),
            Declaration::Relation(r) => Some((r.name.clone(), true, true)),
            Declaration::UserDefinedPrimitive(_) => None,
        })
        .collect();
    let mut tables = HashSet::new();
    let mut relation_sorts = HashSet::new();
    for (name, relation, constructor) in &tables_to_export {
        let native = native_name("call", name);
        let function = session.graph.get_function(&native).ok_or_else(|| {
            egglog::Error::BackendError(format!("Freeze declaration has no native table {name}"))
        })?;
        if *relation {
            relation_sorts.insert(function.func_type().output.name().to_owned());
        }
        tables.insert(native);
        if *constructor {
            let cost_table = crate::set_cost::get_cost_table_name(&native_name("call", name));
            if session.graph.get_function(&cost_table).is_some() {
                tables.insert(cost_table);
            }
        }
    }
    let bindings: Vec<_> = export
        .program
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(index, node)| {
            if let Some(pb::node::Kind::Binding(name)) = &node.kind {
                Some((index as u32, native_name("binding", name)))
            } else {
                None
            }
        })
        .collect();
    tables.extend(bindings.iter().map(|(_, name)| name.clone()));
    for (name, _) in session.graph.functions_iter() {
        if !tables.contains(name) {
            return Err(egglog::Error::BackendError(format!(
                "Freeze cannot export native table without canonical declaration {name}"
            )));
        }
    }
    // Reserve every class before following any row or container reference.
    for (name, value) in session.graph.materialized_eq_classes() {
        if relation_sorts.contains(name.as_ref()) {
            continue;
        }
        let sort = session.graph.get_sort_by_name(&name).ok_or_else(|| {
            egglog::Error::BackendError(format!("Freeze unknown native equality sort {name}"))
        })?;
        let sort_id = export.sort(sort)?;
        let index = export.append(pb::Node {
            sort_id,
            kind: Some(pb::node::Kind::Eq(pb::Eq { members: vec![] })),
        })?;
        export
            .classes
            .insert((export.canonical)(sort, value), index);
        export.program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Term(index)),
            })),
        });
    }
    let mut row_commands = vec![];
    let mut assigned_costs = vec![];
    let mut subsumed = vec![];
    for (name, relation, constructor) in tables_to_export {
        let name = &name;
        let native = native_name("call", name);
        let signature = session.graph.get_function(&native).unwrap().func_type();
        let mut rows = vec![];
        if constructor {
            session.graph.constructor_enodes(&native, |row| {
                rows.push((row.children.to_vec(), row.eclass, row.subsumed))
            })?;
        } else {
            session.graph.function_entries(&native, |row| {
                rows.push((row.inputs.to_vec(), row.output, row.subsumed))
            })?;
        }
        for (args, value, is_subsumed) in rows {
            let assigned_cost = if constructor && !relation {
                let cost_table = crate::set_cost::get_cost_table_name(&native);
                if session.graph.get_function(&cost_table).is_some() {
                    session.graph.read(|state| {
                        egglog::Read::lookup(&state, &cost_table, egglog::RawValues(args.clone()))
                    })?
                } else {
                    None
                }
            } else {
                None
            };
            let args = signature
                .input
                .iter()
                .zip(args)
                .map(|(sort, value)| export.value(sort, value))
                .collect::<Result<Vec<_>, _>>()?;
            let call = pb::Call {
                func: name.clone(),
                args,
            };
            if let Some(cost) = assigned_cost {
                let cost = export.value(session.graph.get_sort_by_name("i64").unwrap(), cost)?;
                assigned_costs.push(pb::action::Kind::SetCost(pb::SetCost {
                    target: Some(call.clone()),
                    cost: Some(cost),
                }));
            }
            if constructor {
                let sort = if relation {
                    session.graph.get_sort_by_name("Unit").unwrap()
                } else {
                    &signature.output
                };
                let sort_id = export.sort(sort)?;
                let index = export.append(pb::Node {
                    sort_id,
                    kind: Some(pb::node::Kind::Call(call.clone())),
                })?;
                if relation {
                    row_commands.push(pb::action::Kind::Term(index));
                } else {
                    let class = export.value(sort, value)?;
                    let Some(pb::node::Kind::Eq(union)) =
                        &mut export.program.nodes[class as usize].kind
                    else {
                        unreachable!("reserved class")
                    };
                    union.members.push(index);
                }
                if is_subsumed {
                    if relation {
                        return Err(egglog::Error::BackendError(
                            "Freeze cannot represent a subsumed relation row".into(),
                        ));
                    }
                    subsumed.push(pb::action::Kind::Subsume(call));
                }
            } else {
                if is_subsumed {
                    return Err(egglog::Error::BackendError(
                        "Freeze cannot represent a subsumed function row".into(),
                    ));
                }
                row_commands.push(pb::action::Kind::Set(pb::Set {
                    target: Some(call),
                    value: Some(export.value(&signature.output, value)?),
                }));
            }
        }
    }
    let mut binding_commands = vec![];
    for (binding, name) in bindings {
        let function = session.graph.get_function(&name).ok_or_else(|| {
            egglog::Error::BackendError(format!("Freeze binding has no native slot {name}"))
        })?;
        let sort = function.func_type().output.clone();
        let mut values = vec![];
        session
            .graph
            .function_entries(&name, |row| values.push(row.output))?;
        for value in values {
            let value = export.value(&sort, value)?;
            binding_commands.push(pb::Command {
                kind: Some(pb::command::Kind::Let(pb::Let {
                    binding: Some(binding),
                    value: Some(value),
                })),
            });
        }
    }
    // Evaluated literal/container roots need not occur in any stored row.
    for (sort, value) in roots {
        export.value(sort, *value)?;
    }
    export.close_values()?;
    export.program.commands.extend(
        row_commands
            .into_iter()
            .chain(assigned_costs)
            .chain(subsumed)
            .map(|kind| pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action { kind: Some(kind) })),
            }),
    );
    export.program.commands.extend(binding_commands);
    let calls = export
        .program
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(index, node)| {
            let Some(pb::node::Kind::Call(call)) = &node.kind else {
                return None;
            };
            Some(((call.func.clone(), call.args.clone()), index as u32))
        })
        .collect();
    Ok(cost_model::Observation {
        program: export.program,
        values: export.values,
        classes: export.classes,
        calls,
        names: session.names.callables.clone(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::protobuf::fixtures::Observed;

    fn create(engine: &mut Engine, mode: pb::ExecutionMode) -> u64 {
        let request = pb::CreateEGraphRequest {
            sorts: vec![pb::Sort {
                kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
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
        };
        pb::CreateEGraphResponse::decode(
            engine.create(&request.encode_to_vec()).unwrap().as_slice(),
        )
        .unwrap()
        .egraph_id
    }

    fn run(engine: &mut Engine, id: u64, program: pb::Program) -> Observed {
        let request = pb::RunProgramRequest {
            egraph_id: id,
            program: Some(program),
            diagnostics: false,
        };
        Observed::from_frames(
            (engine.run(&request.encode_to_vec()).unwrap())
                .iter()
                .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()),
        )
    }

    #[test]
    fn empty_snapshot_only_keeps_cost_sort() {
        let mut engine = Engine::default();
        let id = create(&mut engine, pb::ExecutionMode::Normal);
        let response = run(
            &mut engine,
            id,
            pb::Program {
                commands: vec![pb::Command {
                    kind: Some(pb::command::Kind::Freeze(pb::Freeze {})),
                }],
                ..Default::default()
            },
        );
        assert_eq!(response.error, None);
        let Some(pb::command_output::Kind::Snapshot(snapshot)) = &response.output.outputs[0].kind
        else {
            panic!("missing snapshot")
        };
        let program = snapshot.program.as_ref().unwrap();
        assert_eq!(program.sorts.len(), 1);
        assert!(matches!(
            &program.sorts[snapshot.options.as_ref().unwrap().cost_sort.unwrap() as usize].kind,
            Some(pb::sort::Kind::Primitive(family)) if family.name == "i64" && family.args.is_empty()
        ));
        assert!(program.nodes.is_empty());
        assert!(declarations(program).next().is_none());
    }

    #[test]
    fn hidden_tables_remain_in_custom_cost_observation() {
        let mut engine = Engine::default();
        let id = create(&mut engine, pb::ExecutionMode::Normal);
        for phase in source::Source::new(
            None,
            "(sort E) (constructor Hidden () E :internal-hidden)
             (function hidden-f () i64 :no-merge :internal-hidden)
             (Hidden) (set (hidden-f) 9)",
        )
        .unwrap()
        {
            assert_eq!(run(&mut engine, id, phase.unwrap()).error, None);
        }
        // This is the same complete, inert Program supplied to NativeCostModel::start.
        let session = &engine.graphs[&id];
        let observed = observation(
            View {
                graph: &session.graph,
                names: &session.names,
                definitions: &session.definitions,
                lambdas: &session.lambdas,
                mode: session.mode,
                extension: session.extension.as_ref(),
            },
            &[],
        )
        .unwrap();
        let program = &observed.program;
        assert_eq!(program.sorts.len(), 2);
        assert!(program.sorts.iter().any(|sort| matches!(
            &sort.kind, Some(pb::sort::Kind::Eq(name)) if name == "E"
        )));
        assert!(program.sorts.iter().any(|sort| matches!(
            &sort.kind, Some(pb::sort::Kind::Primitive(family))
                if family.name == "i64" && family.args.is_empty()
        )));
        assert_eq!(
            declarations(program)
                .filter(|declaration| matches!(
                    declaration,
                    Declaration::Constructor(pb::Constructor { hidden: true, .. })
                        | Declaration::Function(pb::Function { hidden: true, .. })
                ))
                .count(),
            2
        );
        assert!(program.nodes.iter().any(|node| matches!(&node.kind,
            Some(pb::node::Kind::Call(call)) if call.func == "Hidden" && call.args.is_empty())));
        assert!(program.commands.iter().any(|command| matches!(&command.kind,
            Some(pb::command::Kind::Action(pb::Action { kind: Some(pb::action::Kind::Set(set)), .. }))
            if set.target.as_ref().is_some_and(|call| call.func == "hidden-f")
                && matches!(program.nodes[set.value.unwrap() as usize].kind,
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue { value: Some(pb::primitive_value::Value::I64(9)) }))))));
    }

    #[test]
    fn unstored_literal_roots_keep_inert_native_sort_identity() {
        use pb::primitive_value::Value as V;

        let mut engine = Engine::default();
        let id = create(&mut engine, pb::ExecutionMode::Normal);
        let session = engine.graphs.get_mut(&id).unwrap();
        for (literal, expected) in [
            (Literal::Int(7), V::I64(7)),
            (Literal::Float(1.25.into()), V::F64Bits(1.25f64.to_bits())),
            (Literal::String("root".into()), V::String("root".into())),
            (Literal::Bool(true), V::Bool(true)),
            (Literal::Unit, V::Unit(pb::Unit {})),
        ] {
            let root = session
                .graph
                .eval_expr(&Expr::Lit(span!(), literal))
                .unwrap();
            let observed = observation(
                View {
                    graph: &session.graph,
                    names: &session.names,
                    definitions: &session.definitions,
                    lambdas: &session.lambdas,
                    mode: session.mode,
                    extension: session.extension.as_ref(),
                },
                std::slice::from_ref(&root),
            )
            .unwrap();
            let index = observed.values[&(root.0.name().to_owned(), root.1)];
            assert_eq!(observed.program.sorts.len(), 1);
            assert!(matches!(
                &observed.program.sorts[0].kind,
                Some(pb::sort::Kind::Primitive(family))
                    if family.name == root.0.name() && family.args.is_empty()
            ));
            assert_eq!(
                observed.program.nodes[index as usize].kind,
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(expected),
                }))
            );
        }

        session
            .graph
            .parse_and_run_program(None, "(sort V (Vec i64)) (sort VV (Vec V))")
            .unwrap();
        let root = session
            .graph
            .eval_expr(&Expr::Call(
                span!(),
                "vec-of".into(),
                vec![Expr::Call(
                    span!(),
                    "vec-of".into(),
                    vec![Expr::Lit(span!(), Literal::Int(7))],
                )],
            ))
            .unwrap();
        let observed = observation(
            View {
                graph: &session.graph,
                names: &session.names,
                definitions: &session.definitions,
                lambdas: &session.lambdas,
                mode: session.mode,
                extension: session.extension.as_ref(),
            },
            std::slice::from_ref(&root),
        )
        .unwrap();
        assert_eq!(observed.program.sorts.len(), 3);
        let index = observed.values[&(root.0.name().to_owned(), root.1)];
        let Some(pb::sort::Kind::Primitive(outer)) =
            &observed.program.sorts[observed.program.nodes[index as usize].sort_id as usize].kind
        else {
            panic!("outer Vec sort")
        };
        assert_eq!(outer.name, "Vec");
        let [inner] = outer.args.as_slice() else {
            panic!("one outer Vec type argument")
        };
        let Some(pb::sort::Kind::Primitive(inner)) = &observed.program.sorts[*inner as usize].kind
        else {
            panic!("inner Vec sort")
        };
        assert_eq!(inner.name, "Vec");
        let [element] = inner.args.as_slice() else {
            panic!("one inner Vec type argument")
        };
        assert!(matches!(
            &observed.program.sorts[*element as usize].kind,
            Some(pb::sort::Kind::Primitive(family)) if family.name == "i64" && family.args.is_empty()
        ));
    }

    // Two classes: one has three alternatives and a self-cycle; the other has
    // no producers. Container slots repeat the first class around the second.
    fn fixture() -> pb::Program {
        use pb::{action::Kind as A, node::Kind as N, primitive_value::Value as V};
        pb::Program {
            sorts: vec![
                pb::Sort {
                    kind: Some(pb::sort::Kind::Eq("State".into())),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
                        name: "i64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
                        name: "Unit".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
                        name: "Vec".into(),
                        args: vec![0],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
                        name: "f64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
                        name: "Vec".into(),
                        args: vec![1],
                    })),
                    ..Default::default()
                },
            ],
            constructors: vec![
                pb::Constructor {
                    name: "Num".into(),
                    inputs: vec![1],
                    output: 0,
                    ..Default::default()
                },
                pb::Constructor {
                    name: "Next".into(),
                    inputs: vec![0],
                    output: 0,
                    ..Default::default()
                },
                pb::Constructor {
                    name: "Float".into(),
                    inputs: vec![4],
                    output: 0,
                    ..Default::default()
                },
            ],
            functions: vec![
                pb::Function {
                    hidden: false,
                    name: "score".into(),
                    inputs: vec![0],
                    output: 1,
                    merge: None,
                    ..Default::default()
                },
                pb::Function {
                    hidden: false,
                    name: "store".into(),
                    inputs: vec![],
                    output: 3,
                    merge: None,
                    ..Default::default()
                },
                pb::Function {
                    hidden: false,
                    name: "ready".into(),
                    inputs: vec![],
                    output: 2,
                    merge: None,
                    ..Default::default()
                },
                pb::Function {
                    hidden: false,
                    name: "computed".into(),
                    inputs: vec![],
                    output: 1,
                    merge: None,
                    ..Default::default()
                },
                pb::Function {
                    hidden: false,
                    name: "computed_vector".into(),
                    inputs: vec![],
                    output: 5,
                    merge: None,
                    ..Default::default()
                },
            ],
            relations: vec![pb::Relation {
                name: "marked".into(),
                inputs: vec![0],
                ..Default::default()
            }],
            user_defined_primitives: vec![
                pb::UserDefinedPrimitive {
                    name: "saved_identity".into(),
                    inputs: vec![1],
                    output: 1,
                    body: Some(10),
                    ..Default::default()
                },
                pb::UserDefinedPrimitive {
                    name: "saved_vector".into(),
                    inputs: vec![],
                    output: 5,
                    body: Some(12),
                    ..Default::default()
                },
            ],
            nodes: vec![
                (
                    0,
                    N::Eq(pb::Eq {
                        members: vec![1, 2, 9],
                    }),
                ),
                (
                    0,
                    N::Call(pb::Call {
                        func: "Num".into(),
                        args: vec![4],
                    }),
                ),
                (
                    0,
                    N::Call(pb::Call {
                        func: "Next".into(),
                        args: vec![0],
                    }),
                ),
                (0, N::Eq(pb::Eq { members: vec![] })),
                (
                    1,
                    N::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(V::I64(-3)),
                    }),
                ),
                (
                    2,
                    N::Call(pb::Call {
                        func: "marked".into(),
                        args: vec![0],
                    }),
                ),
                (
                    3,
                    N::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(V::Vec(pb::ValueList {
                            items: vec![0, 3, 0],
                        })),
                    }),
                ),
                (
                    2,
                    N::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(V::Unit(pb::Unit {})),
                    }),
                ),
                (
                    4,
                    N::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(V::F64Bits((-0.0f64).to_bits())),
                    }),
                ),
                (
                    0,
                    N::Call(pb::Call {
                        func: "Float".into(),
                        args: vec![8],
                    }),
                ),
                (1, N::Var("_0".into())),
                (
                    1,
                    N::Call(pb::Call {
                        func: "saved_identity".into(),
                        args: vec![4],
                    }),
                ),
                (
                    5,
                    N::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(V::Vec(pb::ValueList { items: vec![4, 4] })),
                    }),
                ),
                (
                    5,
                    N::Call(pb::Call {
                        func: "saved_vector".into(),
                        args: vec![],
                    }),
                ),
            ]
            .into_iter()
            .map(|(sort_id, kind)| pb::Node {
                sort_id,
                kind: Some(kind),
            })
            .collect(),
            commands: vec![
                A::Term(0),
                A::Term(3),
                A::Set(pb::Set {
                    target: Some(pb::Call {
                        func: "score".into(),
                        args: vec![0],
                    }),
                    value: Some(4),
                }),
                A::Term(5),
                A::Set(pb::Set {
                    target: Some(pb::Call {
                        func: "store".into(),
                        args: vec![],
                    }),
                    value: Some(6),
                }),
                A::Set(pb::Set {
                    target: Some(pb::Call {
                        func: "ready".into(),
                        args: vec![],
                    }),
                    value: Some(7),
                }),
                A::Subsume(pb::Call {
                    func: "Num".into(),
                    args: vec![4],
                }),
                A::Set(pb::Set {
                    target: Some(pb::Call {
                        func: "computed".into(),
                        args: vec![],
                    }),
                    value: Some(11),
                }),
                A::Set(pb::Set {
                    target: Some(pb::Call {
                        func: "computed_vector".into(),
                        args: vec![],
                    }),
                    value: Some(13),
                }),
            ]
            .into_iter()
            .map(|kind| pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action { kind: Some(kind) })),
            })
            .chain([pb::Command {
                kind: Some(pb::command::Kind::Freeze(pb::Freeze {})),
            }])
            .collect(),
            ..Default::default()
        }
    }

    fn assert_forest(snapshot: &pb::EGraphSnapshot) {
        use pb::{action::Kind as A, node::Kind as N, primitive_value::Value as V};
        let program = snapshot.program.as_ref().unwrap();
        assert_eq!(program.sorts.len(), 6);
        assert_eq!(
            snapshot.options.as_ref().unwrap().execution_mode,
            pb::ExecutionMode::Normal as i32
        );
        assert_eq!(
            declarations(program)
                .filter(|d| matches!(d,
            Declaration::UserDefinedPrimitive(p) if p.name == "saved_identity"))
                .count(),
            1
        );
        assert!(declarations(program).all(|d| !matches!(d,
            Declaration::UserDefinedPrimitive(p) if p.name.starts_with("__egglog"))));
        let saved = declarations(program)
            .find_map(|d| match d {
                Declaration::UserDefinedPrimitive(p) if p.name == "saved_vector" => Some(p),
                _ => None,
            })
            .unwrap();
        assert!(matches!(
            &program.nodes[saved.body.unwrap() as usize].kind,
            Some(N::PrimitiveValue(pb::PrimitiveValue {
                value: Some(V::Vec(_))
            }))
        ));
        let classes: Vec<_> = program
            .commands
            .iter()
            .filter_map(|command| match &command.kind {
                Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(A::Term(index)),
                    ..
                })) if matches!(program.nodes[*index as usize].kind, Some(N::Eq(_))) => {
                    Some(*index)
                }
                _ => None,
            })
            .collect();
        assert_eq!(
            classes.len(),
            2,
            "relation row IDs are not equality classes"
        );
        let full = *classes.iter().find(|index| matches!(&program.nodes[**index as usize].kind, Some(N::Eq(u)) if u.members.len() == 3)).unwrap();
        let empty = *classes.iter().find(|index| matches!(&program.nodes[**index as usize].kind, Some(N::Eq(u)) if u.members.is_empty())).unwrap();
        let Some(N::Eq(union)) = &program.nodes[full as usize].kind else {
            unreachable!()
        };
        assert!(union.members.iter().any(|index| matches!(&program.nodes[*index as usize].kind, Some(N::Call(c)) if c.func == "Next" && c.args == [full])));
        let mut function_count = 0;
        let mut relation_count = 0;
        let mut subsumed_count = 0;
        for command in &program.commands {
            let Some(pb::command::Kind::Action(action)) = &command.kind else {
                panic!("snapshot must contain only actions")
            };
            match &action.kind {
                Some(A::Set(set)) => {
                    function_count += 1;
                    let node = &program.nodes[set.value.unwrap() as usize];
                    if set.target.as_ref().unwrap().func == "store" {
                        assert!(
                            matches!(&node.kind, Some(N::PrimitiveValue(pb::PrimitiveValue { value: Some(V::Vec(v)) })) if v.items == [full, empty, full])
                        );
                    }
                    if set.target.as_ref().unwrap().func == "ready" {
                        assert!(matches!(
                            &node.kind,
                            Some(N::PrimitiveValue(pb::PrimitiveValue {
                                value: Some(V::Unit(_))
                            }))
                        ));
                    }
                }
                Some(A::Term(index)) if matches!(&program.nodes[*index as usize].kind, Some(N::Call(c)) if c.func == "marked") => {
                    relation_count += 1
                }
                Some(A::Subsume(call)) => {
                    assert_eq!(call.func, "Num");
                    subsumed_count += 1;
                }
                _ => (),
            }
        }
        assert_eq!((function_count, relation_count, subsumed_count), (5, 1, 1));
        assert!(program.nodes.iter().any(|n| matches!(&n.kind, Some(N::PrimitiveValue(pb::PrimitiveValue { value: Some(V::F64Bits(bits)) })) if *bits == (-0.0f64).to_bits())));
        assert!(program.nodes.iter().any(|n| matches!(
            &n.kind,
            Some(N::PrimitiveValue(pb::PrimitiveValue {
                value: Some(V::I64(-3))
            }))
        )));
    }

    #[test]
    fn bytes_preserve_empty_classes_cycles_rows_and_reconstruct() {
        let mut engine = Engine::default();
        let id = create(&mut engine, pb::ExecutionMode::Normal);
        let response = run(&mut engine, id, fixture());
        assert!(response.error.is_none(), "{:?}", response.error);
        let Some(pb::command_output::Kind::Snapshot(snapshot)) =
            &response.output.outputs.last().unwrap().kind
        else {
            panic!("missing snapshot")
        };
        assert_forest(snapshot);
        let next = create(&mut engine, pb::ExecutionMode::Normal);
        let mut program = snapshot.program.clone().unwrap();
        program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Freeze(pb::Freeze {})),
        });
        let restored = run(&mut engine, next, program);
        assert!(restored.error.is_none(), "{:?}", restored.error);
        let Some(pb::command_output::Kind::Snapshot(snapshot)) =
            &restored.output.outputs.last().unwrap().kind
        else {
            panic!("missing restored snapshot")
        };
        assert_forest(snapshot);
    }

    #[test]
    fn nonnormal_modes_fail_without_partial_snapshot() {
        for mode in [
            pb::ExecutionMode::TermEncoding,
            pb::ExecutionMode::Proofs,
            pb::ExecutionMode::ProofTesting,
        ] {
            let mut engine = Engine::default();
            let id = create(&mut engine, mode);
            let response = run(
                &mut engine,
                id,
                pb::Program {
                    commands: vec![pb::Command {
                        kind: Some(pb::command::Kind::Freeze(pb::Freeze {})),
                    }],
                    ..Default::default()
                },
            );
            let error = response.error.unwrap();
            assert_eq!(error.code, pb::ErrorCode::RuntimeFailure as i32);
            assert_eq!(error.location.unwrap().path, [0]);
            assert!(response.output.outputs.is_empty());
        }
    }
}
