//! Inert state export into the existing reconstruction Program.
use super::*;
use std::hash::Hash;

// The only retained graph is the generated Program. These maps assign wire
// locations to native values; the queue closes container edges iteratively.
struct Export<'a, K, F> {
    session: &'a Session,
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
            let payload = if sort.is_container_sort() {
                use std::any::TypeId;
                let actual = sort.value_type();
                let family = self.program.sorts
                    [self.program.nodes[index as usize].sort_id as usize]
                    .kind
                    .as_ref();
                let admitted = match family {
                    Some(pb::sort::Kind::Func(_)) => {
                        actual == Some(TypeId::of::<egglog::sort::FunctionContainer>())
                            && sort.clone().as_arc_any().is::<egglog::sort::FunctionSort>()
                    }
                    Some(pb::sort::Kind::Family(f)) => match f.name.as_str() {
                        "Vec" => actual == Some(TypeId::of::<egglog::sort::VecContainer>()),
                        "Set" => actual == Some(TypeId::of::<egglog::sort::SetContainer>()),
                        "MultiSet" => {
                            actual == Some(TypeId::of::<egglog::sort::MultiSetContainer>())
                        }
                        "Pair" => actual == Some(TypeId::of::<egglog::sort::PairContainer>()),
                        "Map" => actual == Some(TypeId::of::<egglog::sort::MapContainer>()),
                        "Maybe" => actual == Some(TypeId::of::<crate::maybe::MaybeContainer>()),
                        _ => false,
                    },
                    _ => false,
                };
                if !admitted {
                    return Err(egglog::Error::BackendError(format!(
                        "Freeze has no inert container codec for {}",
                        sort.name()
                    )));
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
                        V::PartialCall(pb::Call {
                            func: self
                                .session
                                .names
                                .callables
                                .get(&name)
                                .unwrap_or(&name)
                                .clone(),
                            args: children,
                        })
                    }
                    Some(pb::sort::Kind::Family(f)) => match (f.name.as_str(), actual) {
                        ("Vec", Some(t)) if t == TypeId::of::<egglog::sort::VecContainer>() => {
                            V::Vec(pb::ValueList { items: children })
                        }
                        ("Set", Some(t)) if t == TypeId::of::<egglog::sort::SetContainer>() => {
                            V::Set(pb::ValueList { items: children })
                        }
                        ("MultiSet", Some(t))
                            if t == TypeId::of::<egglog::sort::MultiSetContainer>() =>
                        {
                            V::Multiset(pb::ValueList { items: children })
                        }
                        ("Pair", Some(t))
                            if t == TypeId::of::<egglog::sort::PairContainer>()
                                && children.len() == 2 =>
                        {
                            V::Pair(pb::PairValue {
                                first: Some(children[0]),
                                second: Some(children[1]),
                            })
                        }
                        ("Map", Some(t))
                            if t == TypeId::of::<egglog::sort::MapContainer>()
                                && children.len().is_multiple_of(2) =>
                        {
                            V::Map(pb::MapValue {
                                entries: children
                                    .chunks_exact(2)
                                    .map(|pair| pb::MapEntry {
                                        key: Some(pair[0]),
                                        value: Some(pair[1]),
                                    })
                                    .collect(),
                            })
                        }
                        ("Maybe", Some(t))
                            if t == TypeId::of::<crate::maybe::MaybeContainer>()
                                && children.len() <= 1 =>
                        {
                            V::Maybe(pb::MaybeValue {
                                value: children.first().copied(),
                            })
                        }
                        _ => {
                            return Err(egglog::Error::BackendError(format!(
                                "Freeze has no inert container codec for {}",
                                sort.name()
                            )));
                        }
                    },
                    _ => {
                        return Err(egglog::Error::BackendError(format!(
                            "Freeze has no inert container codec for {}",
                            sort.name()
                        )));
                    }
                }
            } else {
                // Invoke only known inert base reconstructions. An arbitrary
                // host sort's default reconstruction may panic or materialize.
                use std::any::TypeId;
                let actual = sort.value_type();
                let family = self.program.sorts
                    [self.program.nodes[index as usize].sort_id as usize]
                    .kind
                    .as_ref();
                let expected = match family {
                    Some(pb::sort::Kind::Family(f)) if f.args.is_empty() => match f.name.as_str() {
                        "Unit" => Some(TypeId::of::<()>()),
                        "bool" => Some(TypeId::of::<bool>()),
                        "i64" => Some(TypeId::of::<i64>()),
                        "f64" => Some(TypeId::of::<egglog::sort::F>()),
                        "String" => Some(TypeId::of::<egglog::sort::S>()),
                        "BigInt" => Some(TypeId::of::<egglog::sort::Z>()),
                        "BigRat" => Some(TypeId::of::<egglog::sort::Q>()),
                        "Rational" => Some(TypeId::of::<crate::rational::R>()),
                        _ => None,
                    },
                    _ => None,
                };
                let registered = match family {
                    Some(pb::sort::Kind::Family(f)) => self.session.graph.get_sort_by_name(&f.name),
                    _ => None,
                };
                if expected.is_none()
                    || expected != actual
                    || !registered.is_some_and(|registered| Arc::ptr_eq(registered, &sort))
                {
                    return Err(egglog::Error::BackendError(format!(
                        "Freeze has no inert value codec for {}",
                        sort.name()
                    )));
                }
                let mut terms = TermDag::default();
                let term = self
                    .session
                    .graph
                    .reconstruct_base_value(&sort, value, &mut terms);
                if let Some(number) =
                    encode_exact_number(&terms, term, &sort).map_err(egglog::Error::BackendError)?
                {
                    number
                } else if let Term::Lit(literal) = terms.get(term) {
                    match literal {
                        Literal::Int(n) => V::I64(*n),
                        Literal::Float(n) => V::F64Bits(n.0.to_bits()),
                        Literal::String(s) => V::String(s.clone()),
                        Literal::Bool(b) => V::Bool(*b),
                        Literal::Unit => V::Unit(pb::Unit {}),
                    }
                } else {
                    return Err(egglog::Error::BackendError(format!(
                        "Freeze base reconstruction is not inert data for {}",
                        sort.name()
                    )));
                }
            };
            self.program.nodes[index as usize].kind =
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(payload),
                }));
        }
        Ok(())
    }
}

pub(super) fn export(session: &mut Session) -> Result<pb::EGraphSnapshot, egglog::Error> {
    if session.mode != pb::ExecutionMode::Normal {
        return Err(egglog::Error::BackendError(
            "Freeze currently requires normal execution mode".into(),
        ));
    }
    let mut catalog = session
        .graph
        .type_info()
        .portable_builtin_catalog()
        .map_err(egglog::Error::BackendError)?;
    // Native program-defined primitives retain native callable/sort names.
    // Reuse the session's exact projection receipts before reconciling their
    // portable code with the original authored declarations.
    for sort in &mut catalog.definitions.sorts {
        if let Some(pb::sort::Kind::Eq(name)) = &mut sort.kind
            && let Some(logical) = session.names.sorts.get(name)
        {
            *name = logical.clone();
        }
    }
    catalog.definitions.declarations.retain_mut(|declaration| {
        let name = match &mut declaration.kind {
            Some(pb::declaration::Kind::EqSort(s)) => {
                if let Some(logical) = session.names.sorts.get(&s.name) {
                    s.name = logical.clone();
                }
                return true;
            }
            Some(pb::declaration::Kind::Constructor(c)) => &mut c.name,
            Some(pb::declaration::Kind::Function(f)) => &mut f.name,
            Some(pb::declaration::Kind::Relation(r)) => &mut r.name,
            Some(pb::declaration::Kind::Primitive(p)) => {
                if let Some(logical) = session.names.callables.get(&p.name)
                    && session.definitions.declarations.iter().any(|declaration| {
                        matches!(&declaration.kind, Some(pb::declaration::Kind::Primitive(saved)) if &saved.name == logical)
                    })
                {
                    // This receipt identifies code whose exact authored body
                    // we already retain. Execution-only container/numeric
                    // lowering need not be structurally identical to it.
                    return false;
                }
                &mut p.name
            }
            _ => return true,
        };
        if let Some(logical) = session.names.callables.get(name) {
            *name = logical.clone();
        }
        true
    });
    for node in &mut catalog.definitions.nodes {
        let call = match &mut node.kind {
            Some(pb::node::Kind::Call(c) | pb::node::Kind::GetCost(c)) => c,
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::PartialCall(c)),
            })) => c,
            _ => continue,
        };
        if let Some(logical) = session.names.callables.get(&call.func) {
            call.func = logical.clone();
        }
    }
    let gaps = catalog
        .undescribed_primitives
        .into_iter()
        .chain(catalog.undescribed_families)
        .chain(catalog.undescribed_family_primitives)
        .chain(catalog.undescribed_sorts)
        .collect::<Vec<_>>();
    if !gaps.is_empty() {
        return Err(egglog::Error::BackendError(format!(
            "Freeze cannot export definitions without canonical descriptors: {}",
            gaps.join(", ")
        )));
    }
    let mut definitions = session.definitions.clone();
    crate::builtin::definitions::reconcile_declarations(&catalog.definitions, &mut definitions)
        .map_err(egglog::Error::BackendError)?;
    let mut export = Export {
        session,
        program: definitions,
        classes: HashMap::new(),
        canonical: |sort: &ArcSort, value| session.graph.value_to_class_id(sort, value),
        values: HashMap::new(),
        pending: vec![],
    };
    export.program.commands.clear();
    let declarations = export.program.declarations.clone();
    let mut tables = HashSet::new();
    let mut relation_sorts = HashSet::new();
    for declaration in &declarations {
        let name = match &declaration.kind {
            Some(pb::declaration::Kind::Constructor(c)) => &c.name,
            Some(pb::declaration::Kind::Function(f)) => &f.name,
            Some(pb::declaration::Kind::Relation(r)) => &r.name,
            _ => continue,
        };
        let native = native_name("call", name);
        let function = session.graph.get_function(&native).ok_or_else(|| {
            egglog::Error::BackendError(format!("Freeze declaration has no native table {name}"))
        })?;
        if matches!(declaration.kind, Some(pb::declaration::Kind::Relation(_))) {
            relation_sorts.insert(function.func_type().output.name().to_owned());
        }
        tables.insert(native);
        if matches!(
            declaration.kind,
            Some(pb::declaration::Kind::Constructor(_))
        ) {
            let cost_table = crate::set_cost::get_cost_table_name(&native_name("call", name));
            if session.graph.get_function(&cost_table).is_some() {
                tables.insert(cost_table);
            }
        }
    }
    for (name, _) in session.graph.functions_iter() {
        if !tables.contains(name) {
            return Err(egglog::Error::BackendError(format!(
                "Freeze cannot export native table without canonical declaration {name}"
            )));
        }
    }
    for sort in session.graph.get_arcsorts_by(|_| true) {
        if !relation_sorts.contains(sort.name()) {
            export.sort(&sort)?;
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
            kind: Some(pb::node::Kind::Union(pb::Union { members: vec![] })),
            ..Default::default()
        })?;
        export
            .classes
            .insert((export.canonical)(sort, value), index);
        export.program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Term(index)),
                ..Default::default()
            })),
            ..Default::default()
        });
    }
    let mut row_commands = vec![];
    let mut assigned_costs = vec![];
    let mut subsumed = vec![];
    for declaration in &declarations {
        let (name, relation, constructor) = match &declaration.kind {
            Some(pb::declaration::Kind::Constructor(c)) => (&c.name, false, true),
            Some(pb::declaration::Kind::Function(f)) => (&f.name, false, false),
            Some(pb::declaration::Kind::Relation(r)) => (&r.name, true, true),
            _ => continue,
        };
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
                    ..Default::default()
                })?;
                if relation {
                    row_commands.push(pb::action::Kind::Term(index));
                } else {
                    let class = export.value(sort, value)?;
                    let Some(pb::node::Kind::Union(union)) =
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
    export.close_values()?;
    export.program.commands.extend(
        row_commands
            .into_iter()
            .chain(assigned_costs)
            .chain(subsumed)
            .map(|kind| pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(kind),
                    ..Default::default()
                })),
                ..Default::default()
            }),
    );
    let cost_sort = export.sort(session.graph.get_sort_by_name("i64").unwrap())?;
    Ok(pb::EGraphSnapshot {
        options: Some(pb::EGraphOptions {
            cost_sort: Some(cost_sort),
            execution_mode: session.mode.into(),
        }),
        program: Some(export.program),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create(engine: &mut Engine, mode: pb::ExecutionMode) -> u64 {
        let request = pb::CreateEGraphRequest {
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
        };
        pb::CreateEGraphResponse::decode(
            engine.create(&request.encode_to_vec()).unwrap().as_slice(),
        )
        .unwrap()
        .egraph_id
    }

    fn run(engine: &mut Engine, id: u64, program: pb::Program) -> pb::RunProgramResponse {
        let request = pb::RunProgramRequest {
            egraph_id: id,
            program: Some(program),
            profile: true,
            include_run_reports: false,
        };
        pb::RunProgramResponse::decode(engine.run(&request.encode_to_vec()).unwrap().as_slice())
            .unwrap()
    }

    // Two classes: one has three alternatives and a self-cycle; the other has
    // no producers. Container slots repeat the first class around the second.
    fn fixture() -> pb::Program {
        use pb::{
            action::Kind as A, declaration::Kind as D, node::Kind as N, primitive_value::Value as V,
        };
        pb::Program {
            ir_version: 1,
            sorts: vec![
                pb::Sort {
                    kind: Some(pb::sort::Kind::Eq("State".into())),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "i64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "Unit".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "Vec".into(),
                        args: vec![0],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "f64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "Vec".into(),
                        args: vec![1],
                    })),
                    ..Default::default()
                },
            ],
            declarations: vec![
                D::EqSort(pb::EqSort {
                    name: "State".into(),
                    ..Default::default()
                }),
                D::Constructor(pb::Constructor {
                    name: "Num".into(),
                    inputs: vec![pb::Arg {
                        name: "n".into(),
                        sort: 1,
                    }],
                    output: 0,
                    ..Default::default()
                }),
                D::Constructor(pb::Constructor {
                    name: "Next".into(),
                    inputs: vec![pb::Arg {
                        name: "state".into(),
                        sort: 0,
                    }],
                    output: 0,
                    ..Default::default()
                }),
                D::Constructor(pb::Constructor {
                    name: "Float".into(),
                    inputs: vec![pb::Arg {
                        name: "n".into(),
                        sort: 4,
                    }],
                    output: 0,
                    ..Default::default()
                }),
                D::Function(pb::Function {
                    name: "score".into(),
                    inputs: vec![pb::Arg {
                        name: "state".into(),
                        sort: 0,
                    }],
                    output: 1,
                    merge: None,
                }),
                D::Function(pb::Function {
                    name: "store".into(),
                    inputs: vec![],
                    output: 3,
                    merge: None,
                }),
                D::Function(pb::Function {
                    name: "ready".into(),
                    inputs: vec![],
                    output: 2,
                    merge: None,
                }),
                D::Relation(pb::Relation {
                    name: "marked".into(),
                    inputs: vec![pb::Arg {
                        name: "state".into(),
                        sort: 0,
                    }],
                }),
                D::Primitive(pb::Primitive {
                    name: "saved_identity".into(),
                    inputs: vec![pb::Arg {
                        name: "value".into(),
                        sort: 1,
                    }],
                    output: 1,
                    body: Some(10),
                }),
                D::Function(pb::Function {
                    name: "computed".into(),
                    inputs: vec![],
                    output: 1,
                    merge: None,
                }),
                D::Primitive(pb::Primitive {
                    name: "saved_vector".into(),
                    inputs: vec![],
                    output: 5,
                    body: Some(12),
                }),
                D::Function(pb::Function {
                    name: "computed_vector".into(),
                    inputs: vec![],
                    output: 5,
                    merge: None,
                }),
            ]
            .into_iter()
            .map(|kind| pb::Declaration {
                kind: Some(kind),
                ..Default::default()
            })
            .collect(),
            nodes: vec![
                (
                    0,
                    N::Union(pb::Union {
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
                (0, N::Union(pb::Union { members: vec![] })),
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
                ..Default::default()
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
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(kind),
                    ..Default::default()
                })),
                ..Default::default()
            })
            .chain([pb::Command {
                kind: Some(pb::command::Kind::Freeze(pb::Freeze {})),
                ..Default::default()
            }])
            .collect(),
            rulesets: vec![pb::Ruleset {
                name: Some("retained_empty".into()),
                kind: Some(pb::ruleset::Kind::Rules(pb::RuleList { rules: vec![] })),
                ..Default::default()
            }],
            ..Default::default()
        }
    }

    fn assert_forest(snapshot: &pb::EGraphSnapshot) {
        use pb::{action::Kind as A, node::Kind as N, primitive_value::Value as V};
        let program = snapshot.program.as_ref().unwrap();
        assert_eq!(
            snapshot.options.as_ref().unwrap().execution_mode,
            pb::ExecutionMode::Normal as i32
        );
        assert!(
            program
                .rulesets
                .iter()
                .any(|r| r.name.as_deref() == Some("retained_empty"))
        );
        assert_eq!(
            program
                .declarations
                .iter()
                .filter(|d| matches!(&d.kind,
            Some(pb::declaration::Kind::Primitive(p)) if p.name == "saved_identity"))
                .count(),
            1
        );
        assert!(program.declarations.iter().all(|d| !matches!(&d.kind,
            Some(pb::declaration::Kind::Primitive(p)) if p.name.starts_with("__egglog"))));
        let saved = program
            .declarations
            .iter()
            .find_map(|d| match &d.kind {
                Some(pb::declaration::Kind::Primitive(p)) if p.name == "saved_vector" => Some(p),
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
                })) if matches!(program.nodes[*index as usize].kind, Some(N::Union(_))) => {
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
        let full = *classes.iter().find(|index| matches!(&program.nodes[**index as usize].kind, Some(N::Union(u)) if u.members.len() == 3)).unwrap();
        let empty = *classes.iter().find(|index| matches!(&program.nodes[**index as usize].kind, Some(N::Union(u)) if u.members.is_empty())).unwrap();
        let Some(N::Union(union)) = &program.nodes[full as usize].kind else {
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
            &response.outputs.last().unwrap().kind
        else {
            panic!("missing snapshot")
        };
        assert_forest(snapshot);
        let next = create(&mut engine, pb::ExecutionMode::Normal);
        let mut program = snapshot.program.clone().unwrap();
        program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Freeze(pb::Freeze {})),
            ..Default::default()
        });
        let restored = run(&mut engine, next, program);
        assert!(restored.error.is_none(), "{:?}", restored.error);
        let Some(pb::command_output::Kind::Snapshot(snapshot)) =
            &restored.outputs.last().unwrap().kind
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
                    ir_version: 1,
                    commands: vec![pb::Command {
                        kind: Some(pb::command::Kind::Freeze(pb::Freeze {})),
                        ..Default::default()
                    }],
                    ..Default::default()
                },
            );
            let error = response.error.unwrap();
            assert_eq!(error.code, pb::ErrorCode::EvaluationFailed as i32);
            assert_eq!(error.location.unwrap().path, [0]);
            assert!(response.outputs.is_empty());
        }
    }
}
