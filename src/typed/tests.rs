use super::{
    SortRef, close,
    decl::Callable,
    expr::Expr,
    pb,
    storage::{Arena, DeclarationKind, Packer, Record, Slot, publish},
};
pub(super) use crate::protobuf::fixtures as observations;

use observations::Observed;
use prost::Message;
use std::sync::Arc;

// Shared nominal fixture for canonical-record and private transport tests.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct ActionTerm(pub(super) Expr);
impl super::expr::ValueInput for ActionTerm {
    type Owned = Self;
}
impl From<&ActionTerm> for ActionTerm {
    fn from(value: &ActionTerm) -> Self {
        value.clone()
    }
}
impl super::EgglogValue for ActionTerm {
    fn sort_ref() -> SortRef {
        SortRef::equality("ActionTerm")
    }
    fn expression(&self) -> &Expr {
        &self.0
    }
    fn from_expression(expr: Expr) -> Self {
        Self(expr)
    }
}
impl super::EqualitySort for ActionTerm {}

#[test]
fn function_values_author_computed_lambda_bodies_without_helper_declarations() {
    use super::{
        EgglogValue,
        builtins::{Function, I64},
        eq,
    };
    let plus_one = Function::<(I64,), I64>::new(|x| x + I64::from(1)).unwrap();
    let double = Function::<(I64,), I64>::new(|x| x + x).unwrap();
    let constant = Function::<(), I64>::new(|| I64::from(7)).unwrap();
    let independent = Function::<(), Function<(I64,), I64>>::new(|| {
        Function::<(I64,), I64>::new(|y| y + I64::from(1)).unwrap()
    })
    .unwrap();
    let nested_capture = Function::<(I64,), Function<(I64,), I64>>::new(|x| {
        Function::<(I64,), I64>::with_captures((x.clone(),), |(captured,), y| y + captured).unwrap()
    })
    .unwrap();
    let mut graph = super::EGraph::default();
    for (result, expected) in [
        (plus_one.call(4), 5),
        (double.call(4), 8),
        (constant.call(), 7),
        (independent.call().call(5), 6),
        (nested_capture.call(10).call(5), 15),
    ] {
        let program =
            pb::Program::decode(action_program(&result).encode_to_vec().as_slice()).unwrap();
        assert_eq!(
            i64::try_from(&graph.extract(result).unwrap()).unwrap(),
            expected
        );
        assert!(
            program
                .sorts
                .iter()
                .any(|sort| matches!(sort.kind, Some(pb::sort::Kind::Func(_))))
        );
        assert!(program.nodes.iter().any(|node| matches!(
            &node.kind,
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Lambda(_))
            }))
        )));
        assert!(!program.declarations.iter().any(|declaration| matches!(
            &declaration.kind,
            Some(pb::declaration::Kind::UserDefinedPrimitive(_))
        )));
    }
    assert!(graph.check(eq(plus_one.call(5), 6)).unwrap());
    let sort = Function::<(I64,), I64>::sort_ref();
    assert!(sort == Function::<(I64,), I64>::sort_ref());
    assert!(sort != Function::<(), I64>::sort_ref());
    let mut hash = std::hash::DefaultHasher::new();
    std::hash::Hash::hash(&sort, &mut hash);
}

#[test]
fn function_values_capture_external_reads_when_the_value_is_constructed() {
    use super::{
        EgglogValue,
        builtins::{Function, I64},
        let_, set,
    };
    let cell = I64::from_expression(Expr::call(
        &Callable::function(
            "FunctionCaptureCell",
            vec![],
            I64::sort_ref(),
            Some(|_, new| new),
        ),
        vec![],
    ));
    let callback =
        Function::<(I64,), I64>::with_captures((cell.clone(),), |(captured,), x| x + captured)
            .unwrap();
    let retained = let_("retained function", callback);
    let mut graph = super::EGraph::default();
    graph.register(set(&cell, 10)).unwrap();
    graph.register(&retained).unwrap();
    graph.register(set(&cell, 20)).unwrap();
    assert_eq!(
        i64::try_from(&graph.extract(retained.call(1)).unwrap()).unwrap(),
        11
    );
    assert_eq!(i64::try_from(&graph.extract(cell).unwrap()).unwrap(), 20);
}

#[test]
fn function_values_feed_catalog_higher_order_multisets() {
    use super::builtins::{F64, Function, I64, MultiSet, Unit, multiset_flat_map, multiset_fold};
    let values = MultiSet::<I64>::new([1, 1, 2]);
    let plus_one = Function::<(I64,), I64>::new(|x| x + I64::from(1)).unwrap();
    let sum = Function::<(I64, I64), I64>::new(|x, y| x + y).unwrap();
    let mut graph = super::EGraph::default();
    let mapped = graph.extract(values.map(plus_one)).unwrap();
    let mut mapped = std::vec::Vec::<I64>::try_from(&mapped)
        .unwrap()
        .iter()
        .map(|v| i64::try_from(v).unwrap())
        .collect::<std::vec::Vec<_>>();
    mapped.sort();
    assert_eq!(mapped, [2, 2, 3]);
    let float_map: MultiSet<F64> =
        values.map(Function::<(I64,), F64>::new(|_| F64::from(1.5)).unwrap());
    let floats = graph.extract(float_map).unwrap();
    assert_eq!(std::vec::Vec::<F64>::try_from(&floats).unwrap().len(), 3);
    let positive = Function::<(I64,), Unit>::new(|x| x.gt(1)).unwrap();
    assert_eq!(
        std::vec::Vec::<I64>::try_from(&graph.extract(values.filter(&positive)).unwrap())
            .unwrap()
            .len(),
        1
    );
    assert_eq!(
        std::vec::Vec::<I64>::try_from(&graph.extract(values.filter_not(positive)).unwrap())
            .unwrap()
            .len(),
        2
    );
    let duplicate =
        Function::<(I64,), MultiSet<I64>>::new(|x| MultiSet::<I64>::new([x, x])).unwrap();
    assert_eq!(
        std::vec::Vec::<I64>::try_from(
            &graph
                .extract(multiset_flat_map(duplicate, values.clone()))
                .unwrap()
        )
        .unwrap()
        .len(),
        6
    );
    let sum = graph
        .extract(multiset_fold(sum, I64::from(0), values))
        .unwrap();
    assert_eq!(i64::try_from(&sum).unwrap(), 4);
}

#[test]
fn function_values_preserve_named_table_targets_for_multiset_indexes() {
    use super::{
        EgglogValue,
        builtins::{Function, I64, MultiSet},
        set,
    };
    let table = Callable::function(
        "FunctionIndex",
        vec![MultiSet::<I64>::sort_ref(), I64::sort_ref()],
        I64::sort_ref(),
        Some(|_, new| new),
    );
    let index = Function::<(MultiSet<I64>, I64), I64>::new(|xs, x| {
        I64::from_expression(Expr::call(
            &table,
            vec![xs.expression().clone(), x.expression().clone()],
        ))
    })
    .unwrap();
    let values = MultiSet::<I64>::new([1, 1, 2]);
    let mut graph = super::EGraph::default();
    graph.register(values.fill_index(&index)).unwrap();
    assert_eq!(
        i64::try_from(&graph.extract(index.call(&values, 1)).unwrap()).unwrap(),
        2
    );
    let row = I64::from_expression(Expr::call(
        &table,
        vec![
            values.expression().clone(),
            I64::from(1).expression().clone(),
        ],
    ));
    graph.register(set(row, 7)).unwrap();
    assert_eq!(
        i64::try_from(&graph.extract(index.call(&values, 1)).unwrap()).unwrap(),
        7
    );
    graph.register(values.clear_index(&index)).unwrap();
    assert!(graph.extract(index.call(values, 1)).is_err());
}

#[test]
fn function_values_computed_callbacks_do_not_gain_writable_table_capability() {
    use super::{
        EgglogValue,
        builtins::{Function, I64, MultiSet},
        eq,
    };
    let table = Callable::function(
        "FunctionIndexCapability",
        vec![MultiSet::<I64>::sort_ref(), I64::sort_ref()],
        I64::sort_ref(),
        Some(|_, new| new),
    );
    let computed = Function::<(MultiSet<I64>, I64), I64>::new(|xs, x| {
        I64::from_expression(Expr::call(
            &table,
            vec![xs.expression().clone(), x.expression().clone()],
        )) + I64::from(0)
    })
    .unwrap();
    let direct = Function::<(MultiSet<I64>, I64), I64>::new(|xs, x| {
        I64::from_expression(Expr::call(
            &table,
            vec![xs.expression().clone(), x.expression().clone()],
        ))
    })
    .unwrap();
    let values = MultiSet::<I64>::new([1, 1, 2]);
    let mut graph = super::EGraph::default();
    assert!(graph.register(values.fill_index(computed)).is_err());
    for value in [1, 2] {
        assert!(!graph.check(eq(direct.call(&values, value), value)).unwrap());
    }
}

#[test]
fn function_values_reject_deferred_unions_without_eager_allocation() {
    use super::{EgglogValue, builtins::Function};
    let mut slots = std::array::from_fn(|_| vec![]);
    slots[Arena::Sort as usize].push(Slot::External(ActionTerm::sort_ref().0));
    let fresh = ActionTerm::from_expression(Expr(
        publish(
            pb::Program {
                nodes: vec![pb::Node {
                    kind: Some(pb::node::Kind::Union(pb::Union { members: vec![] })),
                    ..Default::default()
                }],
                ..Default::default()
            },
            slots,
            vec![],
            Arena::Node,
            0,
            vec![],
        )
        .unwrap(),
    ));
    let error = Function::<(), ActionTerm>::new(|| fresh).unwrap_err();
    assert!(error.to_string().contains("Unions in callback bodies"));
}

#[test]
fn primitive_sort_documentation_is_retained_without_changing_type_identity() {
    use super::{EgglogValue, builtins::I64};
    use std::hash::{DefaultHasher, Hash, Hasher};
    let catalog =
        pb::BuiltinCatalog::decode(include_bytes!("builtins/catalog.pb").as_slice()).unwrap();
    let mut sorts = vec![];
    for doc in [None, Some("A"), Some("Z"), Some("A and Z")] {
        let mut supplied = catalog.clone();
        supplied
            .primitive_sorts
            .iter_mut()
            .find(|family| family.name == "Vec")
            .unwrap()
            .doc = doc.map(str::to_owned);
        let context = super::storage::publish_catalog(supplied).unwrap();
        let definition = context
            .declaration("Vec", DeclarationKind::PrimitiveSort)
            .unwrap();
        assert_eq!(definition.primitive_sort().unwrap().doc.as_deref(), doc);
        sorts.push(SortRef::family(&definition, vec![I64::sort_ref()]).unwrap());
    }
    for sort in &sorts {
        assert!(&sorts[0] == sort);
        let mut left = DefaultHasher::new();
        let mut right = DefaultHasher::new();
        sorts[0].hash(&mut left);
        sort.hash(&mut right);
        assert_eq!(left.finish(), right.finish());
    }
    assert!(SortRef::equality("A") != SortRef::equality("Z"));
}

#[test]
fn typed_capture_recipe_identity_ownership_and_negative_markers() {
    use super::{EgglogValue, builtins::I64, eq, let_};
    use std::hash::{DefaultHasher, Hash, Hasher};
    let value = let_("λ", I64::from(7));
    let recipe = value.expression().0.capture().unwrap().unwrap();
    assert_eq!(recipe.name, "__typed_capture_recipe_cebb");
    assert_eq!(Expr(recipe.initializer), I64::from(7).expression().clone());
    let plain = I64::from_expression(Expr::call(
        &Callable::function(
            &recipe.name,
            vec![],
            I64::sort_ref(),
            None::<fn(Expr, Expr) -> Expr>,
        ),
        vec![],
    ));
    assert_ne!(
        value, plain,
        "a spelling cannot manufacture capture provenance"
    );
    let shared = I64::from_expression(eq(I64::from(1), 1).0);
    assert_eq!(let_("union", &shared), let_("union", &shared));
    assert_ne!(
        let_("union", &shared),
        let_("union", I64::from_expression(eq(I64::from(1), 1).0))
    );
    let mut left = I64::from(1);
    let mut right = I64::from(1);
    for i in 0..4000 {
        left = let_(i.to_string(), left);
        right = let_(i.to_string(), right);
    }
    assert_eq!(left, right);
    let hash = |value: &I64| {
        let mut h = DefaultHasher::new();
        value.hash(&mut h);
        h.finish()
    };
    assert_eq!(hash(&left), hash(&right));
    drop((left, right));
    for case in 0..5 {
        let value = let_("bad", I64::from(7));
        let mut record = value.expression().0.clone();
        drop(value);
        let owner = Arc::get_mut(record.owner.as_mut().unwrap()).unwrap();
        match case {
            0 => owner.capture = Some((99, 0)),
            1 => owner.capture = Some((0, 99)),
            _ => {
                let Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Set(set)),
                    ..
                })) = &mut owner.program_mut().unwrap().commands[0].kind
                else {
                    unreachable!()
                };
                match case {
                    2 => set.value = None,
                    3 => set.target.as_mut().unwrap().func = "foreign".into(),
                    _ => set.target.as_mut().unwrap().args.push(0),
                }
            }
        }
        assert!(record.capture().is_err(), "malformed recipe {case}");
        let mut graph = super::EGraph::default();
        assert!(graph.register(I64::from_expression(Expr(record))).is_err());
    }
}

fn action_program(values: impl super::rule::Actions) -> pb::Program {
    let mut packer = Packer::default();
    let mut actions = vec![];
    let mut declarations = vec![];
    values
        .append_actions(&mut actions, &mut declarations, &mut |expr| {
            packer.intern(expr.0, 0)
        })
        .unwrap();
    for declaration in declarations {
        packer.intern(declaration.0, 0);
    }
    packer.program.commands = actions
        .into_iter()
        .map(|action| pb::Command {
            kind: Some(pb::command::Kind::Action(action)),
            ..Default::default()
        })
        .collect();
    packer.finish().unwrap();
    packer.program
}

#[test]
fn union_subsume_records_preserve_operands_closure_and_identity() {
    use super::{EgglogValue, builtins::I64, eq, subsume, union};
    let definition = Callable::constructor(
        "ActionRow",
        vec![I64::sort_ref(), I64::sort_ref()],
        ActionTerm::sort_ref(),
        None,
        false,
    );
    let nullary = Callable::constructor("ActionEmpty", vec![], ActionTerm::sort_ref(), None, false);
    let target = ActionTerm(Expr::call(
        &definition,
        vec![
            I64::from(17).expression().clone(),
            I64::from(23).expression().clone(),
        ],
    ));
    let empty = ActionTerm(Expr::call(&nullary, vec![]));
    let actions = [subsume(&target), subsume(&empty)];
    let merge = union(&target, &empty);
    let independent = union(&target, &empty);
    let equality = eq(&target, &empty);
    let nested = ActionTerm(equality.0.clone());
    drop((target, empty, definition, nullary));
    let program = action_program(actions);
    assert_eq!(
        program.nodes.len(),
        2,
        "row addresses must not import target lookup nodes"
    );
    for (node, expected) in program.nodes.iter().zip([17, 23]) {
        assert!(
            matches!(&node.kind, Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::I64(actual))
        })) if *actual == expected)
        );
    }
    for (command, (name, args)) in program
        .commands
        .iter()
        .zip([("ActionRow", vec![0, 1]), ("ActionEmpty", vec![])])
    {
        assert!(
            matches!(&command.kind, Some(pb::command::Kind::Action(pb::Action {
            kind: Some(pb::action::Kind::Subsume(call)), ..
        })) if call.func == name && call.args == args)
        );
        assert!(program.declarations.iter().any(|d| matches!(&d.kind,
            Some(pb::declaration::Kind::Constructor(c)) if c.name == name)));
    }
    assert_eq!(
        pb::Program::decode(program.encode_to_vec().as_slice()).unwrap(),
        program
    );
    let program = action_program((&merge, merge.clone(), independent));
    let roots: Vec<_> = program
        .commands
        .iter()
        .map(|command| {
            let Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Term(root)),
                ..
            })) = &command.kind
            else {
                panic!()
            };
            *root
        })
        .collect();
    assert_eq!(roots[0], roots[1]);
    assert_ne!(roots[0], roots[2]);
    let Some(pb::node::Kind::Union(first)) = &program.nodes[roots[0] as usize].kind else {
        panic!()
    };
    assert_eq!(first.members.len(), 2);
    assert_eq!(
        program.nodes[roots[0] as usize],
        program.nodes[roots[2] as usize]
    );
    for (index, name) in first.members.iter().zip(["ActionRow", "ActionEmpty"]) {
        assert!(
            matches!(&program.nodes[*index as usize].kind, Some(pb::node::Kind::Call(c)) if c.func == name)
        );
        assert_eq!(
            program.sorts[program.nodes[*index as usize].sort_id as usize],
            program.sorts[program.nodes[roots[0] as usize].sort_id as usize]
        );
    }
    let mut graph = super::EGraph::default();
    graph.register(union(&nested, &nested)).unwrap();
    assert!(graph.check(equality).unwrap());
}

#[test]
fn typed_table_actions_preserve_exact_wire_operands_and_real_execution() {
    use super::{EgglogValue, builtins::I64, delete, set};
    let definition = Callable::function(
        "Read",
        vec![I64::sort_ref()],
        I64::sort_ref(),
        None::<fn(Expr, Expr) -> Expr>,
    );
    let key = I64::from(1);
    let target = I64::from_expression(Expr::call(&definition, vec![key.expression().clone()]));
    let actions = (set(&target, 10), delete(&target), set(&target, 20));
    drop(target);
    drop(definition);
    drop(key);
    let program = action_program(actions);
    // Hand-written protobuf bytes for Command(Action(Set/ Delete)): the key's
    // packed NodeId is zero, not an absent reference; RHS follows the arguments.
    assert_eq!(
        program.commands[0].encode_to_vec(),
        b"\x0a\x0f\x12\x0d\x0a\x09\x0a\x04Read\x12\x01\x00\x10\x01"
    );
    assert_eq!(
        program.commands[1].encode_to_vec(),
        b"\x0a\x0b\x1a\x09\x0a\x04Read\x12\x01\x00"
    );
    assert_eq!(
        program.commands[2].encode_to_vec(),
        b"\x0a\x0f\x12\x0d\x0a\x09\x0a\x04Read\x12\x01\x00\x10\x02"
    );
    assert_eq!(
        program.nodes.len(),
        3,
        "target lookup was not imported as an evaluated node"
    );
    for (node, value) in program.nodes.iter().zip([1, 10, 20]) {
        assert_eq!(
            node.kind,
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::I64(value))
            }))
        );
    }
    assert!(program.declarations.iter().any(|d| matches!(&d.kind, Some(pb::declaration::Kind::Function(f)) if f.name == "Read" && f.inputs.len() == 1 && f.merge.is_none())));
    let mut decoded = pb::Program::decode(program.encode_to_vec().as_slice()).unwrap();
    assert_eq!(decoded, program);
    decoded.nodes.push(pb::Node {
        sort_id: program.nodes[0].sort_id,
        kind: Some(pb::node::Kind::Call(pb::Call {
            func: "Read".into(),
            args: vec![0],
        })),
        ..Default::default()
    });
    let extraction = pb::Command {
        kind: Some(pb::command::Kind::Extract(pb::Extract {
            roots: vec![3],
            variants: 1,
            extractor: pb::Extractor::Tree.into(),
            ..Default::default()
        })),
        ..Default::default()
    };
    decoded.commands.insert(1, extraction.clone());
    decoded.commands.push(extraction);
    let mut engine = crate::protobuf::Engine::default();
    let created = engine
        .create(
            &pb::CreateEGraphRequest {
                sorts: vec![pb::Sort {
                    kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
                        name: "i64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                }],
                options: Some(pb::EGraphOptions {
                    cost_sort: Some(0),
                    execution_mode: pb::ExecutionMode::Normal.into(),
                    ..Default::default()
                }),
                ..Default::default()
            }
            .encode_to_vec(),
        )
        .unwrap();
    let handle = pb::CreateEGraphResponse::decode(created.as_slice())
        .unwrap()
        .egraph_id;
    let request = pb::RunProgramRequest {
        egraph_id: handle,
        program: Some(decoded),
        diagnostics: false,
    };
    let response_bytes = engine.run(&request.encode_to_vec()).unwrap();
    let response = Observed::from_frames(
        response_bytes
            .iter()
            .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()),
    );
    assert!(response.error.is_none(), "{:?}", response.error);
    let extracted: Vec<_> = response
        .output
        .outputs
        .iter()
        .filter_map(|output| match &output.kind {
            Some(pb::command_output::Kind::Extraction(result)) => {
                Some(&response.output.nodes[result.roots[0].variants[0].term as usize].kind)
            }
            _ => None,
        })
        .collect();
    assert_eq!(extracted.len(), 2);
    for (kind, value) in extracted.into_iter().zip([10, 20]) {
        assert_eq!(
            *kind,
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::I64(value))
            }))
        );
    }
}

#[test]
fn typed_table_heads_import_nullary_targets_close_one_binder_and_keep_shared_union() {
    use super::{EgglogValue, builtins::I64, delete, eq, rule, set};
    let definition = Callable::function(
        "HeadOnly",
        vec![I64::sort_ref()],
        I64::sort_ref(),
        None::<fn(Expr, Expr) -> Expr>,
    );
    let nullary = Callable::function(
        "Nullary",
        vec![],
        I64::sort_ref(),
        None::<fn(Expr, Expr) -> Expr>,
    );
    let x = super::expr::variable::<I64>(super::expr::fresh_scope(), 0);
    let shared = I64::from_expression(eq(&x, 1).0);
    let target = I64::from_expression(Expr::call(&definition, vec![shared.expression().clone()]));
    let nullary = I64::from_expression(Expr::call(&nullary, vec![]));
    let nullary_action = set(&nullary, 8);
    let retained = nullary_action.clone();
    drop(nullary_action);
    let nullary_program = action_program(&retained);
    assert_eq!(nullary_program.nodes.len(), 1);
    assert!(
        matches!(&nullary_program.commands[0].kind, Some(pb::command::Kind::Action(pb::Action { kind: Some(pb::action::Kind::Set(set)), .. })) if set.target.as_ref().unwrap().args.is_empty() && set.value == Some(0))
    );
    let authored = rule(
        eq(&x, 1),
        (set(&target, &shared), delete(&target), set(&nullary, &x)),
    )
    .when(eq(&x, 2));
    let mut packer = Packer::default();
    packer.intern(authored.0, 0);
    packer.intern(rule(eq(&x, 3), set(&target, &shared)).0, 0);
    packer.finish().unwrap();
    assert!(
        packer.program.commands.is_empty(),
        "inline head must never become top-level actions"
    );
    assert_eq!(packer.declarations.len(), 2);
    for name in ["HeadOnly", "Nullary"] {
        let record = &packer.declarations[name];
        assert!(matches!(
            &record.owner.as_ref().unwrap().program().unwrap().declarations[record.index as usize].kind,
            Some(pb::declaration::Kind::Function(function)) if function.name == name
        ));
        assert!(packer.program.declarations.iter().any(
            |d| matches!(&d.kind, Some(pb::declaration::Kind::Function(f)) if f.name == name)
        ));
    }
    let Some(pb::rule::Kind::Rule(body)) = &packer.rules[0].kind else {
        panic!()
    };
    let Some(pb::action::Kind::Set(first)) = &body.head[0].kind else {
        panic!()
    };
    let Some(pb::action::Kind::Delete(second)) = &body.head[1].kind else {
        panic!()
    };
    assert_eq!(first.target.as_ref().unwrap().args, second.args);
    assert_eq!(
        first.value,
        Some(second.args[0]),
        "one imported Union occurrence stays one node"
    );
    let Some(pb::node::Kind::Union(shared)) = &packer.program.nodes[second.args[0] as usize].kind
    else {
        panic!()
    };
    let Some(pb::node::Kind::Union(query)) = &packer.program.nodes[body.query[0] as usize].kind
    else {
        panic!()
    };
    let Some(pb::action::Kind::Set(last)) = &body.head[2].kind else {
        panic!()
    };
    assert!(last.target.as_ref().unwrap().args.is_empty());
    assert_eq!(last.value, Some(query.members[0]));
    assert_eq!(shared.members[0], query.members[0]);
    let Some(pb::rule::Kind::Rule(other)) = &packer.rules[1].kind else {
        panic!()
    };
    let Some(pb::action::Kind::Set(other)) = &other.head[0].kind else {
        panic!()
    };
    assert_ne!(
        first.value, other.value,
        "each rule closes its own binder context"
    );
    assert_eq!(other.value, Some(other.target.as_ref().unwrap().args[0]));
    assert_eq!(
        pb::Program::decode(packer.program.encode_to_vec().as_slice()).unwrap(),
        packer.program
    );
}

#[test]
fn typed_table_function_syntax_rejects_inert_data_and_incompatible_selectors() {
    use super::{
        EgglogValue,
        builtins::{I64, String as EString},
    };
    let function = Callable::function(
        "Same",
        vec![I64::sort_ref()],
        I64::sort_ref(),
        None::<fn(Expr, Expr) -> Expr>,
    );
    let independent = Callable::function(
        "Same",
        vec![I64::sort_ref()],
        I64::sort_ref(),
        None::<fn(Expr, Expr) -> Expr>,
    );
    let key = I64::from(1);
    let actual = Expr::call(&function, vec![key.expression().clone()]);
    let authored = I64::from_expression(actual.clone());
    assert_eq!(authored.call_name(), Some("Same"));
    assert_eq!(key.call_name(), None);
    assert_eq!(super::var::<I64>("key").call_name(), None);
    assert_eq!(super::let_("call", &authored).call_name(), None);
    assert_eq!(
        I64::from_expression(super::eq(&key, &key).0).call_name(),
        None
    );
    let mut observed = Expr::call(&function, vec![key.expression().clone()]);
    Arc::get_mut(observed.0.owner.as_mut().unwrap())
        .unwrap()
        .observed = true;
    assert_eq!(I64::from_expression(observed).call_name(), None);
    assert!(actual.validate_inert().is_err());
    assert!(key.expression().validate_inert().is_ok());
    assert_eq!(
        actual,
        Expr::call(&independent, vec![key.expression().clone()])
    );
    use std::hash::{DefaultHasher, Hash, Hasher};
    let mut original_hash = DefaultHasher::new();
    let mut independent_hash = DefaultHasher::new();
    actual.hash(&mut original_hash);
    Expr::call(&independent, vec![key.expression().clone()]).hash(&mut independent_hash);
    assert_eq!(original_hash.finish(), independent_hash.finish());
    let constructor =
        Callable::constructor("Same", vec![I64::sort_ref()], I64::sort_ref(), None, false);
    let pattern = Expr::call(&constructor, vec![key.expression().clone()]);
    assert!(
        actual
            .select(&pattern, &[key.expression().clone()])
            .is_err()
    );
    let other = Callable::function(
        "Same",
        vec![EString::sort_ref()],
        I64::sort_ref(),
        None::<fn(Expr, Expr) -> Expr>,
    );
    let text = EString::from("key");
    let pattern = Expr::call(&other, vec![text.expression().clone()]);
    assert!(
        actual
            .select(&pattern, &[text.expression().clone()])
            .is_err()
    );
    let primitive = &key + &key;
    let Some(pb::node::Kind::Call(call)) = &primitive
        .expression()
        .0
        .owner
        .as_ref()
        .unwrap()
        .program()
        .unwrap()
        .nodes[primitive.expression().0.index as usize]
        .kind
    else {
        panic!()
    };
    let function = Callable::function(
        &call.func,
        vec![I64::sort_ref(), I64::sort_ref()],
        I64::sort_ref(),
        None::<fn(Expr, Expr) -> Expr>,
    );
    let pattern = Expr::call(
        &function,
        vec![key.expression().clone(), key.expression().clone()],
    );
    assert!(
        primitive
            .expression()
            .select(
                &pattern,
                &[key.expression().clone(), key.expression().clone()]
            )
            .is_err()
    );
}

#[test]
fn exact_number_literals_close_pack_compare_and_hash_by_canonical_payload() {
    use super::{
        EgglogValue,
        builtins::{BigInt, BigRat, Rational},
        rule,
    };
    use std::hash::{DefaultHasher, Hash, Hasher};
    let integer: num::BigInt = "1234567890123456789012345678901".parse().unwrap();
    let ratio = num::BigRational::new(integer.clone(), num::BigInt::from(2));
    let bounded = num::rational::Rational64::new(i64::MIN, 1);
    let pairs = [
        (
            BigInt::from(&integer).expression().clone(),
            BigInt::from(integer).expression().clone(),
        ),
        (
            BigRat::try_from(&ratio).unwrap().expression().clone(),
            BigRat::try_from(ratio).unwrap().expression().clone(),
        ),
        (
            Rational::try_from(&bounded).unwrap().expression().clone(),
            Rational::try_from(bounded).unwrap().expression().clone(),
        ),
    ];
    for (a, b) in pairs {
        assert_eq!(a, b);
        let mut ah = DefaultHasher::new();
        let mut bh = DefaultHasher::new();
        a.hash(&mut ah);
        b.hash(&mut bh);
        assert_eq!(ah.finish(), bh.finish());
        let mut packer = Packer::default();
        let root = packer.intern(a.0, 0);
        packer.finish().unwrap();
        let roundtrip = pb::Program::decode(packer.program.encode_to_vec().as_slice()).unwrap();
        assert_eq!(roundtrip, packer.program);
        assert!(matches!(
            roundtrip.nodes[root as usize].kind,
            Some(pb::node::Kind::PrimitiveValue(_))
        ));
    }
    // Rule closing must accept all three terminal payloads without new binders.
    let head = rule(
        (),
        (
            BigInt::from(num::BigInt::from(7)),
            BigRat::try_from(num::BigRational::new(1.into(), 2.into())).unwrap(),
            Rational::try_from(bounded).unwrap(),
        ),
    );
    let mut packed = Packer::default();
    packed.intern(head.0, 0);
    packed.finish().unwrap();
    assert!(
        packed
            .program
            .nodes
            .iter()
            .all(|n| matches!(n.kind, Some(pb::node::Kind::PrimitiveValue(_))))
    );
}

#[test]
fn rule_conditions_relocate_once_and_close_the_whole_ordered_binder() {
    use super::{builtins::I64, eq, rule, var};
    let fresh = super::expr::variable::<I64>(super::expr::fresh_scope(), 0);
    let named = var::<I64>("__typed_v_0");
    let original = rule(eq(&fresh, 7), (&fresh, &named));
    let unchanged = original.clone().when(());
    assert!(Arc::ptr_eq(
        original.0.owner.as_ref().unwrap(),
        unchanged.0.owner.as_ref().unwrap()
    ));
    let extended = original.clone().when(eq(&named, 8)).when(eq(&fresh, 9));
    assert!(!Arc::ptr_eq(
        original.0.owner.as_ref().unwrap(),
        extended.0.owner.as_ref().unwrap()
    ));
    let mut packer = Packer::default();
    let old = packer.intern(original.0, 0);
    let new = packer.intern(extended.0, 0);
    packer.finish().unwrap();
    let packed_rules = packer.rules;
    let program = packer.program;
    let Some(pb::rule::Kind::Rule(old)) = &packed_rules[old as usize].kind else {
        panic!()
    };
    assert_eq!(old.query.len(), 1);
    let Some(pb::rule::Kind::Rule(body)) = &packed_rules[new as usize].kind else {
        panic!()
    };
    assert_eq!(body.query.len(), 3);
    assert_eq!(body.head.len(), 2);
    let mut variables = vec![];
    for (fact, value) in body.query.iter().zip([7, 8, 9]) {
        let Some(pb::node::Kind::Union(equality)) = &program.nodes[*fact as usize].kind else {
            panic!()
        };
        assert_eq!(equality.members.len(), 2);
        variables.push(equality.members[0]);
        assert_eq!(
            program.nodes[equality.members[1] as usize].kind,
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::I64(value)),
            }))
        );
    }
    assert_eq!(variables[0], variables[2]);
    for (action, (variable, name)) in body
        .head
        .iter()
        .zip(variables.iter().zip(["__typed_v_1", "__typed_v_0"]))
    {
        assert_eq!(action.kind, Some(pb::action::Kind::Term(*variable)));
        assert_eq!(
            program.nodes[*variable as usize].kind,
            Some(pb::node::Kind::Var(name.into()))
        );
    }
    assert_eq!(
        pb::Program::decode(program.encode_to_vec().as_slice()).unwrap(),
        program
    );
}

#[test]
fn registration_and_rule_heads_use_the_same_canonical_action_input() {
    use super::{
        builtins::{F64, I64},
        rule,
    };
    let values = [I64::from(3), I64::from(5)];
    let heads = (values.as_slice(), (F64::from(7.5),), Vec::<I64>::new(), ());
    let commands = action_program(heads.clone());
    let mut packed = Packer::default();
    packed.intern(rule((), heads).0, 0);
    packed.finish().unwrap();
    let Some(pb::rule::Kind::Rule(body)) = &packed.rules[0].kind else {
        panic!()
    };
    assert!(body.query.is_empty());
    assert_eq!(body.head.len(), 3);
    assert_eq!(packed.program.nodes, commands.nodes);
    assert_eq!(packed.program.sorts, commands.sorts);
    assert_eq!(packed.program.declarations, commands.declarations);
    for (head, command) in body.head.iter().zip(commands.commands) {
        assert_eq!(command.kind, Some(pb::command::Kind::Action(head.clone())));
    }
}

#[test]
fn nested_fail_keeps_packed_roots_and_fragment_admission() {
    use super::{EgglogValue, TypedError, builtins::I64, eq};

    let a = I64::from(7);
    let b = I64::from(11);
    assert!(!Arc::ptr_eq(
        a.expression().0.owner.as_ref().unwrap(),
        b.expression().0.owner.as_ref().unwrap(),
    ));
    let first = eq(&a, &b).0;
    let second = eq(&b, &a).0;
    let roots = [first.0.clone(), second.0, first.0];
    let mut packer = Packer::default();
    packer.binders.push(close::binder(&roots).unwrap());
    let facts: Vec<_> = roots.into_iter().map(|r| packer.intern(r, 1)).collect();
    assert_eq!(facts[0], facts[2]);
    assert_ne!(facts[0], facts[1]);
    let mut command = pb::Command {
        kind: Some(pb::command::Kind::Check(pb::Check {
            facts: facts.clone(),
        })),
        ..Default::default()
    };
    for _ in 0..2 {
        command = pb::Command {
            kind: Some(pb::command::Kind::Fail(Box::new(command))),
            ..Default::default()
        };
    }
    packer.program.commands.push(command);
    packer.finish().unwrap();
    let program = packer.program;
    let Some(pb::command::Kind::Fail(outer)) = &program.commands[0].kind else {
        panic!("missing outer Fail")
    };
    let Some(pb::command::Kind::Fail(inner)) = &outer.kind else {
        panic!("missing inner Fail")
    };
    assert_eq!(
        inner.kind,
        Some(pb::command::Kind::Check(pb::Check {
            facts: facts.clone(),
        }))
    );
    let Some(pb::node::Kind::Union(first)) = &program.nodes[facts[0] as usize].kind else {
        panic!("missing first equality")
    };
    let Some(pb::node::Kind::Union(second)) = &program.nodes[facts[1] as usize].kind else {
        panic!("missing second equality")
    };
    assert_eq!(program.nodes.len(), 4);
    assert_eq!(first.members, [second.members[1], second.members[0]]);
    assert_ne!(first.members[0], first.members[1]);
    for (index, value) in first.members.iter().zip([7, 11]) {
        assert_eq!(
            program.nodes[*index as usize].kind,
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::I64(value)),
            }))
        );
    }
    assert_eq!(
        pb::Program::decode(program.encode_to_vec().as_slice()).unwrap(),
        program
    );
    assert!(matches!(
        publish(
            program,
            std::array::from_fn(|_| vec![]),
            vec![],
            Arena::Node,
            facts[0], vec![],),
        Err(TypedError::Invalid(message)) if message == "unsupported typed fragment sections"
    ));
}

#[test]
fn collection_composition_packs_shared_rule_records_and_empty_values() {
    use super::{rule, ruleset};
    let shared = rule((), ());
    let independent = rule((), ());
    let empty = ruleset(());
    let leaf = ruleset(vec![shared.clone(), shared.clone(), independent]);
    let group = ruleset((&leaf, &empty, vec![shared.clone()]));
    let diamond = ruleset((&group, &group, &empty, shared));
    assert_eq!(diamond.rules.len(), 9);
    let mut packer = Packer::default();
    for rule in diamond.rules {
        packer.intern(rule.0, 0);
    }
    packer.finish().unwrap();
    assert_eq!(packer.rules.len(), 2);
    assert!(packer.program.commands.is_empty());
    assert!(packer.program.rulesets.is_empty());
    assert!(empty.is_empty());
    assert_eq!(super::Schedule::from(&empty).commands.len(), 1);
}

#[test]
fn wide_callbacks_author_generated_binders_without_claiming_grounded_execution() {
    use super::{builtins::I64, rule, ruleset};
    let mut calls = 0;
    let thirteen = ruleset(
        |a0: &I64,
         a1: &I64,
         a2: &I64,
         a3: &I64,
         a4: &I64,
         a5: &I64,
         a6: &I64,
         a7: &I64,
         a8: &I64,
         a9: &I64,
         a10: &I64,
         a11: &I64,
         a12: &I64| {
            calls += 1;
            vec![rule(
                [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12],
                (),
            )]
        },
    );
    let thirty_five = ruleset(
        |a0: &I64,
         a1: &I64,
         a2: &I64,
         a3: &I64,
         a4: &I64,
         a5: &I64,
         a6: &I64,
         a7: &I64,
         a8: &I64,
         a9: &I64,
         a10: &I64,
         a11: &I64,
         a12: &I64,
         a13: &I64,
         a14: &I64,
         a15: &I64,
         a16: &I64,
         a17: &I64,
         a18: &I64,
         a19: &I64,
         a20: &I64,
         a21: &I64,
         a22: &I64,
         a23: &I64,
         a24: &I64,
         a25: &I64,
         a26: &I64,
         a27: &I64,
         a28: &I64,
         a29: &I64,
         a30: &I64,
         a31: &I64,
         a32: &I64,
         a33: &I64,
         a34: &I64| {
            calls += 1;
            rule(
                [
                    a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
                    a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33,
                    a34,
                ],
                (),
            )
        },
    );
    let group = super::ruleset((&thirteen, &thirty_five, thirteen.clone()));
    assert_eq!(
        calls, 2,
        "composition never re-executes authoring callbacks"
    );
    let mut packed = Packer::default();
    for rule in group.rules {
        packed.intern(rule.0, 0);
    }
    packed.finish().unwrap();
    let widths: Vec<_> = packed
        .rules
        .iter()
        .map(|r| {
            let Some(pb::rule::Kind::Rule(body)) = &r.kind else {
                panic!()
            };
            let distinct: std::collections::HashSet<_> = body
                .query
                .iter()
                .map(|i| {
                    let Some(pb::node::Kind::Var(name)) = &packed.program.nodes[*i as usize].kind
                    else {
                        panic!()
                    };
                    name
                })
                .collect();
            assert_eq!(distinct.len(), body.query.len());
            body.query.len()
        })
        .collect();
    assert_eq!(widths, [13, 35]);
}

// The same spelling deliberately names a nominal sort, an applied family,
// and a constructor. Imports retain the original generated records.
fn namespace_fragment(imported: bool, reversed: bool, missing: Option<DeclarationKind>) -> Record {
    let family = super::storage::publish_catalog(pb::BuiltinCatalog {
        primitive_sorts: (missing != Some(DeclarationKind::PrimitiveSort))
            .then(|| pb::PrimitiveSort {
                name: "Shared".into(),
                arity: 1,
                ..Default::default()
            })
            .into_iter()
            .collect(),
        ..Default::default()
    })
    .unwrap();
    let mut declarations = vec![
        (
            DeclarationKind::EqSort,
            pb::declaration::Kind::EqSort(pb::EqSort {
                name: "Shared".into(),
            }),
        ),
        (
            DeclarationKind::Callable,
            pb::declaration::Kind::Constructor(pb::Constructor {
                name: "Shared".into(),
                output: 0,
                ..Default::default()
            }),
        ),
    ];
    if reversed {
        declarations.reverse();
    }
    let mut program = pb::Program {
        sorts: vec![
            pb::Sort {
                kind: Some(pb::sort::Kind::Eq("Shared".into())),
                ..Default::default()
            },
            pb::Sort {
                kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
                    name: "Shared".into(),
                    args: vec![0],
                })),
                ..Default::default()
            },
        ],
        nodes: vec![pb::Node {
            sort_id: 0,
            kind: Some(pb::node::Kind::Call(pb::Call {
                func: "Shared".into(),
                args: vec![],
            })),
            ..Default::default()
        }],
        declarations: declarations
            .into_iter()
            .filter(|(kind, _)| Some(*kind) != missing)
            .map(|(_, kind)| pb::Declaration {
                kind: Some(kind),
                ..Default::default()
            })
            .collect(),
        ..Default::default()
    };
    let slots = || {
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Sort as usize] = vec![Slot::Local(0), Slot::Local(1)];
        slots
    };
    let mut imports = vec![family];
    if imported {
        let source = publish(
            program.clone(),
            slots(),
            imports.clone(),
            Arena::Node,
            0,
            vec![],
        )
        .unwrap();
        imports.extend((0..program.declarations.len()).map(|index| Record {
            owner: source.owner.clone(),
            arena: Arena::Declaration,
            index: index as u32,
        }));
        program.declarations.clear();
    }
    publish(program, slots(), imports, Arena::Node, 0, vec![]).unwrap()
}

#[test]
fn nominal_family_and_callable_names_close_independently() {
    for imported in [false, true] {
        for reversed in [false, true] {
            let root = namespace_fragment(imported, reversed, None);
            let nominal = SortRef(root.resolve(Arena::Sort, 0).unwrap());
            let family = SortRef(root.resolve(Arena::Sort, 1).unwrap());
            family.validate_closed().unwrap();
            assert!(nominal != family);
            assert!(nominal == SortRef::equality("Shared"));
            for kind in [
                DeclarationKind::EqSort,
                DeclarationKind::PrimitiveSort,
                DeclarationKind::Callable,
            ] {
                let declaration = root.declaration("Shared", kind).unwrap();
                if kind == DeclarationKind::PrimitiveSort {
                    assert_eq!(declaration.primitive_sort().unwrap().name, "Shared");
                    assert_eq!(declaration.arena, Arena::PrimitiveSort);
                } else {
                    let definition = &declaration
                        .owner
                        .as_ref()
                        .unwrap()
                        .program()
                        .unwrap()
                        .declarations[declaration.index as usize];
                    assert!(matches!(
                        (kind, &definition.kind),
                        (
                            DeclarationKind::EqSort,
                            Some(pb::declaration::Kind::EqSort(_))
                        ) | (
                            DeclarationKind::Callable,
                            Some(pb::declaration::Kind::Constructor(_))
                        )
                    ));
                    // Wrong-kind local records must not shadow the correct import.
                    let mut program = root.owner.as_ref().unwrap().program().unwrap().clone();
                    program.declarations.retain(|d| d != definition);
                    let mut slots = std::array::from_fn(|_| vec![]);
                    slots[Arena::Sort as usize] = vec![Slot::Local(0), Slot::Local(1)];
                    let mixed = publish(
                        program,
                        slots,
                        vec![declaration.clone()],
                        Arena::Node,
                        0,
                        vec![],
                    )
                    .unwrap();
                    let selected = mixed.declaration("Shared", kind).unwrap();
                    assert!(Arc::ptr_eq(
                        selected.owner.as_ref().unwrap(),
                        declaration.owner.as_ref().unwrap()
                    ));
                    assert_eq!(selected.index, declaration.index);
                }
            }
            let definition = root
                .declaration("Shared", DeclarationKind::PrimitiveSort)
                .unwrap();
            let applied = SortRef::family(&definition, vec![nominal]).unwrap();
            assert!(applied == family);
            assert!(SortRef::family(&definition, vec![]).is_err());
            let hash = |sort: &SortRef| {
                let mut h = std::hash::DefaultHasher::new();
                std::hash::Hash::hash(sort, &mut h);
                std::hash::Hasher::finish(&h)
            };
            assert_eq!(hash(&applied), hash(&family));
            for family_first in [false, true] {
                let mut roots = [root.clone(), family.0.clone()];
                if family_first {
                    roots.reverse();
                }
                let mut packer = Packer::default();
                for record in roots {
                    packer.intern(record, 0);
                }
                packer.finish().unwrap();
                assert_eq!(packer.program.declarations.len(), 2);
                assert!(packer.program.declarations.iter().any(|d| matches!(&d.kind,
                    Some(pb::declaration::Kind::EqSort(d)) if d.name == "Shared")));
                assert!(packer.program.declarations.iter().any(|d| matches!(&d.kind,
                    Some(pb::declaration::Kind::Constructor(d)) if d.name == "Shared")));
                assert!(
                    packer
                        .builtin_demands
                        .iter()
                        .any(|d| d.arena == Arena::PrimitiveSort
                            && d.primitive_sort().unwrap().name == "Shared")
                );
                let bytes = packer.program.encode_to_vec();
                assert_eq!(
                    pb::Program::decode(bytes.as_slice()).unwrap(),
                    packer.program
                );
            }
        }
    }
}

#[test]
fn missing_declaration_kind_never_uses_a_same_named_other_kind() {
    for imported in [false, true] {
        for reversed in [false, true] {
            for missing in [
                DeclarationKind::EqSort,
                DeclarationKind::PrimitiveSort,
                DeclarationKind::Callable,
            ] {
                let root = namespace_fragment(imported, reversed, Some(missing));
                assert!(root.declaration("Shared", missing).is_err());
                let required = match missing {
                    DeclarationKind::EqSort => root.resolve(Arena::Sort, 0).unwrap(),
                    DeclarationKind::PrimitiveSort => {
                        let family = root.resolve(Arena::Sort, 1).unwrap();
                        assert!(SortRef(family.clone()).validate_closed().is_err());
                        family
                    }
                    DeclarationKind::Callable => root,
                };
                let mut packer = Packer::default();
                packer.intern(required, 0);
                assert!(packer.finish().is_err());
            }
        }
    }
}

#[test]
fn namespace_split_keeps_same_kind_and_callable_kind_conflicts() {
    for changed in 1..4 {
        let root = namespace_fragment(false, false, None);
        let mut program = root.owner.as_ref().unwrap().program().unwrap().clone();
        let mut imports = root.owner.as_ref().unwrap().declarations.clone();
        match changed {
            1 => {
                let Some(pb::declaration::Kind::Constructor(d)) = &mut program.declarations[1].kind
                else {
                    panic!()
                };
                d.unextractable = true;
            }
            2 => {
                program.declarations[1].kind = Some(pb::declaration::Kind::Function(pb::Function {
                    name: "Shared".into(),
                    output: 0,
                    ..Default::default()
                }))
            }
            3 => {
                imports = vec![
                    super::storage::publish_catalog(pb::BuiltinCatalog {
                        primitive_sorts: vec![pb::PrimitiveSort {
                            name: "Shared".into(),
                            arity: 2,
                            ..Default::default()
                        }],
                        ..Default::default()
                    })
                    .unwrap(),
                ]
            }
            _ => unreachable!(),
        }
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Sort as usize] = vec![Slot::Local(0), Slot::Local(1)];
        let other = publish(program, slots, imports, Arena::Node, 0, vec![]).unwrap();
        let mut packer = Packer::default();
        for record in [root, other] {
            packer.intern(record.resolve(Arena::Sort, 1).unwrap(), 0);
            packer.intern(record, 0);
        }
        assert!(packer.finish().is_err(), "conflict case {changed}");
    }
}

#[test]
fn family_sort_comparison_resolves_slots_not_raw_indices() {
    use super::{EgglogValue, builtins::I64};
    let family = super::storage::builtin_catalog()
        .declaration("Vec", DeclarationKind::PrimitiveSort)
        .unwrap();
    let integers = SortRef::family(&family, vec![I64::sort_ref()]).unwrap();
    let atoms = SortRef::family(&family, vec![SortRef::equality("Atom")]).unwrap();
    assert!(
        integers != atoms,
        "same local slot 0 must not hide different imported sorts"
    );
    let mut slots = std::array::from_fn(|_| vec![]);
    slots[Arena::Sort as usize] = vec![
        Slot::External(SortRef::equality("Unused").0),
        Slot::External(I64::sort_ref().0),
    ];
    let shifted = SortRef(
        publish(
            pb::Program {
                sorts: vec![pb::Sort {
                    kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
                        name: "Vec".into(),
                        args: vec![1],
                    })),
                    ..Default::default()
                }],
                ..Default::default()
            },
            slots,
            vec![family],
            Arena::Sort,
            0,
            vec![],
        )
        .unwrap(),
    );
    assert!(
        integers == shifted,
        "equal sorts at different slots must agree"
    );
}

#[test]
fn generic_calls_infer_from_actual_arguments_and_result_records() {
    use super::{EgglogValue, builtins::I64};
    let catalog = super::storage::builtin_catalog();
    let family = catalog
        .declaration("Vec", DeclarationKind::PrimitiveSort)
        .unwrap();
    let integers = SortRef::family(&family, vec![I64::sort_ref()]).unwrap();
    let atoms = SortRef::family(&family, vec![SortRef::equality("A")]).unwrap();
    let empty = Callable(
        catalog
            .declaration("egglog.core.vec.empty", DeclarationKind::Callable)
            .unwrap(),
    );
    let of = Callable(
        catalog
            .declaration("egglog.core.vec.of", DeclarationKind::Callable)
            .unwrap(),
    );
    let get = Callable(
        catalog
            .declaration("egglog.core.vec.get", DeclarationKind::Callable)
            .unwrap(),
    );
    assert!(Expr::call_with_result(&empty, vec![], integers.clone()).is_ok());
    assert!(Expr::call_with_result(&of, vec![], atoms.clone()).is_ok());
    assert!(Expr::call_with_result(&empty, vec![], I64::sort_ref()).is_err());
    let scalar = I64::from(7).expression().clone();
    assert!(Expr::call_with_result(&of, vec![scalar.clone()], atoms).is_err());
    let vector = Expr::call_with_result(&of, vec![scalar.clone()], integers).unwrap();
    assert!(
        Expr::call_with_result(&get, vec![vector.clone(), scalar.clone()], I64::sort_ref()).is_ok()
    );
    assert!(Expr::call_with_result(&get, vec![vector, scalar], SortRef::equality("A")).is_err());
}

#[test]
fn generic_tail_patterns_keep_group_width_and_share_every_binding() {
    use super::{
        EgglogValue,
        builtins::{F64, I64},
    };
    // Locations 0/1 are binder variables; 2/3 are owned concrete scalar sorts.
    let declaration = |inputs: &[u32], tail: &[u32], output, parameters| {
        let catalog = super::storage::publish_catalog(pb::BuiltinCatalog {
            sorts: vec![
                pb::Sort {
                    kind: Some(pb::sort::Kind::Var(0)),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Var(1)),
                    ..Default::default()
                },
                I64::sort_ref().0.sort().unwrap().clone(),
                F64::sort_ref().0.sort().unwrap().clone(),
            ],
            primitive_sorts: vec![
                pb::PrimitiveSort {
                    name: "i64".into(),
                    arity: 0,
                    ..Default::default()
                },
                pb::PrimitiveSort {
                    name: "f64".into(),
                    arity: 0,
                    ..Default::default()
                },
            ],
            primitives: vec![pb::Primitive {
                name: "test.grouped".into(),
                signature: Some(pb::GenericSignature {
                    type_param_count: parameters,
                    inputs: inputs
                        .iter()
                        .map(|sort| pb::Arg {
                            sort: *sort,
                            ..Default::default()
                        })
                        .collect(),
                    varargs: tail
                        .iter()
                        .map(|sort| pb::Arg {
                            sort: *sort,
                            ..Default::default()
                        })
                        .collect(),
                    output: Some(output),
                }),
                ..Default::default()
            }],
            ..Default::default()
        })
        .unwrap();
        Callable(
            catalog
                .declaration("test.grouped", DeclarationKind::Callable)
                .unwrap(),
        )
    };
    let integer = I64::from(7).expression().clone();
    let float = F64::from(2.5).expression().clone();
    let huge = declaration(&[0], &[], 0, u32::MAX);
    assert!(
        matches!(huge.check_call(&[I64::sort_ref()], &I64::sort_ref()), Err(super::TypedError::Invalid(message)) if message == "undetermined generic parameter")
    );
    let fixed = declaration(&[0], &[], 0, 1);
    assert!(Expr::call_with_result(&fixed, vec![integer.clone()], I64::sort_ref()).is_ok());
    for arguments in [vec![], vec![integer.clone(), integer.clone()]] {
        assert!(Expr::call_with_result(&fixed, arguments, I64::sort_ref()).is_err());
    }
    let homogeneous = declaration(&[], &[0], 0, 1);
    assert!(Expr::call_with_result(&homogeneous, vec![], I64::sort_ref()).is_ok());
    assert!(
        Expr::call_with_result(&homogeneous, vec![integer.clone(); 3], I64::sort_ref()).is_ok()
    );
    let repeated = declaration(&[], &[0, 0], 0, 1);
    for count in [0, 2, 4] {
        assert!(
            Expr::call_with_result(&repeated, vec![integer.clone(); count], I64::sort_ref())
                .is_ok()
        );
    }
    for count in [1, 3] {
        assert!(
            Expr::call_with_result(&repeated, vec![integer.clone(); count], I64::sort_ref())
                .is_err(),
            "equal tail patterns must not collapse their group width"
        );
    }
    let pairs = declaration(&[1], &[0, 1], 0, 2);
    let valid = vec![
        float.clone(),
        integer.clone(),
        float.clone(),
        integer.clone(),
        float.clone(),
    ];
    assert!(Expr::call_with_result(&pairs, valid.clone(), I64::sort_ref()).is_ok());
    assert!(Expr::call_with_result(&pairs, vec![float.clone()], I64::sort_ref()).is_ok());
    assert!(Expr::call_with_result(&pairs, vec![], I64::sort_ref()).is_err());
    assert!(Expr::call_with_result(&pairs, valid[..4].to_vec(), I64::sort_ref()).is_err());
    assert!(Expr::call_with_result(&pairs, valid.clone(), F64::sort_ref()).is_err());
    let mut swapped = valid.clone();
    swapped.swap(1, 2);
    assert!(Expr::call_with_result(&pairs, swapped, I64::sort_ref()).is_err());
    for position in [0, 2, 4] {
        let mut invalid = valid.clone();
        invalid[position] = integer.clone();
        assert!(
            Expr::call_with_result(&pairs, invalid, I64::sort_ref()).is_err(),
            "fixed prefix and every group share the same substitution"
        );
    }
    let triples = declaration(&[], &[0, 1, 0], 0, 2);
    let mut arguments: Vec<_> = (0..3)
        .flat_map(|_| [integer.clone(), float.clone(), integer.clone()])
        .collect();
    assert!(Expr::call_with_result(&triples, arguments.clone(), I64::sort_ref()).is_ok());
    arguments[4] = integer.clone();
    assert!(
        Expr::call_with_result(&triples, arguments, I64::sort_ref()).is_err(),
        "a mismatch inside the middle group must be checked"
    );
    assert!(
        Expr::call_with_result(&declaration(&[], &[0, 1], 0, 2), vec![], I64::sort_ref()).is_err(),
        "result inference must not leave the other parameter undetermined"
    );
    assert!(
        Expr::call_with_result(&declaration(&[], &[0], 2, 1), vec![], I64::sort_ref()).is_err(),
        "a concrete result cannot determine an unused tail parameter"
    );
    assert!(
        Expr::call_with_result(
            &declaration(&[], &[2, 3], 2, 0),
            vec![integer.clone(), integer],
            I64::sort_ref()
        )
        .is_err(),
        "concrete tail positions are checked too"
    );
}

#[test]
fn grouped_builtin_demands_retain_every_tail_position() {
    use super::{
        EgglogValue,
        builtins::{F64, I64},
    };
    let declaration = |sorts: Vec<SortRef>, tail: Vec<u32>| {
        let catalog = super::storage::publish_catalog(pb::BuiltinCatalog {
            sorts: sorts
                .into_iter()
                .map(|s| s.0.sort().unwrap().clone())
                .collect(),
            primitive_sorts: vec![
                pb::PrimitiveSort {
                    name: "i64".into(),
                    arity: 0,
                    ..Default::default()
                },
                pb::PrimitiveSort {
                    name: "f64".into(),
                    arity: 0,
                    ..Default::default()
                },
            ],
            primitives: vec![pb::Primitive {
                name: "test.relocated.group".into(),
                signature: Some(pb::GenericSignature {
                    inputs: vec![pb::Arg {
                        sort: tail[0],
                        name: "prefix".into(),
                    }],
                    output: Some(tail[0]),
                    varargs: tail
                        .into_iter()
                        .enumerate()
                        .map(|(i, sort)| pb::Arg {
                            sort,
                            name: format!("item{i}"),
                        })
                        .collect(),
                    ..Default::default()
                }),
                doc: Some("retain complete grouped record".into()),
                ..Default::default()
            }],
            ..Default::default()
        })
        .unwrap();
        Callable(
            catalog
                .declaration("test.relocated.group", DeclarationKind::Callable)
                .unwrap(),
        )
    };
    let original = declaration(vec![I64::sort_ref(), F64::sort_ref()], vec![0, 1, 0]);
    let relocated = declaration(vec![F64::sort_ref(), I64::sort_ref()], vec![1, 0, 1]);
    let changed = declaration(vec![I64::sort_ref(), I64::sort_ref()], vec![0, 1, 0]);
    assert!(super::decl::same_callable(&original.0, &relocated.0).unwrap());
    assert!(super::decl::same_callable(&original.0, &changed.0).is_err());
    for callable in [&original, &relocated] {
        let mut packer = Packer::default();
        packer.intern(callable.0.clone(), 0);
        packer.finish().unwrap();
        assert!(packer.program.declarations.is_empty());
        assert!(packer.program.sorts.is_empty());
        let demand = &packer.builtin_demands[0];
        let primitive = demand.primitive().unwrap();
        assert_eq!(
            primitive.doc.as_deref(),
            Some("retain complete grouped record")
        );
        let Some(signature) = &primitive.signature else {
            panic!()
        };
        assert_eq!(signature.varargs.len(), 3);
        for (position, (arg, name)) in signature
            .varargs
            .iter()
            .zip(["i64", "f64", "i64"])
            .enumerate()
        {
            assert_eq!(arg.name, format!("item{position}"));
            assert!(
                matches!(&demand.resolve(Arena::Sort,arg.sort).unwrap().sort().unwrap().kind,
                Some(pb::sort::Kind::Primitive(f)) if f.name == name)
            );
        }
    }
}

#[test]
fn set_values_relocate_without_changing_order_multiplicity_or_occurrences() {
    use super::{
        EgglogValue,
        builtins::{I64, Set},
    };
    use std::hash::{DefaultHasher, Hash, Hasher};
    let value = |items, children| {
        Set::<I64>::from_expression(Expr(node(
            &Set::<I64>::sort_ref(),
            pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Set(pb::ValueList { items })),
            }),
            children,
            vec![],
        )))
    };
    let first = I64::from(7).expression().0.clone();
    let second = I64::from(11).expression().0.clone();
    let a = value(vec![0, 1, 0], vec![first.clone(), second.clone()]);
    let relocated = value(vec![1, 0, 1], vec![second.clone(), first.clone()]);
    assert_eq!(a, relocated);
    assert_ne!(a, value(vec![0, 1, 0], vec![second.clone(), first.clone()]));
    assert_ne!(a, value(vec![0, 1], vec![first, second]));
    let mut ah = DefaultHasher::new();
    let mut bh = DefaultHasher::new();
    a.hash(&mut ah);
    relocated.hash(&mut bh);
    assert_eq!(ah.finish(), bh.finish());
    let packed = packed_query(std::slice::from_ref(&a.expression().0));
    assert_eq!(
        packed,
        packed_query(std::slice::from_ref(&relocated.expression().0))
    );
    assert_eq!(
        pb::Program::decode(packed.encode_to_vec().as_slice()).unwrap(),
        packed
    );
    let members = Vec::<I64>::try_from(&a).unwrap();
    assert_eq!(members, [I64::from(7), I64::from(11), I64::from(7)]);
    assert_eq!(
        members[0].expression().0.index,
        members[2].expression().0.index
    );
    let parent = Arc::downgrade(a.expression().0.owner.as_ref().unwrap());
    drop(a);
    assert!(
        parent.upgrade().is_none(),
        "children do not retain authored parents"
    );

    let named = super::var::<I64>("__typed_v_0");
    let fresh = super::expr::variable::<I64>(super::expr::fresh_scope(), 0);
    let open = value(
        vec![1, 0, 1],
        vec![named.expression().0.clone(), fresh.expression().0.clone()],
    );
    assert_eq!(
        Vec::<I64>::try_from(&open).unwrap(),
        [fresh.clone(), named, fresh]
    );
    assert!(open.expression().validate_inert().is_err());
    let packed = packed_query(&[open.expression().0.clone()]);
    let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
        value: Some(pb::primitive_value::Value::Set(items)),
    })) = &packed.nodes[0].kind
    else {
        panic!()
    };
    assert_eq!(items.items[0], items.items[2]);
    assert!(
        matches!(&packed.nodes[items.items[0] as usize].kind, Some(pb::node::Kind::Var(name)) if name == "__typed_v_1")
    );
    assert!(
        matches!(&packed.nodes[items.items[1] as usize].kind, Some(pb::node::Kind::Var(name)) if name == "__typed_v_0")
    );

    let atom = SortRef::equality("SetOccurrenceAtom");
    let family = super::storage::builtin_catalog()
        .declaration("Set", DeclarationKind::PrimitiveSort)
        .unwrap();
    let set = SortRef::family(&family, vec![atom.clone()]).unwrap();
    let union = || {
        node(
            &atom,
            pb::node::Kind::Union(pb::Union { members: vec![] }),
            vec![],
            vec![],
        )
    };
    let set_value = |children| {
        Expr(node(
            &set,
            pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Set(pb::ValueList {
                    items: vec![0, 1],
                })),
            }),
            children,
            vec![],
        ))
    };
    let first = union();
    let shared = set_value(vec![first.clone(), first.clone()]);
    assert_eq!(shared, set_value(vec![first.clone(), first.clone()]));
    let distinct = set_value(vec![first, union()]);
    assert_ne!(shared, distinct);
    for (expr, same) in [(shared, true), (distinct, false)] {
        let packed = packed_query(&[expr.0]);
        let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Set(items)),
        })) = &packed.nodes[0].kind
        else {
            panic!()
        };
        assert_eq!(items.items[0] == items.items[1], same);
        for index in &items.items {
            assert!(matches!(
                packed.nodes[*index as usize].kind,
                Some(pb::node::Kind::Union(_))
            ));
        }
    }
}

#[test]
fn set_payload_walkers_handle_deep_finite_data_iteratively() {
    use std::hash::{DefaultHasher, Hash, Hasher};
    let atom = SortRef::equality("SetDeepAtom");
    let family = super::storage::builtin_catalog()
        .declaration("Set", DeclarationKind::PrimitiveSort)
        .unwrap();
    let set = SortRef::family(&family, vec![atom.clone()]).unwrap();
    let leaf = Callable::constructor("SetDeepLeaf", vec![], atom.clone(), None, false);
    let pack = Callable::constructor("SetDeepPack", vec![set.clone()], atom, None, false);
    let chain = || {
        let mut term = Expr::call(&leaf, vec![]);
        for _ in 0..10_000 {
            let value = Expr(node(
                &set,
                pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Set(pb::ValueList {
                        items: vec![0],
                    })),
                }),
                vec![term.0],
                vec![],
            ));
            term = Expr::call(&pack, vec![value]);
        }
        term
    };
    let a = chain();
    let b = chain();
    a.validate_inert().unwrap();
    assert_eq!(a, b);
    let mut ah = DefaultHasher::new();
    let mut bh = DefaultHasher::new();
    a.hash(&mut ah);
    b.hash(&mut bh);
    assert_eq!(ah.finish(), bh.finish());
    let packed = packed_query(std::slice::from_ref(&a.0));
    assert_eq!(packed.nodes.len(), 20_001);
    std::thread::spawn(move || drop((a, b))).join().unwrap();
}

#[test]
fn map_values_preserve_order_aliases_structural_hash_and_open_binders() {
    use super::{
        EgglogValue,
        builtins::{I64, Map},
    };
    use std::hash::{DefaultHasher, Hash, Hasher};
    let value = |entries: Vec<[u32; 2]>, children| {
        Map::<I64, I64>::from_expression(Expr(node(
            &Map::<I64, I64>::sort_ref(),
            pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Map(pb::MapValue {
                    entries: entries
                        .into_iter()
                        .map(|[key, value]| pb::MapEntry {
                            key: Some(key),
                            value: Some(value),
                        })
                        .collect(),
                })),
            }),
            children,
            vec![],
        )))
    };
    let first = I64::from(7).expression().0.clone();
    let second = I64::from(11).expression().0.clone();
    let a = value(vec![[0, 1], [0, 0]], vec![first.clone(), second.clone()]);
    let relocated = value(vec![[1, 0], [1, 1]], vec![second.clone(), first.clone()]);
    let swapped = value(vec![[0, 0], [0, 1]], vec![first.clone(), second]);
    assert_eq!(a, relocated);
    assert_ne!(a, swapped);
    assert_ne!(a, value(vec![[0, 0]], vec![first]));
    let mut ah = DefaultHasher::new();
    let mut bh = DefaultHasher::new();
    a.hash(&mut ah);
    relocated.hash(&mut bh);
    assert_eq!(ah.finish(), bh.finish());
    assert_eq!(
        packed_query(std::slice::from_ref(&a.expression().0)),
        packed_query(std::slice::from_ref(&relocated.expression().0))
    );
    a.expression().validate_inert().unwrap();
    let parent = Arc::downgrade(a.expression().0.owner.as_ref().unwrap());
    let entries = a.entries().unwrap();
    assert_eq!(
        entries,
        [(I64::from(7), I64::from(11)), (I64::from(7), I64::from(7))]
    );
    assert!(Arc::ptr_eq(
        entries[0].0.expression().0.owner.as_ref().unwrap(),
        entries[1].1.expression().0.owner.as_ref().unwrap()
    ));
    assert_eq!(
        entries[0].0.expression().0.index,
        entries[1].1.expression().0.index
    );
    drop(a);
    assert!(
        parent.upgrade().is_none(),
        "entry children retain their own owners"
    );
    let open = value(
        vec![[0, 1]],
        vec![
            super::var::<I64>("key").expression().0.clone(),
            super::expr::variable::<I64>(super::expr::fresh_scope(), 0)
                .expression()
                .0
                .clone(),
        ],
    );
    assert!(open.entries().is_ok());
    assert!(open.expression().validate_inert().is_err());
    let closed = packed_query(std::slice::from_ref(&open.expression().0));
    for name in ["key", "__typed_v_0"] {
        assert!(
            closed
                .nodes
                .iter()
                .any(|n| matches!(&n.kind, Some(pb::node::Kind::Var(v)) if v == name))
        );
    }
}

#[test]
fn map_inspection_rejects_same_headed_user_calls_and_wrong_children() {
    use super::{
        EgglogValue,
        builtins::{F64, I64, Map, Pair, Vec as EVec},
    };
    let pairs = EVec::<Pair<I64, F64>>::of([Pair::new(1_i64, 2.5_f64)]);
    for name in ["map-of", "map-from-pairs", "egglog.core.map.of"] {
        let fake = Callable::constructor(
            name,
            vec![EVec::<Pair<I64, F64>>::sort_ref()],
            Map::<I64, F64>::sort_ref(),
            None,
            false,
        );
        let map =
            Map::<I64, F64>::from_expression(Expr::call(&fake, vec![pairs.expression().clone()]));
        assert!(map.entries().is_err());
    }
    for name in [
        "vec-empty",
        "vec-of",
        "egglog.core.vec.empty",
        "egglog.core.vec.of",
    ] {
        let fake = Callable::constructor(
            name,
            vec![],
            EVec::<Pair<I64, F64>>::sort_ref(),
            None,
            false,
        );
        let pairs = EVec::<Pair<I64, F64>>::from_expression(Expr::call(&fake, vec![]));
        assert!(Map::<I64, F64>::from_pairs(pairs).entries().is_err());
    }
    for name in ["pair", "egglog.core.pair.make"] {
        let fake = Callable::constructor(
            name,
            vec![I64::sort_ref(), F64::sort_ref()],
            Pair::<I64, F64>::sort_ref(),
            None,
            false,
        );
        let pair = Pair::<I64, F64>::from_expression(Expr::call(
            &fake,
            vec![
                I64::from(1).expression().clone(),
                F64::from(2.5).expression().clone(),
            ],
        ));
        assert!(
            Map::<I64, F64>::from_pairs(EVec::of([pair]))
                .entries()
                .is_err()
        );
    }
    let nominal = SortRef::equality("Map");
    let fake = Map::<I64, F64>::from_expression(Expr::call(
        &Callable::constructor("map-empty", vec![], nominal, None, false),
        vec![],
    ));
    assert!(fake.entries().is_err());
    for imports in [
        vec![
            F64::from(1.0).expression().0.clone(),
            F64::from(2.5).expression().0.clone(),
        ],
        vec![
            I64::from(1).expression().0.clone(),
            I64::from(2).expression().0.clone(),
        ],
    ] {
        let malformed = Map::<I64, F64>::from_expression(Expr(node(
            &Map::<I64, F64>::sort_ref(),
            pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Map(pb::MapValue {
                    entries: vec![pb::MapEntry {
                        key: Some(0),
                        value: Some(1),
                    }],
                })),
            }),
            imports,
            vec![],
        )));
        assert!(malformed.entries().is_err());
        assert!(malformed.expression().validate_inert().is_err());
    }
    // Data inspection retains symbolic child records; from_pairs remains an
    // operation even when its argument is a direct Vec of Pair data.
    let key = super::var::<I64>("k");
    let value = F64::from(2.5);
    let pair = node(
        &Pair::<I64, F64>::sort_ref(),
        pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Pair(pb::PairValue {
                first: Some(0),
                second: Some(1),
            })),
        }),
        vec![key.expression().0.clone(), value.expression().0.clone()],
        vec![],
    );
    let vector = EVec::<Pair<I64, F64>>::from_expression(Expr(node(
        &EVec::<Pair<I64, F64>>::sort_ref(),
        pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Vec(pb::ValueList {
                items: vec![0, 0],
            })),
        }),
        vec![pair],
        vec![],
    )));
    let children = Vec::<Pair<I64, F64>>::try_from(&vector).unwrap();
    assert_eq!(children.len(), 2);
    assert_eq!(children[0].fields().unwrap(), (key, value));
    assert!(Map::<I64, F64>::from_pairs(vector).entries().is_err());
}

#[test]
fn map_publication_requires_both_refs_and_preserves_union_identity() {
    use super::{
        EgglogValue,
        builtins::{I64, Map},
    };
    let sort = Map::<I64, I64>::sort_ref();
    for (key, value) in [
        (None, Some(0)),
        (Some(0), None),
        (Some(99), Some(0)),
        (Some(0), Some(99)),
    ] {
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Sort as usize] = vec![Slot::External(sort.0.clone())];
        slots[Arena::Node as usize] = vec![Slot::External(I64::from(7).expression().0.clone())];
        assert!(
            publish(
                pb::Program {
                    nodes: vec![pb::Node {
                        kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                            value: Some(pb::primitive_value::Value::Map(pb::MapValue {
                                entries: vec![pb::MapEntry { key, value }]
                            })),
                        })),
                        ..Default::default()
                    }],
                    ..Default::default()
                },
                slots,
                vec![],
                Arena::Node,
                0,
                vec![]
            )
            .is_err()
        );
    }
    let atom = SortRef::equality("Atom");
    let family = super::storage::builtin_catalog()
        .declaration("Map", DeclarationKind::PrimitiveSort)
        .unwrap();
    let sort = SortRef::family(&family, vec![atom.clone(), atom.clone()]).unwrap();
    let union = || {
        node(
            &atom,
            pb::node::Kind::Union(pb::Union { members: vec![] }),
            vec![],
            vec![],
        )
    };
    let first = union();
    let value = |children| {
        Expr(node(
            &sort,
            pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Map(pb::MapValue {
                    entries: vec![pb::MapEntry {
                        key: Some(0),
                        value: Some(1),
                    }],
                })),
            }),
            children,
            vec![],
        ))
    };
    let shared = value(vec![first.clone(), first.clone()]);
    assert_eq!(shared, value(vec![first.clone(), first.clone()]));
    assert_ne!(shared, value(vec![first, union()]));
    let packed = packed_query(&[shared.0]);
    let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
        value: Some(pb::primitive_value::Value::Map(map)),
    })) = &packed.nodes[0].kind
    else {
        panic!()
    };
    assert_eq!(map.entries[0].key, map.entries[0].value);
    assert!(matches!(
        packed.nodes[map.entries[0].key.unwrap() as usize].kind,
        Some(pb::node::Kind::Union(_))
    ));
}

#[test]
fn pair_fields_relocate_preserve_aliases_and_reject_impostors() {
    use super::{
        EgglogValue,
        builtins::{F64, I64},
    };
    use std::hash::{DefaultHasher, Hash, Hasher};
    let catalog = super::storage::builtin_catalog();
    let family = catalog
        .declaration("Pair", DeclarationKind::PrimitiveSort)
        .unwrap();
    let sort = SortRef::family(&family, vec![I64::sort_ref(), I64::sort_ref()]).unwrap();
    let value = |indices: [u32; 2], children| {
        Expr(node(
            &sort,
            pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Pair(pb::PairValue {
                    first: Some(indices[0]),
                    second: Some(indices[1]),
                })),
            }),
            children,
            vec![],
        ))
    };
    let first = I64::from(7).expression().0.clone();
    let second = I64::from(11).expression().0.clone();
    let a = value([0, 1], vec![first.clone(), second.clone()]);
    let relocated = value([1, 0], vec![second.clone(), first.clone()]);
    let swapped = value([0, 1], vec![second, first.clone()]);
    assert_eq!(a, relocated);
    assert_ne!(a, swapped);
    let mut ah = DefaultHasher::new();
    let mut bh = DefaultHasher::new();
    a.hash(&mut ah);
    relocated.hash(&mut bh);
    assert_eq!(ah.finish(), bh.finish());
    assert_eq!(
        packed_query(std::slice::from_ref(&a.0)),
        packed_query(&[relocated.0])
    );
    let repeated = value([0, 0], vec![first]);
    let parent = Arc::downgrade(repeated.0.owner.as_ref().unwrap());
    let [left, right] = repeated
        .pair_fields(&I64::sort_ref(), &I64::sort_ref())
        .unwrap();
    assert!(Arc::ptr_eq(
        left.0.owner.as_ref().unwrap(),
        right.0.owner.as_ref().unwrap()
    ));
    assert_eq!(left.0.index, right.0.index);
    drop(repeated);
    assert!(
        parent.upgrade().is_none(),
        "fields must not retain the parent"
    );
    assert_eq!(i64::try_from(&I64::from_expression(left)).unwrap(), 7);

    let variable = super::var::<I64>("named");
    let fresh = super::expr::variable::<I64>(super::expr::fresh_scope(), 0);
    let open = value(
        [1, 0],
        vec![
            variable.expression().0.clone(),
            fresh.expression().0.clone(),
        ],
    );
    assert!(open.pair_fields(&I64::sort_ref(), &I64::sort_ref()).is_ok());
    assert!(open.validate_inert().is_err());
    let closed = packed_query(&[open.0]);
    assert!(
        closed
            .nodes
            .iter()
            .any(|n| matches!(&n.kind, Some(pb::node::Kind::Var(v)) if v == "named"))
    );
    assert!(
        closed
            .nodes
            .iter()
            .any(|n| matches!(&n.kind, Some(pb::node::Kind::Var(v)) if v == "__typed_v_0"))
    );
    assert!(a.pair_fields(&F64::sort_ref(), &I64::sort_ref()).is_err());
    let wrong_child = value(
        [0, 1],
        vec![
            I64::from(1).expression().0.clone(),
            F64::from(1.0).expression().0.clone(),
        ],
    );
    assert!(
        wrong_child
            .pair_fields(&I64::sort_ref(), &I64::sort_ref())
            .is_err()
    );
    assert!(wrong_child.validate_inert().is_err());
    for name in ["pair", "egglog.core.pair.make"] {
        let fake = Callable::constructor(
            name,
            vec![I64::sort_ref(), I64::sort_ref()],
            sort.clone(),
            None,
            false,
        );
        let call = Expr::call(
            &fake,
            vec![
                I64::from(1).expression().clone(),
                I64::from(2).expression().clone(),
            ],
        );
        assert!(
            call.pair_fields(&I64::sort_ref(), &I64::sort_ref())
                .is_err()
        );
    }
    let nominal = SortRef::equality("Pair");
    let fake = Expr::call(
        &Callable::constructor("pair", vec![], nominal, None, false),
        vec![],
    );
    assert!(
        fake.pair_fields(&I64::sort_ref(), &I64::sort_ref())
            .is_err()
    );
}

#[test]
fn pair_publication_requires_both_valid_references() {
    use super::{EgglogValue, builtins::I64};
    let catalog = super::storage::builtin_catalog();
    let family = catalog
        .declaration("Pair", DeclarationKind::PrimitiveSort)
        .unwrap();
    let sort = SortRef::family(&family, vec![I64::sort_ref(), I64::sort_ref()]).unwrap();
    for (first, second) in [
        (None, Some(0)),
        (Some(0), None),
        (Some(99), Some(0)),
        (Some(0), Some(99)),
    ] {
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Sort as usize] = vec![Slot::External(sort.0.clone())];
        slots[Arena::Node as usize] = vec![Slot::External(I64::from(7).expression().0.clone())];
        assert!(
            publish(
                pb::Program {
                    nodes: vec![pb::Node {
                        kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                            value: Some(pb::primitive_value::Value::Pair(pb::PairValue {
                                first,
                                second
                            })),
                        })),
                        ..Default::default()
                    }],
                    ..Default::default()
                },
                slots,
                vec![],
                Arena::Node,
                0,
                vec![]
            )
            .is_err()
        );
    }
}

#[test]
fn pair_values_keep_union_allocation_identity() {
    let atom = SortRef::equality("Atom");
    let catalog = super::storage::builtin_catalog();
    let family = catalog
        .declaration("Pair", DeclarationKind::PrimitiveSort)
        .unwrap();
    let sort = SortRef::family(&family, vec![atom.clone(), atom.clone()]).unwrap();
    let union = || {
        node(
            &atom,
            pb::node::Kind::Union(pb::Union { members: vec![] }),
            vec![],
            vec![],
        )
    };
    let first = union();
    let value = |children| {
        Expr(node(
            &sort,
            pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Pair(pb::PairValue {
                    first: Some(0),
                    second: Some(1),
                })),
            }),
            children,
            vec![],
        ))
    };
    let shared = value(vec![first.clone(), first.clone()]);
    let same = value(vec![first.clone(), first.clone()]);
    let distinct = value(vec![first, union()]);
    assert_eq!(shared, same);
    assert_ne!(shared, distinct);
    let [left, right] = shared.pair_fields(&atom, &atom).unwrap();
    assert_eq!(left, right);
    let packed = packed_query(&[shared.0]);
    let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
        value: Some(pb::primitive_value::Value::Pair(pair)),
    })) = &packed.nodes[0].kind
    else {
        panic!()
    };
    assert_eq!(pair.first, pair.second);
    assert!(matches!(
        packed.nodes[pair.first.unwrap() as usize].kind,
        Some(pb::node::Kind::Union(_))
    ));
}

#[test]
fn vec_calls_and_values_preserve_actual_ordered_child_records() {
    use super::{
        EgglogValue,
        builtins::{I64, Vec as EVec},
    };
    let leaf = I64::from(7);
    let vector = EVec::<I64>::of([leaf.clone(), I64::from(11), leaf.clone()]);
    let weak = Arc::downgrade(vector.expression().0.owner.as_ref().unwrap());
    let p = packed_query(&[vector.expression().0.clone()]);
    let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
        value: Some(pb::primitive_value::Value::Vec(values)),
    })) = &p.nodes[0].kind
    else {
        panic!()
    };
    assert_eq!(values.items.len(), 3);
    assert_eq!(values.items[0], values.items[2]);
    for (index, expected) in values.items.iter().zip([7, 11, 7]) {
        assert!(matches!(&p.nodes[*index as usize].kind,
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue { value: Some(pb::primitive_value::Value::I64(v)) })) if *v == expected));
    }
    let owner = vector.expression().0.owner.as_ref().unwrap();
    assert_eq!(owner.program().unwrap().nodes.len(), 1);
    assert_eq!(owner.slots[Arena::Node as usize].len(), 3);
    drop(vector);
    assert!(
        weak.upgrade().is_none(),
        "retained leaf must not retain parent"
    );
    let sort = EVec::<I64>::sort_ref();
    let first = leaf.expression().0.clone();
    let second = I64::from(11).expression().0.clone();
    let value = |items, imports| {
        Expr(node(
            &sort,
            pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Vec(pb::ValueList { items })),
            }),
            imports,
            vec![],
        ))
    };
    let a = value(vec![0, 1, 0], vec![first.clone(), second.clone()]);
    let relocated = value(vec![1, 0, 1], vec![second.clone(), first.clone()]);
    let different = value(vec![0, 1, 0], vec![second, first]);
    assert_eq!(a, relocated);
    assert_ne!(
        a, different,
        "raw equal ValueList indices are not equal values"
    );
    let mut ah = std::hash::DefaultHasher::new();
    let mut bh = std::hash::DefaultHasher::new();
    std::hash::Hash::hash(&a, &mut ah);
    std::hash::Hash::hash(&relocated, &mut bh);
    assert_eq!(
        std::hash::Hasher::finish(&ah),
        std::hash::Hasher::finish(&bh)
    );

    let named = super::var::<I64>("__typed_v_0");
    let fresh = super::expr::variable::<I64>(super::expr::fresh_scope(), 0);
    let with_variables = value(
        vec![1, 0, 1],
        vec![named.expression().0.clone(), fresh.expression().0.clone()],
    );
    let p = packed_query(&[with_variables.0]);
    let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
        value: Some(pb::primitive_value::Value::Vec(items)),
    })) = &p.nodes[0].kind
    else {
        panic!()
    };
    assert_eq!(items.items[0], items.items[2]);
    assert!(matches!(&p.nodes[items.items[0] as usize].kind,
        Some(pb::node::Kind::Var(name)) if name == "__typed_v_1"));
    assert!(matches!(&p.nodes[items.items[1] as usize].kind,
        Some(pb::node::Kind::Var(name)) if name == "__typed_v_0"));

    let atom = SortRef::equality("VecOwnershipAtom");
    let family = super::storage::builtin_catalog()
        .declaration("Vec", DeclarationKind::PrimitiveSort)
        .unwrap();
    let vector_sort = SortRef::family(&family, vec![atom.clone()]).unwrap();
    let leaf = Expr::call(
        &Callable::constructor("Leaf", vec![], atom.clone(), None, false),
        vec![],
    );
    let pack = Callable::constructor("Pack", vec![vector_sort.clone()], atom, None, false);
    for growing_first in [false, true] {
        let mut term = leaf.clone();
        for _ in 0..100_000 {
            let children = if growing_first {
                vec![term, leaf.clone()]
            } else {
                vec![leaf.clone(), term]
            };
            let vector = Expr::container(vector_sort.clone(), children).unwrap();
            let owner = vector.0.owner.as_ref().unwrap();
            assert_eq!(owner.program().unwrap().nodes.len(), 1);
            assert_eq!(owner.slots[Arena::Node as usize].len(), 2);
            assert_eq!(owner.declarations.len(), 0);
            term = Expr::call(&pack, vec![vector]);
        }
        let weak = Arc::downgrade(term.0.owner.as_ref().unwrap());
        std::thread::spawn(move || drop(term)).join().unwrap();
        assert!(weak.upgrade().is_none());
    }
}

#[test]
// Symbolic Add preserves ordered children; swapping operands also changes
// which operator implementation owns the growing input. It is not arithmetic.
#[allow(clippy::if_same_then_else)]
fn scalar_records_remain_authoritative_and_parents_are_reclaimed() {
    use super::{EgglogValue, builtins::I64};
    let leaf = I64::from(7);
    let a = &leaf + I64::from(11);
    let weak = Arc::downgrade(a.expression().0.owner.as_ref().unwrap());
    let packed = packed_query(&[a.expression().0.clone()]);
    let Some(pb::node::Kind::Call(call)) = &packed.nodes[0].kind else {
        panic!()
    };
    assert_eq!(call.func, "egglog.core.i64.add");
    assert_eq!(call.args.len(), 2);
    for (id, expected) in call.args.iter().zip([7, 11]) {
        assert!(matches!(&packed.nodes[*id as usize].kind,
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::I64(value))
            })) if *value == expected));
    }
    assert_eq!(
        packed.declarations.len(),
        0,
        "builtin descriptors remain in the ambient catalog"
    );
    drop(a);
    assert!(
        weak.upgrade().is_none(),
        "retained leaf cannot retain parents"
    );
    for left in [false, true] {
        let mut value = leaf.clone();
        for _ in 0..100_000 {
            value = if left { value + &leaf } else { &leaf + value };
            let owner = value.expression().0.owner.as_ref().unwrap();
            assert_eq!(owner.program().unwrap().nodes.len(), 1);
            assert_eq!(owner.slots[Arena::Node as usize].len(), 2);
            assert_eq!(owner.declarations.len(), 1);
        }
        let weak = Arc::downgrade(value.expression().0.owner.as_ref().unwrap());
        std::thread::spawn(move || drop(value)).join().unwrap();
        assert!(weak.upgrade().is_none());
    }
}

#[test]
fn builtin_calls_read_owned_definitions_not_cached_signatures() {
    use super::{EgglogValue, builtins::I64};
    let mut catalog =
        pb::BuiltinCatalog::decode(include_bytes!("builtins/catalog.pb").as_slice()).unwrap();
    let primitive = catalog
        .primitives
        .iter_mut()
        .find(|p| p.name == "egglog.core.i64.add")
        .unwrap();
    primitive.name = "test.changed.generated.key".into();
    let context = super::storage::publish_catalog(catalog).unwrap();
    let callable = Callable(
        context
            .declaration("test.changed.generated.key", DeclarationKind::Callable)
            .unwrap(),
    );
    let call = Expr::call(
        &callable,
        vec![
            I64::from(7).expression().clone(),
            I64::from(11).expression().clone(),
        ],
    );
    drop(context);
    let packed = packed_query(&[call.0]);
    assert!(
        matches!(&packed.nodes[0].kind,Some(pb::node::Kind::Call(c)) if c.func == "test.changed.generated.key")
    );
    assert!(
        packed.declarations.is_empty(),
        "backend descriptors never enter Programs"
    );
}

// A private raw-record builder lets tests mutate only generated fields before
// immutable publication, without an authoring-side semantic representation.
fn node(
    sort: &SortRef,
    kind: pb::node::Kind,
    imports: Vec<Record>,
    declarations: Vec<Record>,
) -> Record {
    let mut slots = std::array::from_fn(|_| vec![]);
    slots[Arena::Node as usize] = imports.into_iter().map(Slot::External).collect();
    slots[Arena::Sort as usize] = vec![Slot::External(sort.0.clone())];
    publish(
        pb::Program {
            nodes: vec![pb::Node {
                kind: Some(kind),
                ..Default::default()
            }],
            ..Default::default()
        },
        slots,
        declarations,
        Arena::Node,
        0,
        vec![],
    )
    .unwrap()
}

fn packed_query(roots: &[Record]) -> pb::Program {
    let mut packer = Packer::default();
    packer.binders.push(close::binder(roots).unwrap());
    let facts = roots.iter().map(|r| packer.intern(r.clone(), 1)).collect();
    packer.program.commands.push(pb::Command {
        kind: Some(pb::command::Kind::Check(pb::Check { facts })),
        ..Default::default()
    });
    packer.finish().unwrap();
    packer.program
}

#[test]
fn generated_var_authority_determinism_and_whole_binder_names() {
    let sort = SortRef::equality("M");
    let fresh = |n| {
        node(
            &sort,
            pb::node::Kind::Var(format!("@typed:f:{n}:0")),
            vec![],
            vec![],
        )
    };
    let named = node(
        &sort,
        pb::node::Kind::Var("@typed:n:5f5f74797065645f765f30".into()),
        vec![],
        vec![],
    ); // __typed_v_0
    let a = fresh(7);
    let b = fresh(8);
    let first = packed_query(&[a.clone(), b.clone(), a.clone(), named.clone()]);
    // Construction/allocation order and fresh-token magnitude are not ordering.
    let d = fresh(99);
    let c = fresh(100);
    let second = packed_query(&[c, d, a.clone(), named.clone()]);
    let repeated = packed_query(&[fresh(100), fresh(99), fresh(100), named.clone()]);
    // Different owner aliases versus equal fresh strings preserve the same
    // variable equivalence, though ordinary Node sharing need not match bytes.
    let Some(pb::node::Kind::Var(name)) = &first.nodes[0].kind else {
        panic!()
    };
    assert_eq!(name, "__typed_v_1");
    assert_ne!(first.encode_to_vec(), second.encode_to_vec());
    let aa = fresh(100);
    let bb = fresh(99);
    assert_eq!(
        first.encode_to_vec(),
        packed_query(&[aa.clone(), bb, aa, named]).encode_to_vec()
    );
    assert_eq!(repeated.nodes[0].kind, repeated.nodes[2].kind);
    let changed = node(
        &sort,
        pb::node::Kind::Var("@typed:n:78".into()),
        vec![],
        vec![],
    );
    assert_ne!(Expr(a.clone()), Expr(changed.clone()));
    assert_eq!(
        packed_query(&[changed]).nodes[0].kind,
        Some(pb::node::Kind::Var("x".into()))
    );
    assert!(
        close::binder(&[node(
            &sort,
            pb::node::Kind::Var("foreign".into()),
            vec![],
            vec![]
        )])
        .is_err()
    );
}

#[test]
fn context_sensitive_packing_and_slot_permutation() {
    let sort = SortRef::equality("M");
    let a = node(
        &sort,
        pb::node::Kind::Var("@typed:f:1:0".into()),
        vec![],
        vec![],
    );
    let b = node(
        &sort,
        pb::node::Kind::Var("@typed:f:2:0".into()),
        vec![],
        vec![],
    );
    let call = Callable::constructor(
        "Pair",
        vec![sort.clone(), sort.clone()],
        sort.clone(),
        None,
        false,
    );
    let original = node(
        &sort,
        pb::node::Kind::Call(pb::Call {
            func: "Pair".into(),
            args: vec![0, 1],
        }),
        vec![a.clone(), b.clone()],
        vec![call.0.clone()],
    );
    let permuted = node(
        &sort,
        pb::node::Kind::Call(pb::Call {
            func: "Pair".into(),
            args: vec![1, 0],
        }),
        vec![b.clone(), a.clone()],
        vec![call.0.clone()],
    );
    assert_eq!(
        packed_query(std::slice::from_ref(&original)).encode_to_vec(),
        packed_query(&[permuted]).encode_to_vec()
    );
    let mut p = Packer::default();
    p.binders
        .push(close::binder(&[a.clone(), b.clone()]).unwrap());
    p.binders
        .push(close::binder(&[b.clone(), a.clone()]).unwrap());
    let first = p.intern(original.clone(), 1);
    let second = p.intern(original, 2);
    p.finish().unwrap();
    assert_ne!(first, second);
    let args = |i: u32| {
        let Some(pb::node::Kind::Call(c)) = &p.program.nodes[i as usize].kind else {
            panic!()
        };
        c.args.clone()
    };
    let one = args(first);
    let two = args(second);
    assert_ne!(
        p.program.nodes[one[0] as usize].kind,
        p.program.nodes[two[0] as usize].kind
    );
    assert_eq!(
        p.program.nodes[one[0] as usize].kind,
        p.program.nodes[two[1] as usize].kind
    );
    // Only the generated callee changes, and the descriptor selected changes.
    let other = Callable::constructor(
        "Other",
        vec![sort.clone(), sort.clone()],
        sort.clone(),
        None,
        false,
    );
    let changed = node(
        &sort,
        pb::node::Kind::Call(pb::Call {
            func: "Other".into(),
            args: vec![1, 0],
        }),
        vec![a, b],
        vec![call.0, other.0],
    );
    let packed = packed_query(&[changed]);
    assert!(packed.declarations.iter().any(
        |d| matches!(&d.kind, Some(pb::declaration::Kind::Constructor(c)) if c.name == "Other")
    ));
    assert!(!packed.declarations.iter().any(
        |d| matches!(&d.kind, Some(pb::declaration::Kind::Constructor(c)) if c.name == "Pair")
    ));
}

#[test]
fn shared_union_identity_and_flat_cycle_reclamation() {
    let sort = SortRef::equality("M");
    let a = node(
        &sort,
        pb::node::Kind::Union(pb::Union { members: vec![] }),
        vec![],
        vec![],
    );
    let b = node(
        &sort,
        pb::node::Kind::Union(pb::Union { members: vec![] }),
        vec![],
        vec![],
    );
    assert_ne!(Expr(a.clone()), Expr(b.clone()));
    let mut p = Packer::default();
    assert_eq!(p.intern(a.clone(), 0), p.intern(a, 0));
    assert_ne!(p.intern(b, 0), 0);
    p.finish().unwrap();
    assert_eq!(p.program.nodes.len(), 2);
    let mut slots = std::array::from_fn(|_| vec![]);
    slots[Arena::Node as usize] = vec![Slot::Local(0)];
    slots[Arena::Sort as usize] = vec![Slot::External(sort.0)];
    let cycle = publish(
        pb::Program {
            nodes: vec![pb::Node {
                kind: Some(pb::node::Kind::Union(pb::Union { members: vec![0] })),
                ..Default::default()
            }],
            ..Default::default()
        },
        slots,
        vec![],
        Arena::Node,
        0,
        vec![],
    )
    .unwrap();
    let weak = Arc::downgrade(cycle.owner.as_ref().unwrap());
    let mut p = Packer::default();
    p.intern(cycle.clone(), 0);
    p.finish().unwrap();
    assert_eq!(
        p.program.nodes[0].kind,
        Some(pb::node::Kind::Union(pb::Union { members: vec![0] }))
    );
    drop((p, cycle));
    assert!(weak.upgrade().is_none());
}

#[test]
fn retained_leaf_releases_all_parents_with_bounded_immediate_imports() {
    let sort = SortRef::equality("M");
    let leaf_call = Callable::constructor("Leaf", vec![], sort.clone(), None, false);
    let pair = Callable::constructor("Pair", vec![sort.clone(), sort.clone()], sort, None, false);
    let leaf = Expr::call(&leaf_call, vec![]);
    for left_growing in [false, true] {
        let mut root = leaf.clone();
        let mut parents = vec![];
        for _ in 0..100_000 {
            root = Expr::call(
                &pair,
                if left_growing {
                    vec![root, leaf.clone()]
                } else {
                    vec![leaf.clone(), root]
                },
            );
            let owner = root.0.owner.as_ref().unwrap();
            assert_eq!(owner.program().unwrap().nodes.len(), 1);
            assert_eq!(owner.slots.iter().map(Vec::len).sum::<usize>(), 3);
            assert_eq!(owner.declarations.len(), 1);
            parents.push(Arc::downgrade(owner));
        }
        std::thread::spawn(move || drop(root)).join().unwrap();
        assert!(parents.iter().all(|w| w.upgrade().is_none()));
        assert_eq!(leaf, Expr::call(&leaf_call, vec![]));
    }
}

#[test]
fn generated_rule_fields_and_shared_locations_are_authoritative() {
    let sort = SortRef::equality("M");
    let x = node(
        &sort,
        pb::node::Kind::Var("@typed:n:78".into()),
        vec![],
        vec![],
    );
    let y = node(
        &sort,
        pb::node::Kind::Var("@typed:n:79".into()),
        vec![],
        vec![],
    );
    let make = |rhs, mode| {
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Node as usize] = vec![Slot::External(x.clone()), Slot::External(y.clone())];
        publish(
            pb::Program::default(),
            slots,
            vec![],
            Arena::Rule,
            0,
            vec![pb::Rule {
                kind: Some(pb::rule::Kind::Rewrite(pb::Rewrite {
                    lhs: 0,
                    rhs,
                    ..Default::default()
                })),
                eval_mode: mode,
                name: Some("same diagnostic label".into()),
                ..Default::default()
            }],
        )
        .unwrap()
    };
    let a = make(1, pb::RuleEvalMode::Seminaive.into());
    let independent_equal = make(1, pb::RuleEvalMode::Seminaive.into());
    let changed = make(0, pb::RuleEvalMode::Naive.into());
    let records = [a.clone(), a, independent_equal, changed];
    let mut packer = Packer::default();
    let indices: Vec<_> = records.into_iter().map(|r| packer.intern(r, 0)).collect();
    packer.finish().unwrap();
    let rules: Vec<_> = indices.iter().map(|i| &packer.rules[*i as usize]).collect();
    assert_eq!(rules.len(), 4);
    assert_eq!(rules[0], rules[1]);
    assert_eq!(packer.rules.len(), 3);
    assert_eq!(packer.rules[2].eval_mode, pb::RuleEvalMode::Naive as i32);
    let Some(pb::rule::Kind::Rewrite(rule)) = &packer.rules[2].kind else {
        panic!()
    };
    assert_eq!(rule.lhs, rule.rhs);
}

#[test]
fn declaration_diagnostics_do_not_change_local_compatibility() {
    let sort = SortRef::equality("M");
    let leaf = Expr::call(
        &Callable::constructor("Leaf", vec![], sort.clone(), None, false),
        vec![],
    );
    let declaration = |label: &str, doc: Option<&str>, unextractable: bool| {
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Sort as usize] = vec![Slot::External(sort.0.clone())];
        Callable(
            publish(
                pb::Program {
                    declarations: vec![pb::Declaration {
                        kind: Some(pb::declaration::Kind::Constructor(pb::Constructor {
                            name: "Wrap".into(),
                            inputs: vec![pb::Arg {
                                sort: 0,
                                name: label.into(),
                            }],
                            output: 0,
                            unextractable,
                            ..Default::default()
                        })),
                        doc: doc.map(str::to_owned),
                        ..Default::default()
                    }],
                    ..Default::default()
                },
                slots,
                vec![],
                Arena::Declaration,
                0,
                vec![],
            )
            .unwrap(),
        )
    };
    for doc in [None, Some(""), Some("first docs")] {
        let first = declaration("old label", doc, false);
        let mut packed = Packer::default();
        packed.intern(Expr::call(&first, vec![leaf.clone()]).0, 0);
        for resupplied in [None, Some(""), Some("second docs")] {
            let second = declaration("new label", resupplied, false);
            assert!(super::decl::same_callable(&first.0, &second.0).unwrap());
            packed.intern(Expr::call(&second, vec![leaf.clone()]).0, 0);
        }
        packed
            .finish()
            .expect("diagnostic-only changes are compatible");
        let wraps: Vec<_> = packed
            .program
            .declarations
            .iter()
            .filter(
                |d| matches!(&d.kind, Some(pb::declaration::Kind::Constructor(c)) if c.name == "Wrap"),
            )
            .collect();
        assert_eq!(wraps.len(), 1);
        assert_eq!(
            *wraps[0],
            first
                .0
                .owner
                .as_ref()
                .unwrap()
                .program()
                .unwrap()
                .declarations[0],
            "packing retains the complete first record, including documentation presence"
        );
        let encoded = packed.program.encode_to_vec();
        assert_eq!(
            pb::Program::decode(encoded.as_slice()).unwrap(),
            packed.program
        );

        let mut conflict = Packer::default();
        conflict.intern(Expr::call(&first, vec![leaf.clone()]).0, 0);
        conflict.intern(
            Expr::call(
                &declaration("ignored", Some("ignored"), true),
                vec![leaf.clone()],
            )
            .0,
            0,
        );
        assert!(
            conflict.finish().is_err(),
            "semantic constructor options still conflict"
        );
    }
}
