//! Immutable indexed observation of a Freeze reconstruction Program.
use super::{
    EgglogValue, EqualitySort, SortRef, TypedError,
    expr::Expr,
    pb,
    rule::ensure_sort,
    storage::{Arena, Record, observe},
};
use std::{
    collections::{HashMap, HashSet},
    fmt,
    hash::{Hash, Hasher},
};

/// An independent snapshot. Its only graph storage is the exported Program.
#[derive(Clone)]
pub struct Snapshot {
    source: Record,
    classes: Vec<u32>,
    membership: HashMap<u32, u32>,
    subsumed: HashSet<u32>,
    bindings: HashMap<String, (u32, Option<u32>)>,
    rows: Vec<u32>,
}

impl Snapshot {
    pub(super) fn from_export(
        export: pb::EGraphSnapshot,
        builtins: &Record,
    ) -> Result<Self, TypedError> {
        let root = export
            .options
            .and_then(|options| options.cost_sort)
            .ok_or_else(|| TypedError::Decode("snapshot has no cost sort".into()))?;
        let program = export
            .program
            .ok_or_else(|| TypedError::Decode("snapshot has no Program".into()))?;
        let source = observe(program, root, builtins)?;
        let program = &source.owner.as_ref().unwrap().program().unwrap();
        let mut classes = Vec::new();
        let mut membership = HashMap::new();
        let mut bindings = HashMap::new();
        for (index, node) in program.nodes.iter().enumerate() {
            if let Some(pb::node::Kind::Binding(name)) = &node.kind
                && let Some((previous, _)) = bindings.insert(name.clone(), (index as u32, None))
                && SortRef(source.resolve(Arena::Sort, program.nodes[previous as usize].sort_id)?)
                    != SortRef(source.resolve(Arena::Sort, node.sort_id)?)
            {
                return Err(TypedError::Decode(
                    "snapshot binding has incompatible sorts".into(),
                ));
            }
        }
        let mut rows = Vec::new();
        let mut subsumed_calls = Vec::new();
        for (position, command) in program.commands.iter().enumerate() {
            if let Some(pb::command::Kind::Let(value)) = &command.kind {
                let binding = value.binding.and_then(|i| program.nodes.get(i as usize));
                let Some(pb::Node {
                    kind: Some(pb::node::Kind::Binding(name)),
                    ..
                }) = binding
                else {
                    return Err(TypedError::Decode(
                        "snapshot Let has no binding target".into(),
                    ));
                };
                let value = value
                    .value
                    .filter(|i| (*i as usize) < program.nodes.len())
                    .ok_or_else(|| TypedError::Decode("snapshot Let has no value".into()))?;
                bindings.get_mut(name).unwrap().1 = Some(value);
                continue;
            }
            let Some(pb::command::Kind::Action(action)) = &command.kind else {
                return Err(TypedError::Decode(
                    "snapshot contains a non-data command".into(),
                ));
            };
            match &action.kind {
                Some(pb::action::Kind::Term(index)) => {
                    let node = program.nodes.get(*index as usize).ok_or_else(|| {
                        TypedError::Decode("snapshot inventory index out of bounds".into())
                    })?;
                    if let Some(pb::node::Kind::Eq(union)) = &node.kind {
                        if membership.insert(*index, *index).is_some() {
                            return Err(TypedError::Decode("duplicate snapshot class".into()));
                        }
                        classes.push(*index);
                        for member in &union.members {
                            let Some(pb::Node {
                                sort_id,
                                kind: Some(pb::node::Kind::Call(_)),
                                ..
                            }) = program.nodes.get(*member as usize)
                            else {
                                return Err(TypedError::Decode(
                                    "snapshot class member is not a Call".into(),
                                ));
                            };
                            if *sort_id != node.sort_id
                                || membership.insert(*member, *index).is_some()
                            {
                                return Err(TypedError::Decode(
                                    "incompatible or repeated snapshot row".into(),
                                ));
                            }
                        }
                    } else if matches!(node.kind, Some(pb::node::Kind::Call(_))) {
                        rows.push(position as u32);
                    } else {
                        return Err(TypedError::Decode(
                            "snapshot term is not a class or relation".into(),
                        ));
                    }
                }
                Some(pb::action::Kind::Set(set)) => {
                    if set.target.is_none()
                        || set
                            .value
                            .is_none_or(|value| (value as usize) >= program.nodes.len())
                    {
                        return Err(TypedError::Decode(
                            "incomplete snapshot function row".into(),
                        ));
                    }
                    rows.push(position as u32);
                }
                Some(pb::action::Kind::Subsume(call)) => subsumed_calls.push(call),
                Some(pb::action::Kind::SetCost(_)) => (),
                _ => {
                    return Err(TypedError::Decode(
                        "unsupported snapshot data action".into(),
                    ));
                }
            }
        }
        let mut subsumed = HashSet::new();
        for call in subsumed_calls {
            let index = membership.keys().find(|index| {
                matches!(&program.nodes[**index as usize].kind, Some(pb::node::Kind::Call(candidate)) if candidate == call)
            }).ok_or_else(|| TypedError::Decode("subsumed snapshot row is absent".into()))?;
            subsumed.insert(*index);
        }
        Ok(Self {
            source,
            classes,
            membership,
            subsumed,
            bindings,
            rows,
        })
    }

    /// Read a global by name and exact sort without evaluating an initializer.
    pub fn lookup<S: EgglogValue>(&self, capture: &S) -> Result<S, TypedError> {
        let record = &capture.expression().0;
        if record.owner.as_ref().unwrap().id == self.source.owner.as_ref().unwrap().id {
            return Ok(capture.clone());
        }
        let program = record.owner.as_ref().unwrap().program()?;
        let node = &program.nodes[record.index as usize];
        let Some(pb::node::Kind::Binding(name)) = &node.kind else {
            return Err(TypedError::Decode(
                "lookup requires a global binding".into(),
            ));
        };
        let (binding, value) = self
            .bindings
            .get(name)
            .ok_or_else(|| TypedError::Decode("binding is absent from this snapshot".into()))?;
        let source_program = self.source.owner.as_ref().unwrap().program()?;
        if SortRef(record.resolve(Arena::Sort, node.sort_id)?)
            != SortRef(
                self.source
                    .resolve(Arena::Sort, source_program.nodes[*binding as usize].sort_id)?,
            )
        {
            return Err(TypedError::Decode(
                "snapshot binding has a different sort".into(),
            ));
        }
        let index = value.ok_or_else(|| TypedError::Decode("snapshot binding is unset".into()))?;
        ensure_sort(Expr(self.source.resolve(Arena::Node, index)?))
    }

    /// Inventory stored classes only; Eq nodes in saved code are not observations.
    pub fn eclasses(&self) -> impl ExactSizeIterator<Item = ClassRef<'_>> + Clone {
        self.classes.iter().map(|index| ClassRef {
            snapshot: self,
            index: *index,
        })
    }

    /// Stored relation and function rows in export order.
    /// These are table observations, never runtime constructor producers.
    pub fn rows(&self) -> impl ExactSizeIterator<Item = TableRowRef<'_>> + Clone {
        self.rows.iter().map(|index| TableRowRef {
            snapshot: self,
            index: *index,
        })
    }

    /// Recover a class from its own reference or one of its producer Calls.
    pub fn class_of<S: EgglogValue>(&self, value: &S) -> Result<ClassRef<'_>, TypedError> {
        let record = &value.expression().0;
        if record.owner.as_ref().unwrap().id != self.source.owner.as_ref().unwrap().id {
            return Err(TypedError::Decode(
                "value belongs to another snapshot".into(),
            ));
        }
        let index = *self
            .membership
            .get(&record.index)
            .ok_or_else(|| TypedError::Decode("value is not a stored equality class".into()))?;
        Ok(ClassRef {
            snapshot: self,
            index,
        })
    }

    /// Typed producer inspection preserves child class locations and cycles.
    pub fn nodes<S: EqualitySort>(
        &self,
        value: &S,
    ) -> Result<impl ExactSizeIterator<Item = S> + '_, TypedError> {
        let class = self.class_of(value)?;
        Ok(class
            .nodes()
            .map(|node| self.typed_node(node).expect("class sort is preserved")))
    }

    /// Read a producer with its exact Rust sort; never select child classes.
    pub fn typed_node<S: EgglogValue>(&self, node: ProducerRef<'_>) -> Result<S, TypedError> {
        if self.source.owner.as_ref().unwrap().id != node.snapshot.source.owner.as_ref().unwrap().id
        {
            return Err(TypedError::Decode(
                "producer belongs to another snapshot".into(),
            ));
        }
        ensure_sort(Expr(self.source.resolve(Arena::Node, node.index)?))
    }
}

impl fmt::Debug for Snapshot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Snapshot")
            .field("classes", &self.classes.len())
            .field("producers", &(self.membership.len() - self.classes.len()))
            .field("rows", &self.rows.len())
            .finish()
    }
}

/// A stored class location, scoped to its owning snapshot.
#[derive(Clone, Copy)]
pub struct ClassRef<'s> {
    snapshot: &'s Snapshot,
    index: u32,
}
/// One constructor row in a snapshot class.
#[derive(Clone, Copy)]
pub struct ProducerRef<'s> {
    snapshot: &'s Snapshot,
    index: u32,
}
/// One exact scalar/container value or class reference in a producer argument.
#[derive(Clone, Copy)]
pub struct ValueRef<'s> {
    snapshot: &'s Snapshot,
    index: u32,
}

/// One stored relation or function row, scoped to its snapshot command location.
#[derive(Clone, Copy)]
pub struct TableRowRef<'s> {
    snapshot: &'s Snapshot,
    index: u32,
}

macro_rules! location_identity {
    ($($name:ident),*) => { $(
        impl PartialEq for $name<'_> {
            fn eq(&self, other: &Self) -> bool {
                self.index == other.index && self.snapshot.source.owner.as_ref().unwrap().id
                    == other.snapshot.source.owner.as_ref().unwrap().id
            }
        }
        impl Eq for $name<'_> {}
        impl Hash for $name<'_> {
            fn hash<H: Hasher>(&self, state: &mut H) {
                (self.snapshot.source.owner.as_ref().unwrap().id, self.index).hash(state)
            }
        }
        impl fmt::Debug for $name<'_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_tuple(stringify!($name)).field(&self.snapshot.source.owner.as_ref().unwrap().id)
                    .field(&self.index).finish()
            }
        }
    )* };
}
location_identity!(ClassRef, ProducerRef, ValueRef, TableRowRef);

impl<'s> TableRowRef<'s> {
    // Interpret the two reconstruction forms without copying their stored data.
    fn fields(self) -> (&'s pb::Call, Option<u32>) {
        let program = &self
            .snapshot
            .source
            .owner
            .as_ref()
            .unwrap()
            .program()
            .unwrap();
        match &program.commands[self.index as usize].kind {
            Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Term(index)),
                ..
            })) => match &program.nodes[*index as usize].kind {
                Some(pb::node::Kind::Call(call)) => (call, None),
                _ => unreachable!("inventoried relation row"),
            },
            Some(pb::command::Kind::Action(pb::Action {
                kind: Some(pb::action::Kind::Set(set)),
                ..
            })) => (set.target.as_ref().unwrap(), set.value),
            _ => unreachable!("inventoried table row"),
        }
    }

    /// The stored callable's diagnostic name, not a dispatch handle.
    pub fn name(self) -> &'s str {
        &self.fields().0.func
    }

    /// Ordered input values, without selecting or expanding class references.
    pub fn args(self) -> impl ExactSizeIterator<Item = ValueRef<'s>> + Clone {
        self.fields().0.args.iter().map(move |index| ValueRef {
            snapshot: self.snapshot,
            index: *index,
        })
    }

    /// A function's stored output; relation rows have no output value.
    pub fn value(self) -> Option<ValueRef<'s>> {
        self.fields().1.map(|index| ValueRef {
            snapshot: self.snapshot,
            index,
        })
    }
}

impl<'s> ClassRef<'s> {
    /// Producers in the export's captured order, including subsumed rows.
    pub fn nodes(self) -> impl ExactSizeIterator<Item = ProducerRef<'s>> + Clone {
        let Some(pb::node::Kind::Eq(union)) = &self
            .snapshot
            .source
            .owner
            .as_ref()
            .unwrap()
            .program()
            .unwrap()
            .nodes[self.index as usize]
            .kind
        else {
            unreachable!("inventoried class")
        };
        union.members.iter().map(move |index| ProducerRef {
            snapshot: self.snapshot,
            index: *index,
        })
    }
    /// The exact declared sort of this stored class.
    pub fn sort(self) -> SortRef {
        let record = self
            .snapshot
            .source
            .resolve(Arena::Node, self.index)
            .unwrap();
        let sort =
            record.owner.as_ref().unwrap().program().unwrap().nodes[record.index as usize].sort_id;
        SortRef(record.resolve(Arena::Sort, sort).unwrap())
    }
}

impl<'s> ProducerRef<'s> {
    /// Inspect shallow fields without evaluating or choosing representatives.
    pub fn args(self) -> impl ExactSizeIterator<Item = ValueRef<'s>> + Clone {
        let Some(pb::node::Kind::Call(call)) = &self
            .snapshot
            .source
            .owner
            .as_ref()
            .unwrap()
            .program()
            .unwrap()
            .nodes[self.index as usize]
            .kind
        else {
            unreachable!("inventoried producer")
        };
        call.args.iter().map(move |index| ValueRef {
            snapshot: self.snapshot,
            index: *index,
        })
    }
    /// Direct class-valued fields, preserving repeated positions.
    pub fn eclass_children(self) -> impl Iterator<Item = ClassRef<'s>> + Clone {
        self.args().filter_map(|value| value.class())
    }
    /// Constructor display name retained by the exact exported declaration.
    pub fn name(self) -> &'s str {
        let Some(pb::node::Kind::Call(call)) = &self
            .snapshot
            .source
            .owner
            .as_ref()
            .unwrap()
            .program()
            .unwrap()
            .nodes[self.index as usize]
            .kind
        else {
            unreachable!("inventoried producer")
        };
        &call.func
    }
    /// Whether this exact constructor row was subsumed at capture time.
    pub fn is_subsumed(self) -> bool {
        self.snapshot.subsumed.contains(&self.index)
    }

    /// The constructor's exact static cost, without imposing a model default.
    pub fn declared_cost(self) -> Option<ValueRef<'s>> {
        self.snapshot
            .source
            .owner
            .as_ref()
            .unwrap()
            .program()
            .unwrap()
            .constructors
            .iter()
            .find(|constructor| constructor.name == self.name())
            .and_then(|constructor| {
                constructor.cost.map(|index| ValueRef {
                    snapshot: self.snapshot,
                    index,
                })
            })
    }
}

impl<'s> ValueRef<'s> {
    /// A class-valued field is a reference, not an extracted expression tree.
    pub fn class(self) -> Option<ClassRef<'s>> {
        self.snapshot
            .membership
            .get(&self.index)
            .map(|index| ClassRef {
                snapshot: self.snapshot,
                index: *index,
            })
    }

    /// Decode the exact Rust sort while retaining this observation's provenance.
    pub fn try_typed<S: EgglogValue>(self) -> Result<S, TypedError> {
        ensure_sort(Expr(self.snapshot.source.resolve(Arena::Node, self.index)?))
    }

    /// The concrete sort of this value location.
    pub fn sort(self) -> SortRef {
        let record = self
            .snapshot
            .source
            .resolve(Arena::Node, self.index)
            .unwrap();
        let sort =
            record.owner.as_ref().unwrap().program().unwrap().nodes[record.index as usize].sort_id;
        SortRef(record.resolve(Arena::Sort, sort).unwrap())
    }

    /// Ordered container fields. Class references are leaves, preserving cycles.
    pub fn children(self) -> impl ExactSizeIterator<Item = ValueRef<'s>> {
        use pb::primitive_value::Value;
        let indices = match &self
            .snapshot
            .source
            .owner
            .as_ref()
            .unwrap()
            .program()
            .unwrap()
            .nodes[self.index as usize]
            .kind
        {
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue { value: Some(value) })) => {
                match value {
                    Value::Vec(items) | Value::Set(items) | Value::Multiset(items) => {
                        items.items.clone()
                    }
                    Value::Pair(pair) => pair.first.into_iter().chain(pair.second).collect(),
                    Value::Map(map) => map
                        .entries
                        .iter()
                        .flat_map(|entry| entry.key.into_iter().chain(entry.value))
                        .collect(),
                    Value::Maybe(maybe) => maybe.value.into_iter().collect(),
                    Value::PartialCall(call) => call.args.clone(),
                    Value::Custom(custom) => custom.args.clone(),
                    _ => vec![],
                }
            }
            _ => vec![],
        };
        indices.into_iter().map(move |index| ValueRef {
            snapshot: self.snapshot,
            index,
        })
    }
}

impl fmt::Display for ValueRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use pb::primitive_value::Value;
        match &self
            .snapshot
            .source
            .owner
            .as_ref()
            .unwrap()
            .program()
            .unwrap()
            .nodes[self.index as usize]
            .kind
        {
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue { value: Some(value) })) => {
                match value {
                    Value::Unit(_) => f.write_str("()"),
                    Value::Bool(value) => write!(f, "{value}"),
                    Value::I64(value) => write!(f, "{value}"),
                    Value::F64Bits(bits) => write!(f, "{:?}", f64::from_bits(*bits)),
                    Value::String(value) => write!(f, "{value:?}"),
                    Value::BigInt(value) => f.write_str(value),
                    Value::BigRat(value) => write!(f, "{}/{}", value.numerator, value.denominator),
                    Value::Rational(value) => {
                        write!(f, "{}/{}", value.numerator, value.denominator)
                    }
                    _ => write!(f, "{}", self.sort()),
                }
            }
            _ => write!(f, "{}", self.sort()),
        }
    }
}

impl fmt::Display for SortRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0.sort().unwrap().kind {
            Some(pb::sort::Kind::Eq(name)) => f.write_str(name),
            Some(pb::sort::Kind::Primitive(family)) => {
                if family.args.is_empty() {
                    return f.write_str(&family.name);
                }
                write!(f, "({}", family.name)?;
                for index in &family.args {
                    write!(
                        f,
                        " {}",
                        SortRef(
                            self.0
                                .resolve(Arena::Sort, *index)
                                .map_err(|_| fmt::Error)?
                        )
                    )?;
                }
                f.write_str(")")
            }
            Some(pb::sort::Kind::Func(function)) => {
                f.write_str("(Func (")?;
                for (position, index) in function.params.iter().enumerate() {
                    if position > 0 {
                        f.write_str(" ")?;
                    }
                    write!(
                        f,
                        "{}",
                        SortRef(
                            self.0
                                .resolve(Arena::Sort, *index)
                                .map_err(|_| fmt::Error)?
                        )
                    )?;
                }
                write!(
                    f,
                    ") {})",
                    SortRef(
                        self.0
                            .resolve(Arena::Sort, function.result)
                            .map_err(|_| fmt::Error)?
                    )
                )
            }
            Some(pb::sort::Kind::Var(variable)) => write!(f, "{variable:?}"),
            None => Err(fmt::Error),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use prost::Message;

    #[test]
    fn opaque_custom_children_are_shallow_ordered_references() {
        // Shape-only observation: no host codec is installed or executed.
        let mut catalog =
            pb::BuiltinCatalog::decode(include_bytes!("builtins/catalog.pb").as_slice()).unwrap();
        catalog.primitive_sorts.push(pb::PrimitiveSort {
            name: "Opaque".into(),
            arity: 0,
            ..Default::default()
        });
        let builtins = super::super::storage::publish_catalog(catalog).unwrap();
        let snapshot = Snapshot::from_export(
            pb::EGraphSnapshot {
                options: Some(pb::EGraphOptions {
                    cost_sort: Some(0),
                    ..Default::default()
                }),
                program: Some(pb::Program {
                    sorts: vec![
                        pb::Sort {
                            kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
                                name: "i64".into(),
                                args: vec![],
                            })),
                            ..Default::default()
                        },
                        pb::Sort {
                            kind: Some(pb::sort::Kind::Eq("Node".into())),
                            ..Default::default()
                        },
                        pb::Sort {
                            kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
                                name: "Opaque".into(),
                                args: vec![],
                            })),
                            ..Default::default()
                        },
                    ],
                    nodes: vec![
                        pb::Node {
                            sort_id: 1,
                            kind: Some(pb::node::Kind::Eq(pb::Eq { members: vec![1] })),
                        },
                        pb::Node {
                            sort_id: 1,
                            kind: Some(pb::node::Kind::Call(pb::Call {
                                func: "Box".into(),
                                args: vec![2],
                            })),
                        },
                        pb::Node {
                            sort_id: 2,
                            kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                                value: Some(pb::primitive_value::Value::Custom(pb::CustomValue {
                                    payload: vec![0xff],
                                    args: vec![0, 3, 0, 3],
                                })),
                            })),
                        },
                        pb::Node {
                            sort_id: 0,
                            kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                                value: Some(pb::primitive_value::Value::I64(7)),
                            })),
                        },
                        pb::Node {
                            sort_id: 2,
                            kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                                value: Some(pb::primitive_value::Value::Custom(pb::CustomValue {
                                    payload: vec![],
                                    args: vec![],
                                })),
                            })),
                        },
                    ],
                    commands: vec![pb::Command {
                        kind: Some(pb::command::Kind::Action(pb::Action {
                            kind: Some(pb::action::Kind::Term(0)),
                        })),
                    }],
                    ..Default::default()
                }),
            },
            &builtins,
        )
        .unwrap();
        let children: Vec<_> = ValueRef {
            snapshot: &snapshot,
            index: 2,
        }
        .children()
        .collect();
        assert_eq!(
            children.iter().map(|value| value.index).collect::<Vec<_>>(),
            [0, 3, 0, 3]
        );
        assert_eq!(children[0].class(), snapshot.eclasses().next());
        assert!(children[0].children().next().is_none());
        assert!(
            ValueRef {
                snapshot: &snapshot,
                index: 4
            }
            .children()
            .next()
            .is_none()
        );
    }
}
