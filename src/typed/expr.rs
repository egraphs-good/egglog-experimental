use super::{
    SortRef, TypedError,
    decl::Callable,
    pb,
    storage::{Arena, DeclarationKind, Key, Record, Slot, publish},
};
use std::{
    collections::{HashMap, HashSet},
    hash::{DefaultHasher, Hash, Hasher},
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

/// A nominal Rust view of an immutable generated expression record.
pub trait EgglogValue: Clone + Eq + Hash + std::fmt::Debug + Send + Sync + 'static {
    #[doc(hidden)]
    fn sort_ref() -> SortRef;
    #[doc(hidden)]
    fn expression(&self) -> &Expr;
    #[doc(hidden)]
    fn from_expression(expr: Expr) -> Self;

    /// Returns the authored root call's name for diagnostics.
    /// Variables, captures, literals, and snapshot observations return `None`.
    /// Use `get_args` for exact typed call inspection.
    fn call_name(&self) -> Option<&str> {
        let record = &self.expression().0;
        let owner = record.owner.as_ref().unwrap();
        if owner.observed || owner.capture.is_some_and(|(read, _)| record.index == read) {
            return None;
        }
        match &owner.program().unwrap().nodes[record.index as usize].kind {
            Some(pb::node::Kind::Call(call)) => Some(&call.func),
            _ => None,
        }
    }
}
/// A sort whose values may participate in equality-class unions.
pub trait EqualitySort: EgglogValue {}

#[doc(hidden)]
pub trait ValueInput: std::borrow::Borrow<Self::Owned> {
    type Owned: EgglogValue;
}
impl<T: EgglogValue + ValueInput<Owned = T>> ValueInput for &T {
    type Owned = T;
}

#[doc(hidden)]
#[derive(Clone)]
pub struct Expr(pub(super) Record);

static NEXT_SCOPE: AtomicU64 = AtomicU64::new(0);
#[doc(hidden)]
pub fn fresh_scope() -> u64 {
    NEXT_SCOPE
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_add(1))
        .expect("fresh variable space exhausted")
}

/// A named query variable. Equal UTF-8 names identify one variable per binder.
/// Names must be nonempty; names resembling generated tokens remain ordinary
/// named variables. Top-level evaluated inputs cannot contain free variables.
pub fn var<S: EgglogValue>(name: &str) -> S {
    assert!(!name.is_empty(), "variable names must not be empty");
    let encoded = name
        .as_bytes()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>();
    S::from_expression(Expr::variable(S::sort_ref(), format!("@typed:n:{encoded}")))
}

/// Capture an initializer once at its ordered registration or extraction point.
/// Equal labels require equal sorts and initializer syntax in one live scope.
/// Construction is inert; the returned value reads the established capture.
pub fn let_<I: ValueInput>(name: impl Into<Arc<str>>, initializer: I) -> I::Owned {
    let initializer = initializer.borrow().expression();
    let node = &initializer
        .0
        .owner
        .as_ref()
        .unwrap()
        .program()
        .unwrap()
        .nodes[initializer.0.index as usize];
    let sort = SortRef(initializer.0.resolve(Arena::Sort, node.sort_id).unwrap());
    let name = name.into();
    let encoded = name
        .as_bytes()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>();
    let name = format!("__typed_capture_recipe_{encoded}");
    let callable = Callable::function(&name, vec![], sort.clone(), None::<fn(Expr, Expr) -> Expr>);
    let call = pb::Call {
        func: name,
        args: vec![],
    };
    let mut slots = std::array::from_fn(|_| vec![]);
    slots[Arena::Sort as usize] = vec![Slot::External(sort.0)];
    slots[Arena::Node as usize] = vec![Slot::External(initializer.0.clone())];
    let mut record = publish(
        pb::Program {
            nodes: vec![pb::Node {
                kind: Some(pb::node::Kind::Call(call.clone())),
                ..Default::default()
            }],
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Set(pb::Set {
                        target: Some(call),
                        value: Some(0),
                    })),
                    ..Default::default()
                })),
                ..Default::default()
            }],
            ..Default::default()
        },
        slots,
        vec![callable.0],
        Arena::Node,
        0,
        vec![],
    )
    .expect("canonical capture fragment");
    Arc::get_mut(record.owner.as_mut().unwrap())
        .expect("unpublished capture owner")
        .capture = Some((0, 0));
    record.capture().expect("canonical capture linkage");
    I::Owned::from_expression(Expr(record))
}
#[doc(hidden)]
pub fn variable<S: EgglogValue>(scope: u64, slot: usize) -> S {
    S::from_expression(Expr::variable(
        S::sort_ref(),
        format!("@typed:f:{scope}:{slot}"),
    ))
}

impl Expr {
    pub(super) fn literal(sort: SortRef, value: pb::PrimitiveValue) -> Result<Self, TypedError> {
        validate_literal(&sort, &value)?;
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Sort as usize] = vec![Slot::External(sort.0)];
        Ok(Self(publish(
            pb::Program {
                nodes: vec![pb::Node {
                    kind: Some(pb::node::Kind::PrimitiveValue(value)),
                    ..Default::default()
                }],
                ..Default::default()
            },
            slots,
            vec![],
            Arena::Node,
            0,
            vec![],
        )?))
    }

    pub(super) fn variable(sort: SortRef, token: String) -> Self {
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Sort as usize] = vec![Slot::External(sort.0)];
        let program = pb::Program {
            nodes: vec![pb::Node {
                kind: Some(pb::node::Kind::Var(token)),
                ..Default::default()
            }],
            ..Default::default()
        };
        Self(publish(program, slots, vec![], Arena::Node, 0, vec![]).unwrap())
    }

    pub fn call(callable: &Callable, arguments: Vec<Self>) -> Self {
        let owner = callable.0.owner.as_ref().unwrap();
        let (name, inputs, output) = if callable.0.arena == Arena::Primitive {
            let primitive = callable.0.primitive().expect("owned builtin primitive");
            let Some(signature) = &primitive.signature else {
                panic!("unsupported callable typing")
            };
            assert!(
                signature.type_param_count == 0 && signature.varargs.is_empty(),
                "generic primitive calls require an explicit result sort"
            );
            (
                &primitive.name,
                &signature.inputs,
                Some(signature.output.expect("callable result sort")),
            )
        } else {
            match &owner.program().expect("owned user callable").declarations
                [callable.0.index as usize]
                .kind
            {
                Some(pb::declaration::Kind::Constructor(c)) => (&c.name, &c.inputs, Some(c.output)),
                Some(pb::declaration::Kind::Function(f)) => (&f.name, &f.inputs, Some(f.output)),
                Some(pb::declaration::Kind::UserDefinedPrimitive(p)) => {
                    (&p.name, &p.inputs, Some(p.output))
                }
                Some(pb::declaration::Kind::Relation(r)) => (&r.name, &r.inputs, None),
                _ => panic!("unsupported callable declaration"),
            }
        };
        assert_eq!(inputs.len(), arguments.len(), "callable arity");
        for (arg, expected) in arguments.iter().zip(inputs) {
            let node =
                &arg.0.owner.as_ref().unwrap().program().unwrap().nodes[arg.0.index as usize];
            assert!(
                SortRef(arg.0.resolve(Arena::Sort, node.sort_id).unwrap())
                    == SortRef(callable.0.resolve(Arena::Sort, expected.sort).unwrap()),
                "callable input sort"
            );
        }
        // Relation's Unit is a wire use annotation, not its native row sort or
        // an invented output field on the input-only declaration.
        let output = match output {
            Some(output) => SortRef(callable.0.resolve(Arena::Sort, output).unwrap()),
            None => super::builtins::Unit::sort_ref(),
        };
        Self::build_call(callable, name, arguments, output)
    }

    pub(super) fn call_with_result(
        callable: &Callable,
        arguments: Vec<Self>,
        output: SortRef,
    ) -> Result<Self, TypedError> {
        let sorts = arguments
            .iter()
            .map(|argument| {
                let node = &argument.0.owner.as_ref().unwrap().program().unwrap().nodes
                    [argument.0.index as usize];
                argument.0.resolve(Arena::Sort, node.sort_id).map(SortRef)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let name = callable.check_call(&sorts, &output)?;
        Ok(Self::build_call(callable, name, arguments, output))
    }

    pub(super) fn apply(function: Self, arguments: Vec<Self>) -> Result<Self, TypedError> {
        let node = &function.0.owner.as_ref().unwrap().program()?.nodes[function.0.index as usize];
        let function_sort = function.0.resolve(Arena::Sort, node.sort_id)?;
        let Some(pb::sort::Kind::Func(signature)) = &function_sort.sort()?.kind else {
            return Err(TypedError::Invalid(
                "application requires a function sort".into(),
            ));
        };
        if arguments.len() != signature.params.len() {
            return Err(TypedError::Invalid("function application arity".into()));
        }
        for (argument, parameter) in arguments.iter().zip(&signature.params) {
            let node =
                &argument.0.owner.as_ref().unwrap().program()?.nodes[argument.0.index as usize];
            if SortRef(argument.0.resolve(Arena::Sort, node.sort_id)?)
                != SortRef(function_sort.resolve(Arena::Sort, *parameter)?)
            {
                return Err(TypedError::Invalid(
                    "function application argument sort".into(),
                ));
            }
        }
        let output = function_sort.resolve(Arena::Sort, signature.result)?;
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Sort as usize] = vec![Slot::External(output)];
        let count = arguments.len() as u32;
        slots[Arena::Node as usize] = std::iter::once(function)
            .chain(arguments)
            .map(|value| Slot::External(value.0))
            .collect();
        Ok(Self(publish(
            pb::Program {
                nodes: vec![pb::Node {
                    kind: Some(pb::node::Kind::Apply(pb::Apply {
                        function: Some(0),
                        args: (1..=count).collect(),
                    })),
                    ..Default::default()
                }],
                ..Default::default()
            },
            slots,
            vec![],
            Arena::Node,
            0,
            vec![],
        )?))
    }

    // Publish one generated Call and location-only imports. Both closed and
    // generic validation paths share this ownership/record construction boundary.
    fn build_call(callable: &Callable, name: &str, arguments: Vec<Self>, output: SortRef) -> Self {
        let program = pb::Program {
            nodes: vec![pb::Node {
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: name.into(),
                    args: (0..arguments.len() as u32).collect(),
                })),
                ..Default::default()
            }],
            ..Default::default()
        };
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Node as usize] = arguments.into_iter().map(|a| Slot::External(a.0)).collect();
        slots[Arena::Sort as usize] = vec![Slot::External(output.0)];
        Self(
            publish(
                program,
                slots,
                vec![callable.0.clone()],
                Arena::Node,
                0,
                vec![],
            )
            .unwrap(),
        )
    }

    // Lift one typed callback into the existing computed-function declaration.
    // Captures are explicit; all body syntax remains deferred, including fresh
    // Union allocation and parameter-independent reads or effects.
    pub(super) fn function(
        body: Self,
        parameters: Vec<Self>,
        captures: Vec<Self>,
        sort: SortRef,
    ) -> Result<Self, TypedError> {
        let key = |record: &Record| {
            (
                record.owner.as_ref().unwrap().id,
                record.arena,
                record.index,
            )
        };
        let formals: HashMap<_, _> = parameters
            .iter()
            .enumerate()
            .map(|(i, p)| (key(&p.0), i))
            .collect();
        let root = &body.0.owner.as_ref().unwrap().program().unwrap().nodes[body.0.index as usize];
        if body.0.capture()?.is_none()
            && let Some(pb::node::Kind::Call(call)) = &root.kind
            && call.args.len() == parameters.len()
            && call
                .args
                .iter()
                .zip(&parameters)
                .all(|(argument, parameter)| {
                    body.0
                        .resolve(Arena::Node, *argument)
                        .is_ok_and(|argument| key(&argument) == key(&parameter.0))
                })
        {
            let declaration = body.0.declaration(&call.func, DeclarationKind::Callable)?;
            if declaration.arena == Arena::Declaration
                && matches!(
                    declaration
                        .owner
                        .as_ref()
                        .unwrap()
                        .program()
                        .unwrap()
                        .declarations[declaration.index as usize]
                        .kind,
                    Some(pb::declaration::Kind::Relation(_))
                )
            {
                return Err(TypedError::Invalid(
                    "relations are predicates, not function values".into(),
                ));
            }
            return Self::partial_call(declaration, call.func.clone(), captures, sort);
        }
        let mut program = pb::Program {
            ..Default::default()
        };
        let mut slots = std::array::from_fn(|_| vec![]);
        let mut declarations = vec![];
        let mut ids = HashMap::from([(key(&body.0), 0)]);
        let mut pending = vec![body.0];
        program.nodes.push(pb::Node::default());
        let mut cursor = 0;
        while cursor < pending.len() {
            let record = pending[cursor].clone();
            if record.capture()?.is_some() {
                return Err(TypedError::Invalid(
                    "retained values in callbacks require explicit captures".into(),
                ));
            }
            let id = key(&record);
            let mut node = record.owner.as_ref().unwrap().program().unwrap().nodes
                [record.index as usize]
                .clone();
            if matches!(node.kind, Some(pb::node::Kind::Union(_))) {
                return Err(TypedError::Invalid(
                    "Unions in callback bodies are not supported yet".into(),
                ));
            }
            let sort = record.resolve(Arena::Sort, node.sort_id)?;
            node.sort_id = slots[Arena::Sort as usize].len() as u32;
            slots[Arena::Sort as usize].push(Slot::External(sort));
            if let Some(position) = formals.get(&id) {
                node.kind = Some(pb::node::Kind::Var(format!("_{position}")));
            } else {
                if matches!(node.kind, Some(pb::node::Kind::Var(_))) {
                    return Err(TypedError::Invalid(
                        "callback body has an uncaptured variable".into(),
                    ));
                }
                let call = match &node.kind {
                    Some(pb::node::Kind::Call(call)) => Some(call),
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::PartialCall(call)),
                    })) => Some(call),
                    _ => None,
                };
                if let Some(call) = call {
                    declarations.push(record.declaration(&call.func, DeclarationKind::Callable)?);
                }
                let mut one = pb::Program {
                    nodes: vec![node],
                    ..Default::default()
                };
                super::storage::visit(&mut one, Arena::Node, 0, |arena, index| {
                    if arena != Arena::Node {
                        return Ok(index);
                    }
                    let child = record.resolve(arena, index)?;
                    Ok(*ids.entry(key(&child)).or_insert_with(|| {
                        let index = pending.len() as u32;
                        pending.push(child);
                        program.nodes.push(pb::Node::default());
                        index
                    }))
                })?;
                node = one.nodes.pop().unwrap();
            }
            program.nodes[cursor] = node;
            cursor += 1;
        }
        let inputs = parameters
            .iter()
            .map(|value| {
                let node = &value.0.owner.as_ref().unwrap().program().unwrap().nodes
                    [value.0.index as usize];
                let index = slots[Arena::Sort as usize].len() as u32;
                slots[Arena::Sort as usize]
                    .push(Slot::External(value.0.resolve(Arena::Sort, node.sort_id)?));
                Ok(pb::Arg {
                    sort: index,
                    name: String::new(),
                })
            })
            .collect::<Result<Vec<_>, TypedError>>()?;
        let output = program.nodes[0].sort_id;
        let name = format!("__typed_callback_{}", fresh_scope());
        program.declarations.push(pb::Declaration {
            kind: Some(pb::declaration::Kind::UserDefinedPrimitive(
                pb::UserDefinedPrimitive {
                    name: name.clone(),
                    inputs,
                    output,
                    body: Some(0),
                },
            )),
            ..Default::default()
        });
        slots[Arena::Node as usize] = (0..program.nodes.len() as u32).map(Slot::Local).collect();
        let callable = publish(program, slots, declarations, Arena::Declaration, 0, vec![])?;
        Self::partial_call(callable, name, captures, sort)
    }

    // Publish the named callable and its evaluated prefix as one inert value.
    // The Func sort carries only the remaining parameter and result sorts.
    fn partial_call(
        callable: Record,
        name: String,
        captures: Vec<Self>,
        sort: SortRef,
    ) -> Result<Self, TypedError> {
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Sort as usize].push(Slot::External(sort.0));
        let count = captures.len() as u32;
        slots[Arena::Node as usize] = captures
            .into_iter()
            .map(|value| Slot::External(value.0))
            .collect();
        Ok(Self(publish(
            pb::Program {
                nodes: vec![pb::Node {
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::PartialCall(pb::Call {
                            func: name,
                            args: (0..count).collect(),
                        })),
                    })),
                    ..Default::default()
                }],
                ..Default::default()
            },
            slots,
            vec![callable],
            Arena::Node,
            0,
            vec![],
        )?))
    }

    // Exact container decoding validates the finite inert closure before
    // exposing child wrappers. It never evaluates a symbolic vec-of/get Call.
    pub(super) fn sequence_elements(
        &self,
        element: &SortRef,
        family: &str,
    ) -> Result<Vec<Self>, TypedError> {
        let owner = self.0.owner.as_ref().unwrap();
        let node = &owner.program().unwrap().nodes[self.0.index as usize];
        let values = match &node.kind {
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Vec(values)),
            })) if family == "Vec" => values,
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Set(values)),
            })) if family == "Set" => values,
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Multiset(values)),
            })) if family == "MultiSet" => values,
            _ => {
                return Err(TypedError::Decode(format!(
                    "expected an inert {family} value"
                )));
            }
        };
        let sort = self.0.resolve(Arena::Sort, node.sort_id)?;
        let Some(pb::sort::Kind::Application(f)) = &sort.sort().unwrap().kind else {
            return Err(TypedError::Decode(format!(
                "{family} payload/sort mismatch"
            )));
        };
        if f.name != family
            || f.args.len() != 1
            || SortRef(sort.resolve(Arena::Sort, f.args[0])?) != *element
        {
            return Err(TypedError::Decode(format!(
                "{family} element sort mismatch"
            )));
        }
        self.validate_inert()?;
        values
            .items
            .iter()
            .map(|i| self.0.resolve(Arena::Node, *i).map(Self))
            .collect()
    }

    // Inspect optional presence without evaluating a symbolic child or making
    // a temporary call. Canonical constructor identities come from the catalog.
    pub(super) fn maybe_value(
        &self,
        [none, some]: [&Callable; 2],
        element: &SortRef,
    ) -> Result<Option<Self>, TypedError> {
        let node = &self.0.owner.as_ref().unwrap().program().unwrap().nodes[self.0.index as usize];
        let sort = self.0.resolve(Arena::Sort, node.sort_id)?;
        let Some(pb::sort::Kind::Application(family)) = &sort.sort().unwrap().kind else {
            return Err(TypedError::Decode("Maybe payload/sort mismatch".into()));
        };
        if family.name != "Maybe"
            || family.args.len() != 1
            || SortRef(sort.resolve(Arena::Sort, family.args[0])?) != *element
        {
            return Err(TypedError::Decode("Maybe element sort mismatch".into()));
        }
        let child = match &node.kind {
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Maybe(maybe)),
            })) => maybe.value,
            Some(pb::node::Kind::Call(call)) if call.args.len() <= 1 => {
                let actual = self.0.declaration(&call.func, DeclarationKind::Callable)?;
                let expected = if call.args.is_empty() { none } else { some };
                if !super::decl::same_callable(&actual, &expected.0)? {
                    return Err(TypedError::Decode("not a catalog Maybe constructor".into()));
                }
                call.args.first().copied()
            }
            _ => return Err(TypedError::Decode("expected a direct Maybe value".into())),
        };
        child
            .map(|index| {
                let child = self.0.resolve(Arena::Node, index)?;
                let node =
                    &child.owner.as_ref().unwrap().program().unwrap().nodes[child.index as usize];
                if SortRef(child.resolve(Arena::Sort, node.sort_id)?) != *element {
                    return Err(TypedError::Decode("Maybe child sort mismatch".into()));
                }
                Ok(Self(child))
            })
            .transpose()
    }

    // Inspect exactly two direct children, never evaluate them. The schema
    // owns the PairValue layout; the catalog owns authored make-call identity.
    pub(super) fn pair_fields(
        &self,
        make: &Callable,
        first: &SortRef,
        second: &SortRef,
    ) -> Result<[Self; 2], TypedError> {
        let owner = self.0.owner.as_ref().unwrap();
        let node = &owner.program().unwrap().nodes[self.0.index as usize];
        let sort = self.0.resolve(Arena::Sort, node.sort_id)?;
        let Some(pb::sort::Kind::Application(family)) = &sort.sort().unwrap().kind else {
            return Err(TypedError::Decode("Pair payload/sort mismatch".into()));
        };
        if family.name != "Pair" || family.args.len() != 2 {
            return Err(TypedError::Decode("Pair payload/sort mismatch".into()));
        }
        for (arg, expected) in family.args.iter().zip([first, second]) {
            if SortRef(sort.resolve(Arena::Sort, *arg)?) != *expected {
                return Err(TypedError::Decode("Pair component sort mismatch".into()));
            }
        }
        let indices = match &node.kind {
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Pair(pair)),
            })) => [pair.first, pair.second]
                .map(|child| child.ok_or_else(|| TypedError::Decode("missing Pair child".into()))),
            Some(pb::node::Kind::Call(call)) if call.args.len() == 2 => {
                let actual = self.0.declaration(&call.func, DeclarationKind::Callable)?;
                if !super::decl::same_callable(&actual, &make.0)? {
                    return Err(TypedError::Decode(
                        "not the catalog Pair constructor".into(),
                    ));
                }
                [Ok(call.args[0]), Ok(call.args[1])]
            }
            _ => return Err(TypedError::Decode("expected direct Pair fields".into())),
        };
        let [left, right] = indices;
        let children = [
            Self(self.0.resolve(Arena::Node, left?)?),
            Self(self.0.resolve(Arena::Node, right?)?),
        ];
        for (child, expected) in children.iter().zip([first, second]) {
            let node =
                &child.0.owner.as_ref().unwrap().program().unwrap().nodes[child.0.index as usize];
            if SortRef(child.0.resolve(Arena::Sort, node.sort_id)?) != *expected {
                return Err(TypedError::Decode(
                    "Pair payload child sort mismatch".into(),
                ));
            }
        }
        Ok(children)
    }

    // Map inspection admits only direct canonical construction, not arbitrary
    // Vec computations. Keep Vec's public inert-only decoder separate.
    pub(super) fn map_entries(
        &self,
        [empty, of, vec_empty, vec_of, pair_make]: [&Callable; 5],
        key: &SortRef,
        value: &SortRef,
    ) -> Result<Vec<[Self; 2]>, TypedError> {
        let node = &self.0.owner.as_ref().unwrap().program().unwrap().nodes[self.0.index as usize];
        let sort = self.0.resolve(Arena::Sort, node.sort_id)?;
        let Some(pb::sort::Kind::Application(family)) = &sort.sort().unwrap().kind else {
            return Err(TypedError::Decode("Map payload/sort mismatch".into()));
        };
        if family.name != "Map" || family.args.len() != 2 {
            return Err(TypedError::Decode("Map payload/sort mismatch".into()));
        }
        for (arg, expected) in family.args.iter().zip([key, value]) {
            if SortRef(sort.resolve(Arena::Sort, *arg)?) != *expected {
                return Err(TypedError::Decode("Map component sort mismatch".into()));
            }
        }
        let mut entries = vec![];
        match &node.kind {
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Map(map)),
            })) => {
                for entry in &map.entries {
                    entries.push([
                        Self(
                            self.0.resolve(
                                Arena::Node,
                                entry
                                    .key
                                    .ok_or_else(|| TypedError::Decode("missing Map key".into()))?,
                            )?,
                        ),
                        Self(
                            self.0.resolve(
                                Arena::Node,
                                entry.value.ok_or_else(|| {
                                    TypedError::Decode("missing Map value".into())
                                })?,
                            )?,
                        ),
                    ]);
                }
            }
            Some(pb::node::Kind::Call(call)) => {
                let actual = self.0.declaration(&call.func, DeclarationKind::Callable)?;
                if call.args.is_empty() && super::decl::same_callable(&actual, &empty.0)? {
                    return Ok(entries);
                }
                if call.args.len() != 1 || !super::decl::same_callable(&actual, &of.0)? {
                    return Err(TypedError::Decode(
                        "expected direct catalog Map construction".into(),
                    ));
                }
                let vector = self.0.resolve(Arena::Node, call.args[0])?;
                let node =
                    &vector.owner.as_ref().unwrap().program().unwrap().nodes[vector.index as usize];
                let sort = vector.resolve(Arena::Sort, node.sort_id)?;
                let Some(pb::sort::Kind::Application(family)) = &sort.sort().unwrap().kind else {
                    return Err(TypedError::Decode(
                        "Map input must be a Vec of Pairs".into(),
                    ));
                };
                if family.name != "Vec" || family.args.len() != 1 {
                    return Err(TypedError::Decode(
                        "Map input must be a Vec of Pairs".into(),
                    ));
                }
                let pair = sort.resolve(Arena::Sort, family.args[0])?;
                let Some(pb::sort::Kind::Application(family)) = &pair.sort().unwrap().kind else {
                    return Err(TypedError::Decode("Map input must contain Pairs".into()));
                };
                if family.name != "Pair" || family.args.len() != 2 {
                    return Err(TypedError::Decode("Map input must contain Pairs".into()));
                }
                for (arg, expected) in family.args.iter().zip([key, value]) {
                    if SortRef(pair.resolve(Arena::Sort, *arg)?) != *expected {
                        return Err(TypedError::Decode(
                            "Map input Pair component sort mismatch".into(),
                        ));
                    }
                }
                let children = match &node.kind {
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Vec(values)),
                    })) => &values.items,
                    Some(pb::node::Kind::Call(call)) => {
                        let actual = vector.declaration(&call.func, DeclarationKind::Callable)?;
                        if !(call.args.is_empty()
                            && super::decl::same_callable(&actual, &vec_empty.0)?
                            || super::decl::same_callable(&actual, &vec_of.0)?)
                        {
                            return Err(TypedError::Decode(
                                "Map entries require a direct catalog Vec construction".into(),
                            ));
                        }
                        &call.args
                    }
                    _ => {
                        return Err(TypedError::Decode(
                            "Map entries require a direct Vec value".into(),
                        ));
                    }
                };
                for child in children {
                    entries.push(
                        Self(vector.resolve(Arena::Node, *child)?)
                            .pair_fields(pair_make, key, value)?,
                    );
                }
            }
            _ => return Err(TypedError::Decode("expected direct Map entries".into())),
        }
        for entry in &entries {
            for (child, expected) in entry.iter().zip([key, value]) {
                let node = &child.0.owner.as_ref().unwrap().program().unwrap().nodes
                    [child.0.index as usize];
                if SortRef(child.0.resolve(Arena::Sort, node.sort_id)?) != *expected {
                    return Err(TypedError::Decode("Map payload child sort mismatch".into()));
                }
            }
        }
        Ok(entries)
    }

    pub(super) fn validate_inert(&self) -> Result<(), TypedError> {
        let mut colors = HashMap::new();
        let mut pending = vec![(self.0.clone(), false)];
        while let Some((record, finish)) = pending.pop() {
            let owner = record.owner.as_ref().unwrap();
            let key = (owner.id, record.index);
            if finish {
                colors.insert(key, 2);
                continue;
            }
            match colors.get(&key) {
                Some(2) => continue,
                Some(1) => {
                    return Err(TypedError::Decode(
                        "cyclic extraction is not inert data".into(),
                    ));
                }
                _ => {}
            }
            colors.insert(key, 1);
            pending.push((record.clone(), true));
            let node = &owner.program().unwrap().nodes[record.index as usize];
            let sort = SortRef(record.resolve(Arena::Sort, node.sort_id)?);
            sort.validate_closed()?;
            let pair_children;
            let map_children;
            let children: &[u32] = match &node.kind {
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Maybe(maybe)),
                })) => {
                    let Some(pb::sort::Kind::Application(f)) = &sort.0.sort().unwrap().kind else {
                        return Err(TypedError::Decode("Maybe payload/sort mismatch".into()));
                    };
                    if f.name != "Maybe" || f.args.len() != 1 {
                        return Err(TypedError::Decode("Maybe payload/sort mismatch".into()));
                    }
                    if let Some(index) = maybe.value {
                        let child = record.resolve(Arena::Node, index)?;
                        let node = &child.owner.as_ref().unwrap().program().unwrap().nodes
                            [child.index as usize];
                        if SortRef(child.resolve(Arena::Sort, node.sort_id)?)
                            != SortRef(sort.0.resolve(Arena::Sort, f.args[0])?)
                        {
                            return Err(TypedError::Decode("Maybe child sort mismatch".into()));
                        }
                    }
                    maybe.value.as_slice()
                }
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Map(map)),
                })) => {
                    let Some(pb::sort::Kind::Application(f)) = &sort.0.sort().unwrap().kind else {
                        return Err(TypedError::Decode("Map payload/sort mismatch".into()));
                    };
                    if f.name != "Map" || f.args.len() != 2 {
                        return Err(TypedError::Decode("Map payload/sort mismatch".into()));
                    }
                    map_children = map
                        .entries
                        .iter()
                        .flat_map(|entry| [entry.key, entry.value])
                        .map(|child| {
                            child.ok_or_else(|| TypedError::Decode("missing Map child".into()))
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    for (index, expected) in map_children.iter().zip(f.args.iter().cycle()) {
                        let child = record.resolve(Arena::Node, *index)?;
                        let node = &child.owner.as_ref().unwrap().program().unwrap().nodes
                            [child.index as usize];
                        if SortRef(child.resolve(Arena::Sort, node.sort_id)?)
                            != SortRef(sort.0.resolve(Arena::Sort, *expected)?)
                        {
                            return Err(TypedError::Decode(
                                "Map payload child sort mismatch".into(),
                            ));
                        }
                    }
                    &map_children
                }
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Pair(pair)),
                })) => {
                    let Some(pb::sort::Kind::Application(f)) = &sort.0.sort().unwrap().kind else {
                        return Err(TypedError::Decode("Pair payload/sort mismatch".into()));
                    };
                    if f.name != "Pair" || f.args.len() != 2 {
                        return Err(TypedError::Decode("Pair payload/sort mismatch".into()));
                    }
                    pair_children = [
                        pair.first
                            .ok_or_else(|| TypedError::Decode("missing Pair child".into()))?,
                        pair.second
                            .ok_or_else(|| TypedError::Decode("missing Pair child".into()))?,
                    ];
                    for (index, expected) in pair_children.iter().zip(&f.args) {
                        let child = record.resolve(Arena::Node, *index)?;
                        let node = &child.owner.as_ref().unwrap().program().unwrap().nodes
                            [child.index as usize];
                        if SortRef(child.resolve(Arena::Sort, node.sort_id)?)
                            != SortRef(sort.0.resolve(Arena::Sort, *expected)?)
                        {
                            return Err(TypedError::Decode(
                                "Pair payload child sort mismatch".into(),
                            ));
                        }
                    }
                    &pair_children
                }
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value:
                        Some(
                            value @ (pb::primitive_value::Value::Vec(values)
                            | pb::primitive_value::Value::Set(values)
                            | pb::primitive_value::Value::Multiset(values)),
                        ),
                })) => {
                    let family = if matches!(value, pb::primitive_value::Value::Set(_)) {
                        "Set"
                    } else if matches!(value, pb::primitive_value::Value::Multiset(_)) {
                        "MultiSet"
                    } else {
                        "Vec"
                    };
                    let Some(pb::sort::Kind::Application(f)) = &sort.0.sort().unwrap().kind else {
                        return Err(TypedError::Decode(format!(
                            "{family} payload/sort mismatch"
                        )));
                    };
                    if f.name != family || f.args.len() != 1 {
                        return Err(TypedError::Decode(format!(
                            "{family} payload/sort mismatch"
                        )));
                    }
                    let expected = SortRef(sort.0.resolve(Arena::Sort, f.args[0])?);
                    for index in &values.items {
                        let child = record.resolve(Arena::Node, *index)?;
                        let node = &child.owner.as_ref().unwrap().program().unwrap().nodes
                            [child.index as usize];
                        if SortRef(child.resolve(Arena::Sort, node.sort_id)?) != expected {
                            return Err(TypedError::Decode(format!(
                                "{family} payload element sort mismatch"
                            )));
                        }
                    }
                    &values.items
                }
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::PartialCall(call)),
                })) => {
                    let Some(pb::sort::Kind::Func(function)) = &sort.0.sort().unwrap().kind else {
                        return Err(TypedError::Decode(
                            "partial call requires a function sort".into(),
                        ));
                    };
                    let mut arguments = call
                        .args
                        .iter()
                        .map(|index| {
                            let child = record.resolve(Arena::Node, *index)?;
                            let node = &child.owner.as_ref().unwrap().program().unwrap().nodes
                                [child.index as usize];
                            child.resolve(Arena::Sort, node.sort_id).map(SortRef)
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    for parameter in &function.params {
                        arguments.push(SortRef(sort.0.resolve(Arena::Sort, *parameter)?));
                    }
                    Callable(record.declaration(&call.func, DeclarationKind::Callable)?)
                        .check_call(
                            &arguments,
                            &SortRef(sort.0.resolve(Arena::Sort, function.result)?),
                        )
                        .map_err(|error| TypedError::Decode(error.to_string()))?;
                    &call.args
                }
                Some(pb::node::Kind::PrimitiveValue(value)) => {
                    validate_literal(&sort, value)?;
                    &[]
                }
                Some(pb::node::Kind::Call(call)) => {
                    let declaration = record.declaration(&call.func, DeclarationKind::Callable)?;
                    let Some(pb::declaration::Kind::Constructor(constructor)) = declaration
                        .owner
                        .as_ref()
                        .unwrap()
                        .program()
                        .ok()
                        .and_then(|program| program.declarations.get(declaration.index as usize))
                        .and_then(|declaration| declaration.kind.as_ref())
                    else {
                        return Err(TypedError::Decode(
                            "extracted call is not a constructor".into(),
                        ));
                    };
                    if call.args.len() != constructor.inputs.len()
                        || sort != SortRef(declaration.resolve(Arena::Sort, constructor.output)?)
                    {
                        return Err(TypedError::Decode(format!(
                            "invalid extraction signature for {}",
                            call.func
                        )));
                    }
                    for (index, input) in call.args.iter().zip(&constructor.inputs) {
                        let child = record.resolve(Arena::Node, *index)?;
                        let node = &child.owner.as_ref().unwrap().program().unwrap().nodes
                            [child.index as usize];
                        if SortRef(child.resolve(Arena::Sort, node.sort_id)?)
                            != SortRef(declaration.resolve(Arena::Sort, input.sort)?)
                        {
                            return Err(TypedError::Decode(format!(
                                "invalid extraction argument sort for {}",
                                call.func
                            )));
                        }
                    }
                    &call.args
                }
                _ => {
                    return Err(TypedError::Decode(
                        "extraction must contain inert constructor/value data".into(),
                    ));
                }
            };
            for index in children.iter().rev() {
                pending.push((record.resolve(Arena::Node, *index)?, false));
            }
        }
        Ok(())
    }

    pub(super) fn select(
        &self,
        pattern: &Self,
        variables: &[Self],
    ) -> Result<Option<Vec<Self>>, TypedError> {
        if pattern.0.capture()?.is_some() {
            return Err(TypedError::Invalid(
                "a capture is not a call selector".into(),
            ));
        }
        if self.0.capture()?.is_some() {
            return Ok(None);
        }
        let p =
            &pattern.0.owner.as_ref().unwrap().program().unwrap().nodes[pattern.0.index as usize];
        let Some(pb::node::Kind::Call(call)) = &p.kind else {
            return Err(TypedError::Invalid(
                "selector must return one direct constructor, function or relation".into(),
            ));
        };
        let declaration = pattern
            .0
            .declaration(&call.func, DeclarationKind::Callable)?;
        if declaration.arena != Arena::Declaration
            || !matches!(
                &declaration
                    .owner
                    .as_ref()
                    .unwrap()
                    .program()
                    .unwrap()
                    .declarations[declaration.index as usize]
                    .kind,
                Some(
                    pb::declaration::Kind::Constructor(_)
                        | pb::declaration::Kind::Function(_)
                        | pb::declaration::Kind::Relation(_)
                )
            )
        {
            return Err(TypedError::Invalid(
                "selector must return a constructor, function or relation, not a host operation"
                    .into(),
            ));
        }
        if call.args.len() != variables.len()
            || call
                .args
                .iter()
                .zip(variables)
                .any(|(i, v)| Expr(pattern.0.resolve(Arena::Node, *i).unwrap()) != *v)
        {
            return Err(TypedError::Invalid(
                "selector must use its fresh arguments once in declaration order".into(),
            ));
        }
        let n = &self.0.owner.as_ref().unwrap().program().unwrap().nodes[self.0.index as usize];
        let Some(pb::node::Kind::Call(actual)) = &n.kind else {
            return Ok(None);
        };
        if !super::decl::same_callable(
            &self
                .0
                .declaration(&actual.func, DeclarationKind::Callable)?,
            &declaration,
        )? {
            return Ok(None);
        }
        actual
            .args
            .iter()
            .map(|i| self.0.resolve(Arena::Node, *i).map(Self))
            .collect::<Result<_, _>>()
            .map(Some)
    }
}

impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        let mut pending = vec![(self.0.clone(), other.0.clone())];
        let mut seen = HashSet::new();
        while let Some((a, b)) = pending.pop() {
            let oa = a.owner.as_ref().unwrap();
            let ob = b.owner.as_ref().unwrap();
            let ka = (oa.id, a.index);
            let kb = (ob.id, b.index);
            if ka == kb || !seen.insert((ka, kb)) {
                continue;
            }
            let na = &oa.program().unwrap().nodes[a.index as usize];
            let nb = &ob.program().unwrap().nodes[b.index as usize];
            if SortRef(a.resolve(Arena::Sort, na.sort_id).unwrap())
                != SortRef(b.resolve(Arena::Sort, nb.sort_id).unwrap())
            {
                return false;
            }
            match (a.capture(), b.capture()) {
                (Ok(Some(a)), Ok(Some(b))) if a.name == b.name => {
                    pending.push((a.initializer, b.initializer));
                    continue;
                }
                (Ok(None), Ok(None)) => (),
                _ => return false,
            }
            match (&na.kind, &nb.kind) {
                (Some(pb::node::Kind::Var(a)), Some(pb::node::Kind::Var(b))) if a == b => {}
                (
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Map(ma)),
                    })),
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Map(mb)),
                    })),
                ) if ma.entries.len() == mb.entries.len() => {
                    for (ea, eb) in ma.entries.iter().zip(&mb.entries) {
                        for (ia, ib) in [ea.key, ea.value].into_iter().zip([eb.key, eb.value]) {
                            pending.push((
                                a.resolve(Arena::Node, ia.expect("published Map child"))
                                    .unwrap(),
                                b.resolve(Arena::Node, ib.expect("published Map child"))
                                    .unwrap(),
                            ));
                        }
                    }
                }
                (
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Pair(pa)),
                    })),
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Pair(pb)),
                    })),
                ) => {
                    for (ia, ib) in [pa.first, pa.second].into_iter().zip([pb.first, pb.second]) {
                        pending.push((
                            a.resolve(Arena::Node, ia.expect("published Pair child"))
                                .unwrap(),
                            b.resolve(Arena::Node, ib.expect("published Pair child"))
                                .unwrap(),
                        ));
                    }
                }
                (
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Vec(va)),
                    })),
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Vec(vb)),
                    })),
                )
                | (
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Set(va)),
                    })),
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Set(vb)),
                    })),
                ) if va.items.len() == vb.items.len() => {
                    for (ia, ib) in va.items.iter().zip(&vb.items) {
                        pending.push((
                            a.resolve(Arena::Node, *ia).unwrap(),
                            b.resolve(Arena::Node, *ib).unwrap(),
                        ));
                    }
                }
                (
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Multiset(va)),
                    })),
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Multiset(vb)),
                    })),
                ) if va.items.len() == vb.items.len() => {
                    for (ia, ib) in va.items.iter().zip(&vb.items) {
                        pending.push((
                            a.resolve(Arena::Node, *ia).unwrap(),
                            b.resolve(Arena::Node, *ib).unwrap(),
                        ));
                    }
                }
                (
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Maybe(ma)),
                    })),
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Maybe(mb)),
                    })),
                ) if ma.value.is_some() == mb.value.is_some() => {
                    if let Some((ia, ib)) = ma.value.zip(mb.value) {
                        pending.push((
                            a.resolve(Arena::Node, ia).unwrap(),
                            b.resolve(Arena::Node, ib).unwrap(),
                        ));
                    }
                }
                (
                    Some(pb::node::Kind::PrimitiveValue(a)),
                    Some(pb::node::Kind::PrimitiveValue(b)),
                ) if matches!(
                    a.value,
                    Some(
                        pb::primitive_value::Value::I64(_)
                            | pb::primitive_value::Value::F64Bits(_)
                            | pb::primitive_value::Value::String(_)
                            | pb::primitive_value::Value::Bool(_)
                            | pb::primitive_value::Value::Unit(_)
                            | pb::primitive_value::Value::BigInt(_)
                            | pb::primitive_value::Value::BigRat(_)
                            | pb::primitive_value::Value::Rational(_)
                    )
                ) && a == b => {}
                (Some(pb::node::Kind::Apply(a_apply)), Some(pb::node::Kind::Apply(b_apply)))
                    if a_apply.args.len() == b_apply.args.len() =>
                {
                    let (Some(a_function), Some(b_function)) = (a_apply.function, b_apply.function)
                    else {
                        return false;
                    };
                    for (ia, ib) in std::iter::once(a_function)
                        .chain(a_apply.args.iter().copied())
                        .zip(std::iter::once(b_function).chain(b_apply.args.iter().copied()))
                    {
                        pending.push((
                            a.resolve(Arena::Node, ia).unwrap(),
                            b.resolve(Arena::Node, ib).unwrap(),
                        ));
                    }
                }
                (Some(pb::node::Kind::Call(ca)), Some(pb::node::Kind::Call(cb)))
                | (
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::PartialCall(ca)),
                    })),
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::PartialCall(cb)),
                    })),
                ) if ca.func == cb.func && ca.args.len() == cb.args.len() => {
                    if !super::decl::same_callable(
                        &a.declaration(&ca.func, DeclarationKind::Callable).unwrap(),
                        &b.declaration(&cb.func, DeclarationKind::Callable).unwrap(),
                    )
                    .unwrap_or(false)
                    {
                        return false;
                    }
                    for (ia, ib) in ca.args.iter().zip(&cb.args) {
                        pending.push((
                            a.resolve(Arena::Node, *ia).unwrap(),
                            b.resolve(Arena::Node, *ib).unwrap(),
                        ));
                    }
                }
                // Union identity is allocation identity; never hash-cons it.
                _ => return false,
            }
        }
        true
    }
}
impl Eq for Expr {}

impl Hash for Expr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut hashes: HashMap<Key, u64> = HashMap::new();
        let mut pending = vec![(self.0.clone(), false)];
        while let Some((record, finish)) = pending.pop() {
            let owner = record.owner.as_ref().unwrap();
            let key = (owner.id, record.arena, record.index);
            if hashes.contains_key(&key) {
                continue;
            }
            let node = &owner.program().unwrap().nodes[record.index as usize];
            if let Some(capture) = record.capture().expect("published capture recipe") {
                if !finish {
                    pending.push((record.clone(), true));
                    pending.push((capture.initializer, false));
                    continue;
                }
                let mut h = DefaultHasher::new();
                15u8.hash(&mut h);
                SortRef(record.resolve(Arena::Sort, node.sort_id).unwrap()).hash(&mut h);
                capture.name.hash(&mut h);
                let child = capture.initializer;
                hashes[&(child.owner.as_ref().unwrap().id, child.arena, child.index)].hash(&mut h);
                hashes.insert(key, h.finish());
                continue;
            }
            let pair_children;
            let map_children;
            let apply_children;
            let children: &[u32] = match &node.kind {
                Some(pb::node::Kind::Call(c)) => &c.args,
                Some(pb::node::Kind::Apply(apply)) => {
                    apply_children =
                        std::iter::once(apply.function.expect("published function operand"))
                            .chain(apply.args.iter().copied())
                            .collect::<Vec<_>>();
                    &apply_children
                }
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::PartialCall(c)),
                })) => &c.args,
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Maybe(maybe)),
                })) => maybe.value.as_slice(),
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Map(map)),
                })) => {
                    map_children = map
                        .entries
                        .iter()
                        .flat_map(|entry| {
                            [
                                entry.key.expect("published Map key"),
                                entry.value.expect("published Map value"),
                            ]
                        })
                        .collect::<Vec<_>>();
                    &map_children
                }
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Pair(pair)),
                })) => {
                    pair_children = [
                        pair.first.expect("published Pair child"),
                        pair.second.expect("published Pair child"),
                    ];
                    &pair_children
                }
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value:
                        Some(
                            pb::primitive_value::Value::Vec(v)
                            | pb::primitive_value::Value::Set(v)
                            | pb::primitive_value::Value::Multiset(v),
                        ),
                })) => &v.items,
                _ => &[],
            };
            if !finish && !children.is_empty() {
                pending.push((record.clone(), true));
                for i in children.iter().rev() {
                    pending.push((record.resolve(Arena::Node, *i).unwrap(), false));
                }
                continue;
            }
            let mut h = DefaultHasher::new();
            SortRef(record.resolve(Arena::Sort, node.sort_id).unwrap()).hash(&mut h);
            match &node.kind {
                Some(pb::node::Kind::Var(v)) => {
                    0u8.hash(&mut h);
                    v.hash(&mut h);
                }
                Some(pb::node::Kind::Call(c)) => {
                    1u8.hash(&mut h);
                    c.func.hash(&mut h);
                    c.args.len().hash(&mut h);
                    for i in &c.args {
                        let child = record.resolve(Arena::Node, *i).unwrap();
                        hashes[&(child.owner.as_ref().unwrap().id, child.arena, child.index)]
                            .hash(&mut h);
                    }
                }
                Some(pb::node::Kind::Apply(apply)) => {
                    16u8.hash(&mut h);
                    apply.args.len().hash(&mut h);
                    for index in
                        std::iter::once(apply.function.expect("published function operand"))
                            .chain(apply.args.iter().copied())
                    {
                        let child = record.resolve(Arena::Node, index).unwrap();
                        hashes[&(child.owner.as_ref().unwrap().id, child.arena, child.index)]
                            .hash(&mut h);
                    }
                }
                Some(pb::node::Kind::Union(_)) => {
                    2u8.hash(&mut h);
                    key.hash(&mut h);
                }
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue { value: Some(value) })) => {
                    match value {
                        pb::primitive_value::Value::I64(value) => {
                            3u8.hash(&mut h);
                            value.hash(&mut h);
                        }
                        pb::primitive_value::Value::F64Bits(bits) => {
                            4u8.hash(&mut h);
                            bits.hash(&mut h);
                        }
                        pb::primitive_value::Value::String(value) => {
                            8u8.hash(&mut h);
                            value.hash(&mut h);
                        }
                        pb::primitive_value::Value::Bool(value) => {
                            9u8.hash(&mut h);
                            value.hash(&mut h);
                        }
                        pb::primitive_value::Value::Unit(_) => {
                            10u8.hash(&mut h);
                        }
                        pb::primitive_value::Value::BigInt(value) => {
                            11u8.hash(&mut h);
                            value.hash(&mut h);
                        }
                        pb::primitive_value::Value::BigRat(value) => {
                            12u8.hash(&mut h);
                            value.numerator.hash(&mut h);
                            value.denominator.hash(&mut h);
                        }
                        pb::primitive_value::Value::Rational(value) => {
                            13u8.hash(&mut h);
                            value.numerator.hash(&mut h);
                            value.denominator.hash(&mut h);
                        }
                        pb::primitive_value::Value::Vec(values)
                        | pb::primitive_value::Value::Set(values)
                        | pb::primitive_value::Value::Multiset(values) => {
                            if matches!(value, pb::primitive_value::Value::Set(_)) {
                                14u8
                            } else if matches!(value, pb::primitive_value::Value::Multiset(_)) {
                                16u8
                            } else {
                                5u8
                            }
                            .hash(&mut h);
                            values.items.len().hash(&mut h);
                            for i in &values.items {
                                let child = record.resolve(Arena::Node, *i).unwrap();
                                hashes
                                    [&(child.owner.as_ref().unwrap().id, child.arena, child.index)]
                                    .hash(&mut h);
                            }
                        }
                        pb::primitive_value::Value::Maybe(maybe) => {
                            15u8.hash(&mut h);
                            maybe.value.is_some().hash(&mut h);
                            if let Some(index) = maybe.value {
                                let child = record.resolve(Arena::Node, index).unwrap();
                                hashes
                                    [&(child.owner.as_ref().unwrap().id, child.arena, child.index)]
                                    .hash(&mut h);
                            }
                        }
                        pb::primitive_value::Value::Pair(_) => {
                            6u8.hash(&mut h);
                            for i in children {
                                let child = record.resolve(Arena::Node, *i).unwrap();
                                hashes
                                    [&(child.owner.as_ref().unwrap().id, child.arena, child.index)]
                                    .hash(&mut h);
                            }
                        }
                        pb::primitive_value::Value::Map(map) => {
                            7u8.hash(&mut h);
                            map.entries.len().hash(&mut h);
                            for i in children {
                                let child = record.resolve(Arena::Node, *i).unwrap();
                                hashes
                                    [&(child.owner.as_ref().unwrap().id, child.arena, child.index)]
                                    .hash(&mut h);
                            }
                        }
                        pb::primitive_value::Value::PartialCall(call) => {
                            17u8.hash(&mut h);
                            call.func.hash(&mut h);
                            call.args.len().hash(&mut h);
                            for i in &call.args {
                                let child = record.resolve(Arena::Node, *i).unwrap();
                                hashes
                                    [&(child.owner.as_ref().unwrap().id, child.arena, child.index)]
                                    .hash(&mut h);
                            }
                        }
                        _ => unreachable!("unsupported typed scalar codec"),
                    }
                }
                _ => unreachable!(),
            }
            hashes.insert(key, h.finish());
        }
        hashes[&(
            self.0.owner.as_ref().unwrap().id,
            self.0.arena,
            self.0.index,
        )]
            .hash(state);
    }
}
impl std::fmt::Debug for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let n = &self.0.owner.as_ref().unwrap().program().unwrap().nodes[self.0.index as usize];
        // Deliberately bounded, with no recursive child formatting.
        match &n.kind {
            Some(pb::node::Kind::Call(c)) => write!(f, "Call({:?}, {} args)", c.func, c.args.len()),
            Some(pb::node::Kind::Apply(apply)) => write!(f, "Apply({} args)", apply.args.len()),
            Some(pb::node::Kind::Var(v)) => write!(f, "Var({v:?})"),
            Some(pb::node::Kind::Union(u)) => write!(f, "Union({} members)", u.members.len()),
            Some(pb::node::Kind::PrimitiveValue(v)) => write!(f, "Literal({:?})", v.value),
            _ => f.write_str("unsupported node"),
        }
    }
}

// The shared wire codec owns scalar validity and sort agreement.
pub(super) fn validate_literal(
    sort: &SortRef,
    value: &pb::PrimitiveValue,
) -> Result<(), TypedError> {
    if let Some(pb::sort::Kind::Application(family)) = &sort.0.sort().unwrap().kind
        && family.args.is_empty()
    {
        return crate::protobuf::value::Scalar::decode(Some(&family.name), value)
            .map(|_| ())
            .map_err(TypedError::Decode);
    }
    Err(TypedError::Decode(
        "scalar payload does not match its sort".into(),
    ))
}
