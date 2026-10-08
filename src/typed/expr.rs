use super::{
    SortRef, TypedError,
    decl::Callable,
    pb,
    storage::{Arena, Key, Record, Slot, publish},
};
use std::{
    collections::{HashMap, HashSet},
    hash::{DefaultHasher, Hash, Hasher},
    sync::atomic::{AtomicU64, Ordering},
};

/// A nominal Rust view of an immutable generated expression record.
pub trait EgglogValue: Clone + Eq + Hash + std::fmt::Debug + Send + Sync + 'static {
    #[doc(hidden)]
    fn sort_ref() -> SortRef;
    #[doc(hidden)]
    fn expression(&self) -> &Expr;
    #[doc(hidden)]
    fn from_expression(expr: Expr) -> Self;
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
                ir_version: 1,
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
        )?))
    }

    fn variable(sort: SortRef, token: String) -> Self {
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Sort as usize] = vec![Slot::External(sort.0)];
        let program = pb::Program {
            ir_version: 1,
            nodes: vec![pb::Node {
                kind: Some(pb::node::Kind::Var(token)),
                ..Default::default()
            }],
            ..Default::default()
        };
        Self(publish(program, slots, vec![], Arena::Node, 0).unwrap())
    }

    pub fn call(callable: &Callable, arguments: Vec<Self>) -> Self {
        let owner = callable.0.owner.as_ref().unwrap();
        let (name, inputs, output) =
            match &owner.program.declarations[callable.0.index as usize].kind {
                Some(pb::declaration::Kind::Constructor(c)) => (&c.name, &c.inputs, c.output),
                Some(pb::declaration::Kind::HostPrimitive(p)) => {
                    let Some(pb::host_primitive::Typing::Signature(signature)) = &p.typing else {
                        panic!("unsupported callable typing");
                    };
                    assert!(
                        signature.type_params.is_empty() && signature.varargs.is_empty(),
                        "generic host calls await instantiation support"
                    );
                    (
                        &p.name,
                        &signature.inputs,
                        signature.output.expect("callable result sort"),
                    )
                }
                _ => panic!("unsupported callable declaration"),
            };
        assert_eq!(inputs.len(), arguments.len(), "callable arity");
        for (arg, expected) in arguments.iter().zip(inputs) {
            let node = &arg.0.owner.as_ref().unwrap().program.nodes[arg.0.index as usize];
            assert!(
                SortRef(arg.0.resolve(Arena::Sort, node.sort_id).unwrap())
                    == SortRef(callable.0.resolve(Arena::Sort, expected.sort).unwrap()),
                "callable input sort"
            );
        }
        let output = SortRef(callable.0.resolve(Arena::Sort, output).unwrap());
        Self::build_call(callable, name, arguments, output)
    }

    pub(super) fn call_with_result(
        callable: &Callable,
        arguments: Vec<Self>,
        output: SortRef,
    ) -> Result<Self, TypedError> {
        let owner = callable.0.owner.as_ref().unwrap();
        let Some(pb::declaration::Kind::HostPrimitive(primitive)) =
            &owner.program.declarations[callable.0.index as usize].kind
        else {
            return Err(TypedError::Invalid("expected host callable".into()));
        };
        let Some(pb::host_primitive::Typing::Signature(signature)) = &primitive.typing else {
            return Err(TypedError::Invalid("unsupported callable typing".into()));
        };
        let tail_len = arguments
            .len()
            .checked_sub(signature.inputs.len())
            .ok_or_else(|| TypedError::Invalid("callable arity".into()))?;
        let valid_tail = if signature.varargs.is_empty() {
            tail_len == 0
        } else {
            tail_len.is_multiple_of(signature.varargs.len())
        };
        if !valid_tail {
            return Err(TypedError::Invalid("callable arity".into()));
        }
        let mut bindings = vec![None; signature.type_params.len()];
        for (argument, expected) in arguments.iter().zip(
            signature
                .inputs
                .iter()
                .chain(signature.varargs.iter().cycle()),
        ) {
            let node = &argument.0.owner.as_ref().unwrap().program.nodes[argument.0.index as usize];
            SortRef(callable.0.resolve(Arena::Sort, expected.sort)?).match_pattern(
                &SortRef(argument.0.resolve(Arena::Sort, node.sort_id)?),
                &mut bindings,
            )?;
        }
        SortRef(
            callable.0.resolve(
                Arena::Sort,
                signature
                    .output
                    .ok_or_else(|| TypedError::Invalid("missing result pattern".into()))?,
            )?,
        )
        .match_pattern(&output, &mut bindings)?;
        if bindings.iter().any(Option::is_none) {
            return Err(TypedError::Invalid("undetermined generic parameter".into()));
        }
        Ok(Self::build_call(
            callable,
            &primitive.name,
            arguments,
            output,
        ))
    }

    // Publish one generated Call and location-only imports. Both closed and
    // generic validation paths share this ownership/record construction boundary.
    fn build_call(callable: &Callable, name: &str, arguments: Vec<Self>, output: SortRef) -> Self {
        let program = pb::Program {
            ir_version: 1,
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
        Self(publish(program, slots, vec![callable.0.clone()], Arena::Node, 0).unwrap())
    }

    // Exact container decoding validates the finite inert closure before
    // exposing child wrappers. It never evaluates a symbolic vec-of/get Call.
    pub(super) fn vec_elements(&self, element: &SortRef) -> Result<Vec<Self>, TypedError> {
        let owner = self.0.owner.as_ref().unwrap();
        let node = &owner.program.nodes[self.0.index as usize];
        let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Vec(values)),
        })) = &node.kind
        else {
            return Err(TypedError::Decode("expected an inert Vec value".into()));
        };
        let sort = self.0.resolve(Arena::Sort, node.sort_id)?;
        let Some(pb::sort::Kind::Family(f)) =
            &sort.owner.as_ref().unwrap().program.sorts[sort.index as usize].kind
        else {
            return Err(TypedError::Decode("Vec payload/sort mismatch".into()));
        };
        if f.name != "Vec"
            || f.args.len() != 1
            || SortRef(sort.resolve(Arena::Sort, f.args[0])?) != *element
        {
            return Err(TypedError::Decode("Vec element sort mismatch".into()));
        }
        self.validate_inert()?;
        values
            .items
            .iter()
            .map(|i| self.0.resolve(Arena::Node, *i).map(Self))
            .collect()
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
            let node = &owner.program.nodes[record.index as usize];
            let sort = SortRef(record.resolve(Arena::Sort, node.sort_id)?);
            sort.validate_closed()?;
            let children: &[u32] = match &node.kind {
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Vec(values)),
                })) => {
                    let Some(pb::sort::Kind::Family(f)) =
                        &sort.0.owner.as_ref().unwrap().program.sorts[sort.0.index as usize].kind
                    else {
                        return Err(TypedError::Decode("Vec payload/sort mismatch".into()));
                    };
                    if f.name != "Vec" || f.args.len() != 1 {
                        return Err(TypedError::Decode("Vec payload/sort mismatch".into()));
                    }
                    let expected = SortRef(sort.0.resolve(Arena::Sort, f.args[0])?);
                    for index in &values.items {
                        let child = record.resolve(Arena::Node, *index)?;
                        let node =
                            &child.owner.as_ref().unwrap().program.nodes[child.index as usize];
                        if SortRef(child.resolve(Arena::Sort, node.sort_id)?) != expected {
                            return Err(TypedError::Decode(
                                "Vec payload element sort mismatch".into(),
                            ));
                        }
                    }
                    &values.items
                }
                Some(pb::node::Kind::PrimitiveValue(value)) => {
                    validate_literal(&sort, value)?;
                    &[]
                }
                Some(pb::node::Kind::Call(call)) => {
                    let declaration = record.declaration(&call.func, false)?;
                    let Some(pb::declaration::Kind::Constructor(constructor)) =
                        &declaration.owner.as_ref().unwrap().program.declarations
                            [declaration.index as usize]
                            .kind
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
                        let node =
                            &child.owner.as_ref().unwrap().program.nodes[child.index as usize];
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
        let p = &pattern.0.owner.as_ref().unwrap().program.nodes[pattern.0.index as usize];
        let Some(pb::node::Kind::Call(call)) = &p.kind else {
            return Err(TypedError::Invalid(
                "selector must return one direct constructor".into(),
            ));
        };
        let declaration = pattern.0.declaration(&call.func, false)?;
        if !matches!(
            &declaration.owner.as_ref().unwrap().program.declarations[declaration.index as usize]
                .kind,
            Some(pb::declaration::Kind::Constructor(_))
        ) {
            return Err(TypedError::Invalid(
                "selector must return a constructor, not a host operation".into(),
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
        let n = &self.0.owner.as_ref().unwrap().program.nodes[self.0.index as usize];
        let Some(pb::node::Kind::Call(actual)) = &n.kind else {
            return Ok(None);
        };
        if !super::decl::same_callable(&self.0.declaration(&actual.func, false)?, &declaration)? {
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
            let na = &oa.program.nodes[a.index as usize];
            let nb = &ob.program.nodes[b.index as usize];
            if SortRef(a.resolve(Arena::Sort, na.sort_id).unwrap())
                != SortRef(b.resolve(Arena::Sort, nb.sort_id).unwrap())
            {
                return false;
            }
            match (&na.kind, &nb.kind) {
                (Some(pb::node::Kind::Var(a)), Some(pb::node::Kind::Var(b))) if a == b => {}
                (
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Vec(va)),
                    })),
                    Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Vec(vb)),
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
                    Some(pb::node::Kind::PrimitiveValue(a)),
                    Some(pb::node::Kind::PrimitiveValue(b)),
                ) if matches!(
                    a.value,
                    Some(
                        pb::primitive_value::Value::I64(_) | pb::primitive_value::Value::F64Bits(_)
                    )
                ) && a == b => {}
                (Some(pb::node::Kind::Call(ca)), Some(pb::node::Kind::Call(cb)))
                    if ca.func == cb.func && ca.args.len() == cb.args.len() =>
                {
                    if !super::decl::same_callable(
                        &a.declaration(&ca.func, false).unwrap(),
                        &b.declaration(&cb.func, false).unwrap(),
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
            let node = &owner.program.nodes[record.index as usize];
            let children: &[u32] = match &node.kind {
                Some(pb::node::Kind::Call(c)) => &c.args,
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Vec(v)),
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
                        pb::primitive_value::Value::Vec(values) => {
                            5u8.hash(&mut h);
                            values.items.len().hash(&mut h);
                            for i in &values.items {
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
        let n = &self.0.owner.as_ref().unwrap().program.nodes[self.0.index as usize];
        // Deliberately bounded, with no recursive child formatting.
        match &n.kind {
            Some(pb::node::Kind::Call(c)) => write!(f, "Call({:?}, {} args)", c.func, c.args.len()),
            Some(pb::node::Kind::Var(v)) => write!(f, "Var({v:?})"),
            Some(pb::node::Kind::Union(u)) => write!(f, "Union({} members)", u.members.len()),
            Some(pb::node::Kind::PrimitiveValue(v)) => write!(f, "Literal({:?})", v.value),
            _ => f.write_str("unsupported node"),
        }
    }
}

// The schema defines these codecs. This checks a literal invariant, not a
// callable signature or native numeric equivalence (f64 payloads are bits).
pub(super) fn validate_literal(
    sort: &SortRef,
    value: &pb::PrimitiveValue,
) -> Result<(), TypedError> {
    let kind = &sort.0.owner.as_ref().unwrap().program.sorts[sort.0.index as usize].kind;
    if let Some(pb::sort::Kind::Family(family)) = kind
        && family.args.is_empty()
        && matches!(
            (&*family.name, &value.value),
            ("i64", Some(pb::primitive_value::Value::I64(_)))
                | ("f64", Some(pb::primitive_value::Value::F64Bits(_)))
        )
    {
        Ok(())
    } else {
        Err(TypedError::Decode(
            "scalar payload does not match its sort".into(),
        ))
    }
}
