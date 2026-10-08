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
        let Some(pb::declaration::Kind::Constructor(c)) =
            &owner.program.declarations[callable.0.index as usize].kind
        else {
            unreachable!()
        };
        assert_eq!(c.inputs.len(), arguments.len(), "constructor arity");
        for (arg, expected) in arguments.iter().zip(&c.inputs) {
            let node = &arg.0.owner.as_ref().unwrap().program.nodes[arg.0.index as usize];
            assert!(
                SortRef(arg.0.resolve(Arena::Sort, node.sort_id).unwrap())
                    == SortRef(callable.0.resolve(Arena::Sort, expected.sort).unwrap()),
                "constructor input sort"
            );
        }
        let program = pb::Program {
            ir_version: 1,
            nodes: vec![pb::Node {
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: c.name.clone(),
                    args: (0..arguments.len() as u32).collect(),
                })),
                ..Default::default()
            }],
            ..Default::default()
        };
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Node as usize] = arguments.into_iter().map(|a| Slot::External(a.0)).collect();
        slots[Arena::Sort as usize] = vec![Slot::External(
            callable.0.resolve(Arena::Sort, c.output).unwrap(),
        )];
        Self(publish(program, slots, vec![callable.0.clone()], Arena::Node, 0).unwrap())
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
        if !super::decl::same_callable(
            &self.0.declaration(&actual.func, false)?,
            &pattern.0.declaration(&call.func, false)?,
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
            let na = &oa.program.nodes[a.index as usize];
            let nb = &ob.program.nodes[b.index as usize];
            if SortRef(a.resolve(Arena::Sort, na.sort_id).unwrap())
                != SortRef(b.resolve(Arena::Sort, nb.sort_id).unwrap())
            {
                return false;
            }
            match (&na.kind, &nb.kind) {
                (Some(pb::node::Kind::Var(a)), Some(pb::node::Kind::Var(b))) if a == b => {}
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
            if !finish && let Some(pb::node::Kind::Call(c)) = &node.kind {
                pending.push((record.clone(), true));
                for i in c.args.iter().rev() {
                    pending.push((record.resolve(Arena::Node, *i).unwrap(), false));
                }
                continue;
            }
            let mut h = DefaultHasher::new();
            let sort = record.resolve(Arena::Sort, node.sort_id).unwrap();
            let Some(pb::sort::Kind::Eq(name)) =
                &sort.owner.as_ref().unwrap().program.sorts[sort.index as usize].kind
            else {
                unreachable!()
            };
            name.hash(&mut h);
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
            _ => f.write_str("unsupported node"),
        }
    }
}
