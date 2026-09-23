use super::{CallableRef, SortRef, decl::CallKind};
use egglog::ast::{Literal, Span};
use std::{
    borrow::Borrow,
    collections::HashSet,
    hash::{Hash, Hasher},
    sync::Arc,
};

/// An owned occurrence identity: keys keep the allocation alive as long as it can be compared.
#[derive(Debug)]
#[doc(hidden)]
pub struct Identity<T>(pub Arc<T>);
impl<T> Clone for Identity<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
impl<T> PartialEq for Identity<T> {
    fn eq(&self, rhs: &Self) -> bool {
        Arc::ptr_eq(&self.0, &rhs.0)
    }
}
impl<T> Eq for Identity<T> {}
impl<T> Hash for Identity<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.0).hash(state);
    }
}

/// An input whose owned nominal sort is known before converting another operand.
#[doc(hidden)]
pub trait ValueInput: Borrow<Self::Owned> {
    type Owned: EgglogValue;
}
impl<S: EgglogValue> ValueInput for &S {
    type Owned = S;
}

/// One exact-sort wrapper for authored expressions and frozen observations.
/// Rust equality compares authored syntax, or snapshot-relative frozen identity;
/// it never queries a live e-graph for equivalence.
pub trait EgglogValue:
    ValueInput<Owned = Self>
    + for<'a> From<&'a Self>
    + Clone
    + Eq
    + Hash
    + std::fmt::Debug
    + Send
    + Sync
    + 'static
{
    /// Describes this exact sort for explicit installation with [`super::EGraph::install`]
    /// or [`super::ProgramBuilder::install`]. Installing a sort does not install
    /// its unrelated constructors or materialize any values.
    fn sort_ref() -> SortRef;
    #[doc(hidden)]
    fn expression(&self) -> &Expr;
    #[doc(hidden)]
    fn from_expression(expr: Expr) -> Self;
    /// Returns the authored root call's name for diagnostics.
    /// Variables, captures, literals, and frozen observations return `None`.
    /// Use `get_args` for exact typed call inspection.
    fn call_name(&self) -> Option<&str> {
        match &self.expression().node().kind {
            NodeKind::Call(f, _) => Some(&f.name),
            _ => None,
        }
    }
}
/// A user-declared equality sort whose values may be unioned.
pub trait EqualitySort: EgglogValue {}

/// Query-local spelling or an allocation-owned fresh binder identity.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[doc(hidden)]
pub enum VariableKey {
    Named(Arc<str>),
    Fresh { scope: Identity<()>, slot: usize },
}

#[derive(Clone)]
#[doc(hidden)]
pub enum NodeKind {
    Literal(Literal),
    Call(CallableRef, Vec<Expr>),
    Variable(VariableKey),
    MergeVariable(&'static str),
    Capture { name: Arc<str>, initializer: Expr },
    Frozen(super::freeze::FrozenReference),
}

pub(crate) struct Node {
    pub sort: SortRef,
    pub kind: NodeKind,
    pub origin: Span,
    pub fingerprint: u64,
    pub shareable: bool,
}

#[derive(Clone)]
#[doc(hidden)]
pub struct Expr(Option<Arc<Node>>);
impl Expr {
    pub(crate) fn node(&self) -> &Node {
        self.0.as_deref().expect("expression is alive")
    }
    pub(crate) fn id(&self) -> usize {
        Arc::as_ptr(self.0.as_ref().unwrap()) as usize
    }
    #[doc(hidden)]
    pub fn new(sort: SortRef, kind: NodeKind, origin: Span) -> Self {
        let mut hash = std::collections::hash_map::DefaultHasher::new();
        sort.hash(&mut hash);
        std::mem::discriminant(&kind).hash(&mut hash);
        let shareable = match &kind {
            NodeKind::Literal(Literal::Float(v)) => {
                v.0.to_bits().hash(&mut hash);
                true
            }
            NodeKind::Literal(l) => {
                l.hash(&mut hash);
                true
            }
            NodeKind::Call(f, xs) => {
                f.hash(&mut hash);
                xs.hash(&mut hash);
                matches!(
                    f.kind,
                    CallKind::Constructor | CallKind::Primitive { total: true }
                ) && xs.iter().all(|x| x.node().shareable)
            }
            NodeKind::Variable(key) => {
                key.hash(&mut hash);
                true
            }
            NodeKind::MergeVariable(name) => {
                name.hash(&mut hash);
                true
            }
            NodeKind::Capture { name, initializer } => {
                name.hash(&mut hash);
                initializer.hash(&mut hash);
                true
            }
            NodeKind::Frozen(reference) => {
                reference.hash(&mut hash);
                false
            }
        };
        Self(Some(Arc::new(Node {
            sort,
            kind,
            origin,
            fingerprint: hash.finish(),
            shareable,
        })))
    }
    #[doc(hidden)]
    #[track_caller]
    pub fn call(sort: SortRef, callable: CallableRef, children: Vec<Self>) -> Self {
        Self::new(sort, NodeKind::Call(callable, children), super::origin())
    }
    pub(crate) fn children(&self) -> &[Self] {
        match &self.node().kind {
            NodeKind::Call(_, children) => children,
            NodeKind::Capture { initializer, .. } => std::slice::from_ref(initializer),
            _ => &[],
        }
    }
}
impl Drop for Expr {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        if let Some(arc) = self.0.take() {
            pending.push(arc);
        }
        while let Some(arc) = pending.pop() {
            if let Some(mut node) = Arc::into_inner(arc) {
                match &mut node.kind {
                    NodeKind::Call(_, children) => {
                        for child in children {
                            if let Some(arc) = child.0.take() {
                                pending.push(arc);
                            }
                        }
                    }
                    NodeKind::Capture { initializer, .. } => {
                        if let Some(arc) = initializer.0.take() {
                            pending.push(arc);
                        }
                    }
                    _ => {}
                }
            }
        }
    }
}
impl Hash for Expr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.node().fingerprint.hash(state);
    }
}
impl PartialEq for Expr {
    fn eq(&self, rhs: &Self) -> bool {
        let mut todo = vec![(self, rhs)];
        let mut seen = HashSet::new();
        while let Some((a, b)) = todo.pop() {
            if a.id() == b.id() || !seen.insert((a.id(), b.id())) {
                continue;
            }
            let (a, b) = (a.node(), b.node());
            if a.fingerprint != b.fingerprint || a.sort != b.sort {
                return false;
            }
            match (&a.kind, &b.kind) {
                (NodeKind::Literal(Literal::Float(a)), NodeKind::Literal(Literal::Float(b)))
                    if a.0.to_bits() == b.0.to_bits() => {}
                (NodeKind::Literal(Literal::Float(_)), NodeKind::Literal(Literal::Float(_))) => {
                    return false;
                }
                (NodeKind::Literal(a), NodeKind::Literal(b)) if a == b => {}
                (NodeKind::Variable(a), NodeKind::Variable(b)) if a == b => {}
                (NodeKind::MergeVariable(a), NodeKind::MergeVariable(b)) if a == b => {}
                (NodeKind::Frozen(a), NodeKind::Frozen(b)) if a == b => {}
                (NodeKind::Call(a, xs), NodeKind::Call(b, ys))
                    if a == b && xs.len() == ys.len() =>
                {
                    todo.extend(xs.iter().zip(ys))
                }
                (
                    NodeKind::Capture {
                        name: a,
                        initializer: x,
                    },
                    NodeKind::Capture {
                        name: b,
                        initializer: y,
                    },
                ) if a == b => todo.push((x, y)),
                _ => return false,
            }
        }
        true
    }
}
impl Eq for Expr {}
impl std::fmt::Debug for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut seen = HashSet::new();
        let mut todo = vec![self];
        let mut list = f.debug_list();
        while let Some(expr) = todo.pop() {
            if !seen.insert(expr.id()) {
                continue;
            }
            if seen.len() > 32 {
                list.entry(&"…");
                break;
            }
            let description = match &expr.node().kind {
                NodeKind::Literal(Literal::String(value)) => {
                    let prefix: String = value.chars().take(80).collect();
                    format!(
                        "{prefix:?}{}",
                        if value.chars().nth(80).is_some() {
                            "…"
                        } else {
                            ""
                        }
                    )
                }
                NodeKind::Literal(v) => format!("{v:?}"),
                NodeKind::Call(call, xs) => {
                    let mut references = xs
                        .iter()
                        .take(32)
                        .map(|x| format!("{:x}", x.id()))
                        .collect::<Vec<_>>();
                    if xs.len() > 32 {
                        references.push(format!("… {} more", xs.len() - 32));
                    }
                    format!("{} [{}]", call.name(), references.join(", "))
                }
                NodeKind::Variable(VariableKey::Named(name)) => format!("var {name:?}"),
                NodeKind::Variable(VariableKey::Fresh { scope, slot }) => {
                    format!("var {:p}/{slot}", Arc::as_ptr(&scope.0))
                }
                NodeKind::MergeVariable(v) => (*v).to_owned(),
                NodeKind::Capture { name, .. } => format!("capture {name}"),
                NodeKind::Frozen(reference) => format!("{reference:?}"),
            };
            list.entry(&(expr.id(), description));
            todo.extend(expr.children().iter().take(32).rev());
        }
        list.finish()
    }
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use super::decl::CallSyntax;
        enum Piece<'a> {
            Expr(&'a Expr, u8),
            Text(&'a str),
        }
        let mut pending = vec![Piece::Expr(self, 0)];
        while let Some(piece) = pending.pop() {
            match piece {
                Piece::Text(text) => f.write_str(text)?,
                Piece::Expr(expr, parent_precedence) => {
                    let precedence = match &expr.node().kind {
                        NodeKind::Call(call, _) => match &call.syntax {
                            Some(CallSyntax::Binary(op)) => match *op {
                                "|" => 1,
                                "^" => 2,
                                "&" => 3,
                                "<<" | ">>" => 4,
                                "+" | "-" => 5,
                                _ => 6,
                            },
                            Some(CallSyntax::Unary(_)) => 7,
                            Some(CallSyntax::Method(_)) => 8,
                            _ => 9,
                        },
                        _ => 9,
                    };
                    if precedence < parent_precedence {
                        f.write_str("(")?;
                        pending.push(Piece::Text(")"));
                    }
                    match &expr.node().kind {
                        NodeKind::Literal(value) => write!(f, "{value}")?,
                        NodeKind::Variable(VariableKey::Named(name)) => f.write_str(name)?,
                        NodeKind::Variable(VariableKey::Fresh { slot, .. }) => {
                            write!(f, "_{slot}")?
                        }
                        NodeKind::MergeVariable(name) => f.write_str(name)?,
                        NodeKind::Capture { name, .. } => f.write_str(name)?,
                        NodeKind::Frozen(reference) => write!(f, "{reference:?}")?,
                        NodeKind::Call(call, args) => match &call.syntax {
                            Some(CallSyntax::Binary(op)) if args.len() == 2 => {
                                pending.extend([
                                    Piece::Expr(&args[1], precedence + 1),
                                    Piece::Text(" "),
                                    Piece::Text(op),
                                    Piece::Text(" "),
                                    Piece::Expr(&args[0], precedence),
                                ]);
                            }
                            Some(CallSyntax::Unary(op)) if args.len() == 1 => {
                                pending.extend([
                                    Piece::Expr(&args[0], precedence + 1),
                                    Piece::Text(op),
                                ]);
                            }
                            syntax => {
                                let (name, start) = match syntax {
                                    Some(CallSyntax::Method(name)) if !args.is_empty() => {
                                        (*name, 1)
                                    }
                                    Some(CallSyntax::Function(name)) => (*name, 0),
                                    _ => (call.name(), 0),
                                };
                                pending.push(Piece::Text(")"));
                                for index in (start..args.len()).rev() {
                                    pending.push(Piece::Expr(&args[index], 0));
                                    if index > start {
                                        pending.push(Piece::Text(", "));
                                    }
                                }
                                pending.extend([Piece::Text("("), Piece::Text(name)]);
                                if start == 1 {
                                    pending.extend([Piece::Text("."), Piece::Expr(&args[0], 8)]);
                                }
                            }
                        },
                    }
                }
            }
        }
        Ok(())
    }
}

#[track_caller]
/// Names an explicit top-level capture while preserving the initializer's expression type.
/// Registration evaluates it once per active destination scope. Rust binding alone does not.
pub fn let_<I: ValueInput>(name: impl Into<Arc<str>>, initializer: I) -> I::Owned {
    I::Owned::from_expression(Expr::new(
        I::Owned::sort_ref(),
        NodeKind::Capture {
            name: name.into(),
            initializer: initializer.borrow().expression().clone(),
        },
        super::origin(),
    ))
}
#[track_caller]
/// Authors a named query variable of exact sort `S`.
///
/// The exact UTF-8 name identifies one binder within each rule, check, or until
/// query. Reusing a name with different sorts in one query is a submission error.
/// Variables can be retained and reused, but cannot be evaluated as exact values.
pub fn var<S: EgglogValue>(name: impl Into<Arc<str>>) -> S {
    S::from_expression(Expr::new(
        S::sort_ref(),
        NodeKind::Variable(VariableKey::Named(name.into())),
        super::origin(),
    ))
}

/// Constructs one exact-sort input of a fresh callback scope.
#[doc(hidden)]
#[track_caller]
pub fn variable<S: EgglogValue>(scope: Identity<()>, slot: usize) -> S {
    S::from_expression(Expr::new(
        S::sort_ref(),
        NodeKind::Variable(VariableKey::Fresh { scope, slot }),
        super::origin(),
    ))
}
