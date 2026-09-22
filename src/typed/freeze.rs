//! Exact owned observations of native rows and values, without tree extraction.
use super::{
    CallableRef, EGraph, EgglogValue, SortRef, TypedError,
    decl::{CallKind, SortKind},
    expr::{Expr, Identity, NodeKind},
    lower::Installed,
    selector::{CallRoot, SelectCall, SelectedArgs, Selection},
};
use egglog::{ArcSort, Read, Value, ast::FunctionSubtype, sort};
use std::{
    collections::HashMap,
    hash::{Hash, Hasher},
    ptr,
    sync::Arc,
};

/// Exact-observation limits. Exceeding a limit never returns a partial graph.
/// Native readers may allocate an individual payload before its size is checked;
/// declaration signatures and sort metadata are not charged as value/row entries.
/// These counts are not hard allocator or byte limits.
#[derive(Clone, Copy, Debug)]
pub struct FreezeLimits {
    /// Maximum entries in each value/row/table/capture/root collection.
    pub max_nodes: usize,
    /// Maximum copied row and container references, including duplicates.
    pub max_edges: usize,
}
impl Default for FreezeLimits {
    fn default() -> Self {
        Self {
            max_nodes: 100_000,
            max_edges: 1_000_000,
        }
    }
}

/// Exact copied native scalars, never decoded from display text.
/// Floating-point equality compares stored bits. Native interning may already
/// have discarded distinctions before observation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum FrozenScalar {
    /// The unit value.
    Unit,
    /// A boolean value, including false.
    Bool(bool),
    /// A signed integer.
    I64(i64),
    /// Stored IEEE-754 bits; decode with `f64::from_bits`.
    F64(u64),
    /// Exact UTF-8 contents, without display quoting.
    String(String),
    /// An arbitrary-precision integer.
    BigInt(num::BigInt),
    /// An arbitrary-precision rational.
    BigRat(num::BigRational),
    /// An experimental fixed-width rational.
    Rational(num::rational::Rational64),
}
#[derive(Debug)]
enum ValueData {
    Pending,
    Class(Vec<usize>),
    Scalar(FrozenScalar),
    Container(Vec<usize>),
}
#[derive(Debug)]
struct StoredValue {
    sort: SortRef,
    data: ValueData,
}
#[derive(Debug)]
struct Row {
    table: usize,
    args: Vec<usize>,
    output: usize,
    subsumed: bool,
}
#[derive(Debug)]
struct Table {
    callable: CallableRef,
    inputs: Vec<SortRef>,
    output: SortRef,
    rows: Vec<usize>,
}
#[derive(Debug)]
struct Capture {
    initializer: Expr,
    value: usize,
}

/// An immutable exact observation, independent of the source EGraph and roots.
/// Public rows, scalar/container fields, equality cycles, and typed captures are
/// copied once. Hidden tables and executor state are not public data. This is
/// not a checkpoint and observing never evaluates or extracts an expression.
#[derive(Debug)]
pub(crate) struct SnapshotData {
    values: Vec<StoredValue>,
    rows: Vec<Row>,
    tables: Vec<Table>,
    classes: Vec<usize>,
    captures: HashMap<Arc<str>, Capture>,
}
#[derive(Clone, Debug)]
/// An owned immutable snapshot; clones retain the same snapshot identity.
pub struct FrozenEGraph {
    data: Arc<SnapshotData>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum FrozenTarget {
    Value(usize),
    ConstructorNode(usize),
}
#[derive(Clone, PartialEq, Eq, Hash)]
#[doc(hidden)]
pub struct FrozenReference {
    snapshot: Identity<SnapshotData>,
    target: FrozenTarget,
}
impl std::fmt::Debug for FrozenReference {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "frozen@{:p}/{:?}",
            Arc::as_ptr(&self.snapshot.0),
            self.target
        )
    }
}
impl FrozenReference {
    fn expression(snapshot: &Arc<SnapshotData>, target: FrozenTarget) -> Expr {
        let index = match target {
            FrozenTarget::Value(i) => i,
            FrozenTarget::ConstructorNode(i) => snapshot.rows[i].output,
        };
        Expr::new(
            snapshot.values[index].sort.clone(),
            NodeKind::Frozen(Self {
                snapshot: Identity(snapshot.clone()),
                target,
            }),
            super::origin(),
        )
    }
    pub(crate) fn project(&self, selection: &Selection) -> Result<Option<Vec<Expr>>, TypedError> {
        let FrozenTarget::ConstructorNode(index) = self.target else {
            return Ok(None);
        };
        let row = &self.snapshot.0.rows[index];
        let table = &self.snapshot.0.tables[row.table];
        if !selection.validate(&table.callable, &table.inputs, &table.output)? {
            return Ok(None);
        }
        Ok(Some(
            row.args
                .iter()
                .map(|&i| Self::expression(&self.snapshot.0, FrozenTarget::Value(i)))
                .collect(),
        ))
    }
    pub(crate) fn scalar(&self) -> Option<&FrozenScalar> {
        let FrozenTarget::Value(index) = self.target else {
            return None;
        };
        match &self.snapshot.0.values[index].data {
            ValueData::Scalar(value) => Some(value),
            _ => None,
        }
    }
    pub(crate) fn children(&self) -> Result<Vec<Expr>, super::DecodeError> {
        let FrozenTarget::Value(index) = self.target else {
            return Err(super::DecodeError(
                "expected a frozen container value".into(),
            ));
        };
        let ValueData::Container(children) = &self.snapshot.0.values[index].data else {
            return Err(super::DecodeError(
                "expected a frozen container value".into(),
            ));
        };
        Ok(children
            .iter()
            .map(|&i| Self::expression(&self.snapshot.0, FrozenTarget::Value(i)))
            .collect())
    }
}

/// Exact typed arguments and output of one observed row.
#[derive(Clone, Debug)]
pub struct TableRow<A, O> {
    /// Ordered exact-sort input values, retaining snapshot identity.
    pub args: A,
    /// Exact output value, never a constructor producer.
    pub output: O,
    /// Native visibility flag for this row.
    pub subsumed: bool,
}
/// One selected table with its complete signature, including when empty.
#[derive(Clone, Debug)]
pub struct TableSnapshot<A, O> {
    /// The selected table's name for diagnostics.
    pub name: Arc<str>,
    /// All stored rows, including subsumed rows, in native iteration order.
    pub rows: Vec<TableRow<A, O>>,
}
impl<A, O> IntoIterator for TableSnapshot<A, O> {
    type Item = TableRow<A, O>;
    type IntoIter = std::vec::IntoIter<Self::Item>;
    fn into_iter(self) -> Self::IntoIter {
        self.rows.into_iter()
    }
}
impl<'a, A, O> IntoIterator for &'a TableSnapshot<A, O> {
    type Item = &'a TableRow<A, O>;
    type IntoIter = std::slice::Iter<'a, TableRow<A, O>>;
    fn into_iter(self) -> Self::IntoIter {
        self.rows.iter()
    }
}
/// A borrowed value identified within one immutable snapshot.
#[derive(Clone, Copy)]
pub struct FrozenValue<'f> {
    graph: &'f SnapshotData,
    index: usize,
}
/// A borrowed equality class, including classes with no remaining constructor.
#[derive(Clone, Copy)]
pub struct FrozenEClass<'f> {
    graph: &'f SnapshotData,
    index: usize,
}
/// A constructor alternative belonging to an equality class.
#[derive(Clone, Copy)]
pub struct FrozenENode<'f> {
    graph: &'f SnapshotData,
    index: usize,
}
/// A public constructor, relation, or function table, possibly empty.
#[derive(Clone, Copy)]
pub struct FrozenTable<'f> {
    graph: &'f SnapshotData,
    index: usize,
}
/// An exact row; function outputs are not constructor alternatives.
#[derive(Clone, Copy)]
pub struct FrozenRow<'f> {
    graph: &'f SnapshotData,
    index: usize,
}

/// Ordered fields, retaining repeated references.
#[derive(Clone)]
pub struct FrozenValues<'f> {
    graph: &'f SnapshotData,
    indices: std::slice::Iter<'f, usize>,
}
impl<'f> Iterator for FrozenValues<'f> {
    type Item = FrozenValue<'f>;
    fn next(&mut self) -> Option<Self::Item> {
        self.indices.next().map(|&index| FrozenValue {
            graph: self.graph,
            index,
        })
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.indices.size_hint()
    }
}
impl DoubleEndedIterator for FrozenValues<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.indices.next_back().map(|&index| FrozenValue {
            graph: self.graph,
            index,
        })
    }
}
impl ExactSizeIterator for FrozenValues<'_> {}
/// Ordered map entries whose keys and values remain paired.
#[derive(Clone)]
pub struct FrozenEntries<'f> {
    graph: &'f SnapshotData,
    indices: std::slice::ChunksExact<'f, usize>,
}
impl<'f> Iterator for FrozenEntries<'f> {
    type Item = (FrozenValue<'f>, FrozenValue<'f>);
    fn next(&mut self) -> Option<Self::Item> {
        self.indices.next().map(|pair| {
            (
                FrozenValue {
                    graph: self.graph,
                    index: pair[0],
                },
                FrozenValue {
                    graph: self.graph,
                    index: pair[1],
                },
            )
        })
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.indices.size_hint()
    }
}
impl ExactSizeIterator for FrozenEntries<'_> {}
/// Immediate observed shape; containers retain the exact applied sort on their handle.
pub enum FrozenValueView<'f> {
    /// A class reference, never an expanded representative.
    EClass(FrozenEClass<'f>),
    /// Exact scalar contents.
    Scalar(&'f FrozenScalar),
    /// Ordered vector members.
    Vec(FrozenValues<'f>),
    /// Native canonical set order.
    Set(FrozenValues<'f>),
    /// Native canonical multiset order and multiplicity.
    MultiSet(FrozenValues<'f>),
    /// Native canonical key order with paired values.
    Map(FrozenEntries<'f>),
    /// First and second fields.
    Pair(FrozenValue<'f>, FrozenValue<'f>),
}

#[derive(Clone, Copy)]
enum Codec {
    Equality,
    Unit,
    Bool,
    I64,
    F64,
    String,
    BigInt,
    BigRat,
    Rational,
    Vec,
    Set,
    MultiSet,
    Map,
    Pair,
}
fn codec(sort: &ArcSort) -> Result<Codec, TypedError> {
    if sort.is_eq_sort() {
        return Ok(Codec::Equality);
    }
    let value_type = sort.value_type();
    macro_rules! recognize { ($($native:ty => $kind:ident),+ $(,)?) => { $( if value_type == Some(std::any::TypeId::of::<$native>()) { return Ok(Codec::$kind); } )+ }; }
    recognize!(() => Unit, bool => Bool, i64 => I64, sort::F => F64, sort::S => String,
        sort::Z => BigInt, sort::Q => BigRat, crate::R => Rational,
        sort::VecContainer => Vec, sort::SetContainer => Set, sort::MultiSetContainer => MultiSet,
        sort::MapContainer => Map, sort::PairContainer => Pair);
    Err(TypedError::Decode(format!(
        "no exact frozen codec for native sort {}",
        sort.name()
    )))
}
struct Builder<'a> {
    core: &'a egglog::EGraph,
    graph: SnapshotData,
    limits: FreezeLimits,
    edges: usize,
    sorts: HashMap<String, SortRef>,
    values: HashMap<(SortRef, Value), usize>,
    pending: Vec<(usize, ArcSort, Value)>,
    unit: Option<usize>,
}
impl Builder<'_> {
    fn sort(&mut self, native: &ArcSort) -> Result<SortRef, TypedError> {
        codec(native)?;
        if let Some(sort) = self.sorts.get(native.name()) {
            return Ok(sort.clone());
        }
        let mut pending = vec![(native.clone(), false)];
        while let Some((native, done)) = pending.pop() {
            if self.sorts.contains_key(native.name()) {
                continue;
            }
            let kind = codec(&native)?;
            let family = match kind {
                Codec::Vec => Some("Vec"),
                Codec::Set => Some("Set"),
                Codec::MultiSet => Some("MultiSet"),
                Codec::Map => Some("Map"),
                Codec::Pair => Some("Pair"),
                _ => None,
            };
            let shape = if let Some(family) = family {
                let arguments = native.inner_sorts();
                if !done {
                    pending.push((native.clone(), true));
                    pending.extend(arguments.into_iter().rev().map(|s| (s, false)));
                    continue;
                }
                SortKind::Container {
                    family,
                    arguments: arguments
                        .iter()
                        .map(|s| self.sorts[s.name()].clone())
                        .collect(),
                }
            } else if matches!(kind, Codec::Equality) {
                SortKind::Equality
            } else {
                SortKind::Builtin
            };
            self.sorts.insert(
                native.name().into(),
                SortRef {
                    name: native.name().into(),
                    kind: shape,
                },
            );
        }
        Ok(self.sorts[native.name()].clone())
    }
    fn edges(&mut self, count: usize) -> Result<(), TypedError> {
        self.edges = self
            .edges
            .checked_add(count)
            .filter(|n| *n <= self.limits.max_edges)
            .ok_or_else(|| TypedError::LoweringLimit("freeze edge limit exceeded".into()))?;
        Ok(())
    }
    fn push_value(&mut self, sort: SortRef, data: ValueData) -> Result<usize, TypedError> {
        if self.graph.values.len() >= self.limits.max_nodes {
            return Err(TypedError::LoweringLimit(
                "freeze value limit exceeded".into(),
            ));
        }
        let index = self.graph.values.len();
        if matches!(data, ValueData::Class(_)) {
            self.graph.classes.push(index);
        }
        self.graph.values.push(StoredValue { sort, data });
        Ok(index)
    }
    fn intern(&mut self, sort: &ArcSort, value: Value) -> Result<usize, TypedError> {
        let exact = self.sort(sort)?;
        if matches!(codec(sort)?, Codec::Unit) && exact == SortRef::builtin("Unit") {
            return self.unit();
        }
        // Canonical native identity is a construction-only key, never exposed
        // to consumers. Native alias sorts remain distinct, including Unit aliases.
        let key = (exact.clone(), self.core.canonical_value(sort, value));
        if let Some(&index) = self.values.get(&key) {
            return Ok(index);
        }
        let data = if sort.is_eq_sort() {
            ValueData::Class(Vec::new())
        } else {
            ValueData::Pending
        };
        let index = self.push_value(exact, data)?;
        self.values.insert(key, index);
        if !sort.is_eq_sort() {
            self.pending.push((index, sort.clone(), value));
        }
        Ok(index)
    }
    fn unit(&mut self) -> Result<usize, TypedError> {
        if let Some(index) = self.unit {
            return Ok(index);
        }
        let index = self.push_value(
            SortRef::builtin("Unit"),
            ValueData::Scalar(FrozenScalar::Unit),
        )?;
        self.unit = Some(index);
        Ok(index)
    }
    fn decode_pending(&mut self) -> Result<(), TypedError> {
        while let Some((index, sort, value)) = self.pending.pop() {
            let kind = codec(&sort)?;
            let scalar = match kind {
                Codec::Unit => Some(FrozenScalar::Unit),
                Codec::Bool => Some(FrozenScalar::Bool(self.core.value_to_base(value))),
                Codec::I64 => Some(FrozenScalar::I64(self.core.value_to_base(value))),
                Codec::F64 => Some(FrozenScalar::F64(
                    self.core.value_to_base::<sort::F>(value).0.0.to_bits(),
                )),
                Codec::String => Some(FrozenScalar::String(
                    self.core.value_to_base::<sort::S>(value).0,
                )),
                Codec::BigInt => Some(FrozenScalar::BigInt(
                    self.core.value_to_base::<sort::Z>(value).0,
                )),
                Codec::BigRat => Some(FrozenScalar::BigRat(
                    self.core.value_to_base::<sort::Q>(value).0,
                )),
                Codec::Rational => Some(FrozenScalar::Rational(
                    self.core.value_to_base::<crate::R>(value).0,
                )),
                _ => None,
            };
            self.graph.values[index].data = if let Some(scalar) = scalar {
                ValueData::Scalar(scalar)
            } else {
                let members = self.core.container_inner_values(&sort, value);
                self.edges(members.len())?;
                if matches!(kind, Codec::Pair) && members.len() != 2
                    || matches!(kind, Codec::Map) && !members.len().is_multiple_of(2)
                {
                    return Err(TypedError::Decode(format!(
                        "malformed {} container fields",
                        sort.name()
                    )));
                }
                ValueData::Container(
                    members
                        .iter()
                        .map(|(s, v)| self.intern(s, *v))
                        .collect::<Result<_, _>>()?,
                )
            };
        }
        Ok(())
    }
    fn row(
        &mut self,
        table: usize,
        signature: &egglog::FuncType,
        args: &[Value],
        output: Value,
        subsumed: bool,
    ) -> Result<(), TypedError> {
        if args.len() != signature.input.len() {
            return Err(TypedError::Decode("native row arity mismatch".into()));
        }
        if self.graph.rows.len() >= self.limits.max_nodes {
            return Err(TypedError::LoweringLimit(
                "freeze row limit exceeded".into(),
            ));
        }
        self.edges(args.len() + 1)?;
        let args = signature
            .input
            .iter()
            .zip(args)
            .map(|(s, v)| self.intern(s, *v))
            .collect::<Result<_, _>>()?;
        let output = if signature.is_relation {
            self.unit()?
        } else {
            self.intern(&signature.output, output)?
        };
        let index = self.graph.rows.len();
        if self.graph.tables[table].callable.kind == CallKind::Constructor {
            let ValueData::Class(nodes) = &mut self.graph.values[output].data else {
                return Err(TypedError::Decode(
                    "constructor output is not an equality class".into(),
                ));
            };
            nodes.push(index);
        }
        self.graph.rows.push(Row {
            table,
            args,
            output,
            subsumed,
        });
        self.graph.tables[table].rows.push(index);
        Ok(())
    }
}

fn build(
    core: &egglog::EGraph,
    state: Option<&Installed>,
    roots: &[(ArcSort, Value)],
    limits: FreezeLimits,
) -> Result<(FrozenEGraph, Vec<usize>), TypedError> {
    if core.is_term_encoding_enabled() {
        return Err(TypedError::Invalid(
            "exact frozen observation does not support proof/term encoding".into(),
        ));
    }
    if state.is_some_and(|s| s.poisoned) {
        return Err(TypedError::NeedsRestore);
    }
    if roots.len() > limits.max_nodes || state.is_some_and(|s| s.captures.len() > limits.max_nodes)
    {
        return Err(TypedError::LoweringLimit(
            "freeze capture/root limit exceeded".into(),
        ));
    }
    let mut builder = Builder {
        core,
        limits,
        edges: 0,
        unit: None,
        values: HashMap::new(),
        pending: Vec::new(),
        sorts: state
            .into_iter()
            .flat_map(|s| {
                s.sorts
                    .iter()
                    .map(|(name, sort)| (name.to_string(), sort.clone()))
            })
            .collect(),
        graph: SnapshotData {
            values: Vec::new(),
            rows: Vec::new(),
            tables: Vec::new(),
            classes: Vec::new(),
            captures: HashMap::new(),
        },
    };
    for (name, function) in core.functions_iter() {
        if function.is_hidden() || function.is_let_binding() {
            continue;
        }
        if builder.graph.tables.len() >= limits.max_nodes {
            return Err(TypedError::LoweringLimit(
                "freeze table limit exceeded".into(),
            ));
        }
        let signature = function.func_type();
        let kind = if signature.is_relation {
            CallKind::Relation
        } else if signature.subtype == FunctionSubtype::Constructor {
            CallKind::Constructor
        } else {
            CallKind::Function
        };
        let callable = state
            .and_then(|s| s.declarations.get(name.as_str()))
            .map(|d| d.callable.clone())
            .unwrap_or_else(|| CallableRef {
                name: name.as_str().into(),
                kind,
                source: None,
                syntax: None,
            });
        let inputs = signature
            .input
            .iter()
            .map(|s| builder.sort(s))
            .collect::<Result<_, _>>()?;
        let output = if signature.is_relation {
            SortRef::builtin("Unit")
        } else {
            builder.sort(&signature.output)?
        };
        let table = builder.graph.tables.len();
        builder.graph.tables.push(Table {
            callable,
            inputs,
            output,
            rows: Vec::new(),
        });
        let mut result = Ok(());
        let native = if signature.subtype == FunctionSubtype::Constructor {
            core.constructor_enodes_while(name, |row| {
                result = builder.row(table, signature, row.children, row.eclass, row.subsumed);
                result.is_ok()
            })
        } else {
            core.function_entries_while(name, |row| {
                result = builder.row(table, signature, row.inputs, row.output, row.subsumed);
                result.is_ok()
            })
        };
        native
            .map_err(|error| TypedError::Decode(format!("cannot freeze table {name}: {error}")))?;
        result?;
    }
    if let Some(state) = state {
        core.read(|reader| -> Result<(), TypedError> {
            for (name, (initializer, backend)) in &state.captures {
                let function = core.get_function(backend).ok_or_else(|| {
                    TypedError::Decode(format!("installed capture {name} has no table"))
                })?;
                let value = reader
                    .lookup(backend, egglog::RawValues(vec![]))
                    .map_err(|error| {
                        TypedError::Decode(format!("cannot read capture {name}: {error}"))
                    })?
                    .ok_or_else(|| {
                        TypedError::Decode(format!("installed capture {name} has no value"))
                    })?;
                builder.edges(1)?;
                let value = builder.intern(&function.func_type().output, value)?;
                builder.graph.captures.insert(
                    name.clone(),
                    Capture {
                        initializer: initializer.clone(),
                        value,
                    },
                );
            }
            Ok(())
        })?;
    }
    let roots = roots
        .iter()
        .map(|(sort, value)| builder.intern(sort, *value))
        .collect::<Result<Vec<_>, _>>()?;
    builder.decode_pending()?;
    Ok((
        FrozenEGraph {
            data: Arc::new(builder.graph),
        },
        roots,
    ))
}
impl EGraph {
    /// Copy exact public rows and captures without roots, execution, or extraction.
    pub fn freeze(&self) -> Result<FrozenEGraph, TypedError> {
        build(
            &self.core,
            self.core.extension_state::<Installed>(),
            &[],
            self.options.freeze_limits,
        )
        .map(|(graph, _)| graph)
    }
}
/// Native execution integration, outside the typed authoring prelude.
pub mod native {
    use super::*;
    /// Observe native roots while their exact snapshot remains in scope.
    ///
    /// Roots must be resolved values of the supplied EGraph and their stated
    /// sorts. Only the observation callback runs, not Egglog expressions. This
    /// uses the same builder as typed `freeze`; raw root indices stay private and
    /// the snapshot remembers no root list.
    pub fn with_frozen<R>(
        core: &egglog::EGraph,
        roots: &[(ArcSort, Value)],
        limits: FreezeLimits,
        observe: impl FnOnce(&FrozenEGraph, &[FrozenValue<'_>]) -> Result<R, TypedError>,
    ) -> Result<R, TypedError> {
        let (graph, indices) = build(core, core.extension_state::<Installed>(), roots, limits)?;
        let roots: Vec<_> = indices
            .into_iter()
            .map(|index| FrozenValue {
                graph: &graph.data,
                index,
            })
            .collect();
        observe(&graph, &roots)
    }
}
impl FrozenEGraph {
    /// Resolve an installed typed capture of any supported exact sort.
    /// Names, sorts, and structural initializers must match. Ordinary expressions
    /// are not accepted and the supplied initializer never executes.
    pub fn lookup<S: EgglogValue>(&self, expression: &S) -> Result<S, TypedError> {
        let unresolved = |reason: &str| TypedError::UnresolvedRoot {
            index: None,
            reason: reason.into(),
        };
        let NodeKind::Capture { name, initializer } = &expression.expression().node().kind else {
            return Err(unresolved(
                "frozen lookup accepts only explicit let_ captures",
            ));
        };
        let capture = self
            .data
            .captures
            .get(name)
            .ok_or_else(|| unresolved("capture was not installed in this snapshot"))?;
        if capture.initializer != *initializer
            || self.data.values[capture.value].sort != S::sort_ref()
        {
            return Err(unresolved(
                "capture sort or initializer does not match this snapshot",
            ));
        }
        Ok(S::from_expression(FrozenReference::expression(
            &self.data,
            FrozenTarget::Value(capture.value),
        )))
    }
    /// Check exact nominal sort and snapshot ownership at the heterogeneous boundary.
    pub fn as_view<S: EgglogValue>(&self, value: &S) -> Result<FrozenValue<'_>, TypedError> {
        let NodeKind::Frozen(reference) = &value.expression().node().kind else {
            return Err(TypedError::Invalid("expected a frozen reference".into()));
        };
        if !Arc::ptr_eq(&self.data, &reference.snapshot.0) {
            return Err(TypedError::Invalid(
                "reference belongs to a different frozen snapshot".into(),
            ));
        }
        let index = match reference.target {
            FrozenTarget::Value(i) => i,
            FrozenTarget::ConstructorNode(i) => self.data.rows[i].output,
        };
        if self.data.values[index].sort != S::sort_ref() {
            return Err(TypedError::Invalid(
                "frozen reference has an incompatible exact sort".into(),
            ));
        }
        Ok(FrozenValue {
            graph: &self.data,
            index,
        })
    }
    /// Borrow a heterogeneous constructor alternative as an owned exact-sort value.
    /// The node must belong to this snapshot and have exactly `S` as its output
    /// sort. The constructor identity and declaration metadata are retained, so
    /// typed selectors still validate the complete declaration before decoding.
    pub fn typed_node<S: super::EqualitySort>(
        &self,
        node: FrozenENode<'_>,
    ) -> Result<S, TypedError> {
        if !ptr::eq(self.data.as_ref(), node.graph) {
            return Err(TypedError::Invalid(
                "constructor belongs to a different frozen snapshot".into(),
            ));
        }
        let row = &self.data.rows[node.index];
        if self.data.values[row.output].sort != S::sort_ref() {
            return Err(TypedError::Invalid(
                "constructor has an incompatible exact output sort".into(),
            ));
        }
        Ok(S::from_expression(FrozenReference::expression(
            &self.data,
            FrozenTarget::ConstructorNode(node.index),
        )))
    }

    /// All constructor alternatives, including subsumed rows, as the same sort.
    pub fn nodes<S: super::EqualitySort>(
        &self,
        value: &S,
    ) -> Result<impl ExactSizeIterator<Item = S> + '_, TypedError> {
        if !matches!(
            &value.expression().node().kind,
            NodeKind::Frozen(FrozenReference {
                target: FrozenTarget::Value(_),
                ..
            })
        ) {
            return Err(TypedError::Invalid(
                "nodes requires a frozen equality class value".into(),
            ));
        }
        let value = self.as_view(value)?;
        let ValueData::Class(nodes) = &self.data.values[value.index].data else {
            return Err(TypedError::Invalid("expected an equality class".into()));
        };
        Ok(nodes.iter().map(|&i| {
            S::from_expression(FrozenReference::expression(
                &self.data,
                FrozenTarget::ConstructorNode(i),
            ))
        }))
    }
    /// Whether one selected constructor alternative is subsumed.
    pub fn is_subsumed<S: super::EqualitySort>(&self, node: &S) -> Result<bool, TypedError> {
        self.as_view(node)?;
        let NodeKind::Frozen(reference) = &node.expression().node().kind else {
            unreachable!()
        };
        let FrozenTarget::ConstructorNode(index) = reference.target else {
            return Err(TypedError::Invalid(
                "subsumption requires a selected constructor node".into(),
            ));
        };
        Ok(self.data.rows[index].subsumed)
    }
    /// Observe every row of one exactly selected installed table, without execution.
    pub fn table<F, A>(
        &self,
        selector: F,
    ) -> Result<TableSnapshot<A, <F::Root as CallRoot>::Output>, TypedError>
    where
        F: SelectCall<A>,
        A: SelectedArgs,
    {
        let selection = selector.select()?;
        if matches!(selection.callable.kind, CallKind::Primitive { .. }) {
            return Err(TypedError::Invalid(
                "primitive calls do not select stored tables".into(),
            ));
        }
        let table = self
            .data
            .tables
            .iter()
            .find(|t| t.callable.name == selection.callable.name)
            .ok_or_else(|| TypedError::UnresolvedRoot {
                index: None,
                reason: "selected table is absent from this snapshot".into(),
            })?;
        if !selection.validate(&table.callable, &table.inputs, &table.output)? {
            return Err(TypedError::Invalid(
                "selected table has an incompatible callable kind".into(),
            ));
        }
        let rows = table
            .rows
            .iter()
            .map(|&i| {
                let row = &self.data.rows[i];
                let args = row
                    .args
                    .iter()
                    .map(|&i| FrozenReference::expression(&self.data, FrozenTarget::Value(i)))
                    .collect::<Vec<_>>();
                Ok(TableRow {
                    args: A::decode(&args)?,
                    output: <F::Root as CallRoot>::Output::from_expression(
                        FrozenReference::expression(&self.data, FrozenTarget::Value(row.output)),
                    ),
                    subsumed: row.subsumed,
                })
            })
            .collect::<Result<_, TypedError>>()?;
        Ok(TableSnapshot {
            name: table.callable.name.clone(),
            rows,
        })
    }
    /// All equality classes, including those outside caller-selected roots.
    pub fn eclasses(&self) -> impl ExactSizeIterator<Item = FrozenEClass<'_>> {
        self.data.classes.iter().map(|&index| FrozenEClass {
            graph: &self.data,
            index,
        })
    }
    /// Public tables in native declaration order, including empty tables.
    pub fn tables(&self) -> impl ExactSizeIterator<Item = FrozenTable<'_>> {
        (0..self.data.tables.len()).map(|index| FrozenTable {
            graph: &self.data,
            index,
        })
    }
    /// Whether a value belongs to this snapshot rather than another freeze.
    pub fn contains(&self, value: FrozenValue<'_>) -> bool {
        ptr::eq(self.data.as_ref(), value.graph)
    }
}
impl<'f> FrozenValue<'f> {
    /// Exact nominal sort, including applied container arguments.
    pub fn sort(self) -> SortRef {
        self.graph.values[self.index].sort.clone()
    }
    /// Inspect immediate fields without choosing equality representatives.
    pub fn view(self) -> FrozenValueView<'f> {
        let value = &self.graph.values[self.index];
        match &value.data {
            ValueData::Class(_) => FrozenValueView::EClass(FrozenEClass {
                graph: self.graph,
                index: self.index,
            }),
            ValueData::Scalar(scalar) => FrozenValueView::Scalar(scalar),
            ValueData::Container(children) => {
                let SortKind::Container { family, .. } = value.sort.kind else {
                    unreachable!()
                };
                match family {
                    "Map" => FrozenValueView::Map(FrozenEntries {
                        graph: self.graph,
                        indices: children.chunks_exact(2),
                    }),
                    "Pair" => FrozenValueView::Pair(
                        FrozenValue {
                            graph: self.graph,
                            index: children[0],
                        },
                        FrozenValue {
                            graph: self.graph,
                            index: children[1],
                        },
                    ),
                    family => {
                        let values = FrozenValues {
                            graph: self.graph,
                            indices: children.iter(),
                        };
                        match family {
                            "Vec" => FrozenValueView::Vec(values),
                            "Set" => FrozenValueView::Set(values),
                            "MultiSet" => FrozenValueView::MultiSet(values),
                            _ => unreachable!(),
                        }
                    }
                }
            }
            ValueData::Pending => unreachable!("complete snapshots have no pending values"),
        }
    }
}
impl<'f> FrozenEClass<'f> {
    /// Exact nominal equality sort.
    pub fn sort(self) -> SortRef {
        self.graph.values[self.index].sort.clone()
    }
    /// The same snapshot-relative identity as a general observed value.
    pub fn value(self) -> FrozenValue<'f> {
        FrozenValue {
            graph: self.graph,
            index: self.index,
        }
    }
    /// Constructor alternatives with native order and subsumption flags.
    pub fn nodes(self) -> impl ExactSizeIterator<Item = FrozenENode<'f>> {
        let ValueData::Class(nodes) = &self.graph.values[self.index].data else {
            unreachable!()
        };
        nodes.iter().map(|&index| FrozenENode {
            graph: self.graph,
            index,
        })
    }
}
impl<'f> FrozenENode<'f> {
    /// The constructor's name for diagnostics.
    pub fn name(self) -> &'f str {
        &self.graph.tables[self.graph.rows[self.index].table]
            .callable
            .name
    }
    /// Whether this constructor alternative was subsumed.
    pub fn is_subsumed(self) -> bool {
        self.graph.rows[self.index].subsumed
    }
    /// Positional fields, including scalars and structured containers.
    pub fn args(self) -> FrozenValues<'f> {
        FrozenValues {
            graph: self.graph,
            indices: self.graph.rows[self.index].args.iter(),
        }
    }
    /// Derived equality topology in field/container order, retaining duplicates.
    /// Scalars are skipped and traversal stops at equality references, including cycles.
    pub fn eclass_children(self) -> impl Iterator<Item = FrozenEClass<'f>> {
        let roots = &self.graph.rows[self.index].args;
        // Memoize class-free closures before enumerating occurrences: doubling
        // an empty/shared container must not cause exponential work before None.
        // Real equality occurrences are still yielded once per incoming path.
        let mut has_class = HashMap::new();
        let mut work: Vec<_> = roots.iter().map(|&index| (index, false)).collect();
        while let Some((index, done)) = work.pop() {
            if has_class.contains_key(&index) {
                continue;
            }
            match &self.graph.values[index].data {
                ValueData::Class(_) => {
                    has_class.insert(index, true);
                }
                ValueData::Container(children) => {
                    if done {
                        has_class.insert(index, children.iter().any(|c| has_class[c]));
                    } else {
                        work.push((index, true));
                        work.extend(children.iter().rev().map(|&c| (c, false)));
                    }
                }
                _ => {
                    has_class.insert(index, false);
                }
            }
        }
        let mut pending = roots.iter().rev().copied().collect::<Vec<_>>();
        std::iter::from_fn(move || {
            while let Some(index) = pending.pop() {
                if !has_class[&index] {
                    continue;
                }
                match &self.graph.values[index].data {
                    ValueData::Class(_) => {
                        return Some(FrozenEClass {
                            graph: self.graph,
                            index,
                        });
                    }
                    ValueData::Container(children) => pending.extend(children.iter().rev()),
                    _ => {}
                }
            }
            None
        })
    }
}
impl<'f> FrozenTable<'f> {
    /// The table's name for diagnostics.
    pub fn name(self) -> &'f str {
        &self.graph.tables[self.index].callable.name
    }
    /// Positional input sorts, even for an empty table.
    pub fn inputs(self) -> &'f [SortRef] {
        &self.graph.tables[self.index].inputs
    }
    /// Declared output sort; relation rows expose Unit outputs.
    pub fn output(self) -> SortRef {
        self.graph.tables[self.index].output.clone()
    }
    /// Rows in native iteration order.
    pub fn rows(self) -> impl ExactSizeIterator<Item = FrozenRow<'f>> {
        self.graph.tables[self.index]
            .rows
            .iter()
            .map(|&index| FrozenRow {
                graph: self.graph,
                index,
            })
    }
}
impl<'f> FrozenRow<'f> {
    /// Positional input values.
    pub fn args(self) -> FrozenValues<'f> {
        FrozenValues {
            graph: self.graph,
            indices: self.graph.rows[self.index].args.iter(),
        }
    }
    /// Exact output; equality values remain references rather than extracted terms.
    pub fn output(self) -> FrozenValue<'f> {
        FrozenValue {
            graph: self.graph,
            index: self.graph.rows[self.index].output,
        }
    }
    /// Whether this row was subsumed.
    pub fn is_subsumed(self) -> bool {
        self.graph.rows[self.index].subsumed
    }
}
macro_rules! handle_identity {
    ($($handle:ident),+) => { $(
        impl PartialEq for $handle<'_> { fn eq(&self, other: &Self) -> bool { ptr::eq(self.graph, other.graph) && self.index == other.index } }
        impl Eq for $handle<'_> {}
        impl Hash for $handle<'_> { fn hash<H: Hasher>(&self, state: &mut H) { ptr::hash(self.graph, state); self.index.hash(state); } }
        impl std::fmt::Debug for $handle<'_> { fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { f.debug_struct(stringify!($handle)).field("snapshot", &ptr::from_ref(self.graph)).field("index", &self.index).finish() } }
    )+ };
}
handle_identity!(
    FrozenValue,
    FrozenEClass,
    FrozenENode,
    FrozenTable,
    FrozenRow
);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hundred_thousand_node_snapshot_traverses_and_drops_iteratively() {
        // Flat observation fixture: this tests the snapshot, not native parsing
        // of a recursively authored 100k-node term.
        const N: usize = 100_000;
        let sort = SortRef::equality("Chain");
        let mut graph = SnapshotData {
            values: Vec::new(),
            rows: Vec::new(),
            tables: vec![
                Table {
                    callable: CallableRef {
                        name: "End".into(),
                        kind: CallKind::Constructor,
                        source: None,
                        syntax: None,
                    },
                    inputs: vec![],
                    output: sort.clone(),
                    rows: vec![0],
                },
                Table {
                    callable: CallableRef {
                        name: "Next".into(),
                        kind: CallKind::Constructor,
                        source: None,
                        syntax: None,
                    },
                    inputs: vec![sort.clone()],
                    output: sort.clone(),
                    rows: (1..N).collect(),
                },
            ],
            classes: (0..N).collect(),
            captures: HashMap::new(),
        };
        for index in 0..N {
            graph.values.push(StoredValue {
                sort: sort.clone(),
                data: ValueData::Class(vec![index]),
            });
            graph.rows.push(Row {
                table: usize::from(index != 0),
                args: if index == 0 { vec![] } else { vec![index - 1] },
                output: index,
                subsumed: false,
            });
        }
        let mut pending = vec![FrozenValue {
            graph: &graph,
            index: N - 1,
        }];
        let mut seen = 0;
        while let Some(value) = pending.pop() {
            let FrozenValueView::EClass(class) = value.view() else {
                panic!("class")
            };
            seen += 1;
            pending.extend(class.nodes().next().unwrap().args());
        }
        assert_eq!(seen, N);
        assert_eq!(graph.classes.len(), N);
        drop(graph);
    }

    #[test]
    fn shared_class_free_container_closures_do_not_expand_exponentially() {
        let term = SortRef::equality("Term");
        for scalar_leaf in [false, true] {
            let mut graph = SnapshotData {
                values: Vec::new(),
                rows: vec![],
                tables: vec![],
                classes: vec![],
                captures: HashMap::new(),
            };
            let mut sort = if scalar_leaf {
                SortRef::builtin("i64")
            } else {
                SortRef::container("Vec", vec![term.clone()])
            };
            graph.values.push(StoredValue {
                sort: sort.clone(),
                data: if scalar_leaf {
                    ValueData::Scalar(FrozenScalar::I64(1))
                } else {
                    ValueData::Container(vec![])
                },
            });
            for index in 1..=64 {
                sort = SortRef::container("Vec", vec![sort]);
                graph.values.push(StoredValue {
                    sort: sort.clone(),
                    data: ValueData::Container(vec![index - 1, index - 1]),
                });
            }
            graph.tables.push(Table {
                callable: CallableRef {
                    name: "Nested".into(),
                    kind: CallKind::Constructor,
                    source: None,
                    syntax: None,
                },
                inputs: vec![sort],
                output: term.clone(),
                rows: vec![0],
            });
            graph.values.push(StoredValue {
                sort: term.clone(),
                data: ValueData::Class(vec![0]),
            });
            graph.classes.push(65);
            graph.rows.push(Row {
                table: 0,
                args: vec![64],
                output: 65,
                subsumed: false,
            });
            let node = FrozenEClass {
                graph: &graph,
                index: 65,
            }
            .nodes()
            .next()
            .unwrap();
            assert_eq!(node.eclass_children().count(), 0);
        }
    }
}
