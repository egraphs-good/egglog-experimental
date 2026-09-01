//! Implementation of `(unstable-subst root map)`.
//!
//! The map's keys and values share one eq-sort and are applied simultaneously
//! while copying the affected constructor subgraph. The root must have
//! committed rows when traversal is needed; copied equations are sound only
//! when substitution preserves their derivations and premises. See
//! `docs/unstable-subst.md` for the complete interface, safety boundary,
//! algorithm, and cost model.

use std::any::TypeId;
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

use egglog::api::RawValues;
use egglog::ast::Span;
use egglog::constraint::{self, Constraint, ImpossibleConstraint, TypeConstraint};
use egglog::sort::MapContainer;
use egglog::{
    ArcSort, Atom, AtomTerm, Core, Error, FullPrim, FullState, FuncType, Primitive, Read, TypeInfo,
    Value, Write,
};

const SUBST: &str = "unstable-subst";

/// A constructor the walk can follow.
type Constructor<'a> = &'a FuncType;

/// What a column of a given sort holds, as far as the walk cares.
enum Kind {
    /// An e-class: walk into it, and copy it if it is affected.
    Eclass,
    /// A container with e-classes somewhere inside: walk into its contents and
    /// rebuild it if any of them change. Carries the Rust [`TypeId`] its values
    /// are interned under.
    Container(TypeId),
    /// Nothing an e-class can hide in: copied through untouched.
    Opaque,
}

fn kind_of(sort: &ArcSort) -> Kind {
    if sort.is_eq_sort() {
        Kind::Eclass
    } else if sort.is_container_sort() {
        // Deliberately not `is_eq_container_sort`, which answers from the
        // sort's declared element sorts. For an `unstable-fn` value those are
        // the arguments still to be applied, not the ones it captured — a
        // `(UnstableFn () Math)` holding an e-class reports no eq-sort
        // elements. Walking every container and asking the value what it holds
        // costs an `inner_values` call on containers that turn out to have no
        // e-classes inside, and cannot miss one.
        Kind::Container(
            sort.value_type()
                .expect("a container sort has a value type"),
        )
    } else {
        Kind::Opaque
    }
}

/// One reachable constructor row, keyed by the constructor it came from so the
/// build pass can re-apply it.
struct ENode {
    ctor: usize,
    children: Vec<Value>,
}

/// The reachable sub-e-graph.
#[derive(Default)]
struct Snapshot {
    /// E-nodes of each reachable e-class. Subsumed rows are left out: they are
    /// excluded from extraction, so a copy must not resurrect them.
    nodes: HashMap<Value, Vec<ENode>>,
    /// Contents of each reachable container value, with the [`TypeId`] to
    /// rebuild it under.
    containers: HashMap<Value, (TypeId, Vec<(ArcSort, Value)>)>,
    /// The e-classes each e-class references, flattened through containers.
    /// Drives both the affected fixpoint and the build order.
    deps: HashMap<Value, Vec<Value>>,
}

struct Walk<'a> {
    ctors: Vec<Constructor<'a>>,
    /// Indices into `ctors`, by output sort name.
    by_output: HashMap<String, Vec<usize>>,
    map: &'a BTreeMap<Value, Value>,
    snapshot: Snapshot,
    /// E-classes the substitution changes: a key, or a reference to an
    /// affected e-class.
    affected: HashSet<Value>,
    /// The copy of each affected e-class that has been named so far.
    images: HashMap<Value, Value>,
    container_images: HashMap<Value, Value>,
    /// Memo for [`Walk::container_leaves`].
    container_leaves: HashMap<Value, Vec<(ArcSort, Value)>>,
}

/// The constructors with an eq-sort output: the rows that make up the term
/// structure. Resolved per call, since an e-graph gains constructors over time.
fn constructors<'db>(state: &FullState<'_, 'db>) -> Vec<Constructor<'db>> {
    let names: Vec<String> = state
        .table_sizes()
        .into_iter()
        .filter(|&(_, size)| size != 0)
        .map(|(name, _)| name.to_owned())
        .collect();
    names
        .into_iter()
        .filter_map(|name| {
            // `constructor_schema` rejects the function tables, which is also
            // what keeps globals out: they lower to function tables.
            let func_type = state.constructor_schema(&name).ok()?;
            func_type.output.is_eq_sort().then_some(func_type)
        })
        .collect()
}

/// Substitute `map` through the sub-e-graph reachable from `root`, returning
/// the root of the copy. See the module docs for the semantics.
///
/// When traversal is needed, `root` must be an e-class that already has rows:
/// one the query bound, or one from an earlier command. A root the enclosing
/// action just built is not in the tables yet and comes back unchanged, with
/// no error. A root that is itself a key returns its mapped value without a walk.
fn substitute<'db>(
    state: &mut FullState<'_, 'db>,
    root: Value,
    map: &BTreeMap<Value, Value>,
) -> Result<Value, Error> {
    if let Some(target) = map.get(&root) {
        return Ok(*target);
    }
    if map.is_empty() {
        return Ok(root);
    }

    let ctors = constructors(state);
    let mut by_output: HashMap<String, Vec<usize>> = HashMap::new();
    for (index, ctor) in ctors.iter().enumerate() {
        by_output
            .entry(ctor.output.name().to_owned())
            .or_default()
            .push(index);
    }

    let mut walk = Walk {
        ctors,
        by_output,
        map,
        snapshot: Snapshot::default(),
        affected: HashSet::new(),
        images: HashMap::new(),
        container_images: HashMap::new(),
        container_leaves: HashMap::new(),
    };
    walk.collect(state, root)?;
    walk.mark();
    if !walk.affected.contains(&root) {
        return Ok(root);
    }
    walk.build(state, root)
}

/// A pending e-class visit in the collect pass. The sort is unknown for the
/// root only.
struct Visit(Value, Option<ArcSort>);

impl Walk<'_> {
    /// Gather the reachable e-nodes, container contents, and e-class
    /// dependency edges, starting from `root`.
    fn collect(&mut self, state: &FullState<'_, '_>, root: Value) -> Result<(), Error> {
        let mut stack = vec![Visit(root, None)];
        while let Some(Visit(value, sort)) = stack.pop() {
            if self.snapshot.nodes.contains_key(&value) {
                continue;
            }
            // E-class ids all come from one counter, so probing a constructor
            // of the wrong sort just finds nothing. That is what makes the
            // root's unknown sort affordable: it costs one probe per eq-sorted
            // constructor, once.
            let candidates: Vec<usize> = match &sort {
                Some(sort) => self.by_output.get(sort.name()).cloned().unwrap_or_default(),
                None => (0..self.ctors.len()).collect(),
            };
            let mut nodes = Vec::new();
            for index in candidates {
                let mut rows = Vec::new();
                state.constructor_enodes_for_eclass(&self.ctors[index].name, value, |enode| {
                    if !enode.subsumed {
                        rows.push(enode.children.to_vec());
                    }
                })?;
                nodes.extend(rows.into_iter().map(|children| ENode {
                    ctor: index,
                    children,
                }));
            }

            let mut deps = Vec::new();
            for node in &nodes {
                let ctor = self.ctors[node.ctor];
                for (child, child_sort) in node.children.iter().zip(&ctor.input) {
                    match kind_of(child_sort) {
                        Kind::Eclass => {
                            deps.push(*child);
                            stack.push(Visit(*child, Some(child_sort.clone())));
                        }
                        Kind::Container(type_id) => {
                            for (leaf_sort, leaf) in
                                self.container_leaves(state, *child, type_id, child_sort)
                            {
                                deps.push(leaf);
                                stack.push(Visit(leaf, Some(leaf_sort)));
                            }
                        }
                        Kind::Opaque => {}
                    }
                }
            }
            // Recorded after the children are read, but before they are
            // visited, so a cycle back to `value` terminates.
            self.snapshot.nodes.insert(value, nodes);
            self.snapshot.deps.insert(value, deps);
        }
        Ok(())
    }

    /// The e-class leaves of a container value, flattened through nested
    /// containers, recording its contents on the way. Recursion is bounded by
    /// how deeply the program's sorts nest containers.
    fn container_leaves(
        &mut self,
        state: &FullState<'_, '_>,
        value: Value,
        type_id: TypeId,
        sort: &ArcSort,
    ) -> Vec<(ArcSort, Value)> {
        if let Some(leaves) = self.container_leaves.get(&value) {
            return leaves.clone();
        }
        let contents = sort.inner_values(state.container_values(), value);
        let mut leaves = Vec::new();
        for (inner_sort, inner) in &contents {
            match kind_of(inner_sort) {
                Kind::Eclass => leaves.push((inner_sort.clone(), *inner)),
                Kind::Container(inner_type_id) => {
                    leaves.extend(self.container_leaves(state, *inner, inner_type_id, inner_sort))
                }
                Kind::Opaque => {}
            }
        }
        self.snapshot.containers.insert(value, (type_id, contents));
        self.container_leaves.insert(value, leaves.clone());
        leaves
    }

    /// Least fixpoint of "references something the substitution changes",
    /// seeded with the map keys the walk actually reached.
    fn mark(&mut self) {
        let mut users: HashMap<Value, Vec<Value>> = HashMap::new();
        for (owner, deps) in &self.snapshot.deps {
            for dep in deps {
                users.entry(*dep).or_default().push(*owner);
            }
        }

        let mut queue: VecDeque<Value> = self
            .map
            .keys()
            .copied()
            .filter(|key| self.snapshot.nodes.contains_key(key))
            .collect();
        self.affected.extend(queue.iter().copied());
        while let Some(value) = queue.pop_front() {
            for user in users.get(&value).into_iter().flatten() {
                if self.affected.insert(*user) {
                    queue.push_back(*user);
                }
            }
        }
    }

    /// The e-classes a copy of `node` needs to resolve first, including leaves
    /// reached through containers.
    fn node_deps(&self, node: &ENode) -> Vec<Value> {
        let ctor = self.ctors[node.ctor];
        let mut deps = Vec::new();
        for (child, child_sort) in node.children.iter().zip(&ctor.input) {
            match kind_of(child_sort) {
                Kind::Eclass => deps.push(*child),
                Kind::Container(_) => deps.extend(
                    self.container_leaves
                        .get(child)
                        .into_iter()
                        .flatten()
                        .map(|(_, leaf)| *leaf),
                ),
                Kind::Opaque => {}
            }
        }
        deps
    }

    /// Whether a copied row can already name `dep`: it is replaced outright, it
    /// is shared with the original, or its own copy has been accounted for.
    fn resolved(&self, dep: Value, copyable: &HashSet<Value>) -> bool {
        self.map.contains_key(&dep) || !self.affected.contains(&dep) || copyable.contains(&dep)
    }

    /// Decide, without writing anything, whether the region can be copied at
    /// all, and in what order its e-classes can be named.
    ///
    /// Doing this before the first write is what keeps a failure from leaving a
    /// partial copy behind: egglog flushes an action's staged writes even when
    /// it ends in an error, so a write pass that discovered an ungrounded cycle
    /// only after copying its way up to it could not take those rows back.
    fn plan(&self, root: Value) -> Result<Vec<Value>, Error> {
        let region = self.postorder(root);
        let mut copyable: HashSet<Value> = HashSet::new();
        let mut order: Vec<Value> = Vec::with_capacity(region.len());

        // Least fixpoint of "has an e-node whose children all resolve". A class
        // joins `order` when it becomes nameable, so the order is one the
        // copies can actually be built in.
        loop {
            let mut progress = false;
            for eclass in &region {
                if copyable.contains(eclass) {
                    continue;
                }
                let nameable = self.snapshot.nodes[eclass].iter().any(|node| {
                    self.node_deps(node)
                        .iter()
                        .all(|dep| self.resolved(*dep, &copyable))
                });
                if nameable {
                    copyable.insert(*eclass);
                    order.push(*eclass);
                    progress = true;
                }
            }
            if !progress {
                break;
            }
        }

        // Every e-node has to be copyable, not just one per class: a class can
        // be nameable while another of its e-nodes still points into a cycle.
        for eclass in &region {
            let mut blocked: Vec<&str> = self.snapshot.nodes[eclass]
                .iter()
                .filter(|node| {
                    !self
                        .node_deps(node)
                        .iter()
                        .all(|dep| self.resolved(*dep, &copyable))
                })
                .map(|node| self.ctors[node.ctor].name.as_str())
                .collect();
            if !blocked.is_empty() {
                blocked.sort_unstable();
                blocked.dedup();
                return Err(error(format!(
                    "no order copies e-class {eclass:?}: its e-nodes ({}) refer to copies that \
                     nothing can produce. Every cycle in the substituted region needs at least \
                     one e-node whose children all lie outside it.",
                    blocked.join(", "),
                )));
            }
        }
        Ok(order)
    }

    /// Copy the affected e-classes and return the root's image.
    ///
    /// Every copied e-node goes in through `lookup_or_insert`, so egglog names
    /// the copy's e-class — nothing here invents an id. [`Walk::plan`] has
    /// already established that every e-node in the region can be copied, and
    /// in what order, so this writes without having to discover blockage.
    fn build(&mut self, state: &mut FullState<'_, '_>, root: Value) -> Result<Value, Error> {
        let order = self.plan(root)?;

        // Name each class from the first of its e-nodes that can be built. Its
        // other e-nodes may name classes further along, so they wait.
        let mut leftovers: Vec<(Value, ENode)> = Vec::new();
        for eclass in order {
            let mut named = false;
            for node in self.snapshot.nodes.remove(&eclass).unwrap_or_default() {
                if !named && let Some(args) = self.copied_args(state, &node) {
                    let copy = state.add(&self.ctors[node.ctor].name, RawValues(args))?;
                    self.images.insert(eclass, copy);
                    named = true;
                    continue;
                }
                leftovers.push((eclass, node));
            }
            debug_assert!(named, "plan said {eclass:?} was nameable");
        }

        // Every class has an image now, so the rest go in as further ways to
        // say the class they came from.
        for (eclass, node) in leftovers {
            let args = self
                .copied_args(state, &node)
                .expect("plan said every e-node was copyable");
            let copy = state.add(&self.ctors[node.ctor].name, RawValues(args))?;
            let image = self.images[&eclass];
            if copy != image {
                state.union(copy, image)?;
            }
        }

        self.images
            .get(&root)
            .copied()
            .ok_or_else(|| error(format!("the root e-class {root:?} was not copied")))
    }

    /// The affected e-classes that need copying, children before parents.
    fn postorder(&self, root: Value) -> Vec<Value> {
        enum Frame {
            Enter(Value),
            Exit(Value),
        }

        let mut order = Vec::new();
        let mut seen = HashSet::new();
        let mut stack = vec![Frame::Enter(root)];
        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Enter(eclass) => {
                    if !seen.insert(eclass) {
                        continue;
                    }
                    stack.push(Frame::Exit(eclass));
                    for dep in self.snapshot.deps.get(&eclass).into_iter().flatten() {
                        if self.affected.contains(dep)
                            && !self.map.contains_key(dep)
                            && !seen.contains(dep)
                        {
                            stack.push(Frame::Enter(*dep));
                        }
                    }
                }
                Frame::Exit(eclass) => order.push(eclass),
            }
        }
        order
    }

    /// The substituted children of `node`, or `None` if some child's copy does
    /// not exist yet.
    fn copied_args(&mut self, state: &mut FullState<'_, '_>, node: &ENode) -> Option<Vec<Value>> {
        let ctor = self.ctors[node.ctor];
        let mut args = Vec::with_capacity(node.children.len());
        for (child, child_sort) in node.children.iter().zip(&ctor.input) {
            let image = match kind_of(child_sort) {
                Kind::Eclass => self.eclass_image(*child)?,
                Kind::Container(type_id) => self.container_image(state, *child, type_id)?,
                Kind::Opaque => *child,
            };
            args.push(image);
        }
        Some(args)
    }

    fn eclass_image(&self, eclass: Value) -> Option<Value> {
        if let Some(target) = self.map.get(&eclass) {
            return Some(*target);
        }
        if !self.affected.contains(&eclass) {
            return Some(eclass);
        }
        self.images.get(&eclass).copied()
    }

    /// The interned value of `container` with its contents substituted, or
    /// `container` itself if nothing inside it changed. `None` while any
    /// e-class inside it is still waiting for its copy.
    fn container_image(
        &mut self,
        state: &mut FullState<'_, '_>,
        container: Value,
        type_id: TypeId,
    ) -> Option<Value> {
        if let Some(image) = self.container_images.get(&container) {
            return Some(*image);
        }
        let Some((_, contents)) = self.snapshot.containers.get(&container).cloned() else {
            return Some(container);
        };

        // Nothing is interned until every value inside resolves, so a blocked
        // container leaves no half-substituted copy behind.
        let mut remap: HashMap<Value, Value> = HashMap::new();
        for (inner_sort, inner) in &contents {
            let image = match kind_of(inner_sort) {
                Kind::Eclass => self.eclass_image(*inner)?,
                Kind::Container(inner_type_id) => {
                    self.container_image(state, *inner, inner_type_id)?
                }
                Kind::Opaque => continue,
            };
            if image != *inner {
                remap.insert(*inner, image);
            }
        }

        let image = if remap.is_empty() {
            container
        } else {
            let mapped = state.map_container(type_id, container, &|value| {
                remap.get(&value).copied().unwrap_or(value)
            });
            // `collect` already read this value's contents through the same
            // sort, so it is a container of this type.
            mapped.expect("collect read this value as the same container type")
        };
        self.container_images.insert(container, image);
        Some(image)
    }
}

fn error(message: String) -> Error {
    Error::BackendError(format!("{SUBST}: {message}"))
}

/// The full-context `(unstable-subst root map)` primitive.
///
/// [`new_experimental_egraph`](crate::new_experimental_egraph) registers it by
/// default. Callers must ensure that substitution preserves the derivation and
/// every premise of each copied equation; see the [guide] for the full semantic
/// safety boundary.
///
/// [guide]: https://github.com/egraphs-good/egglog-experimental/blob/main/docs/unstable-subst.md
#[derive(Clone)]
pub struct Subst;

impl Primitive for Subst {
    fn name(&self) -> &str {
        SUBST
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        Box::new(SubstTypeConstraint { span: span.clone() })
    }
}

impl FullPrim for Subst {
    /// Returns `None` only after raising a primitive panic, so the program
    /// stops rather than continuing with a missing value. Shapes the
    /// typechecker rules out panic directly, since reaching one means a bug
    /// here rather than a program egglog should have admitted.
    fn apply<'a, 'db>(&self, mut state: FullState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let [root, map] = args else {
            panic!(
                "{SUBST} takes a root and a map; the typechecker admitted {} arguments",
                args.len()
            )
        };
        // Cloned out so the container registry is not still borrowed when the
        // walk starts interning new containers.
        let entries = state
            .value_to_container::<MapContainer>(*map)
            .unwrap_or_else(|| panic!("{SUBST}'s type constraint admits only `Map` values"))
            .data
            .clone();
        match substitute(&mut state, *root, &entries) {
            Ok(image) => Some(image),
            Err(err) => {
                // A primitive cannot return an `Error`, and registering a
                // custom panic message needs the backend, which egglog does not
                // expose. So the reason goes to the log and the program sees a
                // generic primitive panic.
                log::error!("{err}");
                state.panic();
                None
            }
        }
    }
}

/// `(unstable-subst root map) : (R, Map<K, K>) -> R` for any eq-sort `R`.
///
/// `R` is free rather than pinned to `K` because a substitution reaches through
/// every sort in the term structure, so a root of one sort can perfectly well
/// be rewritten by a map over another. `K` must be an eq-sort mapping to
/// itself: replacing a `K`-sorted child with a value of another sort would
/// produce an ill-typed row.
struct SubstTypeConstraint {
    span: Span,
}

impl TypeConstraint for SubstTypeConstraint {
    fn get(
        &self,
        arguments: &[AtomTerm],
        typeinfo: &TypeInfo,
    ) -> Vec<Box<dyn Constraint<AtomTerm, ArcSort>>> {
        let [root, map, out] = arguments else {
            return vec![constraint::impossible(
                ImpossibleConstraint::ArityMismatch {
                    atom: Atom {
                        span: self.span.clone(),
                        head: SUBST.to_owned(),
                        args: arguments.to_vec(),
                    },
                    expected: 3,
                },
            )];
        };

        let mut cs: Vec<Box<dyn Constraint<AtomTerm, ArcSort>>> =
            vec![constraint::eq(root.clone(), out.clone())];

        // One instantiation per declared sort that could stand in each
        // position; `xor` defers until the surrounding program pins it down.
        //
        // A `Map` sort is identified by the Rust type its values intern
        // under, since the `ContainerSort` impl behind an `ArcSort` is
        // wrapped in a private type that out-of-tree code cannot downcast to.
        let mut map_sorts: Vec<ArcSort> = typeinfo.get_arcsorts_by(|sort| {
            sort.value_type() == Some(TypeId::of::<MapContainer>())
                && match sort.inner_sorts().as_slice() {
                    [key, value] => key.is_eq_sort() && key.name() == value.name(),
                    _ => false,
                }
        });
        map_sorts.sort_by_key(|sort| sort.name().to_owned());
        cs.push(constraint::xor(
            map_sorts
                .into_iter()
                .map(|sort| constraint::assign(map.clone(), sort))
                .collect(),
        ));

        let mut eq_sorts = typeinfo.get_arcsorts_by(|sort| sort.is_eq_sort());
        eq_sorts.sort_by_key(|sort| sort.name().to_owned());
        cs.push(constraint::xor(
            eq_sorts
                .into_iter()
                .map(|sort| {
                    constraint::and(vec![
                        constraint::assign(root.clone(), sort.clone()),
                        constraint::assign(out.clone(), sort),
                    ])
                })
                .collect(),
        ));

        cs
    }
}
