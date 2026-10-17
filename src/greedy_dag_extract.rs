//! Greedy DAG extraction over intrinsic marginal costs.
//!
//! The extractor takes a [`MonoidCost`] and a [`DagCostModel`]. It
//! tracks the reachable `(sort, value)` dependencies for each candidate and
//! charges each dependency's marginal cost once, even when the returned
//! [`TermDag`] shares it. Marginal costs may inspect egraph values and analyses,
//! but they are independent of selected child extraction costs; objectives that
//! depend on those costs belong in core's [`egglog::extract::TreeCostModel`].

use crate::secondary_map::{
    AggregatedSparseSecondaryMap, InternId, Interner, InternerBuilder, SecondaryMap, SecondarySet,
};
use egglog::{
    ArcSort, EGraph, Enode, Error, Function, Read, ReadState, TermDag, TermId, Value,
    ast::{Expr, FunctionSubtype, ParseError},
    extract::{DagCostModel, ExtractedTerm, ExtractedTermVariants, ExtractedTerms, MonoidCost},
};
use hashbrown::{HashMap, hash_map::Entry};
use std::collections::{HashSet, VecDeque};
use std::sync::Arc;

/// `:extractor` is an ordinary identifier, so user-defined commands receive it
/// as a plain [`Expr::Var`] positional argument like any other name. Only the
/// trailing `:extractor <symbol>` pair is read as the selector, so a value that
/// happens to be named `:extractor` elsewhere in the argument list, or a
/// non-symbol final argument, stays positional.
///
/// A trailing `<symbol> <symbol>` pair remains ambiguous and resolves to the
/// selector, which also keeps a misspelled extractor name an error rather than
/// silently positional. Removing that last case needs a surface form ordinary
/// `Expr::Var` parsing cannot produce.
pub(crate) fn split_trailing_extractor(args: &[Expr]) -> Result<(&[Expr], bool), Error> {
    let Some([keyword, extractor]) = args.last_chunk::<2>() else {
        return Ok((args, false));
    };

    if !matches!(keyword, Expr::Var(_, keyword) if keyword == ":extractor") {
        return Ok((args, false));
    }

    let Expr::Var(_, name) = extractor else {
        return Ok((args, false));
    };

    if name != "greedy-dag" {
        return Err(Error::ParseError(ParseError(
            extractor.span(),
            format!("unknown extractor: {name}; omit :extractor to use the default tree extractor"),
        )));
    }

    Ok((&args[..args.len() - 2], true))
}

// Greedy-DAG extraction.
//
// This is a root-aware adaptation of extraction-gym's `faster-greedy-dag`:
// https://github.com/egraphs-good/extraction-gym/blob/903ba0f818b50608fe20ae9e0f03c35cb27bc50a/src/extract/faster_greedy_dag.rs.
// Each candidate records the dependencies whose marginal costs have already
// been paid. Candidate construction unions child dependency sets, rejects
// self-reachable rows, and propagates improvements to affected producer rows
// with a worklist.
// Related extraction-gym issues:
// - root arguments in DAG extractors: https://github.com/egraphs-good/extraction-gym/issues/49
// - greedy variants can differ in quality: https://github.com/egraphs-good/extraction-gym/issues/19
// - global-greedy correctness caveat: https://github.com/egraphs-good/extraction-gym/issues/28
//
// The egglog-specific pieces are:
// - root discovery only records producer rows reachable from the requested roots;
// - producer-row dependencies include eq values nested inside containers;
// - costs are keyed by `(sort, value)` because egglog values are sort-local;
// - reconstruction emits a shared `TermDag` instead of an `ExtractionResult`.
//
// This experimental version intentionally supports normal constructors only.
// View tables with `term_constructor` are proof/term-encoding internals; skipping
// them avoids stabilizing their special row layout for custom extractors.
//
// `docs/greedy-dag-extractor.md` describes the algorithm, invariants, measured
// representation choices, and alternatives that were considered.

/// Borrowed metadata for one extractable constructor.
///
/// The prepared extractor immutably borrows the e-graph, so producer rows can
/// retain `Function` metadata without cloning names and sort vectors or looking
/// functions up again during scoring and reconstruction.
type Constructor<'egraph> = &'egraph Function;

/// Once-paid dependency costs for one potential extracted DAG.
///
/// The keys are reachable `(sort, value)` dependencies and the values are their
/// marginal costs. The underlying sparse secondary map caches the combined
/// total, so cost comparison does not require subtraction or inspecting
/// the cost type.
type PaidDagCosts<C> = AggregatedSparseSecondaryMap<DagCostKey, C>;

/// One selected constructor row for each reachable eq-sort dependency.
type ProducerPlan = HashMap<InternId<DagCostKey>, ProducerRowId>;

/// A complete, immutable witness for one scored greedy-DAG candidate.
///
/// `paid_costs` records every dependency charged by this candidate, while
/// `producer_choices` records the exact constructor row selected for every
/// eq-sort dependency. Keeping them together prevents a later improvement to a
/// child e-class from changing the term reconstructed for an older score.
struct DagCandidate<C: MonoidCost> {
    /// Exact once-paid dependency closure whose aggregate is this score.
    paid_costs: PaidDagCosts<C>,
    /// Transitively closed, acyclic constructor choices for every eq-sort key
    /// reachable from this candidate's root.
    producer_choices: ProducerPlan,
}

/// Keyed on sort and value, since one raw value can have sort-specific costs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct DagCostKey {
    /// Per-extractor dense id for the sort name.
    sort_id: InternId<String>,
    value: Value,
}

/// A reachable constructor row that can produce a target `(sort, value)`.
///
/// These are producer rows for extraction, not e-graph parents: root discovery
/// records every reachable row whose output is a value that may be extracted.
/// The worklist uses a reverse dependency index to revisit producer rows when a
/// child dependency becomes cheaper.
struct GreedyDagProducerRow<'egraph, C> {
    /// Constructor function for this row.
    func: &'egraph Function,
    /// Owned child values. Backend row callbacks are borrowed, but the greedy
    /// DAG fixed point revisits producer rows after root discovery.
    children: Vec<Value>,
    /// Canonical e-class produced by this constructor row.
    eclass: Value,
    /// Interned `(sort, value)` produced by this row.
    target: InternId<DagCostKey>,
    /// Marginal enode cost computed once while freezing the reachable problem.
    cost: C,
}

/// Typed index into the greedy-DAG producer-row arena.
///
/// This is intentionally separate from [`InternId<DagCostKey>`]: cost keys
/// identify paid `(sort, value)` dependencies, while producer-row ids identify
/// rows that can produce one such dependency.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct ProducerRowId(usize);

/// Selected-occurrence projection shared by reconstruction and its typed cache.
type TermObserver<'a, N> =
    dyn FnMut(&TermDag, TermId, &ArcSort, Value, &[N]) -> Result<N, Error> + 'a;

/// Mutable state shared by one term reconstruction traversal.
struct TermReconstructionState<'a, C: MonoidCost, N: Clone> {
    termdag: &'a mut TermDag,
    candidate: &'a DagCandidate<C>,
    cache: HashMap<InternId<DagCostKey>, (TermId, N)>,
    visiting: SecondarySet<DagCostKey>,
    observe: &'a mut TermObserver<'a, N>,
}

// These traversals are naturally recursive, which keeps their invariants local
// and substantially smaller than explicit task stacks. Stacker grows the stack
// only near the red zone. On unsupported targets it is a no-op:
// https://github.com/rust-lang/stacker#platform-support.
// Checking at every recursive entry was 1.13% faster than threading a depth
// counter and checking every 64 levels on Taylor 51. The sizes follow rustc's
// established stacker configuration:
// https://github.com/rust-lang/rust/blob/1.90.0/compiler/rustc_data_structures/src/stack.rs#L1-L14.
const STACK_RED_ZONE: usize = 100 * 1024;
const STACK_SEGMENT_SIZE: usize = 1024 * 1024;

/// Producer rows plus indexes by dependency and produced target.
///
/// The rows form a small extraction-local arena because backend callbacks
/// borrow row data, while greedy-DAG propagation needs to revisit rows after
/// reachable discovery completes. The dependency index maps an improved
/// `(sort, value)` cost key to only the rows whose cost may change. The target
/// index maps an extracted e-class to only its candidate producer rows. It is
/// built only for variant extraction because best extraction never reads it;
/// an alternating paired benchmark found eagerly indexing every row made best
/// extraction about 2.3% slower.
struct ProducerRows<'egraph, C> {
    rows: Vec<GreedyDagProducerRow<'egraph, C>>,
    by_dependency: SecondaryMap<DagCostKey, Vec<ProducerRowId>>,
    by_target: Option<SecondaryMap<DagCostKey, Vec<ProducerRowId>>>,
}

#[derive(Default)]
struct ProducerRowsBuilder<'egraph> {
    rows: Vec<GreedyDagProducerRow<'egraph, ()>>,
    by_dependency: HashMap<InternId<DagCostKey>, Vec<ProducerRowId>>,
    by_target: Option<HashMap<InternId<DagCostKey>, Vec<ProducerRowId>>>,
}

impl<'egraph> ProducerRowsBuilder<'egraph> {
    fn push(
        &mut self,
        row: GreedyDagProducerRow<'egraph, ()>,
        dependencies: impl IntoIterator<Item = InternId<DagCostKey>>,
    ) {
        let row_id = ProducerRowId(self.rows.len());
        if let Some(by_target) = &mut self.by_target {
            by_target.entry(row.target).or_default().push(row_id);
        }
        self.rows.push(row);
        for dependency in dependencies {
            self.by_dependency
                .entry(dependency)
                .or_default()
                .push(row_id);
        }
    }

    fn freeze<C: MonoidCost, M: DagCostModel<C>>(
        self,
        egraph: &'egraph EGraph,
        cost_model: &M,
        key_ids: &Interner<DagCostKey>,
    ) -> ProducerRows<'egraph, C> {
        let mut by_dependency = key_ids.secondary_map();
        for (key, producer_row_ids) in self.by_dependency {
            by_dependency.insert(key, producer_row_ids);
        }
        let by_target = self.by_target.map(|rows_by_target| {
            let mut by_target = key_ids.secondary_map();
            for (target, producer_row_ids) in rows_by_target {
                by_target.insert(target, producer_row_ids);
            }
            by_target
        });
        let rows = self
            .rows
            .into_iter()
            .map(|row| {
                let enode = Enode {
                    name: row.func.name(),
                    children: &row.children,
                    eclass: row.eclass,
                    subsumed: false,
                };
                let cost = cost_model.enode_cost(egraph, row.func, &enode);
                GreedyDagProducerRow {
                    func: row.func,
                    children: row.children,
                    eclass: row.eclass,
                    target: row.target,
                    cost,
                }
            })
            .collect();
        ProducerRows {
            rows,
            by_dependency,
            by_target,
        }
    }
}

/// A greedy DAG extractor.
///
/// Unlike the tree extractor, which optimizes tree cost under a local cost
/// model, this extractor greedily chooses one producer row per reachable
/// eq-sort value while charging each selected `(sort, value)` dependency at
/// most once. This is not globally optimal, but it is much cheaper than an
/// exact DAG extractor and avoids the optimal-substructure assumption required
/// by encoding DAG sharing inside a normal `TreeCostModel`.
///
/// Every returned root or variant carries one internally consistent producer
/// snapshot. Separate results may choose different representatives for a shared
/// e-class; optimizing one joint choice across roots would require a non-local
/// result representation. See:
/// https://github.com/egraphs-good/extraction-gym/issues/36.
///
/// Preparation evaluates the cost model once per reachable producer row and
/// once per distinct primitive or container value. Fixed-point propagation,
/// variant ranking, and conflict rescoring reuse that frozen cost snapshot.
struct GreedyDagExtractor<'egraph, C: MonoidCost> {
    egraph: &'egraph EGraph,

    /// Sort-name interner used only to build compact [`DagCostKey`]s.
    sort_ids: Interner<String>,
    /// Dense id-space for every reachable dependency that can be charged once.
    key_ids: Interner<DagCostKey>,

    /// Reachable producer rows and the reverse index used by the worklist.
    producer_rows: ProducerRows<'egraph, C>,

    /// Cached marginal costs for reachable primitive and container values.
    structural_costs: SecondaryMap<DagCostKey, C>,

    /// Best known greedy-DAG candidate for each reachable eq-sort value.
    ///
    /// Only eq-sort values get entries here; primitive and container values
    /// are computed structurally.
    best_candidates: SecondaryMap<DagCostKey, Arc<DagCandidate<C>>>,
}

struct ReachableExtractionBuilder<'egraph> {
    egraph: &'egraph EGraph,

    /// Growable sort-name interner used while discovering reachable values.
    sort_ids: InternerBuilder<String>,
    /// Growable id-space for reachable `(sort, value)` dependencies.
    key_ids: InternerBuilder<DagCostKey>,
    /// Reachable producer rows and their reverse dependency index.
    producer_rows: ProducerRowsBuilder<'egraph>,
    /// Unique reachable primitive and container values to cost after discovery.
    structural_nodes: HashMap<InternId<DagCostKey>, (ArcSort, Value)>,
    /// Deduplication set for reachable eq-sort values.
    seen_eq_values: HashSet<InternId<DagCostKey>>,
    /// Constructors by encountered output sort name, in `functions_iter()`
    /// order. Lists are built lazily and shared across values of the same sort.
    constructors_by_sort: HashMap<String, Arc<[Constructor<'egraph>]>>,
}

impl<'egraph> ReachableExtractionBuilder<'egraph> {
    fn intern_key(&mut self, sort_name: &str, value: Value) -> InternId<DagCostKey> {
        let sort_id = self
            .sort_ids
            .get(sort_name)
            .unwrap_or_else(|| self.sort_ids.intern(sort_name.to_owned()));
        self.key_ids.intern(DagCostKey { sort_id, value })
    }

    fn constructors_for_sort(&mut self, sort_name: &str) -> Arc<[Constructor<'egraph>]> {
        if let Some(constructors) = self.constructors_by_sort.get(sort_name) {
            return constructors.clone();
        }

        // Sharing one immutable list per encountered sort avoids rescanning
        // unrelated constructors for every reachable value.
        let constructors: Arc<[Constructor<'egraph>]> = self
            .egraph
            .functions_iter()
            .filter(|(_, func)| {
                func.func_type().subtype == FunctionSubtype::Constructor
                    && !func.is_hidden()
                    && !func.is_unextractable()
                    && func.func_type().output.name() == sort_name
            })
            .map(|(_, func)| func)
            .collect::<Vec<_>>()
            .into();
        self.constructors_by_sort
            .insert(sort_name.to_owned(), constructors.clone());
        constructors
    }

    fn intern_nested_eq_dependencies(
        &mut self,
        sort: &ArcSort,
        value: Value,
        dependencies: &mut HashSet<InternId<DagCostKey>>,
    ) {
        let mut pending = vec![(sort.clone(), value)];
        while let Some((sort, value)) = pending.pop() {
            if sort.is_container_sort() {
                pending.extend(
                    self.egraph
                        .container_inner_values(&sort, value)
                        .into_iter()
                        .rev(),
                );
            } else if sort.is_eq_sort() {
                dependencies.insert(self.intern_key(sort.name(), value));
            }
        }
    }

    fn discover_node(&mut self, read_state: &ReadState<'_, '_>, sort: &ArcSort, value: Value) {
        // Discovery can follow unextractable paths that never reach later
        // scoring or reconstruction, so protect recursion at this entry point.
        stacker::maybe_grow(STACK_RED_ZONE, STACK_SEGMENT_SIZE, || {
            let sort_name = sort.name().to_owned();
            let key = self.intern_key(&sort_name, value);
            if !sort.is_eq_sort() {
                self.structural_nodes
                    .entry(key)
                    .or_insert_with(|| (sort.clone(), value));
            }

            if sort.is_container_sort() {
                for (child_sort, child_value) in self.egraph.container_inner_values(sort, value) {
                    self.discover_node(read_state, &child_sort, child_value);
                }
                return;
            }
            if !sort.is_eq_sort() || !self.seen_eq_values.insert(key) {
                return;
            }

            let constructors = self.constructors_for_sort(&sort_name);
            let mut producer_rows = Vec::new();
            for &func in constructors.iter() {
                read_state
                    .constructor_enodes_for_eclass(func.name(), value, |enode| {
                        if !enode.subsumed {
                            producer_rows.push((func, enode.children.to_vec()));
                        }
                    })
                    .expect("constructor name came from the egraph");
            }

            for (func, children) in producer_rows {
                let child_nodes: Vec<_> = func
                    .func_type()
                    .input
                    .iter()
                    .cloned()
                    .zip(children.iter().copied())
                    .collect();
                let mut dependencies = HashSet::default();
                for (child_value, child_sort) in children.iter().zip(func.func_type().input.iter())
                {
                    self.intern_nested_eq_dependencies(child_sort, *child_value, &mut dependencies);
                }
                self.producer_rows.push(
                    GreedyDagProducerRow {
                        func,
                        children,
                        eclass: value,
                        target: key,
                        cost: (),
                    },
                    dependencies,
                );
                for (child_sort, child_value) in child_nodes {
                    self.discover_node(read_state, &child_sort, child_value);
                }
            }
        })
    }
}

impl<'egraph, C: MonoidCost> GreedyDagExtractor<'egraph, C> {
    fn prepare<M: DagCostModel<C>>(
        egraph: &'egraph EGraph,
        roots: &[(ArcSort, Value)],
        cost_model: M,
        index_targets: bool,
    ) -> Self {
        // Build the root-local problem: collect extractable functions, intern
        // reachable `(sort, value)` dependencies, and record producer rows with
        // their reverse dependency edges.
        let mut builder = ReachableExtractionBuilder {
            egraph,
            sort_ids: Default::default(),
            key_ids: Default::default(),
            producer_rows: ProducerRowsBuilder {
                by_target: index_targets.then(HashMap::default),
                ..Default::default()
            },
            structural_nodes: Default::default(),
            seen_eq_values: Default::default(),
            constructors_by_sort: Default::default(),
        };

        // Keep one read guard for the complete discovery pass. Reacquiring it
        // for every reachable node was measurable on extraction-heavy programs.
        // Cost callbacks run only after this closure because custom models may
        // read the e-graph themselves.
        egraph.read(|read_state| {
            for (sort, value) in roots {
                builder.discover_node(&read_state, sort, *value);
            }
        });

        // Discovery is complete, so freeze the interned id spaces before
        // constructing secondary maps. From here on, greedy-DAG propagation can
        // use dense ids and bitsets instead of hashing `(sort, value)` keys.
        let ReachableExtractionBuilder {
            sort_ids,
            key_ids,
            producer_rows,
            structural_nodes,
            ..
        } = builder;
        let sort_ids = sort_ids.freeze();
        let key_ids = key_ids.freeze();
        // Freeze every model callback into the reachable problem. The worklist
        // and variant rescoring may revisit nodes many times, but their costs
        // remain stable and do not repeat potentially expensive e-graph reads.
        let producer_rows = producer_rows.freeze(egraph, &cost_model, &key_ids);
        let mut structural_costs = key_ids.secondary_map();
        for (key, (sort, value)) in structural_nodes {
            let cost = if sort.is_container_sort() {
                cost_model.container_cost(egraph, &sort, value)
            } else {
                cost_model.base_value_cost(egraph, &sort, value)
            };
            structural_costs.insert(key, cost);
        }
        let best_candidates = key_ids.secondary_map();

        // Run the greedy fixed point over the reachable producer rows and keep
        // the resulting best producer choice for each reachable eq-sort value.
        let mut extractor = Self {
            egraph,
            sort_ids,
            key_ids,
            producer_rows,
            structural_costs,
            best_candidates,
        };

        extractor.greedy_dag();
        extractor
    }

    /// Looks up a key in the frozen reachable universe for this extraction.
    ///
    /// `None` means the `(sort, value)` was not discovered from the requested
    /// roots, so it cannot participate in this root-local greedy DAG.
    fn reachable_cost_key(&self, sort: &ArcSort, value: Value) -> Option<InternId<DagCostKey>> {
        self.key_ids.get(&DagCostKey {
            sort_id: self.sort_ids.get(sort.name())?,
            value,
        })
    }

    /// Build a closed candidate from child producer snapshots.
    ///
    /// Shared dependencies are charged once. When child snapshots disagree on
    /// a producer, the choice from the largest snapshot wins; this candidate's
    /// root producer is then installed and the complete plan is rescored.
    /// Rescoring removes costs reachable only through losing choices, so the
    /// resulting score describes the snapshot used for reconstruction.
    fn candidate_from_children(
        &self,
        value: Value,
        sort: &ArcSort,
        child_candidates: &[Arc<DagCandidate<C>>],
        marginal_cost: C,
        producer_row: Option<ProducerRowId>,
    ) -> Option<Arc<DagCandidate<C>>> {
        let key = self.reachable_cost_key(sort, value)?;
        let root_was_reachable = child_candidates
            .iter()
            .any(|candidate| candidate.paid_costs.contains(key));

        let biggest_choices = child_candidates
            .iter()
            .max_by_key(|candidate| candidate.producer_choices.len());
        let mut producer_choices = biggest_choices
            .map(|candidate| candidate.producer_choices.clone())
            .unwrap_or_default();
        // Variant extraction merges these plans repeatedly. Reserving the
        // upper bound on distinct keys avoids growth while inserting the
        // smaller plans and improved the variants benchmark by about 2.7%.
        let choices_capacity = child_candidates
            .iter()
            .map(|candidate| candidate.producer_choices.len())
            .sum::<usize>()
            .saturating_add(usize::from(producer_row.is_some()))
            .min(self.key_ids.len());
        producer_choices.reserve(choices_capacity.saturating_sub(producer_choices.len()));

        // Each child plan is transitively closed. Keeping the existing choice
        // on overlaps preserves that closure: newly added rows may point into
        // the existing plan, but existing rows cannot point to a newly added
        // key that was absent from their own closed plan.
        let mut conflict = false;
        for candidate in child_candidates {
            if biggest_choices.is_some_and(|biggest| Arc::ptr_eq(biggest, candidate)) {
                continue;
            }
            for (&dependency, &choice) in &candidate.producer_choices {
                match producer_choices.entry(dependency) {
                    Entry::Vacant(entry) => {
                        entry.insert(choice);
                    }
                    Entry::Occupied(entry) if *entry.get() == choice => {}
                    Entry::Occupied(_) => conflict = true,
                }
            }
        }

        // A child reaching this root is usually a cycle. A producer conflict
        // can remove that path, however, so let exact rescoring decide after
        // conflicting child snapshots have been reconciled.
        if root_was_reachable && !conflict {
            return None;
        }

        if let Some(producer_row) = producer_row {
            let previous = producer_choices.insert(key, producer_row);
            debug_assert!(previous.is_none() || root_was_reachable);
        }

        if conflict {
            return self
                .rescore_producer_plan(value, sort, &producer_choices)
                .map(Arc::new);
        }

        let child_costs: Vec<_> = child_candidates
            .iter()
            .map(|candidate| &candidate.paid_costs)
            .collect();
        let mut paid_costs = PaidDagCosts::union_by_cloning_largest(&self.key_ids, &child_costs, 1);
        paid_costs.insert_if_absent(key, marginal_cost);

        Some(Arc::new(DagCandidate {
            paid_costs,
            producer_choices,
        }))
    }

    /// Recompute the exact paid closure for a reconciled producer plan.
    ///
    /// Rescoring traverses the fixed plan once, rejecting cycles and collecting
    /// each reachable dependency's marginal cost. The traversal state is local
    /// because separate calls can choose different producers for the same key.
    fn rescore_producer_plan(
        &self,
        value: Value,
        sort: &ArcSort,
        producer_choices: &ProducerPlan,
    ) -> Option<DagCandidate<C>> {
        enum Task {
            Enter(ArcSort, Value),
            Exit(InternId<DagCostKey>, Option<ProducerRowId>),
        }

        let mut tasks = vec![Task::Enter(sort.clone(), value)];
        let mut visiting = self.key_ids.secondary_set();
        let mut used_choices = HashMap::default();
        let mut paid_costs = self.key_ids.aggregated_map_with_capacity(0);

        while let Some(task) = tasks.pop() {
            match task {
                Task::Enter(sort, value) => {
                    let key = self.reachable_cost_key(&sort, value)?;
                    if paid_costs.contains(key) {
                        continue;
                    }
                    if !visiting.insert(key) {
                        return None;
                    }

                    let (producer_row_id, children) = if sort.is_container_sort() {
                        (None, self.egraph.container_inner_values(&sort, value))
                    } else if sort.is_eq_sort() {
                        let producer_row_id = *producer_choices.get(&key)?;
                        let producer_row = &self.producer_rows.rows[producer_row_id.0];
                        let func = producer_row.func;
                        debug_assert!(producer_row.target == key);
                        (
                            Some(producer_row_id),
                            func.func_type()
                                .input
                                .iter()
                                .cloned()
                                .zip(producer_row.children.iter().copied())
                                .collect(),
                        )
                    } else {
                        (None, Vec::new())
                    };

                    tasks.push(Task::Exit(key, producer_row_id));
                    tasks.extend(
                        children
                            .into_iter()
                            .rev()
                            .map(|(sort, value)| Task::Enter(sort, value)),
                    );
                }
                Task::Exit(key, producer_row_id) => {
                    visiting.remove(key);
                    let marginal_cost = if let Some(producer_row_id) = producer_row_id {
                        used_choices.insert(key, producer_row_id);
                        self.producer_rows.rows[producer_row_id.0].cost.clone()
                    } else {
                        self.structural_costs.get(key)?.clone()
                    };
                    paid_costs.insert_if_absent(key, marginal_cost);
                }
            }
        }

        Some(DagCandidate {
            paid_costs,
            producer_choices: used_choices,
        })
    }

    fn compute_cost_node(&self, value: Value, sort: &ArcSort) -> Option<Arc<DagCandidate<C>>> {
        stacker::maybe_grow(STACK_RED_ZONE, STACK_SEGMENT_SIZE, || {
            if sort.is_container_sort() {
                let key = self.reachable_cost_key(sort, value)?;
                let elements = self.egraph.container_inner_values(sort, value);
                let child_candidates = elements
                    .iter()
                    .map(|(child_sort, child_value)| {
                        self.compute_cost_node(*child_value, child_sort)
                    })
                    .collect::<Option<Vec<_>>>()?;

                let container_self_cost = self.structural_costs.get(key)?.clone();
                self.candidate_from_children(
                    value,
                    sort,
                    &child_candidates,
                    container_self_cost,
                    None,
                )
            } else if sort.is_eq_sort() {
                let key = self.reachable_cost_key(sort, value)?;
                self.best_candidates.get(key).cloned()
            } else {
                let key = self.reachable_cost_key(sort, value)?;
                self.candidate_from_children(
                    value,
                    sort,
                    &[],
                    self.structural_costs.get(key)?.clone(),
                    None,
                )
            }
        })
    }

    fn compute_cost_hyperedge(
        &self,
        producer_row_id: ProducerRowId,
    ) -> Option<Arc<DagCandidate<C>>> {
        let producer_row = &self.producer_rows.rows[producer_row_id.0];
        let func = producer_row.func;
        let child_candidates = producer_row
            .children
            .iter()
            .zip(func.func_type().input.iter())
            .map(|(value, sort)| self.compute_cost_node(*value, sort))
            .collect::<Option<Vec<_>>>()?;

        self.candidate_from_children(
            producer_row.eclass,
            &func.func_type().output,
            &child_candidates,
            producer_row.cost.clone(),
            Some(producer_row_id),
        )
    }

    /// Recompute one producer row and update its target if it improves.
    fn update_from_producer_row(
        &mut self,
        producer_row_id: ProducerRowId,
        pending: &mut VecDeque<InternId<DagCostKey>>,
        pending_set: &mut SecondarySet<DagCostKey>,
    ) -> bool {
        let target_key = self.producer_rows.rows[producer_row_id.0].target;
        let Some(new_candidate) = self.compute_cost_hyperedge(producer_row_id) else {
            return false;
        };

        let should_update = match self.best_candidates.get(target_key) {
            Some(old_best) => new_candidate.paid_costs.total() < old_best.paid_costs.total(),
            None => true,
        };

        if should_update {
            self.best_candidates.insert(target_key, new_candidate);
            if pending_set.insert(target_key) {
                pending.push_back(target_key);
            }
        }

        should_update
    }

    /// Compute greedy-DAG choices for all reachable eq-sort values.
    ///
    /// The initial pass tries every reachable producer row once. Whenever a row
    /// improves the best cost set for its target `(sort, value)`, that target is
    /// queued as a changed dependency. The worklist then revisits only producer
    /// rows that mention changed dependencies, which avoids repeatedly scanning
    /// unrelated backend rows. Debug builds finish with a full pass to assert
    /// that the reverse dependency index did not miss any improving row.
    fn greedy_dag(&mut self) {
        let mut pending = VecDeque::new();
        let mut pending_set = self.key_ids.secondary_set();

        for producer_row_id in 0..self.producer_rows.rows.len() {
            self.update_from_producer_row(
                ProducerRowId(producer_row_id),
                &mut pending,
                &mut pending_set,
            );
        }

        while let Some(key) = pending.pop_front() {
            pending_set.remove(key);
            let Some(producer_row_ids) = self.producer_rows.by_dependency.get(key).cloned() else {
                continue;
            };
            for producer_row_id in producer_row_ids {
                self.update_from_producer_row(producer_row_id, &mut pending, &mut pending_set);
            }
        }

        #[cfg(debug_assertions)]
        {
            let mut pending = VecDeque::new();
            let mut pending_set = self.key_ids.secondary_set();
            for producer_row_id in 0..self.producer_rows.rows.len() {
                assert!(
                    !self.update_from_producer_row(
                        ProducerRowId(producer_row_id),
                        &mut pending,
                        &mut pending_set
                    ),
                    "greedy-DAG producer-row worklist missed a reachable update"
                );
            }
        }
    }

    /// Reconstruct one selected producer plan into the shared term DAG.
    fn reconstruct_termdag_node_helper<N: Clone>(
        &self,
        value: Value,
        sort: &ArcSort,
        state: &mut TermReconstructionState<'_, C, N>,
    ) -> Result<Option<(TermId, N)>, Error> {
        stacker::maybe_grow(STACK_RED_ZONE, STACK_SEGMENT_SIZE, || {
            let Some(key) = self.reachable_cost_key(sort, value) else {
                return Ok(None);
            };
            if let Some(result) = state.cache.get(&key) {
                return Ok(Some(result.clone()));
            }
            if !state.visiting.insert(key) {
                return Ok(None);
            }

            let mut children = Vec::new();
            let term = if sort.is_container_sort() {
                let elements = self.egraph.container_inner_values(sort, value);
                let mut ch_terms: Vec<TermId> = Vec::new();
                for ch in elements.iter() {
                    let Some((term, node)) =
                        self.reconstruct_termdag_node_helper(ch.1, &ch.0, state)?
                    else {
                        return Ok(None);
                    };
                    ch_terms.push(term);
                    children.push(node);
                }
                self.egraph
                    .reconstruct_container_value(sort, value, state.termdag, ch_terms)
            } else if sort.is_eq_sort() {
                let Some(producer_row_id) = state.candidate.producer_choices.get(&key) else {
                    return Ok(None);
                };
                let producer_row = &self.producer_rows.rows[producer_row_id.0];
                let mut child_terms = Vec::with_capacity(producer_row.children.len());
                for (child, child_sort) in producer_row
                    .children
                    .iter()
                    .zip(producer_row.func.func_type().input.iter())
                {
                    let Some((term, node)) =
                        self.reconstruct_termdag_node_helper(*child, child_sort, state)?
                    else {
                        return Ok(None);
                    };
                    child_terms.push(term);
                    children.push(node);
                }
                state
                    .termdag
                    .app(producer_row.func.name().to_owned(), child_terms)
            } else {
                self.egraph
                    .reconstruct_base_value(sort, value, state.termdag)
            };

            let node = (state.observe)(state.termdag, term, sort, value, &children)?;
            state.visiting.remove(key);
            state.cache.insert(key, (term, node.clone()));
            Ok(Some((term, node)))
        })
    }

    /// Extract the best greedy-DAG term of a value from a given sort.
    fn extract_best_with_sort<N: Clone>(
        &self,
        termdag: &mut TermDag,
        value: Value,
        sort: ArcSort,
        observe: &mut impl FnMut(&TermDag, TermId, &ArcSort, Value, &[N]) -> Result<N, Error>,
    ) -> Result<Option<(ExtractedTerm<C>, N)>, Error> {
        let Some(candidate) = self.compute_cost_node(value, &sort) else {
            return Ok(None);
        };
        let mut state = TermReconstructionState {
            termdag,
            candidate: &candidate,
            cache: Default::default(),
            visiting: self.key_ids.secondary_set(),
            observe,
        };
        let Some((term, node)) = self.reconstruct_termdag_node_helper(value, &sort, &mut state)?
        else {
            return Ok(None);
        };
        Ok(Some((
            ExtractedTerm {
                cost: candidate.paid_costs.total().clone(),
                term,
            },
            node,
        )))
    }

    /// Extract root variants of an e-class using greedy-DAG costs.
    ///
    /// This mirrors the tree extractor variant path by ranking root e-nodes.
    /// Each candidate starts from its children's best immutable snapshots;
    /// overlapping producer choices are reconciled and the resulting closed
    /// plan is rescored. This is not a full k-best DAG extractor.
    fn extract_variants_with_sort<N: Clone>(
        &self,
        termdag: &mut TermDag,
        value: Value,
        nvariants: usize,
        sort: ArcSort,
        observe: &mut impl FnMut(&TermDag, TermId, &ArcSort, Value, &[N]) -> Result<N, Error>,
    ) -> Result<Vec<(ExtractedTerm<C>, N)>, Error> {
        if nvariants == 0 {
            return Ok(vec![]);
        }

        if sort.is_eq_sort() {
            let Some(target_key) = self.reachable_cost_key(&sort, value) else {
                return Ok(vec![]);
            };
            let best_candidate = self.best_candidates.get(target_key);
            let mut root_variants: Vec<(ProducerRowId, Arc<DagCandidate<C>>)> = Vec::new();

            let by_target = self
                .producer_rows
                .by_target
                .as_ref()
                .expect("target index is built for variant extraction");
            let Some(producer_row_ids) = by_target.get(target_key) else {
                return Ok(vec![]);
            };
            for &producer_row_id in producer_row_ids {
                let candidate = best_candidate
                    .filter(|candidate| {
                        candidate.producer_choices.get(&target_key) == Some(&producer_row_id)
                    })
                    .cloned()
                    .or_else(|| self.compute_cost_hyperedge(producer_row_id));
                if let Some(candidate) = candidate {
                    root_variants.push((producer_row_id, candidate));
                }
            }

            let mut res = Vec::new();
            root_variants.sort_by(|(left_id, left), (right_id, right)| {
                left.paid_costs
                    .total()
                    .cmp(right.paid_costs.total())
                    .then_with(|| left_id.cmp(right_id))
            });
            root_variants.truncate(nvariants);
            for (_, candidate) in root_variants {
                let mut state = TermReconstructionState {
                    termdag,
                    candidate: &candidate,
                    cache: Default::default(),
                    visiting: self.key_ids.secondary_set(),
                    observe,
                };
                if let Some((term, node)) =
                    self.reconstruct_termdag_node_helper(value, &sort, &mut state)?
                {
                    res.push((
                        ExtractedTerm {
                            cost: candidate.paid_costs.total().clone(),
                            term,
                        },
                        node,
                    ));
                }
            }

            Ok(res)
        } else {
            log::warn!(
                "extracting multiple greedy-DAG variants for containers or primitives is not implemented, returning a single variant."
            );
            if let Some(res) = self.extract_best_with_sort(termdag, value, sort, observe)? {
                Ok(vec![res])
            } else {
                Ok(vec![])
            }
        }
    }
}

/// Extract the best greedy-DAG term for each requested `(sort, value)` root.
///
/// Shared subterms are charged once within each root according to the marginal
/// cost model. When a root reaches the same `(sort, value)` through multiple
/// paths, its candidate uses one producer choice for that value. Separate roots
/// are optimized and costed independently and may retain different internally
/// consistent producer snapshots, although reconstruction shares one
/// [`TermDag`].
///
/// This is a greedy heuristic, not a globally optimal DAG extractor.
///
/// `cost_model` must satisfy the stability and algebraic requirements of
/// [`DagCostModel`] and [`MonoidCost`].
///
/// This experimental extractor supports normal constructor tables, not the
/// proof/term-encoding view tables used by proof extraction.
pub fn extract_best_greedy_dag<C: MonoidCost, M: DagCostModel<C>>(
    egraph: &EGraph,
    roots: Vec<(ArcSort, Value)>,
    cost_model: M,
) -> Result<ExtractedTerms<C>, Error> {
    extract_best_greedy_dag_with_observer(egraph, roots, cost_model, |_, _, _, _, _| Ok(()))
        .map(|(extracted, _)| extracted)
}

/// Extracts best terms while observing their selected typed occurrences.
///
/// The observer receives semantic children in native container or constructor
/// order. Each immutable candidate has its own reconstruction cache so roots
/// with different producer plans cannot reuse each other's consumer results.
/// The returned roots retain request order, duplicates and availability, and
/// share one term DAG. Observer failures propagate without being suppressed.
#[allow(clippy::type_complexity)]
pub fn extract_best_greedy_dag_with_observer<C: MonoidCost, M: DagCostModel<C>, N: Clone>(
    egraph: &EGraph,
    roots: Vec<(ArcSort, Value)>,
    cost_model: M,
    mut observe: impl FnMut(&TermDag, TermId, &ArcSort, Value, &[N]) -> Result<N, Error>,
) -> Result<(ExtractedTerms<C>, Vec<Option<N>>), Error> {
    let extractor = GreedyDagExtractor::prepare(egraph, &roots, cost_model, false);
    let mut termdag = TermDag::default();
    let mut terms = Vec::new();
    let mut nodes = Vec::new();
    for (sort, value) in roots {
        let result = extractor.extract_best_with_sort(&mut termdag, value, sort, &mut observe)?;
        match result {
            Some((term, node)) => {
                terms.push(Some(term));
                nodes.push(Some(node));
            }
            None => {
                terms.push(None);
                nodes.push(None);
            }
        }
    }
    Ok((ExtractedTerms { termdag, terms }, nodes))
}

/// Extract up to `nvariants` greedy-DAG root variants for each requested root.
///
/// Variants rank root enodes. Each candidate starts from its children's best
/// immutable snapshots, reconciles overlapping producer choices, and exactly
/// rescores the resulting closed plan. This is not a full k-best or globally
/// optimal DAG extraction. Each variant and requested root is costed
/// independently; sharing in the returned [`TermDag`] does not create a joint
/// multi-root cost.
///
/// `cost_model` must satisfy the stability and algebraic requirements of
/// [`DagCostModel`] and [`MonoidCost`].
///
/// This experimental extractor supports normal constructor tables, not the
/// proof/term-encoding view tables used by proof extraction.
pub fn extract_variants_greedy_dag<C: MonoidCost, M: DagCostModel<C>>(
    egraph: &EGraph,
    roots: Vec<(ArcSort, Value)>,
    nvariants: usize,
    cost_model: M,
) -> Result<ExtractedTermVariants<C>, Error> {
    extract_variants_greedy_dag_with_observer(
        egraph,
        roots,
        nvariants,
        cost_model,
        |_, _, _, _, _| Ok(()),
    )
    .map(|(extracted, _)| extracted)
}

/// Extracts root variants with the typed occurrence contract of
/// [`extract_best_greedy_dag_with_observer`]. Each selected variant retains its
/// own consumer result even when its syntax or typed root equals another.
#[allow(clippy::type_complexity)]
pub fn extract_variants_greedy_dag_with_observer<C: MonoidCost, M: DagCostModel<C>, N: Clone>(
    egraph: &EGraph,
    roots: Vec<(ArcSort, Value)>,
    nvariants: usize,
    cost_model: M,
    mut observe: impl FnMut(&TermDag, TermId, &ArcSort, Value, &[N]) -> Result<N, Error>,
) -> Result<(ExtractedTermVariants<C>, Vec<Vec<N>>), Error> {
    if nvariants == 0 {
        return Ok((
            ExtractedTermVariants {
                termdag: TermDag::default(),
                variants: roots.iter().map(|_| Vec::new()).collect(),
            },
            roots.iter().map(|_| Vec::new()).collect(),
        ));
    }

    let extractor = GreedyDagExtractor::prepare(egraph, &roots, cost_model, true);
    let mut termdag = TermDag::default();
    let mut variants = Vec::new();
    let mut nodes = Vec::new();
    for (sort, value) in roots {
        let (terms, observed) = extractor
            .extract_variants_with_sort(&mut termdag, value, nvariants, sort, &mut observe)?
            .into_iter()
            .unzip();
        variants.push(terms);
        nodes.push(observed);
    }
    Ok((ExtractedTermVariants { termdag, variants }, nodes))
}

#[cfg(test)]
mod observer_tests {
    use super::*;
    use egglog::extract::AdditiveCostModel;

    #[test]
    fn selected_occurrences_keep_semantic_sorts_children_and_root_order() {
        let mut graph = crate::new_experimental_egraph();
        graph
            .parse_and_run_program(None, "(datatype E (N i64) (P E E)) (sort Values (Vec E))")
            .unwrap();
        let roots: Vec<_> = [
            "(P (N 1) (N 1))",
            "(vec-of (N 1) (N 1))",
            "1",
            "(P (N 1) (N 1))",
        ]
        .into_iter()
        .map(|source| {
            let expr = graph.parser.get_expr_from_string(None, source).unwrap();
            graph.eval_expr(&expr).unwrap()
        })
        .collect();
        let mut observed = Vec::new();
        let (extracted, nodes) = extract_best_greedy_dag_with_observer(
            &graph,
            roots.clone(),
            AdditiveCostModel::default(),
            |terms, term, sort, value, children: &[usize]| {
                let index = observed.len();
                observed.push((
                    sort.name().to_owned(),
                    value,
                    children.to_vec(),
                    terms.to_string(term),
                ));
                Ok(index)
            },
        )
        .unwrap();
        assert_eq!(extracted.terms.len(), 4);
        assert_eq!(nodes.len(), 4);
        for ((sort, value), node) in roots.iter().zip(&nodes) {
            let node = &observed[node.unwrap()];
            assert_eq!((&node.0, node.1), (&sort.name().to_owned(), *value));
        }
        for root in [0, 1, 3] {
            let node = &observed[nodes[root].unwrap()];
            assert_eq!(node.2.len(), 2);
            assert_eq!(node.2[0], node.2[1], "candidate-local repeated child cache");
            assert_eq!(observed[node.2[0]].0, "E");
        }
        assert_eq!(observed[nodes[2].unwrap()].0, "i64");
        assert_eq!(
            extracted.terms[0].as_ref().unwrap().term,
            extracted.terms[3].as_ref().unwrap().term,
            "shared forest storage"
        );
        assert_eq!(extracted.terms[0].as_ref().unwrap().cost, 3);
        assert_eq!(extracted.terms[1].as_ref().unwrap().cost, 2);

        let error = extract_best_greedy_dag_with_observer(
            &graph,
            roots.clone(),
            AdditiveCostModel::default(),
            |_, _, _, _, _: &[()]| {
                Err::<(), _>(Error::ExtractError("owned observer failure".into()))
            },
        )
        .unwrap_err();
        assert!(
            matches!(error, Error::ExtractError(message) if message == "owned observer failure")
        );

        let mut calls = 0;
        let (empty, nodes) = extract_variants_greedy_dag_with_observer(
            &graph,
            roots,
            0,
            AdditiveCostModel::default(),
            |_, _, _, _, _: &[()]| {
                calls += 1;
                Ok(())
            },
        )
        .unwrap();
        assert_eq!(calls, 0);
        assert_eq!(empty.variants.len(), 4);
        assert!(empty.variants.iter().all(Vec::is_empty));
        assert!(nodes.iter().all(Vec::is_empty));
    }
}
