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
    ArcSort, EGraph, Enode, Error, Read, TermDag, TermId, Value,
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

/// A constructor's name and its input sorts.
type Constructor = (String, Vec<ArcSort>);

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
struct GreedyDagProducerRow<C> {
    /// Constructor function for this row.
    func_name: String,
    /// Owned child values. Backend row callbacks are borrowed, but the greedy
    /// DAG fixed point revisits producer rows after root discovery.
    children: Vec<Value>,
    /// Canonical e-class produced by this constructor row.
    eclass: Value,
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

/// Mutable state for exact rescoring of one reconciled producer plan.
struct ProducerPlanScoringState<C: MonoidCost> {
    used_choices: ProducerPlan,
    cache: HashMap<InternId<DagCostKey>, Arc<PaidDagCosts<C>>>,
    visiting: SecondarySet<DagCostKey>,
}

/// Mutable state shared by one term reconstruction traversal.
struct TermReconstructionState<'a, C: MonoidCost> {
    termdag: &'a mut TermDag,
    candidate: &'a DagCandidate<C>,
    cache: HashMap<InternId<DagCostKey>, TermId>,
    visiting: SecondarySet<DagCostKey>,
}

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
struct ProducerRows<C> {
    rows: Vec<GreedyDagProducerRow<C>>,
    by_dependency: SecondaryMap<DagCostKey, Vec<ProducerRowId>>,
    by_target: Option<SecondaryMap<DagCostKey, Vec<ProducerRowId>>>,
}

#[derive(Default)]
struct ProducerRowsBuilder {
    rows: Vec<GreedyDagProducerRow<()>>,
    by_dependency: HashMap<InternId<DagCostKey>, Vec<ProducerRowId>>,
    by_target: Option<HashMap<InternId<DagCostKey>, Vec<ProducerRowId>>>,
}

impl ProducerRowsBuilder {
    fn push(
        &mut self,
        row: GreedyDagProducerRow<()>,
        target: InternId<DagCostKey>,
        dependencies: impl IntoIterator<Item = InternId<DagCostKey>>,
    ) {
        let row_id = ProducerRowId(self.rows.len());
        self.rows.push(row);
        if let Some(by_target) = &mut self.by_target {
            by_target.entry(target).or_default().push(row_id);
        }
        for dependency in dependencies {
            self.by_dependency
                .entry(dependency)
                .or_default()
                .push(row_id);
        }
    }

    fn freeze<C: MonoidCost, M: DagCostModel<C>>(
        self,
        egraph: &EGraph,
        cost_model: &M,
        key_ids: &Interner<DagCostKey>,
    ) -> ProducerRows<C> {
        let mut by_dependency = key_ids.secondary_map();
        for (key, producer_row_ids) in self.by_dependency {
            by_dependency.insert(key, producer_row_ids);
        }
        let by_target = self.by_target.map(|rows| {
            let mut by_target = key_ids.secondary_map();
            for (key, producer_row_ids) in rows {
                by_target.insert(key, producer_row_ids);
            }
            by_target
        });
        let rows = self
            .rows
            .into_iter()
            .map(|row| {
                let func = egraph
                    .get_function(&row.func_name)
                    .expect("producer constructor came from the egraph");
                let enode = Enode {
                    name: func.name(),
                    children: &row.children,
                    eclass: row.eclass,
                    subsumed: false,
                };
                let cost = cost_model.enode_cost(egraph, func, &enode);
                GreedyDagProducerRow {
                    func_name: row.func_name,
                    children: row.children,
                    eclass: row.eclass,
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
struct GreedyDagExtractor<C: MonoidCost> {
    /// Sort-name interner used only to build compact [`DagCostKey`]s.
    sort_ids: Interner<String>,
    /// Dense id-space for every reachable dependency that can be charged once.
    key_ids: Interner<DagCostKey>,

    /// Reachable producer rows and the reverse index used by the worklist.
    producer_rows: ProducerRows<C>,

    /// Cached marginal costs for reachable primitive and container values.
    structural_costs: SecondaryMap<DagCostKey, C>,

    /// Best known greedy-DAG candidate for each reachable eq-sort value.
    ///
    /// Only eq-sort values get entries here; primitive and container values
    /// are computed structurally.
    best_candidates: SecondaryMap<DagCostKey, Arc<DagCandidate<C>>>,
}

struct ReachableExtractionBuilder {
    /// Growable sort-name interner used while discovering reachable values.
    sort_ids: InternerBuilder<String>,
    /// Growable id-space for reachable `(sort, value)` dependencies.
    key_ids: InternerBuilder<DagCostKey>,
    /// Reachable producer rows and their reverse dependency index.
    producer_rows: ProducerRowsBuilder,
    /// Unique reachable primitive and container values to cost after discovery.
    structural_nodes: HashMap<InternId<DagCostKey>, (ArcSort, Value)>,
    /// Deduplication set for reachable eq-sort values.
    seen_eq_values: HashSet<InternId<DagCostKey>>,
    /// Constructors by output sort name, in `functions_iter()` order, computed
    /// once from the whole e-graph before traversal starts.
    constructors_by_sort: HashMap<String, Arc<[Constructor]>>,
}

impl ReachableExtractionBuilder {
    fn intern_key(&mut self, sort_name: &str, value: Value) -> InternId<DagCostKey> {
        let sort_id = self
            .sort_ids
            .get(sort_name)
            .unwrap_or_else(|| self.sort_ids.intern(sort_name.to_owned()));
        self.key_ids.intern(DagCostKey { sort_id, value })
    }

    fn intern_nested_eq_dependencies(
        &mut self,
        egraph: &EGraph,
        sort: &ArcSort,
        value: Value,
        dependencies: &mut HashSet<InternId<DagCostKey>>,
    ) {
        let mut pending = vec![(sort.clone(), value)];
        while let Some((sort, value)) = pending.pop() {
            if sort.is_container_sort() {
                pending.extend(
                    egraph
                        .container_inner_values(&sort, value)
                        .into_iter()
                        .rev(),
                );
            } else if sort.is_eq_sort() {
                dependencies.insert(self.intern_key(sort.name(), value));
            }
        }
    }

    fn discover_node(&mut self, egraph: &EGraph, sort: &ArcSort, value: Value) {
        let key = self.intern_key(sort.name(), value);

        if !sort.is_eq_sort() {
            self.structural_nodes
                .entry(key)
                .or_insert_with(|| (sort.clone(), value));
        }

        if sort.is_container_sort() {
            for (child_sort, child_value) in egraph.container_inner_values(sort, value) {
                self.discover_node(egraph, &child_sort, child_value);
            }
            return;
        }

        if !sort.is_eq_sort() || !self.seen_eq_values.insert(key) {
            return;
        }

        let Some(constructors) = self.constructors_by_sort.get(sort.name()).cloned() else {
            return;
        };

        for (func_name, input_sorts) in constructors.iter() {
            let mut rows = Vec::new();
            egraph
                .read(|rs| {
                    rs.constructor_enodes_for_eclass(func_name, value, |enode| {
                        if !enode.subsumed {
                            rows.push(enode.children.to_vec());
                        }
                    })
                })
                .expect("constructor name came from the egraph");

            for children in rows {
                let mut child_nodes = Vec::with_capacity(children.len());
                let mut dependencies = HashSet::default();
                for (child_value, child_sort) in children.iter().zip(input_sorts.iter()) {
                    self.intern_nested_eq_dependencies(
                        egraph,
                        child_sort,
                        *child_value,
                        &mut dependencies,
                    );
                    child_nodes.push((child_sort.clone(), *child_value));
                }
                self.producer_rows.push(
                    GreedyDagProducerRow {
                        func_name: func_name.clone(),
                        children,
                        eclass: value,
                        cost: (),
                    },
                    key,
                    dependencies,
                );

                for (child_sort, child_value) in child_nodes {
                    self.discover_node(egraph, &child_sort, child_value);
                }
            }
        }
    }
}

impl<C: MonoidCost> GreedyDagExtractor<C> {
    fn prepare<M: DagCostModel<C>>(
        egraph: &EGraph,
        roots: &[(ArcSort, Value)],
        cost_model: M,
        index_targets: bool,
    ) -> Self {
        // Build the root-local problem: collect extractable functions, intern
        // reachable `(sort, value)` dependencies, and record producer rows with
        // their reverse dependency edges.
        let mut constructors_by_sort: HashMap<String, Vec<Constructor>> = HashMap::default();
        for (func_name, func) in egraph.functions_iter() {
            if func.func_type().subtype == FunctionSubtype::Constructor
                && !func.is_hidden()
                && !func.is_unextractable()
            {
                constructors_by_sort
                    .entry(func.func_type().output.name().to_owned())
                    .or_default()
                    .push((func_name.clone(), func.func_type().input.clone()));
            }
        }

        let mut builder = ReachableExtractionBuilder {
            sort_ids: Default::default(),
            key_ids: Default::default(),
            producer_rows: ProducerRowsBuilder {
                by_target: index_targets.then(HashMap::default),
                ..Default::default()
            },
            structural_nodes: Default::default(),
            seen_eq_values: Default::default(),
            constructors_by_sort: constructors_by_sort
                .into_iter()
                .map(|(sort, funcs)| (sort, funcs.into()))
                .collect(),
        };

        for (sort, value) in roots {
            builder.discover_node(egraph, sort, *value);
        }

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
            sort_ids,
            key_ids,
            producer_rows,
            structural_costs,
            best_candidates,
        };

        extractor.greedy_dag(egraph);
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
        egraph: &EGraph,
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
                .rescore_producer_plan(egraph, value, sort, &producer_choices)
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
    /// The cache lives for one call and is intentionally not hoisted across
    /// calls. Results are keyed by `(sort, value)` but decided by this call's
    /// `producer_choices`, which `candidate_from_children` rebuilds per call
    /// from `best_candidates` snapshots that keep changing until the fixed
    /// point converges. Two calls in one run can therefore resolve the same key
    /// to different producer rows, so a shared cache would score a plan against
    /// choices it did not make.
    fn rescore_producer_plan(
        &self,
        egraph: &EGraph,
        value: Value,
        sort: &ArcSort,
        producer_choices: &ProducerPlan,
    ) -> Option<DagCandidate<C>> {
        let mut state = ProducerPlanScoringState {
            used_choices: HashMap::default(),
            cache: HashMap::default(),
            visiting: self.key_ids.secondary_set(),
        };
        let paid_costs =
            self.rescore_producer_plan_node(egraph, value, sort, producer_choices, &mut state)?;

        let ProducerPlanScoringState {
            used_choices,
            cache,
            ..
        } = state;
        drop(cache);
        let paid_costs = Arc::try_unwrap(paid_costs).unwrap_or_else(|costs| costs.as_ref().clone());
        Some(DagCandidate {
            paid_costs,
            producer_choices: used_choices,
        })
    }

    fn rescore_producer_plan_node(
        &self,
        egraph: &EGraph,
        value: Value,
        sort: &ArcSort,
        producer_choices: &ProducerPlan,
        state: &mut ProducerPlanScoringState<C>,
    ) -> Option<Arc<PaidDagCosts<C>>> {
        let key = self.reachable_cost_key(sort, value)?;
        if let Some(costs) = state.cache.get(&key) {
            return Some(costs.clone());
        }
        if !state.visiting.insert(key) {
            return None;
        }

        let (child_costs, marginal_cost) = if sort.is_container_sort() {
            let mut child_costs = Vec::new();
            for (child_sort, child_value) in egraph.container_inner_values(sort, value) {
                child_costs.push(self.rescore_producer_plan_node(
                    egraph,
                    child_value,
                    &child_sort,
                    producer_choices,
                    state,
                )?);
            }
            (child_costs, self.structural_costs.get(key)?.clone())
        } else if sort.is_eq_sort() {
            let producer_row_id = *producer_choices.get(&key)?;
            let producer_row = &self.producer_rows.rows[producer_row_id.0];
            let func = egraph.get_function(&producer_row.func_name)?;
            if producer_row.eclass != value || func.func_type().output.name() != sort.name() {
                return None;
            }
            state.used_choices.insert(key, producer_row_id);

            let mut child_costs = Vec::new();
            for (child_value, child_sort) in producer_row
                .children
                .iter()
                .zip(func.func_type().input.iter())
            {
                child_costs.push(self.rescore_producer_plan_node(
                    egraph,
                    *child_value,
                    child_sort,
                    producer_choices,
                    state,
                )?);
            }
            (child_costs, producer_row.cost.clone())
        } else {
            (Vec::new(), self.structural_costs.get(key)?.clone())
        };

        let mut paid_costs = PaidDagCosts::union_by_cloning_largest(&self.key_ids, &child_costs, 1);
        paid_costs.insert_if_absent(key, marginal_cost);
        let paid_costs = Arc::new(paid_costs);
        state.visiting.remove(key);
        state.cache.insert(key, paid_costs.clone());
        Some(paid_costs)
    }

    fn compute_cost_node(
        &self,
        egraph: &EGraph,
        value: Value,
        sort: &ArcSort,
    ) -> Option<Arc<DagCandidate<C>>> {
        if sort.is_container_sort() {
            let key = self.reachable_cost_key(sort, value)?;
            let elements = egraph.container_inner_values(sort, value);
            let child_candidates = elements
                .iter()
                .map(|(child_sort, child_value)| {
                    self.compute_cost_node(egraph, *child_value, child_sort)
                })
                .collect::<Option<Vec<_>>>()?;

            let container_self_cost = self.structural_costs.get(key)?.clone();
            self.candidate_from_children(
                egraph,
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
                egraph,
                value,
                sort,
                &[],
                self.structural_costs.get(key)?.clone(),
                None,
            )
        }
    }

    fn compute_cost_hyperedge(
        &self,
        egraph: &EGraph,
        producer_row_id: ProducerRowId,
    ) -> Option<Arc<DagCandidate<C>>> {
        let producer_row = &self.producer_rows.rows[producer_row_id.0];
        let func = egraph.get_function(&producer_row.func_name)?;
        let child_candidates = producer_row
            .children
            .iter()
            .zip(func.func_type().input.iter())
            .map(|(value, sort)| self.compute_cost_node(egraph, *value, sort))
            .collect::<Option<Vec<_>>>()?;

        self.candidate_from_children(
            egraph,
            producer_row.eclass,
            &func.func_type().output,
            &child_candidates,
            producer_row.cost.clone(),
            Some(producer_row_id),
        )
    }

    /// Enqueue a changed dependency once until it is processed.
    fn enqueue_if_absent(
        pending: &mut VecDeque<InternId<DagCostKey>>,
        pending_set: &mut SecondarySet<DagCostKey>,
        key: InternId<DagCostKey>,
    ) {
        if pending_set.insert(key) {
            pending.push_back(key);
        }
    }

    /// Recompute one producer row and update its target if it improves.
    fn update_from_producer_row(
        &mut self,
        egraph: &EGraph,
        producer_row_id: ProducerRowId,
        pending: &mut VecDeque<InternId<DagCostKey>>,
        pending_set: &mut SecondarySet<DagCostKey>,
    ) -> bool {
        let Some((new_candidate, target_key)) = ({
            let producer_row = &self.producer_rows.rows[producer_row_id.0];
            let func = egraph.get_function(&producer_row.func_name).unwrap();
            let target_sort = &func.func_type().output;
            let target = producer_row.eclass;
            let Some(target_key) = self.reachable_cost_key(target_sort, target) else {
                return false;
            };
            self.compute_cost_hyperedge(egraph, producer_row_id)
                .map(|candidate| (candidate, target_key))
        }) else {
            return false;
        };

        let should_update = match self.best_candidates.get(target_key) {
            Some(old_best) => new_candidate.paid_costs.total() < old_best.paid_costs.total(),
            None => true,
        };

        if should_update {
            self.best_candidates.insert(target_key, new_candidate);
            Self::enqueue_if_absent(pending, pending_set, target_key);
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
    fn greedy_dag(&mut self, egraph: &EGraph) {
        let mut pending = VecDeque::new();
        let mut pending_set = self.key_ids.secondary_set();

        for producer_row_id in 0..self.producer_rows.rows.len() {
            self.update_from_producer_row(
                egraph,
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
                self.update_from_producer_row(
                    egraph,
                    producer_row_id,
                    &mut pending,
                    &mut pending_set,
                );
            }
        }

        #[cfg(debug_assertions)]
        {
            let mut pending = VecDeque::new();
            let mut pending_set = self.key_ids.secondary_set();
            for producer_row_id in 0..self.producer_rows.rows.len() {
                assert!(
                    !self.update_from_producer_row(
                        egraph,
                        ProducerRowId(producer_row_id),
                        &mut pending,
                        &mut pending_set
                    ),
                    "greedy-DAG producer-row worklist missed a reachable update"
                );
            }
        }
    }

    /// Reconstruct the term rooted at a producer row, reusing the caller's cache.
    fn reconstruct_producer_row(
        &self,
        egraph: &EGraph,
        producer_row: &GreedyDagProducerRow<C>,
        state: &mut TermReconstructionState<'_, C>,
    ) -> Option<TermId> {
        let func = egraph.get_function(&producer_row.func_name).unwrap();
        let mut ch_terms: Vec<TermId> = Vec::new();
        for (value, sort) in producer_row
            .children
            .iter()
            .zip(func.func_type().input.iter())
        {
            ch_terms.push(self.reconstruct_termdag_node_helper(egraph, *value, sort, state)?);
        }
        Some(state.termdag.app(func.name().to_owned(), ch_terms))
    }

    fn reconstruct_termdag_node_helper(
        &self,
        egraph: &EGraph,
        value: Value,
        sort: &ArcSort,
        state: &mut TermReconstructionState<'_, C>,
    ) -> Option<TermId> {
        let key = self.reachable_cost_key(sort, value)?;
        if let Some(term) = state.cache.get(&key) {
            return Some(*term);
        }
        if !state.visiting.insert(key) {
            return None;
        }

        let term = if sort.is_container_sort() {
            let elements = egraph.container_inner_values(sort, value);
            let mut ch_terms: Vec<TermId> = Vec::new();
            for ch in elements.iter() {
                ch_terms.push(self.reconstruct_termdag_node_helper(egraph, ch.1, &ch.0, state)?);
            }
            egraph.reconstruct_container_value(sort, value, state.termdag, ch_terms)
        } else if sort.is_eq_sort() {
            let producer_row_id = state.candidate.producer_choices.get(&key)?;
            let producer_row = &self.producer_rows.rows[producer_row_id.0];
            self.reconstruct_producer_row(egraph, producer_row, state)?
        } else {
            egraph.reconstruct_base_value(sort, value, state.termdag)
        };

        state.visiting.remove(key);
        state.cache.insert(key, term);
        Some(term)
    }

    /// Extract the best greedy-DAG term of a value from a given sort.
    fn extract_best_with_sort(
        &self,
        egraph: &EGraph,
        termdag: &mut TermDag,
        value: Value,
        sort: ArcSort,
    ) -> Option<ExtractedTerm<C>> {
        let candidate = self.compute_cost_node(egraph, value, &sort)?;
        let mut state = TermReconstructionState {
            termdag,
            candidate: &candidate,
            cache: Default::default(),
            visiting: self.key_ids.secondary_set(),
        };
        let term = self.reconstruct_termdag_node_helper(egraph, value, &sort, &mut state)?;
        Some(ExtractedTerm {
            cost: candidate.paid_costs.total().clone(),
            term,
        })
    }

    /// Extract root variants of an e-class using greedy-DAG costs.
    ///
    /// This mirrors the tree extractor variant path by ranking root e-nodes.
    /// Each candidate starts from its children's best immutable snapshots;
    /// overlapping producer choices are reconciled and the resulting closed
    /// plan is rescored. This is not a full k-best DAG extractor.
    fn extract_variants_with_sort(
        &self,
        egraph: &EGraph,
        termdag: &mut TermDag,
        value: Value,
        nvariants: usize,
        sort: ArcSort,
    ) -> Vec<ExtractedTerm<C>> {
        if nvariants == 0 {
            return vec![];
        }

        if sort.is_eq_sort() {
            let Some(target_key) = self.reachable_cost_key(&sort, value) else {
                return vec![];
            };
            let best_candidate = self.best_candidates.get(target_key);
            let mut root_variants: Vec<(ProducerRowId, Arc<DagCandidate<C>>)> = Vec::new();

            let by_target = self
                .producer_rows
                .by_target
                .as_ref()
                .expect("target index is built for variant extraction");
            let Some(producer_row_ids) = by_target.get(target_key) else {
                return vec![];
            };
            for &producer_row_id in producer_row_ids {
                let producer_row = &self.producer_rows.rows[producer_row_id.0];
                let func = egraph.get_function(&producer_row.func_name).unwrap();
                let target_sort = &func.func_type().output;
                if sort.name() != target_sort.name() {
                    continue;
                }
                if producer_row.eclass != value {
                    continue;
                }
                let candidate = best_candidate
                    .filter(|candidate| {
                        candidate.producer_choices.get(&target_key) == Some(&producer_row_id)
                    })
                    .cloned()
                    .or_else(|| self.compute_cost_hyperedge(egraph, producer_row_id));
                if let Some(candidate) = candidate {
                    root_variants.push((producer_row_id, candidate));
                }
            }

            let mut res: Vec<ExtractedTerm<C>> = Vec::new();
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
                };
                if let Some(term) =
                    self.reconstruct_termdag_node_helper(egraph, value, &sort, &mut state)
                {
                    res.push(ExtractedTerm {
                        cost: candidate.paid_costs.total().clone(),
                        term,
                    });
                }
            }

            res
        } else {
            log::warn!(
                "extracting multiple greedy-DAG variants for containers or primitives is not implemented, returning a single variant."
            );
            if let Some(res) = self.extract_best_with_sort(egraph, termdag, value, sort) {
                vec![res]
            } else {
                vec![]
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
    let extractor = GreedyDagExtractor::prepare(egraph, &roots, cost_model, false);
    let mut termdag = TermDag::default();
    let extracted_roots = roots
        .into_iter()
        .map(|(sort, value)| extractor.extract_best_with_sort(egraph, &mut termdag, value, sort))
        .collect();

    Ok(ExtractedTerms {
        termdag,
        terms: extracted_roots,
    })
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
    if nvariants == 0 {
        return Ok(ExtractedTermVariants {
            termdag: TermDag::default(),
            variants: roots.iter().map(|_| Vec::new()).collect(),
        });
    }

    let extractor = GreedyDagExtractor::prepare(egraph, &roots, cost_model, true);
    let mut termdag = TermDag::default();
    let variants = roots
        .into_iter()
        .map(|(sort, value)| {
            extractor.extract_variants_with_sort(egraph, &mut termdag, value, nvariants, sort)
        })
        .collect();

    Ok(ExtractedTermVariants { termdag, variants })
}
