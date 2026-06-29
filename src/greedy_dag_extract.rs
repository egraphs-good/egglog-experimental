use crate::secondary_map::{
    AggregatedSparseSecondaryMap, InternId, Interner, InternerBuilder, SecondaryMap, SecondarySet,
};
use egglog::{
    ArcSort, EGraph, Enode, Error, Function, Read, TermDag, TermId, Value,
    ast::{Expr, ParseError},
    extract::{
        BaseCostModel, Cost, DefaultCost, ExtractedTerm, ExtractedTermVariants, ExtractedTerms,
        TreeAdditiveCostModel, TreeCostModel,
    },
};
use std::collections::VecDeque;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::sync::Arc;

/// An interface for DAG extraction cost models.
///
/// DAG extraction charges each selected `(sort, value)` dependency once, so it
/// requires marginal costs for adding a single unique node.
pub trait DagCostModel<C: Cost>: BaseCostModel<C> {
    /// The marginal cost of adding this e-node, not including child costs.
    ///
    /// `child_costs` gives the selected child DAG costs for context.
    fn marginal_enode_cost(
        &self,
        egraph: &EGraph,
        func: &Function,
        enode: &Enode<'_>,
        child_costs: &[C],
    ) -> C;

    /// The marginal cost of adding this container value, not including elements.
    ///
    /// The default is the identity cost, matching the default total container
    /// cost of just combining the elements.
    fn marginal_container_cost(
        &self,
        egraph: &EGraph,
        sort: &ArcSort,
        value: Value,
        element_costs: &[C],
    ) -> C {
        let _egraph = egraph;
        let _sort = sort;
        let _value = value;
        let _element_costs = element_costs;
        C::identity()
    }
}

// `TreeCostModel` lives in core egglog, so Rust's orphan rules do not let this
// crate blanket-implement it for every `M: DagCostModel`. Use a local adapter
// when the tree extractor should derive total costs from marginal DAG costs.
struct TreeCostModelFromDag<M>(M);

impl<C: Cost, M: DagCostModel<C>> BaseCostModel<C> for TreeCostModelFromDag<M> {
    fn base_value_cost(&self, egraph: &EGraph, sort: &ArcSort, value: Value) -> C {
        self.0.base_value_cost(egraph, sort, value)
    }
}

impl<C: Cost, M: DagCostModel<C>> TreeCostModel<C> for TreeCostModelFromDag<M> {
    fn total_enode_cost(
        &self,
        egraph: &EGraph,
        func: &Function,
        enode: &Enode<'_>,
        child_costs: &[C],
    ) -> C {
        child_costs.iter().fold(
            self.0.marginal_enode_cost(egraph, func, enode, child_costs),
            |cost, child| cost.combine(child),
        )
    }

    fn total_container_cost(
        &self,
        egraph: &EGraph,
        sort: &ArcSort,
        value: Value,
        element_costs: &[C],
    ) -> C {
        element_costs.iter().fold(
            self.0
                .marginal_container_cost(egraph, sort, value, element_costs),
            |cost, child| cost.combine(child),
        )
    }
}

impl DagCostModel<DefaultCost> for TreeAdditiveCostModel {
    fn marginal_enode_cost(
        &self,
        egraph: &EGraph,
        func: &Function,
        enode: &Enode<'_>,
        _child_costs: &[DefaultCost],
    ) -> DefaultCost {
        TreeCostModel::total_enode_cost(self, egraph, func, enode, &[])
    }
}

pub(crate) fn parse_extractor_keyword(keyword: &Expr, extractor: &Expr) -> Result<bool, Error> {
    match keyword {
        Expr::Var(_, keyword) if keyword == ":extractor" => parse_use_greedy_dag(extractor),
        _ => Err(Error::ParseError(ParseError(
            keyword.span(),
            "expected :extractor".into(),
        ))),
    }
}

pub(crate) fn split_trailing_extractor(args: &[Expr]) -> Result<(&[Expr], bool), Error> {
    let Some(idx) = args
        .iter()
        .position(|arg| matches!(arg, Expr::Var(_, keyword) if keyword == ":extractor"))
    else {
        return Ok((args, false));
    };

    if idx + 2 != args.len() {
        return Err(Error::ParseError(ParseError(
            args[idx].span(),
            "expected trailing :extractor <name>".into(),
        )));
    }

    Ok((&args[..idx], parse_use_greedy_dag(&args[idx + 1])?))
}

fn parse_use_greedy_dag(arg: &Expr) -> Result<bool, Error> {
    match arg {
        Expr::Var(_, name) if name == "greedy-dag" => Ok(true),
        Expr::Var(_, name) => Err(Error::ParseError(ParseError(
            arg.span(),
            format!("unknown extractor: {name}; omit :extractor to use the default tree extractor"),
        ))),
        _ => Err(Error::ParseError(ParseError(
            arg.span(),
            "extractor name must be a symbol".into(),
        ))),
    }
}

pub fn extract_best_tree<C: Cost, M: DagCostModel<C> + 'static>(
    egraph: &EGraph,
    roots: Vec<(ArcSort, Value)>,
    cost_model: M,
) -> Result<ExtractedTerms<C>, Error> {
    egraph.extract_best(roots, TreeCostModelFromDag(cost_model))
}

pub fn extract_variants_tree<C: Cost, M: DagCostModel<C> + 'static>(
    egraph: &EGraph,
    roots: Vec<(ArcSort, Value)>,
    nvariants: usize,
    cost_model: M,
) -> Result<ExtractedTermVariants<C>, Error> {
    egraph.extract_variants(roots, nvariants, TreeCostModelFromDag(cost_model))
}

// Greedy-DAG extraction.
//
// This is a root-aware adaptation of extraction-gym's `faster-greedy-dag`:
// https://github.com/egraphs-good/extraction-gym/blob/903ba0f818b50608fe20ae9e0f03c35cb27bc50a/src/extract/faster_greedy_dag.rs.
// Each producer row records the dependencies whose marginal costs have already
// been paid, unions child dependency sets, rejects self-reachable rows, and
// propagates improvements to affected producer rows with a worklist.
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
// `.agents/logs/2026-06-24-greedy-dag-extractor-perf.md` records the local
// profiling data behind the representation choices below.

/// Once-paid dependency costs for one potential extracted DAG.
///
/// The keys are reachable `(sort, value)` dependencies and the values are their
/// marginal costs. The underlying sparse secondary map caches the combined
/// total, so cost comparison does not require subtraction or inspecting
/// the cost type.
type PaidDagCosts<C> = AggregatedSparseSecondaryMap<DagCostKey, C>;
type ChildDagCosts<C> = (Vec<Arc<PaidDagCosts<C>>>, Vec<C>);

/// Keyed on sort and value, since the same value of different sorts can have different extractions
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
struct GreedyDagProducerRow {
    /// Constructor function for this row.
    func_name: String,
    /// Owned child values. Backend row callbacks are borrowed, but the greedy
    /// DAG fixed point revisits producer rows after root discovery.
    children: Vec<Value>,
    /// Canonical e-class produced by this constructor row.
    eclass: Value,
}

/// Typed index into the greedy-DAG producer-row arena.
///
/// This is intentionally separate from [`InternId<DagCostKey>`]: cost keys
/// identify paid `(sort, value)` dependencies, while producer-row ids identify
/// rows that can produce one such dependency.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct ProducerRowId(usize);

impl ProducerRowId {
    fn new(index: usize) -> Self {
        Self(index)
    }

    fn index(self) -> usize {
        self.0
    }
}

/// Producer rows plus their reverse dependency index.
///
/// The rows form a small extraction-local arena because backend callbacks
/// borrow row data, while greedy-DAG propagation needs to revisit rows after
/// reachable discovery completes. The dependency index maps an improved
/// `(sort, value)` cost key to only the rows whose cost may change.
struct ProducerRows {
    rows: Vec<GreedyDagProducerRow>,
    by_dependency: SecondaryMap<DagCostKey, Vec<ProducerRowId>>,
}

impl ProducerRows {
    fn get(&self, producer_row_id: ProducerRowId) -> &GreedyDagProducerRow {
        &self.rows[producer_row_id.index()]
    }

    fn len(&self) -> usize {
        self.rows.len()
    }

    fn iter(&self) -> impl Iterator<Item = (ProducerRowId, &GreedyDagProducerRow)> {
        self.rows
            .iter()
            .enumerate()
            .map(|(index, row)| (ProducerRowId::new(index), row))
    }

    fn dependents(&self, key: InternId<DagCostKey>) -> Option<&[ProducerRowId]> {
        self.by_dependency.get(key).map(std::vec::Vec::as_slice)
    }
}

#[derive(Default)]
struct ProducerRowsBuilder {
    rows: Vec<GreedyDagProducerRow>,
    by_dependency: HashMap<InternId<DagCostKey>, Vec<ProducerRowId>>,
}

impl ProducerRowsBuilder {
    fn push(
        &mut self,
        row: GreedyDagProducerRow,
        dependencies: impl IntoIterator<Item = InternId<DagCostKey>>,
    ) {
        let row_id = ProducerRowId::new(self.rows.len());
        self.rows.push(row);
        for dependency in dependencies {
            self.by_dependency
                .entry(dependency)
                .or_default()
                .push(row_id);
        }
    }

    fn freeze(self, key_ids: &Interner<DagCostKey>) -> ProducerRows {
        let mut by_dependency = key_ids.secondary_map();
        for (key, producer_row_ids) in self.by_dependency {
            by_dependency.insert(key, producer_row_ids);
        }
        ProducerRows {
            rows: self.rows,
            by_dependency,
        }
    }
}

/// Best greedy-DAG state for a reachable eq-sort value.
///
/// Cost and producer row are stored together because they are a single
/// invariant: reconstruction is valid exactly when a value has a chosen
/// producer row with the corresponding once-paid DAG cost set.
struct BestProducer<C: Cost + Ord + Eq + Clone + Debug> {
    costs: Arc<PaidDagCosts<C>>,
    producer_row: ProducerRowId,
}

/// A greedy DAG extractor.
///
/// Unlike the tree extractor, which optimizes tree cost under a local cost
/// model, this extractor greedily chooses one producer row per reachable
/// eq-sort value while charging each selected `(sort, value)` dependency at
/// most once. This is not globally optimal, but it is much cheaper than an
/// exact DAG extractor and avoids the optimal-substructure assumption required
/// by encoding DAG sharing inside a normal [`TreeCostModel`].
///
/// Multiple requested roots share this single producer choice for any reachable
/// `(sort, value)`. That keeps reconstruction simple and makes sharing explicit
/// in the returned [`TermDag`], but it is not expressive enough for non-local
/// extractors that need different subterms for the same e-class under different
/// roots. See extraction-gym's discussion of that limitation:
/// https://github.com/egraphs-good/extraction-gym/issues/36.
pub struct GreedyDagExtractor<C: Cost + Ord + Eq + Clone + Debug> {
    cost_model: Box<dyn DagCostModel<C>>,

    /// Sort-name interner used only to build compact [`DagCostKey`]s.
    sort_ids: Interner<String>,
    /// Dense id-space for every reachable dependency that can be charged once.
    key_ids: Interner<DagCostKey>,

    /// Reachable producer rows and the reverse index used by the worklist.
    producer_rows: ProducerRows,

    /// Best known greedy-DAG extraction for each reachable eq-sort value.
    ///
    /// Only eq-sort values get entries here; primitive and container values
    /// are computed structurally.
    best_producers: SecondaryMap<DagCostKey, BestProducer<C>>,
}

struct ReachableExtractionBuilder {
    /// Growable sort-name interner used while discovering reachable values.
    sort_ids: InternerBuilder<String>,
    /// Growable id-space for reachable `(sort, value)` dependencies.
    key_ids: InternerBuilder<DagCostKey>,
    /// Reachable producer rows and their reverse dependency index.
    producer_rows: ProducerRowsBuilder,
    /// Deduplication set for reachable eq-sort values.
    seen_eq_values: HashSet<InternId<DagCostKey>>,
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
        if sort.is_container_sort() {
            for (child_sort, child_value) in egraph.container_inner_values(sort, value) {
                self.intern_nested_eq_dependencies(egraph, &child_sort, child_value, dependencies);
            }
        } else if sort.is_eq_sort() {
            dependencies.insert(self.intern_key(sort.name(), value));
        }
    }

    fn discover_node(&mut self, egraph: &EGraph, sort: &ArcSort, value: Value) {
        let sort_name = sort.name().to_owned();
        let key = self.intern_key(&sort_name, value);

        if sort.is_container_sort() {
            for (child_sort, child_value) in egraph.container_inner_values(sort, value) {
                self.discover_node(egraph, &child_sort, child_value);
            }
            return;
        }

        if !sort.is_eq_sort() {
            return;
        }

        if !self.seen_eq_values.insert(key) {
            return;
        }

        let constructors: Vec<_> = egraph
            .functions_iter()
            .filter(|(_, func)| {
                func.is_constructor()
                    && !func.is_hidden()
                    && !func.is_unextractable()
                    && func.schema().output.name() == sort_name
            })
            .map(|(func_name, func)| (func_name.clone(), func.schema().input.clone()))
            .collect();

        for (func_name, input_sorts) in constructors {
            let mut rows = Vec::new();
            egraph
                .read(|rs| {
                    rs.constructor_enodes_for_eclass(&func_name, value, |enode| {
                        if !enode.subsumed {
                            rows.push(enode.children.to_vec());
                        }
                    })
                })
                .expect("constructor name came from the egraph");

            for children in rows {
                // Child `(sort, value)` dependencies from matching rows.
                // Discover them after recording this row so recursive
                // discovery cannot invalidate the dependency ids we just
                // interned.
                let mut discovered_child_values = Vec::new();
                let mut dependencies = HashSet::default();
                for (child_value, child_sort) in children.iter().zip(input_sorts.iter()) {
                    self.intern_nested_eq_dependencies(
                        egraph,
                        child_sort,
                        *child_value,
                        &mut dependencies,
                    );
                    discovered_child_values.push((child_sort.clone(), *child_value));
                }
                self.producer_rows.push(
                    GreedyDagProducerRow {
                        func_name: func_name.clone(),
                        children,
                        eclass: value,
                    },
                    dependencies,
                );

                for (child_sort, child_value) in discovered_child_values {
                    self.discover_node(egraph, &child_sort, child_value);
                }
            }
        }
    }
}

impl<C: Cost + Ord + Eq + Clone + Debug> GreedyDagExtractor<C> {
    fn prepare(
        egraph: &EGraph,
        roots: &[(ArcSort, Value)],
        cost_model: impl DagCostModel<C> + 'static,
    ) -> Self {
        // Build the root-local problem: collect extractable functions, intern
        // reachable `(sort, value)` dependencies, and record producer rows with
        // their reverse dependency edges.
        let mut builder = ReachableExtractionBuilder {
            sort_ids: Default::default(),
            key_ids: Default::default(),
            producer_rows: Default::default(),
            seen_eq_values: Default::default(),
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
            ..
        } = builder;
        let sort_ids = sort_ids.freeze();
        let key_ids = key_ids.freeze();
        let producer_rows = producer_rows.freeze(&key_ids);
        let best_producers = key_ids.secondary_map();

        // Run the greedy fixed point over the reachable producer rows and keep
        // the resulting best producer choice for each reachable eq-sort value.
        let mut extractor = Self {
            cost_model: Box::new(cost_model),
            sort_ids,
            key_ids,
            producer_rows,
            best_producers,
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

    fn compute_child_dag_costs<'a>(
        &self,
        egraph: &EGraph,
        children: impl IntoIterator<Item = (Value, &'a ArcSort)>,
        reject_reachable_key: Option<InternId<DagCostKey>>,
    ) -> Option<ChildDagCosts<C>> {
        let mut child_cost_sets = Vec::new();
        let mut child_costs = Vec::new();

        for (value, sort) in children {
            let child_cost_set = self.compute_cost_node(egraph, value, sort)?;
            if reject_reachable_key.is_some_and(|key| child_cost_set.contains(key)) {
                return None;
            }
            child_costs.push(child_cost_set.total().clone());
            child_cost_sets.push(child_cost_set);
        }

        Some((child_cost_sets, child_costs))
    }

    fn add_marginal_cost(
        &self,
        child_cost_sets: &[Arc<PaidDagCosts<C>>],
        key: InternId<DagCostKey>,
        marginal_cost: C,
    ) -> Arc<PaidDagCosts<C>> {
        let mut cost_set =
            PaidDagCosts::union_by_cloning_largest(&self.key_ids, child_cost_sets, 1);
        cost_set.insert_if_absent(key, marginal_cost);
        Arc::new(cost_set)
    }

    fn compute_cost_node(
        &self,
        egraph: &EGraph,
        value: Value,
        sort: &ArcSort,
    ) -> Option<Arc<PaidDagCosts<C>>> {
        if sort.is_container_sort() {
            let elements = egraph.container_inner_values(sort, value);
            let children = elements
                .iter()
                .map(|(child_sort, child_value)| (*child_value, child_sort));
            let (child_cost_sets, child_costs) =
                self.compute_child_dag_costs(egraph, children, None)?;

            let container_self_cost =
                self.cost_model
                    .marginal_container_cost(egraph, sort, value, &child_costs);
            Some(self.add_marginal_cost(
                &child_cost_sets,
                self.reachable_cost_key(sort, value)?,
                container_self_cost,
            ))
        } else if sort.is_eq_sort() {
            let key = self.reachable_cost_key(sort, value)?;
            self.best_producers
                .get(key)
                .map(|best_producer| best_producer.costs.clone())
        } else {
            let mut cost_set = self.key_ids.aggregated_map_with_capacity(1);
            cost_set.insert_if_absent(
                self.reachable_cost_key(sort, value)?,
                self.cost_model.base_value_cost(egraph, sort, value),
            );
            Some(Arc::new(cost_set))
        }
    }

    fn compute_cost_hyperedge(
        &self,
        egraph: &EGraph,
        func: &Function,
        enode: &Enode<'_>,
        target_sort: &ArcSort,
        target: Value,
    ) -> Option<Arc<PaidDagCosts<C>>> {
        let target_key = self.reachable_cost_key(target_sort, target)?;
        let children = enode
            .children
            .iter()
            .zip(func.schema().input.iter())
            .map(|(value, sort)| (*value, sort));
        let (child_cost_sets, child_costs) =
            self.compute_child_dag_costs(egraph, children, Some(target_key))?;

        let node_cost = self
            .cost_model
            .marginal_enode_cost(egraph, func, enode, &child_costs);
        Some(self.add_marginal_cost(&child_cost_sets, target_key, node_cost))
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
        let Some((new_cost_set, target_key)) = ({
            let producer_row = self.producer_rows.get(producer_row_id);
            let func = egraph.get_function(&producer_row.func_name).unwrap();
            let target_sort = &func.schema().output;
            let target = producer_row.eclass;
            let Some(target_key) = self.reachable_cost_key(target_sort, target) else {
                return false;
            };
            let enode = Enode {
                children: &producer_row.children,
                eclass: producer_row.eclass,
                subsumed: false,
            };
            self.compute_cost_hyperedge(egraph, func, &enode, target_sort, target)
                .map(|cost_set| (cost_set, target_key))
        }) else {
            return false;
        };

        let should_update = match self.best_producers.get(target_key) {
            Some(old_best) => new_cost_set.total() < old_best.costs.total(),
            None => true,
        };

        if should_update {
            self.best_producers.insert(
                target_key,
                BestProducer {
                    costs: new_cost_set,
                    producer_row: producer_row_id,
                },
            );
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

        for producer_row_id in 0..self.producer_rows.len() {
            self.update_from_producer_row(
                egraph,
                ProducerRowId::new(producer_row_id),
                &mut pending,
                &mut pending_set,
            );
        }

        while let Some(key) = pending.pop_front() {
            pending_set.remove(key);
            let Some(producer_row_ids) = self.producer_rows.dependents(key).map(<[_]>::to_vec)
            else {
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
            for producer_row_id in 0..self.producer_rows.len() {
                assert!(
                    !self.update_from_producer_row(
                        egraph,
                        ProducerRowId::new(producer_row_id),
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
        termdag: &mut TermDag,
        producer_row: &GreedyDagProducerRow,
        cache: &mut HashMap<(Value, String), TermId>,
    ) -> TermId {
        let func = egraph.get_function(&producer_row.func_name).unwrap();
        let mut ch_terms: Vec<TermId> = Vec::new();
        for (value, sort) in producer_row.children.iter().zip(func.schema().input.iter()) {
            ch_terms
                .push(self.reconstruct_termdag_node_helper(egraph, termdag, *value, sort, cache));
        }
        termdag.app(func.name().to_owned(), ch_terms)
    }

    fn reconstruct_termdag_node_helper(
        &self,
        egraph: &EGraph,
        termdag: &mut TermDag,
        value: Value,
        sort: &ArcSort,
        cache: &mut HashMap<(Value, String), TermId>,
    ) -> TermId {
        let key = (value, sort.name().to_owned());
        if let Some(term) = cache.get(&key) {
            return *term;
        }

        let term = if sort.is_container_sort() {
            let elements = egraph.container_inner_values(sort, value);
            let mut ch_terms: Vec<TermId> = Vec::new();
            for ch in elements.iter() {
                ch_terms.push(
                    self.reconstruct_termdag_node_helper(egraph, termdag, ch.1, &ch.0, cache),
                );
            }
            egraph.reconstruct_container_value(sort, value, termdag, ch_terms)
        } else if sort.is_eq_sort() {
            let key = self.reachable_cost_key(sort, value).unwrap();
            let producer_row = self
                .producer_rows
                .get(self.best_producers.get(key).unwrap().producer_row);
            self.reconstruct_producer_row(egraph, termdag, producer_row, cache)
        } else {
            egraph.reconstruct_base_value(sort, value, termdag)
        };

        cache.insert(key, term);
        term
    }

    /// Extract the best greedy-DAG term of a value from a given sort.
    fn extract_best_with_sort(
        &self,
        egraph: &EGraph,
        termdag: &mut TermDag,
        value: Value,
        sort: ArcSort,
    ) -> Option<ExtractedTerm<C>> {
        let best_cost = self.compute_cost_node(egraph, value, &sort)?;
        let mut cache = Default::default();
        let term = self.reconstruct_termdag_node_helper(egraph, termdag, value, &sort, &mut cache);
        Some(ExtractedTerm {
            cost: best_cost.total().clone(),
            term,
        })
    }

    /// Extract root variants of an e-class using greedy-DAG costs.
    ///
    /// This mirrors the tree extractor variant path: variants are selected by
    /// ranking root e-nodes. Child e-classes use their single best greedy-DAG
    /// extraction, so this is not a full k-best DAG extractor.
    fn extract_variants_with_sort(
        &self,
        egraph: &EGraph,
        termdag: &mut TermDag,
        value: Value,
        nvariants: usize,
        sort: ArcSort,
    ) -> Vec<ExtractedTerm<C>> {
        if sort.is_eq_sort() {
            let mut root_variants: Vec<(C, ProducerRowId)> = Vec::new();

            for (producer_row_id, producer_row) in self.producer_rows.iter() {
                let func = egraph.get_function(&producer_row.func_name).unwrap();
                let target_sort = &func.schema().output;
                if sort.name() != target_sort.name() {
                    continue;
                }
                if producer_row.eclass != value {
                    continue;
                }
                let enode = Enode {
                    children: &producer_row.children,
                    eclass: producer_row.eclass,
                    subsumed: false,
                };
                if let Some(cost_set) =
                    self.compute_cost_hyperedge(egraph, func, &enode, target_sort, value)
                {
                    root_variants.push((cost_set.total().clone(), producer_row_id));
                }
            }

            let mut res: Vec<ExtractedTerm<C>> = Vec::new();
            let mut cache: HashMap<(Value, String), TermId> = Default::default();
            root_variants.sort();
            root_variants.truncate(nvariants);
            for (cost, producer_row_id) in root_variants {
                let producer_row = self.producer_rows.get(producer_row_id);
                res.push(ExtractedTerm {
                    cost,
                    term: self.reconstruct_producer_row(egraph, termdag, producer_row, &mut cache),
                });
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
/// Shared subterms are charged once according to the DAG cost model. When
/// multiple roots reach the same `(sort, value)`, this greedy extractor uses
/// one shared producer choice for that value rather than choosing root-specific
/// alternatives.
pub fn extract_best_greedy_dag<C: Cost + Ord + Eq + Clone + Debug, M: DagCostModel<C> + 'static>(
    egraph: &EGraph,
    roots: Vec<(ArcSort, Value)>,
    cost_model: M,
) -> Result<ExtractedTerms<C>, Error> {
    let extractor = GreedyDagExtractor::prepare(egraph, &roots, cost_model);
    let mut termdag = TermDag::default();
    let extracted_roots = roots
        .into_iter()
        .map(|(sort, value)| {
            let sort_name = sort.name().to_owned();
            extractor
                .extract_best_with_sort(egraph, &mut termdag, value, sort)
                .ok_or_else(|| {
                    Error::ExtractError(format!(
                        "Unable to find any valid greedy-DAG extraction for sort {sort_name}"
                    ))
                })
        })
        .collect::<Result<Vec<_>, _>>()?;

    Ok(ExtractedTerms {
        termdag,
        terms: extracted_roots,
    })
}

/// Extract up to `nvariants` greedy-DAG root variants for each requested root.
pub fn extract_variants_greedy_dag<
    C: Cost + Ord + Eq + Clone + Debug,
    M: DagCostModel<C> + 'static,
>(
    egraph: &EGraph,
    roots: Vec<(ArcSort, Value)>,
    nvariants: usize,
    cost_model: M,
) -> Result<ExtractedTermVariants<C>, Error> {
    let extractor = GreedyDagExtractor::prepare(egraph, &roots, cost_model);
    let mut termdag = TermDag::default();
    let variants = roots
        .into_iter()
        .map(|(sort, value)| {
            extractor.extract_variants_with_sort(egraph, &mut termdag, value, nvariants, sort)
        })
        .collect();

    Ok(ExtractedTermVariants { termdag, variants })
}
