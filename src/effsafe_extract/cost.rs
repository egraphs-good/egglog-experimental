//! Cost types and the region-boundary cost model.
//!
//! Within a region the extractor charges shared computations once, so e-node
//! costs are marginal costs from a [`DagCostModel`](egglog::extract::DagCostModel).
//! Across region boundaries costs compose like a tree: an e-node with
//! subregions (its `:regions` children) is charged its own cost plus a fold of
//! its subregions' costs, each occurrence separately, through a
//! [`TreeCostModel`]. The fold receives the subregion costs in their argument
//! positions and `0` for every other child; the result stands in for the
//! e-node's marginal cost in the enclosing region. Ordinary children are then
//! charged through the enclosing region's DAG, so nothing is counted twice.

use std::any::Any;
use std::sync::Arc;

use egglog::extract::TreeCostModel;
use egglog::{EGraph, Enode, Function};

/// Extraction costs are plain saturating `u64`s, like egglog's default cost.
pub type Cost = egglog::extract::DefaultCost;

pub const INFINITE: Cost = Cost::MAX;

/// A boundary cost model's per-e-node annotation (see [`RegionBoundary::annotate`]).
pub type Annotation = Arc<dyn Any + Send + Sync>;

/// Object-safe view of a [`TreeCostModel`] for region boundaries. The
/// annotation is computed when the e-graph is read and kept with the e-node;
/// the fold runs whenever a subregion's cost changes during the search and
/// once more to price the final program.
pub trait RegionBoundary: Send + Sync {
    /// The model's annotation for an e-node that has subregions.
    fn annotate(
        &self,
        egraph: &EGraph,
        func: &Function,
        enode: &Enode<'_>,
    ) -> Arc<dyn Any + Send + Sync>;

    /// The e-node's effective cost given its subregions' costs, in argument
    /// positions, with `0` for children that are not subregions.
    fn fold(&self, annotation: &(dyn Any + Send + Sync), child_costs: &[Cost]) -> Cost;
}

impl<M> RegionBoundary for M
where
    M: TreeCostModel<Cost> + Send + Sync,
    M::EnodeCost: Clone + Send + Sync + 'static,
{
    fn annotate(
        &self,
        egraph: &EGraph,
        func: &Function,
        enode: &Enode<'_>,
    ) -> Arc<dyn Any + Send + Sync> {
        Arc::new(self.enode_cost(egraph, func, enode))
    }

    fn fold(&self, annotation: &(dyn Any + Send + Sync), child_costs: &[Cost]) -> Cost {
        let annotation = annotation
            .downcast_ref::<M::EnodeCost>()
            .expect("annotation produced by the same cost model")
            .clone();
        self.fold_enode_cost(annotation, child_costs)
    }
}
