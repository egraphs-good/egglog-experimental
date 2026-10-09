//! Cost types and the region boundary model.
//! See [`super::set_effsafe_cost_models`] for the boundary fold contract.

use std::any::Any;
use std::sync::Arc;

use egglog::extract::{DefaultCost, TreeCostModel};
use egglog::{EGraph, Enode, Function};

/// Extraction cost. Additions performed by the extractor saturate at `u64::MAX`.
pub type Cost = DefaultCost;

pub const INFINITE: Cost = Cost::MAX;

/// A boundary cost model's per-e-node annotation (see [`RegionBoundary::annotate`]).
pub type Annotation = Arc<dyn Any + Send + Sync>;

/// Cost model for children at `:regions` positions, including pure children.
/// Implemented for [`TreeCostModel`] types with cloneable annotations.
pub trait RegionBoundary: Send + Sync {
    /// The model's annotation for an e-node with `:regions` children.
    fn annotate(
        &self,
        egraph: &EGraph,
        func: &Function,
        enode: &Enode<'_>,
    ) -> Arc<dyn Any + Send + Sync>;

    /// Combine the node's own cost with annotated child costs, in argument
    /// positions, with `0` elsewhere. Use saturating arithmetic.
    /// `annotation` must come from this model's [`Self::annotate`].
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
