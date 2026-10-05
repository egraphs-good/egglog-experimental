//! Cost types and the hook for region costs.

use egglog::EGraph;

/// Extraction costs are plain saturating `u64`s, like egglog's default cost.
pub type Cost = egglog::extract::DefaultCost;

pub const INFINITE: Cost = Cost::MAX;

/// How the costs of an e-node's subregions (the children at its `:regions`
/// positions) contribute to the e-node's cost.
///
/// The extractor charges an e-node's own cost and its other children in the
/// usual way; this hook decides what the regions add. The default,
/// [`SumRegions`], adds them up. A compiler can plug in its own heuristics,
/// such as charging only the more expensive branch of a conditional or
/// multiplying a loop body by an iteration estimate.
pub trait RegionCostModel: Send + Sync {
    /// The cost `constructor`'s subregions add, given each region's extracted
    /// cost in `:regions` order.
    fn fold_regions(&self, egraph: &EGraph, constructor: &str, region_costs: &[Cost]) -> Cost;
}

/// Charges every subregion in full.
#[derive(Clone, Copy, Debug, Default)]
pub struct SumRegions;

impl RegionCostModel for SumRegions {
    fn fold_regions(&self, _egraph: &EGraph, _constructor: &str, region_costs: &[Cost]) -> Cost {
        region_costs.iter().fold(0, |acc, &c| acc.saturating_add(c))
    }
}
