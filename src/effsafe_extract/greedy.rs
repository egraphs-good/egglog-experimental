//! Greedy bottom-up extraction with *bag* costs.
//!
//! A bag cost is the sum of the costs of the distinct e-classes a term uses,
//! so shared subterms are only paid for once. It is cheap to maintain but not
//! guaranteed optimal, which is fine for an estimate.

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::hash::BuildHasherDefault;

use egglog::Error;
use indexmap::IndexMap;
use rustc_hash::FxHasher;

use super::cost::{Cost, INFINITE, RegionBoundary};
use super::term_graph::{
    EClassId, EGraphMapping, ENode, ENodeId, ExtractedNode, Extraction, ExtractionId, TermGraph,
};

type FxIndexMap<K, V> = IndexMap<K, V, BuildHasherDefault<FxHasher>>;

/// The cost of a term as a bag of the e-classes it uses.
#[derive(Clone, Debug)]
pub struct BagCost {
    /// Sum of `bag`, plus the term's own e-node costs.
    pub sum: Cost,
    /// Cheapest known cost of each e-class the term depends on.
    bag: FxIndexMap<EClassId, Cost>,
}

impl BagCost {
    pub fn new(own: Cost) -> Self {
        BagCost {
            sum: own,
            bag: FxIndexMap::default(),
        }
    }

    pub fn infinite() -> Self {
        BagCost::new(INFINITE)
    }

    /// Account for depending on `class`, whose chosen term costs `child`.
    pub fn add_child(&mut self, class: EClassId, child: &BagCost) {
        if child.sum == INFINITE {
            self.sum = INFINITE;
            return;
        }
        let mut overhead = child.sum;
        for (&cid, &c) in &child.bag {
            overhead = overhead.saturating_sub(c);
            self.add_class(cid, c);
        }
        self.add_class(class, overhead);
    }

    fn add_class(&mut self, class: EClassId, cost: Cost) {
        match self.bag.get_mut(&class) {
            Some(known) => {
                if *known > cost {
                    self.sum = self.sum.saturating_sub(*known - cost);
                    *known = cost;
                }
            }
            None => {
                self.bag.insert(class, cost);
                self.sum = self.sum.saturating_add(cost);
            }
        }
    }

    fn set_zero(&mut self) {
        self.sum = 0;
        self.bag.clear();
    }
}

impl PartialEq for BagCost {
    fn eq(&self, other: &Self) -> bool {
        self.sum == other.sum
    }
}

impl Eq for BagCost {}

impl PartialOrd for BagCost {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BagCost {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.sum.cmp(&other.sum)
    }
}

/// Dijkstra-style state shared by the greedy passes: the best known cost and
/// pick per e-class, and a work heap ordered by cost (ties: larger id first).
struct Greedy<'g> {
    g: &'g TermGraph,
    parents: Vec<Vec<(EClassId, ENodeId)>>,
    /// Children of each e-node whose e-class has not been settled yet.
    remaining: Vec<Vec<usize>>,
    best: Vec<BagCost>,
    pick: Vec<Option<ENodeId>>,
    heap: BinaryHeap<(Reverse<Cost>, EClassId)>,
}

impl<'g> Greedy<'g> {
    fn new(g: &'g TermGraph) -> Self {
        let mut greedy = Greedy {
            g,
            parents: g.parents(),
            remaining: g.child_counts(),
            best: vec![BagCost::infinite(); g.len()],
            pick: vec![None; g.len()],
            heap: BinaryHeap::new(),
        };
        for (c, n) in g.enode_ids() {
            let enode = g.enode(c, n);
            if enode.is_leaf() {
                greedy.relax(c, n, BagCost::new(enode.cost));
            }
        }
        greedy
    }

    /// Record `node` as the cheapest known e-node of `class` if it is. The
    /// first e-node of a class is always recorded, even when its cost has
    /// saturated to `INFINITE`: reachability is not a matter of cost.
    fn relax(&mut self, class: EClassId, node: ENodeId, cost: BagCost) {
        if self.pick[class].is_none() || cost < self.best[class] {
            self.heap.push((Reverse(cost.sum), class));
            self.best[class] = cost;
            self.pick[class] = Some(node);
        }
    }

    /// Pop the cheapest e-class. Returns `None` when the heap is empty, and
    /// skips entries made stale by a later, cheaper relaxation.
    fn pop(&mut self) -> Option<EClassId> {
        while let Some((Reverse(cost), class)) = self.heap.pop() {
            if cost == self.best[class].sum {
                return Some(class);
            }
        }
        None
    }

    fn pop_unchecked(&mut self) -> Option<(Cost, EClassId)> {
        self.heap.pop().map(|(Reverse(cost), class)| (cost, class))
    }

    /// Bag cost of `enode` given the current best costs of its children.
    fn plain_cost(&self, own: Cost, enode: &ENode) -> BagCost {
        let mut cost = BagCost::new(own);
        for &child in &enode.children {
            cost.add_child(child, &self.best[child]);
        }
        cost
    }

    fn picked(&self, class: EClassId) -> &'g ENode {
        self.g
            .enode(class, self.pick[class].expect("e-class has no pick"))
    }
}

/// The effective marginal cost of `enode` given the costs of its `:regions`
/// children: the boundary fold for e-nodes with such children, the plain
/// marginal cost otherwise. A pure e-class at a `:regions` position (the
/// branches of a conditional that does not touch the state, say) is not a
/// subregion, but it is still priced through the fold, as a tree, so that the
/// boundary model's weighting applies to it too.
pub fn effective_cost(
    _g: &TermGraph,
    boundary: &dyn RegionBoundary,
    enode: &ENode,
    region_cost: impl Fn(EClassId) -> Cost,
) -> Cost {
    if enode.regions.is_empty() {
        return enode.cost;
    }
    let mut by_position = vec![0; enode.children.len()];
    for &i in &enode.regions {
        by_position[i] = region_cost(enode.children[i]);
    }
    let annotation = enode
        .boundary
        .as_deref()
        .expect("e-nodes with regions carry a boundary annotation");
    boundary.fold(annotation, &by_position)
}

/// For every e-class, the cheapest e-node and its bag cost. Subregion costs
/// enter through the boundary fold; the other children are bag costs. Stops
/// early once `root` is settled.
pub fn greedy_costs(
    g: &TermGraph,
    boundary: &dyn RegionBoundary,
    root: Option<EClassId>,
) -> (Vec<Option<ENodeId>>, Vec<Cost>) {
    let mut greedy = Greedy::new(g);
    // A class can be popped again when a later relaxation improves it (a
    // boundary fold may make a parent cheaper than its subregion); it counts
    // towards its parents' remaining children only once.
    let mut processed = vec![false; g.len()];
    while let Some((cost, class)) = greedy.pop_unchecked() {
        if Some(class) == root {
            break;
        }
        if cost != greedy.best[class].sum {
            continue;
        }
        for idx in 0..greedy.parents[class].len() {
            let (pc, pn) = greedy.parents[class][idx];
            if !processed[class] {
                greedy.remaining[pc][pn] -= 1;
            }
            if greedy.remaining[pc][pn] != 0 {
                continue;
            }
            let enode = g.enode(pc, pn);
            let own = effective_cost(g, boundary, enode, |c| greedy.best[c].sum);
            let mut cost = BagCost::new(own);
            for child in g.split_children(enode).0 {
                cost.add_child(child, &greedy.best[child]);
            }
            greedy.relax(pc, pn, cost);
        }
        processed[class] = true;
    }
    let costs = greedy.best.iter().map(|b| b.sum).collect();
    (greedy.pick, costs)
}

/// Estimated cost of every e-class.
pub fn estimate_class_costs(g: &TermGraph, boundary: &dyn RegionBoundary) -> Vec<Cost> {
    greedy_costs(g, boundary, None).1
}

/// Cost of an effectful e-node for the statewalk DP: its own cost, the
/// estimated cost of its pure children, and the folded cost of its regions
/// (effectful children on the statewalk are paid for by the rest of the walk).
fn statewalk_enode_cost(
    g: &TermGraph,
    boundary: &dyn RegionBoundary,
    class_cost: &[Cost],
    enode: &ENode,
) -> Cost {
    let mut cost = effective_cost(g, boundary, enode, |c| class_cost[c]);
    for child in g.split_children(enode).0 {
        if !g.is_effectful(child) {
            cost = cost.saturating_add(class_cost[child]);
        }
    }
    cost
}

/// Statewalk costs for every effectful e-node (pure e-classes get an empty
/// row), given the estimated cost of every e-class.
pub fn statewalk_costs(
    g: &TermGraph,
    boundary: &dyn RegionBoundary,
    class_cost: &[Cost],
) -> Vec<Vec<Cost>> {
    g.classes
        .iter()
        .map(|class| {
            if class.is_effectful {
                class
                    .enodes
                    .iter()
                    .map(|n| statewalk_enode_cost(g, boundary, class_cost, n))
                    .collect()
            } else {
                Vec::new()
            }
        })
        .collect()
}

/// Re-index statewalk costs of the target e-graph for the source of `mapping`.
pub fn project_statewalk_costs(mapping: &EGraphMapping, costs: &[Vec<Cost>]) -> Vec<Vec<Cost>> {
    mapping
        .enodes
        .iter()
        .enumerate()
        .map(|(c, nodes)| {
            let tc = mapping.class(c);
            if costs[tc].is_empty() {
                Vec::new()
            } else {
                nodes
                    .iter()
                    .map(|n| costs[tc][n.expect("e-node is not mapped")])
                    .collect()
            }
        })
        .collect()
}

/// Greedily extract `root` from a *linearized* e-graph, in which every
/// effectful e-class has exactly one e-node (its statewalk pick).
///
/// Pure e-classes are settled cheapest first. Whenever an effectful e-class is
/// settled, the whole term below it is emitted and its e-classes become free
/// for everyone else to reuse (their cost drops to zero), which is what makes
/// the shared statewalk pay for pure subterms only once.
pub fn statewalk_greedy_extraction(g: &TermGraph, root: EClassId) -> Result<Extraction, Error> {
    let mut greedy = Greedy::new(g);
    let mut extraction: Extraction = Vec::new();
    let mut extracted: Vec<Option<ExtractionId>> = vec![None; g.len()];
    let mut processed = vec![false; g.len()];
    let mut member_index: Vec<Option<usize>> = vec![None; g.len()];

    while let Some(class) = greedy.pop() {
        if g.is_effectful(class) {
            emit_term(
                &mut greedy,
                class,
                &mut extraction,
                &mut extracted,
                &mut member_index,
            );
        }
        if class == root {
            break;
        }
        for idx in 0..greedy.parents[class].len() {
            let (pc, pn) = greedy.parents[class][idx];
            // A class can be popped again after its cost was zeroed; only count
            // it towards its parents once.
            if !processed[class] {
                greedy.remaining[pc][pn] -= 1;
            }
            if greedy.remaining[pc][pn] != 0 {
                continue;
            }
            let enode = g.enode(pc, pn);
            let own = if g.is_effectful(pc) { 0 } else { enode.cost };
            let cost = greedy.plain_cost(own, enode);
            greedy.relax(pc, pn, cost);
        }
        processed[class] = true;
    }
    if extracted[root].is_none() {
        return Err(Error::ExtractError(
            "internal error: the region's root was not extracted from its linearized e-graph"
                .to_string(),
        ));
    }
    super::checks::validate!(super::checks::is_effect_safe(g, root, &extraction));
    Ok(extraction)
}

/// Append the picked term below `class` to `extraction` (skipping e-classes
/// already extracted), children before parents, then zero the cost of every
/// e-class it covers.
fn emit_term(
    greedy: &mut Greedy,
    class: EClassId,
    extraction: &mut Extraction,
    extracted: &mut [Option<ExtractionId>],
    member_index: &mut [Option<usize>],
) {
    let g = greedy.g;
    // Members: e-classes of the picked term that are not yet extracted, in BFS order.
    let mut members: Vec<EClassId> = vec![class];
    let mut dependents: Vec<Vec<usize>> = vec![Vec::new()];
    let mut pending: Vec<usize> = vec![0];
    member_index[class] = Some(0);
    let mut i = 0;
    while i < members.len() {
        for &child in &greedy.picked(members[i]).children {
            if extracted[child].is_none() {
                let ci = *member_index[child].get_or_insert_with(|| {
                    members.push(child);
                    dependents.push(Vec::new());
                    pending.push(0);
                    members.len() - 1
                });
                dependents[ci].push(i);
                pending[i] += 1;
            }
        }
        i += 1;
    }
    // Topological order (Kahn), children first; the root `class` comes out last.
    let mut order: Vec<usize> = (0..members.len()).filter(|&m| pending[m] == 0).collect();
    let mut i = 0;
    while i < order.len() {
        for &parent in &dependents[order[i]] {
            pending[parent] -= 1;
            if pending[parent] == 0 {
                order.push(parent);
            }
        }
        i += 1;
    }
    debug_assert!(order.len() == members.len());
    for &m in &order {
        let u = members[m];
        let node = greedy.pick[u].expect("member has a pick");
        let children = g
            .enode(u, node)
            .children
            .iter()
            .map(|&c| extracted[c].expect("children are emitted first"))
            .collect();
        extracted[u] = Some(extraction.len());
        extraction.push(ExtractedNode {
            class: u,
            node,
            children,
        });
    }
    for &u in &members {
        member_index[u] = None;
        if greedy.best[u].sum > 0 {
            greedy.best[u].set_zero();
            if u != class {
                greedy.heap.push((Reverse(0), u));
            }
        }
    }
}
