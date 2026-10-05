//! Splitting the e-graph into regions and extracting them one at a time.
//!
//! A region root is a `Function` body or any effectful e-class that appears as
//! a *second* effectful child of an e-node (the body of an `If` branch or a
//! `DoWhile`, say). Each region is extracted on its own by the statewalk DP;
//! the results are stitched together by placing subregions below the e-nodes
//! that use them.

use super::cost::{Cost, RegionCostModel};
use super::egraph::{
    EClass, EClassId, EGraph, EGraphMapping, ENode, ExtractedNode, Extraction, ExtractionId,
};
use super::greedy::{project_statewalk_costs, statewalk_costs};
use super::statewalk::{StatewalkOptions, extract_region};

/// Extract every function root of `g`.
pub fn extract_all(
    g: &EGraph,
    egraph: &egglog::EGraph,
    region_costs: &dyn RegionCostModel,
    function_roots: &[EClassId],
    opts: StatewalkOptions,
) -> Vec<Extraction> {
    let mut regions = Regions::new(g, egraph, region_costs, function_roots, opts);
    function_roots
        .iter()
        .map(|&root| {
            regions.placed.fill(None);
            let mut extraction = Vec::new();
            regions.place(root, &mut extraction);
            debug_assert!(super::checks::is_effect_safe(g, root, &extraction));
            extraction
        })
        .collect()
}

/// Per-e-class marks that reset in O(1) by bumping a generation counter.
struct Marks {
    generation: Vec<u32>,
    value: Vec<usize>,
    current: u32,
}

impl Marks {
    fn new(n: usize) -> Self {
        Marks {
            generation: vec![0; n],
            value: vec![0; n],
            current: 0,
        }
    }

    fn clear(&mut self) {
        self.current += 1;
    }

    fn get(&self, class: EClassId) -> Option<usize> {
        (self.generation[class] == self.current).then_some(self.value[class])
    }

    fn set(&mut self, class: EClassId, value: usize) {
        self.generation[class] = self.current;
        self.value[class] = value;
    }
}

struct Regions<'g> {
    g: &'g EGraph,
    opts: StatewalkOptions,
    costs: Vec<Vec<Cost>>,
    /// Region number of each region root.
    region_of: Vec<Option<usize>>,
    /// Extraction of each region, over `g`, computed on demand.
    cache: Vec<Option<Extraction>>,
    /// Where each region was placed in the extraction being built.
    placed: Vec<Option<ExtractionId>>,
    marks: Marks,
}

impl<'g> Regions<'g> {
    fn new(
        g: &'g EGraph,
        egraph: &egglog::EGraph,
        region_costs: &dyn RegionCostModel,
        function_roots: &[EClassId],
        opts: StatewalkOptions,
    ) -> Self {
        let roots = region_roots(g, function_roots);
        let mut region_of = vec![None; g.len()];
        for (i, &root) in roots.iter().enumerate() {
            region_of[root] = Some(i);
        }
        Regions {
            g,
            opts,
            costs: statewalk_costs(g, egraph, region_costs),
            region_of,
            cache: vec![None; roots.len()],
            placed: vec![None; roots.len()],
            marks: Marks::new(g.len()),
        }
    }

    /// Append the extraction of the region rooted at `root` to `out`, placing
    /// its subregions first. Returns the position of the root.
    fn place(&mut self, root: EClassId, out: &mut Extraction) -> ExtractionId {
        let g = self.g;
        let rid = self.region_of[root].expect("not a region root");
        if let Some(id) = self.placed[rid] {
            return id;
        }
        if self.cache[rid].is_none() {
            let (region, region_root, to_g) = self.build_region(root);
            let costs = project_statewalk_costs(&to_g, &self.costs);
            let extraction = extract_region(&region, region_root, &costs, self.opts);
            self.cache[rid] = Some(to_g.apply(&extraction));
        }
        let region = self.cache[rid].clone().unwrap();

        // Subregions hang off the effectful children at `:regions` positions.
        let mut subregions = Vec::new();
        for en in &region {
            for child in g.region_children(g.enode(en.class, en.node)) {
                subregions.push(self.place(child, out));
            }
        }
        let base = out.len();
        let mut subregions = subregions.into_iter();
        for en in &region {
            let enode = g.enode(en.class, en.node);
            let positions = g.region_positions(enode);
            let mut inner = en.children.iter();
            let children = enode
                .children
                .iter()
                .enumerate()
                .map(|(i, &child)| {
                    if positions.contains(&i) && g.is_effectful(child) {
                        subregions.next().expect("subregion was placed")
                    } else {
                        base + inner.next().expect("region extraction has the child")
                    }
                })
                .collect();
            out.push(ExtractedNode {
                class: en.class,
                node: en.node,
                children,
            });
        }
        self.placed[rid] = Some(out.len() - 1);
        out.len() - 1
    }

    /// The region e-graph rooted at `root`: the effectful spine reached through
    /// state children, plus the pure e-classes it uses. Subregion children
    /// (effectful children at `:regions` positions) are dropped from e-nodes,
    /// and e-nodes with children outside the region are dropped entirely. Returns the (pruned) region, its root, and
    /// the mapping back into `g`.
    fn build_region(&mut self, root: EClassId) -> (EGraph, EClassId, EGraphMapping) {
        let g = self.g;
        let marks = &mut self.marks;
        marks.clear();
        let mut members = vec![root];
        marks.set(root, 0);
        let mut i = 0;
        while i < members.len() {
            for enode in &g.classes[members[i]].enodes {
                if let Some(child) = g.state_child(enode)
                    && marks.get(child).is_none()
                {
                    marks.set(child, members.len());
                    members.push(child);
                }
            }
            i += 1;
        }
        let mut i = 0;
        while i < members.len() {
            for enode in &g.classes[members[i]].enodes {
                for &child in &enode.children {
                    if !g.is_effectful(child) && marks.get(child).is_none() {
                        marks.set(child, members.len());
                        members.push(child);
                    }
                }
            }
            i += 1;
        }

        let mut region = g.empty_like();
        let mut to_g = EGraphMapping {
            classes: members.iter().map(|&m| Some(m)).collect(),
            enodes: Vec::with_capacity(members.len()),
        };
        for &m in &members {
            let class = &g.classes[m];
            let mut enodes: Vec<ENode> = Vec::new();
            let mut node_map = Vec::new();
            for (n, enode) in class.enodes.iter().enumerate() {
                let positions = g.region_positions(enode);
                let mut children = Vec::with_capacity(enode.children.len());
                let mut inside = true;
                for (i, &child) in enode.children.iter().enumerate() {
                    if positions.contains(&i) && g.is_effectful(child) {
                        continue;
                    }
                    match marks.get(child) {
                        Some(rc) => children.push(rc),
                        None => {
                            inside = false;
                            break;
                        }
                    }
                }
                if inside {
                    node_map.push(Some(n));
                    enodes.push(ENode {
                        kind: enode.kind.clone(),
                        cost: enode.cost,
                        children,
                    });
                }
            }
            region.classes.push(EClass {
                enodes,
                is_effectful: class.is_effectful,
                sort: class.sort,
            });
            to_g.enodes.push(node_map);
        }
        debug_assert!(super::checks::is_wellformed(&region, true, false));

        let (pruned, region_to_pruned) = region.prune_unextractable(Some(0));
        let pruned_root = region_to_pruned.class(0);
        let pruned_to_g = region_to_pruned.inverse(&pruned).then(&to_g);
        debug_assert!(super::checks::is_valid_mapping(
            &pruned_to_g,
            &pruned,
            g,
            false,
            true,
            false,
            false
        ));
        (pruned, pruned_root, pruned_to_g)
    }
}

/// Function roots first, then every effectful e-class at a `:regions`
/// position of some effectful e-node. Each e-class appears once.
fn region_roots(g: &EGraph, function_roots: &[EClassId]) -> Vec<EClassId> {
    let mut is_root = vec![false; g.len()];
    let mut roots = Vec::new();
    let mut add = |c: EClassId, roots: &mut Vec<EClassId>| {
        if !is_root[c] {
            is_root[c] = true;
            roots.push(c);
        }
    };
    for &root in function_roots {
        add(root, &mut roots);
    }
    for c in g.class_ids().filter(|&c| g.is_effectful(c)) {
        for enode in &g.classes[c].enodes {
            for child in g.region_children(enode) {
                add(child, &mut roots);
            }
        }
    }
    roots
}
