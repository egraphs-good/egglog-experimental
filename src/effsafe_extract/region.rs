//! Splitting the e-graph into regions and extracting them one at a time.
//!
//! A region root is an extraction root or any effectful e-class at a
//! `:regions` position of an effectful e-node (the body of an `If` branch or
//! a `DoWhile`, say). Each region is extracted on its own by the statewalk DP;
//! the results are stitched together by placing subregions below the e-nodes
//! that use them.
//!
//! Region choices can conflict: a region's cheapest extraction may use a
//! subregion that in turn (transitively) uses the region itself, or a
//! subregion may have no effect-safe extraction at all. When placing a
//! subregion fails, the e-nodes that chose it are forbidden in the enclosing
//! region, which is extracted again without them. Such a failure depends on
//! what is being placed above, so the exclusions made while placing a failed
//! subregion are undone with it, and all exclusions are dropped between
//! extraction roots.

use egglog::Error;
use rustc_hash::FxHashSet;

use super::cost::{Cost, RegionBoundary};
use super::greedy::{estimate_class_costs, project_statewalk_costs, statewalk_costs};
use super::statewalk::{StatewalkOptions, describe_class, extract_region};
use super::term_graph::{
    EClass, EClassId, EGraphMapping, ENodeId, ExtractedNode, Extraction, ExtractionId, TermGraph,
};

/// Extract every root of `g`.
pub fn extract_all(
    g: &TermGraph,
    boundary: &dyn RegionBoundary,
    roots: &[EClassId],
    opts: StatewalkOptions,
) -> Result<Vec<Extraction>, Error> {
    let mut regions = Regions::new(g, boundary, roots, opts);
    roots
        .iter()
        .map(|&root| {
            regions.placed.fill(None);
            regions.clear_forbidden();
            let mut out = Vec::new();
            regions.place(root, &mut out).map_err(|err| match err {
                PlaceError::Other(err) => err,
                PlaceError::Cycle(class) => Error::ExtractError(format!(
                    "no effect-safe extraction for {}: every choice leads back into the \
                     region rooted at {}, which is being extracted",
                    describe_class(g, root),
                    describe_class(g, class)
                )),
            })?;
            // The final check runs in release builds too: it is linear in the
            // extraction and an unsafe program must never be returned.
            if !super::checks::is_effect_safe(g, root, &out) {
                return Err(Error::ExtractError(format!(
                    "internal error: the extraction of {} is not effect-safe (please report this)",
                    describe_class(g, root)
                )));
            }
            Ok(out)
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

/// Why a region could not be placed.
enum PlaceError {
    /// The region is already being placed higher up the stack; its root is given.
    Cycle(EClassId),
    Other(Error),
}

impl From<Error> for PlaceError {
    fn from(err: Error) -> Self {
        PlaceError::Other(err)
    }
}

struct Regions<'g> {
    g: &'g TermGraph,
    boundary: &'g dyn RegionBoundary,
    opts: StatewalkOptions,
    /// Estimated cost of every e-class (global greedy).
    class_cost: Vec<Cost>,
    /// Statewalk cost of every effectful e-node (subregions folded in).
    costs: Vec<Vec<Cost>>,
    /// Region number of each region root.
    region_of: Vec<Option<usize>>,
    /// Extraction of each region, over `g`, computed on demand.
    cache: Vec<Option<Extraction>>,
    /// E-nodes of `g` excluded from each region, because the subregion they
    /// chose could not be placed below it.
    forbidden: Vec<FxHashSet<(EClassId, ENodeId)>>,
    /// Every exclusion in order, so that those made below a failed placement
    /// can be undone.
    forbidden_log: Vec<(usize, (EClassId, ENodeId))>,
    /// Regions currently being placed (on the recursion stack).
    placing: Vec<bool>,
    /// Where each region was placed in the extraction being built.
    placed: Vec<Option<ExtractionId>>,
    marks: Marks,
}

impl<'g> Regions<'g> {
    fn new(
        g: &'g TermGraph,
        boundary: &'g dyn RegionBoundary,
        roots: &[EClassId],
        opts: StatewalkOptions,
    ) -> Self {
        let t0 = std::time::Instant::now();
        let region_roots = region_roots(g, roots);
        let class_cost = estimate_class_costs(g, boundary);
        let costs = statewalk_costs(g, boundary, &class_cost);
        if log::log_enabled!(log::Level::Debug) {
            log::debug!(
                "effsafe statewalk_costs(global greedy)={:.2}ms",
                t0.elapsed().as_secs_f64() * 1e3
            );
        }
        let mut region_of = vec![None; g.len()];
        for (i, &root) in region_roots.iter().enumerate() {
            region_of[root] = Some(i);
        }
        Regions {
            g,
            boundary,
            opts,
            class_cost,
            costs,
            region_of,
            cache: vec![None; region_roots.len()],
            forbidden: vec![FxHashSet::default(); region_roots.len()],
            forbidden_log: Vec::new(),
            placing: vec![false; region_roots.len()],
            placed: vec![None; region_roots.len()],
            marks: Marks::new(g.len()),
        }
    }

    /// Drop every exclusion (and the cached extractions it affected).
    fn clear_forbidden(&mut self) {
        self.undo_forbidden(0);
    }

    /// Undo the exclusions logged after `checkpoint`.
    fn undo_forbidden(&mut self, checkpoint: usize) {
        while self.forbidden_log.len() > checkpoint {
            let (rid, enode) = self.forbidden_log.pop().unwrap();
            self.forbidden[rid].remove(&enode);
            self.cache[rid] = None;
        }
    }

    /// Append the extraction of the region rooted at `root` to `out`, placing
    /// its subregions first. Returns the position of the root.
    fn place(&mut self, root: EClassId, out: &mut Extraction) -> Result<ExtractionId, PlaceError> {
        let rid = self.region_of[root].expect("not a region root");
        if let Some(id) = self.placed[rid] {
            return Ok(id);
        }
        if self.placing[rid] {
            return Err(PlaceError::Cycle(root));
        }
        self.placing[rid] = true;
        let result = self.place_inner(root, rid, out);
        self.placing[rid] = false;
        result
    }

    fn place_inner(
        &mut self,
        root: EClassId,
        rid: usize,
        out: &mut Extraction,
    ) -> Result<ExtractionId, PlaceError> {
        let g = self.g;
        loop {
            if self.cache[rid].is_none() {
                self.cache[rid] = Some(self.extract_cached(root, rid)?);
            }
            let region = self.cache[rid].clone().unwrap();

            // Place the subregions first. If one cannot be placed, forbid the
            // e-nodes of this region that chose it and extract the region again.
            let checkpoint = (out.len(), self.placed.clone(), self.forbidden_log.len());
            let mut subregions = Vec::new();
            let mut failed: Option<(EClassId, PlaceError)> = None;
            'nodes: for en in &region {
                for child in g.region_children(g.enode(en.class, en.node)) {
                    match self.place(child, out) {
                        Ok(id) => subregions.push(id),
                        Err(err) => {
                            failed = Some((child, err));
                            break 'nodes;
                        }
                    }
                }
            }
            if let Some((child, err)) = failed {
                out.truncate(checkpoint.0);
                self.placed = checkpoint.1;
                // Exclusions made while placing the failed subregion were
                // relative to this attempt; undo them.
                self.undo_forbidden(checkpoint.2);
                let culprits: Vec<(EClassId, ENodeId)> = region
                    .iter()
                    .filter(|en| {
                        g.region_children(g.enode(en.class, en.node))
                            .any(|c| c == child)
                    })
                    .map(|en| (en.class, en.node))
                    .collect();
                if culprits.is_empty() {
                    return Err(err);
                }
                log::debug!(
                    "effsafe region {}: subregion {} cannot be placed; forbidding {} e-node(s) and retrying",
                    describe_class(g, root),
                    describe_class(g, child),
                    culprits.len()
                );
                for culprit in culprits {
                    if self.forbidden[rid].insert(culprit) {
                        self.forbidden_log.push((rid, culprit));
                    }
                }
                self.cache[rid] = None;
                continue;
            }

            let base = out.len();
            let mut subregions = subregions.into_iter();
            for en in &region {
                let enode = g.enode(en.class, en.node);
                let mut inner = en.children.iter();
                let children = enode
                    .children
                    .iter()
                    .enumerate()
                    .map(|(i, &child)| {
                        if enode.regions.contains(&i) && g.is_effectful(child) {
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
            return Ok(out.len() - 1);
        }
    }

    /// Extract the region rooted at `root` (over `g`), honouring its forbidden e-nodes.
    fn extract_cached(&mut self, root: EClassId, rid: usize) -> Result<Extraction, Error> {
        let t0 = std::time::Instant::now();
        let (region, region_root, to_g) = self.build_region(root, rid)?;
        let t_build = t0.elapsed();
        let costs = project_statewalk_costs(&to_g, &self.costs);
        let class_costs: Vec<Cost> = region
            .class_ids()
            .map(|c| self.class_cost[to_g.class(c)])
            .collect();
        let t1 = std::time::Instant::now();
        let extraction = extract_region(
            &region,
            self.boundary,
            region_root,
            &costs,
            &class_costs,
            self.opts,
        )?;
        if log::log_enabled!(log::Level::Debug) {
            log::debug!(
                "effsafe region classes={} build={:.2}ms extract={:.2}ms",
                region.len(),
                t_build.as_secs_f64() * 1e3,
                t1.elapsed().as_secs_f64() * 1e3
            );
        }
        Ok(to_g.apply(&extraction))
    }

    /// The region e-graph rooted at `root`: the effectful spine reached through
    /// state children, plus the pure e-classes it uses. Subregion children
    /// (effectful children at `:regions` positions) are dropped from e-nodes
    /// (their folded cost enters through the statewalk costs), and e-nodes
    /// with children outside the region, or forbidden for this region, are
    /// dropped entirely. Returns the (pruned) region, its root, and
    /// the mapping back into `g`.
    fn build_region(
        &mut self,
        root: EClassId,
        rid: usize,
    ) -> Result<(TermGraph, EClassId, EGraphMapping), Error> {
        let g = self.g;
        let forbidden = &self.forbidden[rid];
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
            let mut enodes = Vec::new();
            let mut node_map = Vec::new();
            for (n, enode) in class.enodes.iter().enumerate() {
                if forbidden.contains(&(m, n)) {
                    continue;
                }
                let mut children = Vec::with_capacity(enode.children.len());
                let mut kept = Vec::with_capacity(enode.children.len());
                let mut inside = true;
                for (i, &child) in enode.children.iter().enumerate() {
                    if enode.regions.contains(&i) && g.is_effectful(child) {
                        continue;
                    }
                    match marks.get(child) {
                        Some(rc) => {
                            children.push(rc);
                            kept.push(i);
                        }
                        None => {
                            inside = false;
                            break;
                        }
                    }
                }
                if inside {
                    node_map.push(Some(n));
                    enodes.push(enode.without_regions(&kept, children, class.is_effectful));
                }
            }
            region.classes.push(EClass {
                enodes,
                is_effectful: class.is_effectful,
                sort: class.sort,
            });
            to_g.enodes.push(node_map);
        }
        super::checks::validate!(super::checks::is_wellformed(&region, true, false));

        let (pruned, region_to_pruned) = region.prune_unextractable(Some(0));
        let Some(pruned_root) = region_to_pruned.classes[0] else {
            return Err(Error::ExtractError(format!(
                "no effect-safe extraction for the region rooted at {}: every term of the \
                 root uses a state from outside the region (a subregion may only use its \
                 own entry and the e-nodes on its own statewalk)",
                describe_class(g, root)
            )));
        };
        let pruned_to_g = region_to_pruned.inverse(&pruned).then(&to_g);
        super::checks::validate!(super::checks::is_valid_mapping(
            &pruned_to_g,
            &pruned,
            g,
            false,
            true,
            false,
            false
        ));
        Ok((pruned, pruned_root, pruned_to_g))
    }
}

/// Extraction roots first, then every effectful e-class at a `:regions`
/// position of some effectful e-node. Each e-class appears once.
fn region_roots(g: &TermGraph, roots: &[EClassId]) -> Vec<EClassId> {
    let mut is_root = vec![false; g.len()];
    let mut out = Vec::new();
    let mut add = |c: EClassId, out: &mut Vec<EClassId>| {
        if !is_root[c] {
            is_root[c] = true;
            out.push(c);
        }
    };
    for &root in roots {
        add(root, &mut out);
    }
    for c in g.class_ids().filter(|&c| g.is_effectful(c)) {
        for enode in &g.classes[c].enodes {
            for child in g.region_children(enode) {
                add(child, &mut out);
            }
        }
    }
    out
}
