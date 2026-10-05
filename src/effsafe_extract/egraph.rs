//! The index-based e-graph the effect-safe extractor works on.
//!
//! E-classes are numbered densely and every e-node lives in exactly one
//! e-class. An e-class is *effectful* when the program marked it so (see
//! [`super::EffsafeConfig`]); the effectful e-nodes chosen for a region form
//! its *statewalk*. Everything else is pure.

use std::collections::VecDeque;

use egglog::Value;

use super::cost::Cost;

pub type EClassId = usize;
pub type ENodeId = usize;
/// Position of an e-node inside an [`Extraction`].
pub type ExtractionId = usize;
/// Index into [`EGraph::ops`].
pub type OpId = usize;
/// Index into [`EGraph::sorts`].
pub type SortId = usize;

/// A constructor the e-graph uses, with its `:regions` annotation.
#[derive(Clone, Debug)]
pub struct OpInfo {
    pub name: String,
    /// Child positions that start subregions, sorted.
    pub regions: Vec<usize>,
}

#[derive(Clone, Debug)]
pub enum NodeKind {
    /// A constructor application.
    Op(OpId),
    /// A base value (int, string, ...). Reconstructed from the egglog value.
    Base(Value),
    /// A container value whose elements are the node's children.
    Container(Value),
    /// A stand-in for a sort the extraction does not descend into.
    Placeholder,
}

#[derive(Clone, Debug)]
pub struct ENode {
    pub kind: NodeKind,
    /// Marginal cost of this e-node, not counting its children.
    pub cost: Cost,
    pub children: Vec<EClassId>,
}

impl ENode {
    pub fn is_leaf(&self) -> bool {
        self.children.is_empty()
    }
}

#[derive(Clone, Debug)]
pub struct EClass {
    pub enodes: Vec<ENode>,
    pub is_effectful: bool,
    pub sort: SortId,
}

#[derive(Clone, Debug, Default)]
pub struct EGraph {
    pub classes: Vec<EClass>,
    pub ops: Vec<OpInfo>,
    pub sorts: Vec<egglog::ArcSort>,
}

impl EGraph {
    pub fn len(&self) -> usize {
        self.classes.len()
    }

    pub fn class_ids(&self) -> std::ops::Range<EClassId> {
        0..self.len()
    }

    pub fn enode(&self, class: EClassId, node: ENodeId) -> &ENode {
        &self.classes[class].enodes[node]
    }

    pub fn is_effectful(&self, class: EClassId) -> bool {
        self.classes[class].is_effectful
    }

    /// Every `(class, node)` pair, in order.
    pub fn enode_ids(&self) -> impl Iterator<Item = (EClassId, ENodeId)> + '_ {
        self.classes
            .iter()
            .enumerate()
            .flat_map(|(c, class)| (0..class.enodes.len()).map(move |n| (c, n)))
    }

    pub fn op_name(&self, enode: &ENode) -> Option<&str> {
        match enode.kind {
            NodeKind::Op(op) => Some(&self.ops[op].name),
            _ => None,
        }
    }

    /// Child positions of `enode` that start subregions.
    pub fn region_positions(&self, enode: &ENode) -> &[usize] {
        match enode.kind {
            NodeKind::Op(op) => &self.ops[op].regions,
            _ => &[],
        }
    }

    /// The children of `enode` with their position, split into
    /// `(non-region children, region children)`.
    pub fn split_children<'a>(
        &'a self,
        enode: &'a ENode,
    ) -> (
        impl Iterator<Item = EClassId> + 'a,
        impl Iterator<Item = EClassId> + 'a,
    ) {
        let regions = self.region_positions(enode);
        let plain = enode
            .children
            .iter()
            .enumerate()
            .filter(move |(i, _)| !regions.contains(i))
            .map(|(_, &c)| c);
        let region = regions.iter().map(move |&i| enode.children[i]);
        (plain, region)
    }

    /// The effectful child of `enode` that continues its region's statewalk:
    /// its effectful child outside the `:regions` positions, if any.
    pub fn state_child(&self, enode: &ENode) -> Option<EClassId> {
        self.split_children(enode).0.find(|&c| self.is_effectful(c))
    }

    /// Region roots below `enode`: effectful children at `:regions` positions.
    pub fn region_children<'a>(&'a self, enode: &'a ENode) -> impl Iterator<Item = EClassId> + 'a {
        self.split_children(enode)
            .1
            .filter(|&c| self.is_effectful(c))
    }

    /// For each e-class, the e-nodes that have it as a child (with multiplicity).
    pub fn parents(&self) -> Vec<Vec<(EClassId, ENodeId)>> {
        let mut parents = vec![Vec::new(); self.len()];
        for (c, n) in self.enode_ids() {
            for &child in &self.enode(c, n).children {
                parents[child].push((c, n));
            }
        }
        parents
    }

    /// The number of children of every e-node, indexed like the e-graph.
    pub fn child_counts(&self) -> Vec<Vec<usize>> {
        self.classes
            .iter()
            .map(|class| class.enodes.iter().map(|n| n.children.len()).collect())
            .collect()
    }

    /// An e-graph with the same ops and sorts but no e-classes.
    pub fn empty_like(&self) -> EGraph {
        EGraph {
            classes: Vec::new(),
            ops: self.ops.clone(),
            sorts: self.sorts.clone(),
        }
    }

    /// Which e-classes have a finite term: an e-node is extractable once all
    /// its children are, and an e-class once one of its e-nodes is.
    pub fn extractable_classes(&self) -> Vec<bool> {
        let parents = self.parents();
        let mut remaining = self.child_counts();
        let mut extractable = vec![false; self.len()];
        let mut queue = VecDeque::new();
        for (c, n) in self.enode_ids() {
            if remaining[c][n] == 0 && !extractable[c] {
                extractable[c] = true;
                queue.push_back(c);
            }
        }
        while let Some(u) = queue.pop_front() {
            for &(pc, pn) in &parents[u] {
                remaining[pc][pn] -= 1;
                if remaining[pc][pn] == 0 && !extractable[pc] {
                    extractable[pc] = true;
                    queue.push_back(pc);
                }
            }
        }
        extractable
    }

    /// Drop e-nodes that cannot be part of any finite term and e-classes that
    /// are unreachable from `root` (every e-class is kept when `root` is `None`).
    /// Returns the pruned e-graph and the mapping from this e-graph into it.
    pub fn prune_unextractable(&self, root: Option<EClassId>) -> (EGraph, EGraphMapping) {
        let extractable = self.extractable_classes();
        let mut queue = VecDeque::new();

        // Reachability from the root through extractable e-nodes.
        let mut reachable = vec![root.is_none(); self.len()];
        if let Some(root) = root {
            reachable[root] = true;
            queue.push_back(root);
            while let Some(u) = queue.pop_front() {
                for enode in &self.classes[u].enodes {
                    if enode.children.iter().all(|&v| extractable[v]) {
                        for &v in &enode.children {
                            if !reachable[v] {
                                reachable[v] = true;
                                queue.push_back(v);
                            }
                        }
                    }
                }
            }
        }

        let mut pruned = self.empty_like();
        let mut mapping = EGraphMapping::unmapped(self);
        for c in self.class_ids() {
            if reachable[c] && extractable[c] {
                mapping.classes[c] = Some(pruned.len());
                pruned.classes.push(EClass {
                    enodes: Vec::new(),
                    is_effectful: self.is_effectful(c),
                    sort: self.classes[c].sort,
                });
            }
        }
        for c in self.class_ids() {
            let Some(target) = mapping.classes[c] else {
                continue;
            };
            for (n, enode) in self.classes[c].enodes.iter().enumerate() {
                let children: Option<Vec<EClassId>> =
                    enode.children.iter().map(|&v| mapping.classes[v]).collect();
                if let Some(children) = children {
                    let class = &mut pruned.classes[target];
                    mapping.enodes[c][n] = Some(class.enodes.len());
                    class.enodes.push(ENode {
                        kind: enode.kind.clone(),
                        cost: enode.cost,
                        children,
                    });
                }
            }
        }
        debug_assert!(super::checks::is_wellformed(&pruned, false, true));
        debug_assert!(super::checks::is_valid_mapping(
            &mapping, self, &pruned, true, true, true, true
        ));
        (pruned, mapping)
    }
}

/// One e-node of an extracted term DAG. Children refer to earlier positions in
/// the [`Extraction`].
#[derive(Clone, Debug, Default)]
pub struct ExtractedNode {
    pub class: EClassId,
    pub node: ENodeId,
    pub children: Vec<ExtractionId>,
}

/// An extracted term DAG in topological order, children before parents. The
/// root is the last node.
pub type Extraction = Vec<ExtractedNode>;

/// A partial mapping from the e-classes and e-nodes of one e-graph (the
/// *source*) to those of another (the *target*).
#[derive(Clone, Debug, Default)]
pub struct EGraphMapping {
    pub classes: Vec<Option<EClassId>>,
    pub enodes: Vec<Vec<Option<ENodeId>>>,
}

impl EGraphMapping {
    /// A mapping with the shape of `source` that maps nothing yet.
    pub fn unmapped(source: &EGraph) -> Self {
        EGraphMapping {
            classes: vec![None; source.len()],
            enodes: source
                .classes
                .iter()
                .map(|class| vec![None; class.enodes.len()])
                .collect(),
        }
    }

    pub fn class(&self, class: EClassId) -> EClassId {
        self.classes[class].expect("e-class is not mapped")
    }

    pub fn enode(&self, class: EClassId, node: ENodeId) -> ENodeId {
        self.enodes[class][node].expect("e-node is not mapped")
    }

    /// The inverse mapping, from `target` back into the source.
    pub fn inverse(&self, target: &EGraph) -> EGraphMapping {
        let mut inv = EGraphMapping::unmapped(target);
        for (c, &mapped) in self.classes.iter().enumerate() {
            if let Some(tc) = mapped {
                inv.classes[tc] = Some(c);
                for (n, &mapped) in self.enodes[c].iter().enumerate() {
                    if let Some(tn) = mapped {
                        inv.enodes[tc][tn] = Some(n);
                    }
                }
            }
        }
        inv
    }

    /// `self` followed by `next`: a mapping from this source into `next`'s target.
    pub fn then(&self, next: &EGraphMapping) -> EGraphMapping {
        EGraphMapping {
            classes: self
                .classes
                .iter()
                .map(|c| c.and_then(|c| next.classes[c]))
                .collect(),
            enodes: self
                .enodes
                .iter()
                .enumerate()
                .map(|(c, nodes)| {
                    nodes
                        .iter()
                        .map(|n| match (self.classes[c], n) {
                            (Some(tc), Some(tn)) => next.enodes[tc][*tn],
                            _ => None,
                        })
                        .collect()
                })
                .collect(),
        }
    }

    /// Re-express an extraction over the source e-graph in terms of the target.
    pub fn apply(&self, extraction: &Extraction) -> Extraction {
        extraction
            .iter()
            .map(|en| ExtractedNode {
                class: self.class(en.class),
                node: self.enode(en.class, en.node),
                children: en.children.clone(),
            })
            .collect()
    }
}
