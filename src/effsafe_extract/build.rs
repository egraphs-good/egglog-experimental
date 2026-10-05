//! Build the extractor's e-graph from an egglog e-graph.
//!
//! Every extractable constructor row becomes an e-node; base values and
//! containers become leaf-like nodes; children of placeholder sorts point at a
//! single placeholder e-class per sort. Effectful e-classes are those in the
//! program's effectful relation. The result is restricted to what the roots
//! reach and pruned of e-nodes that cannot be part of a finite term.

use std::collections::VecDeque;
use std::hash::BuildHasherDefault;

use egglog::ast::FunctionSubtype;
use egglog::extract::DagCostModel;
use egglog::{ArcSort, Error, Value};
use indexmap::IndexMap;
use rustc_hash::FxHasher;

use super::EffsafeConfig;
use super::cost::Cost;
use super::egraph::{EClass, EClassId, EGraph, ENode, NodeKind, OpInfo, SortId};

type FxIndexMap<K, V> = IndexMap<K, V, BuildHasherDefault<FxHasher>>;

/// What to extract.
pub enum Roots<'a> {
    /// These e-classes.
    Values(Vec<(ArcSort, Value)>),
    /// Every e-class holding an e-node of this constructor.
    Constructor(&'a str),
}

/// An e-class before numbering: (sort index, canonical value).
type ClassKey = (SortId, Value);

struct Builder<'e> {
    egraph: &'e egglog::EGraph,
    config: &'e EffsafeConfig,
    cost_model: &'e dyn DagCostModel<Cost>,
    g: EGraph,
    sort_ids: FxIndexMap<String, SortId>,
    class_ids: FxIndexMap<ClassKey, EClassId>,
    /// The single e-class standing in for each placeholder sort.
    placeholder_classes: FxIndexMap<SortId, EClassId>,
}

impl<'e> Builder<'e> {
    fn sort_id(&mut self, sort: &ArcSort) -> SortId {
        if let Some(&id) = self.sort_ids.get(sort.name()) {
            return id;
        }
        let id = self.g.sorts.len();
        self.g.sorts.push(sort.clone());
        self.sort_ids.insert(sort.name().to_string(), id);
        id
    }

    fn class_for(&mut self, sort: SortId, value: Value) -> EClassId {
        *self.class_ids.entry((sort, value)).or_insert_with(|| {
            self.g.classes.push(EClass {
                enodes: Vec::new(),
                is_effectful: false,
                sort,
            });
            self.g.len() - 1
        })
    }

    /// The e-class of a child value of the given sort, creating leaf nodes for
    /// base values and containers on first sight.
    fn child_class(&mut self, sort: &ArcSort, value: Value) -> EClassId {
        let sort_id = self.sort_id(sort);
        if self.config.placeholders.contains_key(sort.name()) {
            return *self.placeholder_classes.entry(sort_id).or_insert_with(|| {
                self.g.classes.push(EClass {
                    enodes: vec![ENode {
                        kind: NodeKind::Placeholder,
                        cost: 0,
                        children: Vec::new(),
                    }],
                    is_effectful: false,
                    sort: sort_id,
                });
                self.g.len() - 1
            });
        }
        if sort.is_eq_sort() {
            return self.class_for(sort_id, value);
        }
        if let Some(&class) = self.class_ids.get(&(sort_id, value)) {
            return class;
        }
        let class = self.class_for(sort_id, value);
        let enode = if sort.is_container_sort() {
            let children = self
                .egraph
                .container_inner_values(sort, value)
                .into_iter()
                .map(|(inner_sort, inner)| self.child_class(&inner_sort, inner))
                .collect();
            ENode {
                kind: NodeKind::Container(value),
                cost: self.cost_model.container_cost(self.egraph, sort, value),
                children,
            }
        } else {
            ENode {
                kind: NodeKind::Base(value),
                cost: self.cost_model.base_value_cost(self.egraph, sort, value),
                children: Vec::new(),
            }
        };
        self.g.classes[class].enodes.push(enode);
        class
    }

    /// Add every row of every extractable constructor.
    fn collect(&mut self) -> Result<(), Error> {
        let functions: Vec<_> = self
            .egraph
            .functions_iter()
            .filter(|(_, func)| {
                let ty = func.func_type();
                ty.subtype == FunctionSubtype::Constructor
                    && ty.output.is_eq_sort()
                    && !func.is_hidden()
                    && !func.is_unextractable()
                    && !func.is_let_binding()
            })
            .map(|(name, func)| (name.clone(), func))
            .collect();
        for (name, func) in functions {
            let ty = func.func_type();
            let regions = self.config.regions.get(&name).cloned().unwrap_or_default();
            if let Some(&bad) = regions.iter().find(|&&p| p >= ty.input.len()) {
                return Err(Error::ExtractError(format!(
                    "constructor {name} has {} arguments, but :regions names position {bad}",
                    ty.input.len()
                )));
            }
            let op = self.g.ops.len();
            self.g.ops.push(OpInfo {
                name: name.clone(),
                regions,
            });
            let out_sort = self.sort_id(&ty.output);
            let mut rows: Vec<(Value, Vec<Value>, Cost)> = Vec::new();
            self.egraph.constructor_enodes(&name, |enode| {
                if !enode.subsumed || self.config.include_subsumed {
                    let cost = self.cost_model.enode_cost(self.egraph, func, &enode);
                    rows.push((enode.eclass, enode.children.to_vec(), cost));
                }
            })?;
            for (eclass, children, cost) in rows {
                let children = children
                    .iter()
                    .zip(&ty.input)
                    .map(|(&v, sort)| self.child_class(sort, v))
                    .collect();
                let class = self.class_for(out_sort, eclass);
                self.g.classes[class].enodes.push(ENode {
                    kind: NodeKind::Op(op),
                    cost,
                    children,
                });
            }
        }
        Ok(())
    }

    /// Mark the e-classes in the effectful relation.
    fn mark_effectful(&mut self, relation: &str) -> Result<(), Error> {
        let Some(func) = self.egraph.get_function(relation) else {
            return Err(Error::ExtractError(format!(
                "effectful relation {relation} is not declared"
            )));
        };
        let ty = func.func_type();
        let [sort] = &ty.input[..] else {
            return Err(Error::ExtractError(format!(
                "effectful relation {relation} must take exactly one argument"
            )));
        };
        if !sort.is_eq_sort() {
            return Err(Error::ExtractError(format!(
                "effectful relation {relation} must range over an eq sort"
            )));
        }
        let sort_id = self.sort_id(sort);
        let mut values = Vec::new();
        match ty.subtype {
            FunctionSubtype::Constructor => self
                .egraph
                .constructor_enodes(relation, |enode| values.push(enode.children[0]))?,
            FunctionSubtype::Custom => self
                .egraph
                .function_entries(relation, |entry| values.push(entry.inputs[0]))?,
        }
        for value in values {
            if let Some(&class) = self.class_ids.get(&(sort_id, value)) {
                self.g.classes[class].is_effectful = true;
            }
        }
        Ok(())
    }

    fn resolve_roots(&mut self, roots: &Roots) -> Result<Vec<EClassId>, Error> {
        match roots {
            Roots::Values(values) => values
                .iter()
                .map(|(sort, value)| {
                    let sort_id = self.sort_id(sort);
                    self.class_ids
                        .get(&(sort_id, *value))
                        .copied()
                        .ok_or_else(|| {
                            Error::ExtractError(format!(
                                "root of sort {} has no extractable e-nodes",
                                sort.name()
                            ))
                        })
                })
                .collect(),
            Roots::Constructor(name) => {
                let Some(op) = self.g.ops.iter().position(|o| o.name == *name) else {
                    return Err(Error::ExtractError(format!(
                        "{name} is not an extractable constructor"
                    )));
                };
                Ok(self
                    .g
                    .class_ids()
                    .filter(|&c| {
                        self.g.classes[c]
                            .enodes
                            .iter()
                            .any(|n| matches!(n.kind, NodeKind::Op(o) if o == op))
                    })
                    .collect())
            }
        }
    }

    /// Every effectful e-node has at most one effectful child outside its
    /// `:regions` positions, and every root is effectful.
    fn validate(&self, roots: &[EClassId]) -> Result<(), Error> {
        let g = &self.g;
        for c in g.class_ids().filter(|&c| g.is_effectful(c)) {
            for enode in &g.classes[c].enodes {
                let effectful: Vec<usize> = g
                    .split_children(enode)
                    .0
                    .enumerate()
                    .filter(|&(_, child)| g.is_effectful(child))
                    .map(|(i, _)| i)
                    .collect();
                if effectful.len() > 1 {
                    let op = g.op_name(enode).unwrap_or("<container>");
                    return Err(Error::ExtractError(format!(
                        "effectful e-node {op} has {} effectful children that are not \
                         marked as regions; annotate the subregions with :regions",
                        effectful.len()
                    )));
                }
            }
        }
        for &root in roots {
            if !g.is_effectful(root) {
                let names: Vec<&str> = g.classes[root]
                    .enodes
                    .iter()
                    .filter_map(|n| g.op_name(n))
                    .collect();
                return Err(Error::ExtractError(format!(
                    "extraction root is not effectful (e-class with {names:?}); \
                     effsafe-extract roots must be in the effectful relation"
                )));
            }
        }
        Ok(())
    }

    /// Keep only the e-classes the roots reach. Returns the new root ids.
    fn restrict_to_reachable(&mut self, roots: &[EClassId]) -> Vec<EClassId> {
        let g = &self.g;
        let mut reachable = vec![false; g.len()];
        let mut queue: VecDeque<EClassId> = VecDeque::new();
        for &root in roots {
            if !reachable[root] {
                reachable[root] = true;
                queue.push_back(root);
            }
        }
        while let Some(u) = queue.pop_front() {
            for enode in &g.classes[u].enodes {
                for &child in &enode.children {
                    if !reachable[child] {
                        reachable[child] = true;
                        queue.push_back(child);
                    }
                }
            }
        }
        let mut new_id = vec![None; g.len()];
        let mut kept = g.empty_like();
        for c in g.class_ids().filter(|&c| reachable[c]) {
            new_id[c] = Some(kept.len());
            kept.classes.push(EClass {
                enodes: Vec::new(),
                is_effectful: g.is_effectful(c),
                sort: g.classes[c].sort,
            });
        }
        for c in g.class_ids().filter(|&c| reachable[c]) {
            let target = new_id[c].unwrap();
            for enode in &g.classes[c].enodes {
                kept.classes[target].enodes.push(ENode {
                    kind: enode.kind.clone(),
                    cost: enode.cost,
                    children: enode.children.iter().map(|&v| new_id[v].unwrap()).collect(),
                });
            }
        }
        let roots = roots.iter().map(|&r| new_id[r].unwrap()).collect();
        self.g = kept;
        roots
    }
}

/// Build the extractor's e-graph for `egraph` and resolve the roots.
pub fn build(
    egraph: &egglog::EGraph,
    config: &EffsafeConfig,
    cost_model: &dyn DagCostModel<Cost>,
    effectful: &str,
    roots: &Roots,
) -> Result<(EGraph, Vec<EClassId>), Error> {
    let mut builder = Builder {
        egraph,
        config,
        cost_model,
        g: EGraph::default(),
        sort_ids: FxIndexMap::default(),
        class_ids: FxIndexMap::default(),
        placeholder_classes: FxIndexMap::default(),
    };
    builder.collect()?;
    builder.mark_effectful(effectful)?;
    let roots = builder.resolve_roots(roots)?;
    builder.validate(&roots)?;
    let roots = builder.restrict_to_reachable(&roots);
    let (pruned, mapping) = builder.g.prune_unextractable(None);
    let roots = roots
        .iter()
        .map(|&r| {
            mapping.classes[r].ok_or_else(|| {
                Error::ExtractError(format!(
                    "extraction root has no finite term: {}",
                    explain_unextractable(&builder.g, r)
                ))
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((pruned, roots))
}

/// Why e-class `class` has no finite term: summarize the e-classes without a
/// finite term by sort, and list the ones with no extractable e-node at all,
/// which are the usual culprits (a sort whose only constructors are
/// `:unextractable`, or one that should be a placeholder).
fn explain_unextractable(g: &EGraph, class: EClassId) -> String {
    let extractable = g.extractable_classes();
    let root_ops: Vec<&str> = g.classes[class]
        .enodes
        .iter()
        .filter_map(|n| g.op_name(n))
        .collect();
    let mut by_sort: Vec<(String, usize)> = Vec::new();
    let mut empty: Vec<String> = Vec::new();
    for c in g.class_ids().filter(|&c| !extractable[c]) {
        let sort = g.sorts[g.classes[c].sort].name().to_string();
        match by_sort.iter_mut().find(|(s, _)| *s == sort) {
            Some((_, n)) => *n += 1,
            None => by_sort.push((sort.clone(), 1)),
        }
        if g.classes[c].enodes.is_empty() && empty.len() < 8 {
            empty.push(sort);
        }
    }
    let mut details = String::new();
    if std::env::var_os("EFFSAFE_DEBUG").is_some() {
        let boring = ["Get", "Bop", "Uop", "Top", "Concat", "Single"];
        for c in g
            .class_ids()
            .filter(|&c| !extractable[c])
            .filter(|&c| {
                std::env::var("EFFSAFE_DEBUG").as_deref() == Ok("all")
                    || g.classes[c]
                        .enodes
                        .iter()
                        .any(|n| !boring.contains(&g.op_name(n).unwrap_or("<leaf>")))
            })
            .take(200)
        {
            details.push_str(&format!(
                "\n  class {c} ({}):",
                g.sorts[g.classes[c].sort].name()
            ));
            for n in &g.classes[c].enodes {
                let op = g.op_name(n).unwrap_or("<leaf>");
                let kids: Vec<String> = n
                    .children
                    .iter()
                    .map(|&k| {
                        format!(
                            "{}#{k}{}",
                            g.sorts[g.classes[k].sort].name(),
                            if extractable[k] { "" } else { "!" }
                        )
                    })
                    .collect();
                details.push_str(&format!("\n    {op} {kids:?}"));
            }
        }
    }
    format!(
        "root e-class (e-nodes {root_ops:?}); e-classes without a finite term by sort: {by_sort:?}; \
         e-classes with no extractable e-node (unextractable constructors only): {empty:?}{details}"
    )
}
