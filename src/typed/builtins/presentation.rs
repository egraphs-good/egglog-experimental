//! Rust generator policy. Semantic signatures remain in the native catalog.
use super::pb;
use prost::Message;
use serde_json::Value;
use std::{
    collections::{BTreeMap, HashMap, HashSet},
    sync::Arc,
};

#[derive(Clone, Debug, PartialEq)]
pub(super) struct SortRef {
    pub graph: Arc<pb::BuiltinCatalog>,
    pub root: u32,
}

#[derive(Clone, Debug, Default, PartialEq)]
pub(super) struct TypeView {
    pub path: Vec<String>,
    pub type_params: Vec<String>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub(super) struct Receiver {
    pub core_input: Option<u32>,
    pub borrowed: bool,
}

#[derive(Clone, Debug, Default, PartialEq)]
pub(super) struct Parameter {
    pub core_input: Option<u32>,
    pub name: String,
    pub borrowed: bool,
}

#[derive(Clone, Debug, Default, PartialEq)]
pub(super) struct TraitType {
    pub sort: Option<SortRef>,
    pub borrowed: bool,
}

#[derive(Clone, Debug, Default, PartialEq)]
pub(super) struct TraitView {
    pub path: Vec<String>,
    pub args: Vec<TraitType>,
    pub output_associated_type: Option<String>,
}

#[derive(Clone, Debug, Default, PartialEq)]
pub(super) struct CallableView {
    pub path: Vec<String>,
    pub owner_sort: Option<SortRef>,
    pub borrowed_self: bool,
    pub receiver: Option<Receiver>,
    pub params: Vec<Parameter>,
    pub trait_impl: Option<TraitView>,
    pub tail_repetitions: Option<u32>,
}

#[derive(Clone, Debug, Default, PartialEq)]
pub(super) struct RustPresentation {
    // Separate existing namespaces; names are exact canonical keys.
    pub families: BTreeMap<String, TypeView>,
    pub callables: BTreeMap<String, Vec<CallableView>>,
}

fn strings(value: &Value, field: &str) -> Result<Vec<String>, String> {
    value.get(field).map_or(Ok(vec![]), |values| {
        values
            .as_array()
            .ok_or_else(|| format!("{field} must be an array"))?
            .iter()
            .map(|v| {
                v.as_str()
                    .map(str::to_owned)
                    .ok_or_else(|| format!("{field} must contain strings"))
            })
            .collect()
    })
}

fn index(value: &Value, field: &str) -> Result<Option<u32>, String> {
    value
        .get(field)
        .map(|v| {
            v.as_u64()
                .and_then(|n| u32::try_from(n).ok())
                .ok_or_else(|| format!("{field} must be a u32"))
        })
        .transpose()
}

fn sort_refs(value: &Value, field: &str) -> Result<Vec<u32>, String> {
    value.get(field).map_or(Ok(vec![]), |values| {
        values
            .as_array()
            .ok_or_else(|| format!("{field} must be an array"))?
            .iter()
            .map(|v| {
                v.as_u64()
                    .and_then(|n| u32::try_from(n).ok())
                    .ok_or_else(|| format!("{field} must contain sort indices"))
            })
            .collect()
    })
}

fn owned_sort(
    value: &Value,
    field: &str,
    graph: &Arc<pb::BuiltinCatalog>,
) -> Result<Option<SortRef>, String> {
    index(value, field)?
        .map(|root| {
            graph
                .sorts
                .get(root as usize)
                .ok_or("presentation sort reference out of bounds")?;
            Ok(SortRef {
                graph: graph.clone(),
                root,
            })
        })
        .transpose()
}

impl RustPresentation {
    pub fn builtin() -> Result<Self, String> {
        let data: Value =
            serde_json::from_str(include_str!("rust.json")).map_err(|e| e.to_string())?;
        let sorts = data["sorts"]
            .as_array()
            .ok_or("missing presentation type graph")?
            .iter()
            .map(|sort| {
                let kind = if let Some(family) = sort.get("primitive") {
                    pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
                        name: family["name"]
                            .as_str()
                            .ok_or("missing presentation family name")?
                            .into(),
                        args: sort_refs(family, "args")?,
                    })
                } else if let Some(function) = sort.get("func") {
                    pb::sort::Kind::Func(pb::FuncSort {
                        params: sort_refs(function, "params")?,
                        result: index(function, "result")?.unwrap_or(0),
                    })
                } else if let Some(variable) = index(sort, "var")? {
                    pb::sort::Kind::Var(variable)
                } else if let Some(name) = sort.get("eq").and_then(Value::as_str) {
                    pb::sort::Kind::Eq(name.into())
                } else {
                    return Err("invalid presentation sort".into());
                };
                Ok(pb::Sort {
                    kind: Some(kind),
                    ..Default::default()
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        let graph = Arc::new(pb::BuiltinCatalog {
            sorts,
            ..Default::default()
        });
        let mut families = BTreeMap::new();
        for (name, value) in data["families"]
            .as_object()
            .ok_or("missing Rust family map")?
        {
            families.insert(
                name.clone(),
                TypeView {
                    path: strings(value, "path")?,
                    type_params: strings(value, "typeParams")?,
                },
            );
        }
        let mut callables = BTreeMap::new();
        for (name, values) in data["callables"]
            .as_object()
            .ok_or("missing Rust callable map")?
        {
            let mut views = vec![];
            for value in values
                .as_array()
                .ok_or("Rust callable views must be an array")?
            {
                let receiver = value
                    .get("receiver")
                    .map(|r| {
                        Ok::<_, String>(Receiver {
                            core_input: index(r, "coreInput")?
                                .or_else(|| r.is_object().then_some(0)),
                            borrowed: r["borrowed"].as_bool().unwrap_or(false),
                        })
                    })
                    .transpose()?;
                let params = value.get("params").map_or(Ok(vec![]), |params| {
                    params
                        .as_array()
                        .ok_or("Rust parameters must be an array")?
                        .iter()
                        .enumerate()
                        .map(|(position, p)| {
                            let slot = position
                                + usize::from(
                                    receiver
                                        .and_then(|r| r.core_input)
                                        .is_some_and(|receiver| position >= receiver as usize),
                                );
                            Ok(Parameter {
                                core_input: Some(
                                    index(p, "coreInput")?.unwrap_or(
                                        u32::try_from(slot)
                                            .map_err(|_| "Rust parameter slot exceeds u32")?,
                                    ),
                                ),
                                name: p["name"]
                                    .as_str()
                                    .ok_or("missing Rust parameter name")?
                                    .into(),
                                borrowed: p["borrowed"].as_bool().unwrap_or(false),
                            })
                        })
                        .collect::<Result<Vec<_>, String>>()
                })?;
                let trait_impl = value
                    .get("traitImpl")
                    .map(|t| {
                        let args = t.get("args").map_or(Ok(vec![]), |args| {
                            args.as_array()
                                .ok_or("Rust trait arguments must be an array")?
                                .iter()
                                .map(|a| {
                                    Ok(TraitType {
                                        sort: owned_sort(a, "sort", &graph)?,
                                        borrowed: a["borrowed"].as_bool().unwrap_or(false),
                                    })
                                })
                                .collect::<Result<Vec<_>, String>>()
                        })?;
                        Ok::<_, String>(TraitView {
                            path: strings(t, "path")?,
                            args,
                            output_associated_type: t
                                .get("outputAssociatedType")
                                .and_then(Value::as_str)
                                .map(str::to_owned),
                        })
                    })
                    .transpose()?;
                views.push(CallableView {
                    path: if value.get("path").is_some() {
                        strings(value, "path")?
                    } else {
                        vec![name.rsplit('.').next().unwrap().into()]
                    },
                    owner_sort: owned_sort(value, "ownerSort", &graph)?,
                    borrowed_self: value["borrowedSelf"].as_bool().unwrap_or(false),
                    receiver,
                    params,
                    trait_impl,
                    tail_repetitions: index(value, "tailRepetitions")?,
                });
            }
            callables.insert(name.clone(), views);
        }
        Ok(Self {
            families,
            callables,
        })
    }

    // Adopt only referenced type closures. The resulting local references all
    // retain the same complete semantic catalog owner; source indices never
    // become mapping identities and original catalog locations stay stable.
    pub fn join(
        &self,
        semantic: &pb::BuiltinCatalog,
    ) -> Result<(pb::BuiltinCatalog, Self), String> {
        let families: HashSet<&str> = semantic
            .primitive_sorts
            .iter()
            .map(|p| p.name.as_str())
            .collect();
        let callables: HashSet<&str> = semantic
            .primitives
            .iter()
            .map(|p| p.name.as_str())
            .collect();
        for name in self.families.keys() {
            if !families.contains(name.as_str()) {
                return Err(format!("orphan Rust family mapping: {name}"));
            }
        }
        for name in self.callables.keys() {
            if !callables.contains(name.as_str()) {
                return Err(format!("orphan Rust callable mapping: {name}"));
            }
        }
        let mut program = semantic.clone();
        let mut kinds = HashMap::new();
        let keys = sort_keys(semantic, &mut kinds)?;
        let mut installed = HashMap::new();
        for (index, key) in keys.into_iter().enumerate() {
            installed.entry(key).or_insert(index as u32);
        }
        let mut graphs = HashMap::new();
        let mut presentation = self.clone();
        for view in presentation.callables.values_mut().flatten() {
            for reference in view.owner_sort.iter_mut().chain(
                view.trait_impl
                    .iter_mut()
                    .flat_map(|t| &mut t.args)
                    .filter_map(|a| a.sort.as_mut()),
            ) {
                let graph_id = Arc::as_ptr(&reference.graph) as usize;
                if let std::collections::hash_map::Entry::Vacant(entry) = graphs.entry(graph_id) {
                    entry.insert(sort_keys(&reference.graph, &mut kinds)?);
                }
                let keys = &graphs[&graph_id];
                reference.root = import_sort(
                    &reference.graph,
                    reference.root,
                    keys,
                    &mut installed,
                    &mut program,
                )?;
            }
        }
        let graph = Arc::new(program.clone());
        for view in presentation.callables.values_mut().flatten() {
            for reference in view.owner_sort.iter_mut().chain(
                view.trait_impl
                    .iter_mut()
                    .flat_map(|t| &mut t.args)
                    .filter_map(|a| a.sort.as_mut()),
            ) {
                reference.graph = graph.clone();
            }
        }
        Ok((program, presentation))
    }
}

// Canonicalize semantic Sort kinds in one shared interner. Positions and docs
// are not identity, and cycle/bounds failures are reported before generation.
fn sort_keys(
    program: &pb::BuiltinCatalog,
    kinds: &mut HashMap<Vec<u8>, u32>,
) -> Result<Vec<u32>, String> {
    let mut keys = vec![None; program.sorts.len()];
    let mut active = vec![false; program.sorts.len()];
    for root in 0..program.sorts.len() as u32 {
        let mut pending = vec![(root, false)];
        while let Some((index, finish)) = pending.pop() {
            let slot = index as usize;
            if keys
                .get(slot)
                .ok_or("presentation sort reference out of bounds")?
                .is_some()
            {
                continue;
            }
            let mut kind = program.sorts[slot]
                .kind
                .clone()
                .ok_or("missing presentation sort kind")?;
            if !finish {
                if std::mem::replace(&mut active[slot], true) {
                    return Err("cyclic presentation sort".into());
                }
                pending.push((index, true));
                match &kind {
                    pb::sort::Kind::Primitive(f) => {
                        pending.extend(f.args.iter().rev().map(|&i| (i, false)))
                    }
                    pb::sort::Kind::Func(f) => pending.extend(
                        f.params
                            .iter()
                            .chain([&f.result])
                            .rev()
                            .map(|&i| (i, false)),
                    ),
                    _ => {}
                }
                continue;
            }
            match &mut kind {
                pb::sort::Kind::Primitive(f) => {
                    for child in &mut f.args {
                        *child = keys[*child as usize].unwrap();
                    }
                }
                pb::sort::Kind::Func(f) => {
                    for child in &mut f.params {
                        *child = keys[*child as usize].unwrap();
                    }
                    f.result = keys[f.result as usize].unwrap();
                }
                _ => {}
            }
            let encoded = pb::Sort {
                kind: Some(kind),
                ..Default::default()
            }
            .encode_to_vec();
            let next =
                u32::try_from(kinds.len()).map_err(|_| "presentation sort space exhausted")?;
            keys[slot] = Some(*kinds.entry(encoded).or_insert(next));
            active[slot] = false;
        }
    }
    Ok(keys.into_iter().map(Option::unwrap).collect())
}

fn import_sort(
    graph: &pb::BuiltinCatalog,
    root: u32,
    keys: &[u32],
    installed: &mut HashMap<u32, u32>,
    program: &mut pb::BuiltinCatalog,
) -> Result<u32, String> {
    let mut pending = vec![(root, false)];
    while let Some((index, finish)) = pending.pop() {
        let key = *keys
            .get(index as usize)
            .ok_or("presentation sort reference out of bounds")?;
        if installed.contains_key(&key) {
            continue;
        }
        let mut sort = graph.sorts[index as usize].clone();
        let kind = sort.kind.as_mut().ok_or("missing presentation sort kind")?;
        if !finish {
            pending.push((index, true));
            match kind {
                pb::sort::Kind::Primitive(f) => {
                    pending.extend(f.args.iter().rev().map(|&i| (i, false)))
                }
                pb::sort::Kind::Func(f) => pending.extend(
                    f.params
                        .iter()
                        .chain([&f.result])
                        .rev()
                        .map(|&i| (i, false)),
                ),
                _ => {}
            }
            continue;
        }
        match kind {
            pb::sort::Kind::Primitive(f) => {
                for child in &mut f.args {
                    *child = installed[&keys[*child as usize]];
                }
            }
            pb::sort::Kind::Func(f) => {
                for child in &mut f.params {
                    *child = installed[&keys[*child as usize]];
                }
                f.result = installed[&keys[f.result as usize]];
            }
            _ => {}
        }
        let destination = u32::try_from(program.sorts.len())
            .map_err(|_| "Rust presentation sort space exhausted")?;
        program.sorts.push(sort);
        installed.insert(key, destination);
    }
    Ok(installed[&keys[root as usize]])
}
