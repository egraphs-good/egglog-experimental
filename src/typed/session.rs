use super::{
    EgglogValue, TypedError,
    expr::{Expr, ValueInput},
    pb,
    rule::{Facts, Ruleset, ensure_sort},
    storage::{Arena, Key, Packer, Record, Slot, publish},
};
use prost::Message;
use std::collections::{HashMap, HashSet};

/// A byte-protocol session. No native EGraph or AST execution escape hatch.
pub struct EGraph {
    engine: crate::protobuf::Engine,
    handle: u64,
    installed: HashMap<Key, (Record, pb::RulesetRef)>,
    installed_rules: HashSet<Key>,
    declarations: HashMap<String, Record>,
    #[cfg(test)]
    last_wire: Option<(Vec<u8>, Vec<u8>)>,
}

impl Default for EGraph {
    fn default() -> Self {
        Self::new().expect("default byte engine creation")
    }
}

impl EGraph {
    /// Create a byte engine with the adapter's supported i64 cost domain.
    pub fn new() -> Result<Self, TypedError> {
        let mut engine = crate::protobuf::Engine::default();
        // Creation's fixed i64 cost domain is an adapter requirement, not a
        // Rust primitive callable registry. No typed scalar API is exposed.
        let request = pb::CreateEGraphRequest {
            sorts: vec![pb::Sort {
                kind: Some(pb::sort::Kind::Family(pb::HostSort {
                    name: "i64".into(),
                    args: vec![],
                })),
                ..Default::default()
            }],
            options: Some(pb::EGraphOptions { cost_sort: Some(0) }),
            ..Default::default()
        };
        let response = engine
            .create(&request.encode_to_vec())
            .map_err(|e| TypedError::Invalid(e.to_string()))?;
        let handle = pb::CreateEGraphResponse::decode(response.as_slice())
            .map_err(|e| TypedError::Decode(e.to_string()))?
            .egraph_id;
        Ok(Self {
            engine,
            handle,
            installed: HashMap::new(),
            installed_rules: HashSet::new(),
            declarations: HashMap::new(),
            #[cfg(test)]
            last_wire: None,
        })
    }

    fn execute(&mut self, mut packer: Packer) -> Result<pb::RunProgramResponse, TypedError> {
        packer.finish()?;
        let request = pb::RunProgramRequest {
            egraph_id: self.handle,
            program: Some(packer.program),
            profile: true,
        }
        .encode_to_vec();
        let bytes = self
            .engine
            .run(&request)
            .map_err(|e| TypedError::Invalid(e.to_string()))?;
        let response = pb::RunProgramResponse::decode(bytes.as_slice())
            .map_err(|e| TypedError::Decode(e.to_string()))?;
        #[cfg(test)]
        {
            self.last_wire = Some((request, bytes));
        }
        if let Some(error) = response.error.clone() {
            return Err(TypedError::Engine(Box::new(error)));
        }
        self.declarations.extend(packer.declarations);
        Ok(response)
    }

    /// Evaluate expressions as ordered top-level actions.
    pub fn register(&mut self, values: impl Facts) -> Result<(), TypedError> {
        let mut roots = vec![];
        values.append(&mut roots);
        let mut packer = Packer::default();
        for root in roots {
            let index = packer.intern(root.0, 0);
            packer.program.commands.push(pb::Command {
                kind: Some(pb::command::Kind::Action(pb::Action {
                    kind: Some(pb::action::Kind::Term(index)),
                    ..Default::default()
                })),
                ..Default::default()
            });
        }
        self.execute(packer)?;
        Ok(())
    }

    /// Returns the decoded wire response, including its actual profile/outcomes.
    /// The current adapter requires profile collection enabled.
    pub fn run(&mut self, ruleset: &Ruleset) -> Result<pb::RunProgramResponse, TypedError> {
        let root = &ruleset.0;
        let owner = root.owner.as_ref().unwrap();
        let key = (owner.id, root.arena, root.index);
        let mut packer = Packer::default();
        let mut newly_installed = None;
        let reference = if let Some((_, reference)) = self.installed.get(&key) {
            reference.clone()
        } else {
            let Some(pb::ruleset::Kind::Rules(list)) =
                &owner.program.rulesets[root.index as usize].kind
            else {
                unreachable!()
            };
            let mut keys = HashSet::new();
            for i in &list.rules {
                let r = root.resolve(Arena::Rule, *i)?;
                let key = (r.owner.as_ref().unwrap().id, r.arena, r.index);
                if self.installed_rules.contains(&key) {
                    return Err(TypedError::Invalid(
                        "shared rules across distinct groups await adapter occurrence matching"
                            .into(),
                    ));
                }
                keys.insert(key);
            }
            let index = packer.intern(root.clone(), 0);
            packer.finish()?;
            let name = if let Some(name) = &packer.program.rulesets[index as usize].name {
                name.clone() // Some("") is the explicit default root, not absent.
            } else {
                let reserved: HashSet<_> = self
                    .installed
                    .values()
                    .filter_map(|(_, reference)| {
                        if let Some(pb::ruleset_ref::Kind::Name(name)) = &reference.kind {
                            Some(name.as_str())
                        } else {
                            None
                        }
                    })
                    .chain(
                        packer
                            .program
                            .rulesets
                            .iter()
                            .filter_map(|r| r.name.as_deref()),
                    )
                    .collect();
                let mut ordinal = self.installed.len();
                let name = loop {
                    let name = format!("__typed_ruleset_{ordinal}");
                    if !reserved.contains(name.as_str()) {
                        break name;
                    }
                    ordinal += 1;
                };
                packer.program.rulesets[index as usize].name = Some(name.clone());
                name
            };
            let reference = pb::RulesetRef {
                kind: Some(pb::ruleset_ref::Kind::Name(name)),
            };
            newly_installed = Some((keys, reference.clone()));
            reference
        };
        packer.program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Run(pb::Run {
                ruleset: Some(reference),
                ..Default::default()
            })),
            ..Default::default()
        });
        let response = self.execute(packer)?;
        if let Some((keys, reference)) = newly_installed {
            self.installed_rules.extend(keys);
            self.installed.insert(key, (root.clone(), reference));
        }
        Ok(response)
    }

    /// Query all facts in one binder without inserting missing rows.
    pub fn check(&mut self, facts: impl Facts) -> Result<bool, TypedError> {
        let mut roots = vec![];
        facts.append(&mut roots);
        let roots: Vec<_> = roots.into_iter().map(|e| e.0).collect();
        let mut packer = Packer::default();
        packer.binders.push(super::close::binder(&roots)?);
        let facts = roots.into_iter().map(|r| packer.intern(r, 1)).collect();
        packer.program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Check(pb::Check { facts })),
            ..Default::default()
        });
        match self.execute(packer) {
            Ok(_) => Ok(true),
            Err(TypedError::Engine(error)) if error.code == pb::ErrorCode::CheckFailed as i32 => {
                Ok(false)
            }
            Err(error) => Err(error),
        }
    }

    /// Tree-extract one equality value and own the decoded finite term closure.
    pub fn extract<L: ValueInput>(&mut self, root: L) -> Result<L::Owned, TypedError> {
        let mut packer = Packer::default();
        let index = packer.intern(root.borrow().expression().0.clone(), 0);
        packer.program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Extract(pb::Extract {
                roots: vec![index],
                variants: 1,
                extractor: pb::Extractor::Tree.into(),
                ..Default::default()
            })),
            ..Default::default()
        });
        let response = self.execute(packer)?;
        let term = response
            .outputs
            .iter()
            .find_map(|output| match &output.kind {
                Some(pb::command_output::Kind::Extraction(result)) => {
                    result.roots.first()?.variants.first().map(|v| v.term)
                }
                _ => None,
            })
            .ok_or_else(|| TypedError::Decode("missing extraction result".into()))?;
        ensure_sort(adopt(
            &response,
            term,
            self.declarations.values().cloned().collect(),
        )?)
    }
}

// Adopt only the selected inert term closure. Other response nodes can be
// scalar costs or independent observations and are not this expression's roots.
fn adopt(
    response: &pb::RunProgramResponse,
    root: u32,
    declarations: Vec<Record>,
) -> Result<Expr, TypedError> {
    let mut program = pb::Program {
        ir_version: 1,
        ..Default::default()
    };
    let mut ids = HashMap::from([(root, 0u32)]);
    let mut pending = vec![root];
    let mut sorts = HashMap::new();
    let mut cursor = 0;
    while cursor < pending.len() {
        let old = pending[cursor];
        let mut node = response
            .nodes
            .get(old as usize)
            .cloned()
            .ok_or_else(|| TypedError::Decode("invalid response node index".into()))?;
        let sort = response
            .sorts
            .get(node.sort_id as usize)
            .ok_or_else(|| TypedError::Decode("invalid response sort index".into()))?;
        let index = if let Some(index) = sorts.get(&node.sort_id) {
            *index
        } else {
            let index = program.sorts.len() as u32;
            let Some(pb::sort::Kind::Eq(name)) = &sort.kind else {
                return Err(TypedError::Decode(
                    "typed extraction currently supports equality sorts".into(),
                ));
            };
            program.sorts.push(sort.clone());
            program.declarations.push(pb::Declaration {
                kind: Some(pb::declaration::Kind::EqSort(pb::EqSort {
                    name: name.clone(),
                    ..Default::default()
                })),
                ..Default::default()
            });
            sorts.insert(node.sort_id, index);
            index
        };
        node.sort_id = index;
        let Some(pb::node::Kind::Call(call)) = &mut node.kind else {
            return Err(TypedError::Decode(
                "extraction must contain inert constructor data, not an open binder".into(),
            ));
        };
        for child in &mut call.args {
            let next = ids.len() as u32;
            if let std::collections::hash_map::Entry::Vacant(entry) = ids.entry(*child) {
                entry.insert(next);
                pending.push(*child);
            }
            *child = ids[child];
        }
        program.nodes.push(node);
        cursor += 1;
    }
    // The selected term must be finite, not merely index-closed. Use an explicit
    // DFS stack so a legitimate deep extraction does not consume the Rust stack.
    let mut colors = vec![0u8; program.nodes.len()];
    let mut pending = vec![(0usize, false)];
    while let Some((index, finish)) = pending.pop() {
        if finish {
            colors[index] = 2;
            continue;
        }
        match colors[index] {
            2 => continue,
            1 => {
                return Err(TypedError::Decode(
                    "cyclic extraction is not inert data".into(),
                ));
            }
            _ => colors[index] = 1,
        }
        pending.push((index, true));
        let Some(pb::node::Kind::Call(call)) = &program.nodes[index].kind else {
            unreachable!()
        };
        for child in call.args.iter().rev() {
            pending.push((*child as usize, false));
        }
    }
    let mut slots = std::array::from_fn(|_| vec![]);
    slots[Arena::Node as usize] = (0..program.nodes.len() as u32).map(Slot::Local).collect();
    slots[Arena::Sort as usize] = (0..program.sorts.len() as u32).map(Slot::Local).collect();
    let root = publish(program, slots, declarations, Arena::Node, 0)?;
    let owner = root.owner.as_ref().unwrap();
    for node in &owner.program.nodes {
        let Some(pb::node::Kind::Call(call)) = &node.kind else {
            unreachable!()
        };
        let declaration = root.declaration(&call.func, false)?;
        let Some(pb::declaration::Kind::Constructor(constructor)) =
            &declaration.owner.as_ref().unwrap().program.declarations[declaration.index as usize]
                .kind
        else {
            unreachable!()
        };
        if call.args.len() != constructor.inputs.len()
            || super::SortRef(root.resolve(Arena::Sort, node.sort_id)?)
                != super::SortRef(declaration.resolve(Arena::Sort, constructor.output)?)
        {
            return Err(TypedError::Decode(format!(
                "invalid extraction signature for {}",
                call.func
            )));
        }
        for (child, input) in call.args.iter().zip(&constructor.inputs) {
            let sort = owner.program.nodes[*child as usize].sort_id;
            if super::SortRef(root.resolve(Arena::Sort, sort)?)
                != super::SortRef(declaration.resolve(Arena::Sort, input.sort)?)
            {
                return Err(TypedError::Decode(format!(
                    "invalid extraction argument sort for {}",
                    call.func
                )));
            }
        }
    }
    Ok(Expr(root))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typed::{SortRef, decl::Callable};

    fn response(args: Vec<u32>, child: bool) -> (pb::RunProgramResponse, Vec<Record>) {
        let sort = SortRef::equality("M");
        let pair = Callable::constructor("Pair", vec![sort.clone(), sort.clone()], sort.clone());
        let leaf = Callable::constructor("Leaf", vec![], sort);
        let mut response = pb::RunProgramResponse {
            sorts: vec![pb::Sort {
                kind: Some(pb::sort::Kind::Eq("M".into())),
                ..Default::default()
            }],
            nodes: vec![pb::Node {
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "Pair".into(),
                    args,
                })),
                ..Default::default()
            }],
            ..Default::default()
        };
        if child {
            response.nodes.push(pb::Node {
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "Leaf".into(),
                    args: vec![],
                })),
                ..Default::default()
            });
        }
        (response, vec![pair.0, leaf.0])
    }

    #[test]
    fn decoded_data_rejects_cycles_missing_children_and_bad_signatures() {
        let (r, declarations) = response(vec![0, 0], false);
        assert!(
            adopt(&r, 0, declarations).is_err(),
            "call-only cycle is not inert data"
        );
        let (r, declarations) = response(vec![1, 1], false);
        assert!(adopt(&r, 0, declarations).is_err(), "missing child");
        let (r, declarations) = response(vec![], false);
        assert!(adopt(&r, 0, declarations).is_err(), "wrong call arity");
        let (mut r, declarations) = response(vec![1, 1], true);
        r.sorts.push(pb::Sort {
            kind: Some(pb::sort::Kind::Eq("N".into())),
            ..Default::default()
        });
        r.nodes[1].sort_id = 1;
        assert!(
            adopt(&r, 0, declarations).is_err(),
            "wrong child/output sort"
        );
        let (mut r, declarations) = response(vec![1, 1], true);
        r.sorts.push(pb::Sort {
            kind: Some(pb::sort::Kind::Eq("N".into())),
            ..Default::default()
        });
        r.nodes[0].sort_id = 1;
        assert!(
            adopt(&r, 0, declarations).is_err(),
            "wrong root output sort"
        );
        let (r, declarations) = response(vec![1, 1], true);
        assert!(
            adopt(&r, 0, declarations).is_ok(),
            "shared finite child is valid"
        );
    }

    #[test]
    fn actual_bytes_are_encoded_executed_and_decoded() {
        let sort = SortRef::equality("ByteWitness");
        let leaf = Callable::constructor("ByteWitness.Leaf", vec![], sort);
        let expression = Expr::call(&leaf, vec![]);
        let mut packer = Packer::default();
        let root = packer.intern(expression.0, 0);
        packer.program.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Extract(pb::Extract {
                roots: vec![root],
                variants: 1,
                extractor: pb::Extractor::Tree.into(),
                ..Default::default()
            })),
            ..Default::default()
        });
        let mut graph = EGraph::default();
        let response = graph.execute(packer).unwrap();
        let (input, output) = graph.last_wire.as_ref().unwrap();
        let request = pb::RunProgramRequest::decode(input.as_slice()).unwrap();
        assert_eq!(request.egraph_id, graph.handle);
        assert!(request.profile);
        assert!(
            matches!(&request.program.unwrap().nodes[root as usize].kind, Some(pb::node::Kind::Call(c)) if c.func == "ByteWitness.Leaf")
        );
        assert_eq!(
            pb::RunProgramResponse::decode(output.as_slice()).unwrap(),
            response
        );
        assert!(matches!(
            response.outputs[0].kind,
            Some(pb::command_output::Kind::Extraction(_))
        ));
    }

    #[test]
    fn explicit_ruleset_names_are_preserved_and_generated_names_do_not_capture() {
        let root = |name: Option<&str>| {
            Ruleset(
                publish(
                    pb::Program {
                        ir_version: 1,
                        rulesets: vec![pb::Ruleset {
                            name: name.map(str::to_owned),
                            kind: Some(pb::ruleset::Kind::Rules(pb::RuleList { rules: vec![] })),
                            ..Default::default()
                        }],
                        ..Default::default()
                    },
                    std::array::from_fn(|_| vec![]),
                    vec![],
                    Arena::Ruleset,
                    0,
                )
                .unwrap(),
            )
        };
        let mut graph = EGraph::default();
        for explicit in ["chosen", "", "__typed_ruleset_3"] {
            graph.run(&root(Some(explicit))).unwrap();
            let request =
                pb::RunProgramRequest::decode(graph.last_wire.as_ref().unwrap().0.as_slice())
                    .unwrap();
            let program = request.program.unwrap();
            assert_eq!(program.rulesets[0].name.as_deref(), Some(explicit));
            let Some(pb::command::Kind::Run(run)) = &program.commands[0].kind else {
                panic!()
            };
            assert_eq!(
                run.ruleset.as_ref().unwrap().kind,
                Some(pb::ruleset_ref::Kind::Name(explicit.into()))
            );
        }
        graph.run(&root(None)).unwrap();
        let request =
            pb::RunProgramRequest::decode(graph.last_wire.as_ref().unwrap().0.as_slice()).unwrap();
        assert_eq!(
            request.program.unwrap().rulesets[0].name.as_deref(),
            Some("__typed_ruleset_4")
        );
    }
}
