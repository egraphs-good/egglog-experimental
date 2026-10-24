//! Host registrations and owned observations, shared by Extract and KeepBest.
//!
//! The host owns objective objects/codecs. Native extraction remains the sole
//! ranking algorithm; no native graph or value crosses a host callback.
use super::*;
use egglog::extract::{DagCostModel, MonoidCost, TreeCostModel};
use std::any::Any;
use std::cmp::Ordering;

/// A closed logical sort, independent of its source arena numbering.
#[derive(Clone)]
pub struct ModelSort {
    /// Source arena for the structural sort.
    pub sorts: Vec<pb::Sort>,
    /// Closed root sort within that arena.
    pub root: u32,
}

/// Explicit registration contract. An additive model supports both algorithms;
/// a tree fold supports only tree extraction.
pub struct CostModelContract {
    /// Stored annotation sort C accepted by this model.
    pub annotation: ModelSort,
    /// Result objective sort D produced by its codec.
    pub objective: ModelSort,
    /// Whether marginal costs support combination and a typed identity.
    pub additive: bool,
}

/// Provider-owned, immutable objective object. This is an internal native
/// extension type, never a protocol token or a Python frontend value wrapper.
pub type Objective = Arc<dyn Any + Send + Sync>;

/// A retained registration creates a fresh runtime for each extraction.
pub trait NativeCostModel: Send + Sync {
    /// Return this registration's stable sort/algorithm contract.
    fn contract(&self) -> CostModelContract;
    /// Prepare extraction-local host resources from owned encoded records.
    fn start(&self, observation: &pb::Program) -> Result<Arc<dyn CostModelRuntime>, egglog::Error>;
}

/// Calls must be deterministic during an extraction. A provider with fallible
/// host comparison/addition uses its private unwind payload and error channel
/// across the infallible native cost traits; unrelated panics remain panics.
pub trait CostModelRuntime: Send + Sync {
    /// Run one owned operation inside the provider's private error boundary.
    /// Translate only that provider's host-error payload; resume native panics.
    /// Returning a native error keeps request/publication receipts intact.
    fn run(
        &self,
        operation: Box<dyn FnOnce() -> Result<(), egglog::Error> + '_>,
    ) -> Result<(), egglog::Error>;
    /// Fold the named observation occurrence over its semantic children, or
    /// return its marginal objective for an additive registration.
    fn cost(&self, node: u32, children: &[Objective]) -> Objective;
    /// Compare two objectives belonging to this runtime.
    fn compare(&self, left: &Objective, right: &Objective) -> Ordering;
    /// Combine two marginal objectives belonging to this runtime.
    fn combine(&self, left: &Objective, right: &Objective) -> Objective;
    /// Materialize this runtime's explicitly typed additive identity.
    fn identity(&self) -> Objective;
    /// An inert leaf codec for D. None means no portable objective value.
    /// Container/record objectives can use an explicit opaque host codec.
    fn encode(&self, value: &Objective) -> Result<Option<pb::PrimitiveValue>, egglog::Error>;
}

/// Owned logical records plus adapter-private native-location indexes.
/// Locations have meaning only within this observation's lifetime.
pub(super) struct Observation {
    pub program: pb::Program,
    pub values: HashMap<(String, Value), u32>,
    pub classes: HashMap<String, u32>,
    pub calls: HashMap<(String, Vec<u32>), u32>,
    pub names: HashMap<String, String>,
}

impl Observation {
    fn value(&self, graph: &EGraph, sort: &ArcSort, value: Value) -> u32 {
        if sort.is_eq_sort() {
            self.classes[&graph.value_to_class_id(sort, value).to_string()]
        } else {
            self.values[&(sort.name().to_owned(), value)]
        }
    }

    fn enode(&self, graph: &EGraph, func: &egglog::Function, enode: &egglog::Enode<'_>) -> u32 {
        let args = func
            .func_type()
            .input
            .iter()
            .zip(enode.children)
            .map(|(sort, value)| self.value(graph, sort, *value))
            .collect();
        let name = self
            .names
            .get(func.name())
            .map_or(func.name(), String::as_str);
        self.calls[&(name.to_owned(), args)]
    }
}

#[derive(Clone)]
pub(super) struct ObservedModel {
    pub observation: Arc<Observation>,
    pub runtime: Arc<dyn CostModelRuntime>,
}

/// Context-free identity is required by MonoidCost. It is materialized only
/// against the extraction-local runtime when comparison/encoding needs it.
#[derive(Clone)]
pub(super) enum ModelCost {
    Identity,
    Value {
        value: Objective,
        runtime: Arc<dyn CostModelRuntime>,
    },
}

impl ModelCost {
    fn object(&self, runtime: &Arc<dyn CostModelRuntime>) -> Objective {
        match self {
            Self::Identity => runtime.identity(),
            Self::Value {
                value,
                runtime: owner,
            } => {
                assert!(
                    Arc::ptr_eq(owner, runtime),
                    "mixed extraction cost contexts"
                );
                value.clone()
            }
        }
    }
}

impl Ord for ModelCost {
    fn cmp(&self, other: &Self) -> Ordering {
        let runtime = match (self, other) {
            (Self::Identity, Self::Identity) => return Ordering::Equal,
            (Self::Value { runtime, .. }, _) | (_, Self::Value { runtime, .. }) => runtime,
        };
        runtime.compare(&self.object(runtime), &other.object(runtime))
    }
}
impl PartialOrd for ModelCost {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl PartialEq for ModelCost {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}
impl Eq for ModelCost {}

impl MonoidCost for ModelCost {
    fn identity() -> Self {
        Self::Identity
    }

    fn combine(self, other: &Self) -> Self {
        let runtime = match (&self, other) {
            (Self::Identity, Self::Identity) => return Self::Identity,
            (Self::Value { runtime, .. }, _) | (_, Self::Value { runtime, .. }) => runtime.clone(),
        };
        let value = runtime.combine(&self.object(&runtime), &other.object(&runtime));
        Self::Value { value, runtime }
    }
}

impl TreeCostModel<ModelCost> for ObservedModel {
    type EnodeCost = u32;
    type ContainerCost = u32;

    fn base_value_cost(&self, graph: &EGraph, sort: &ArcSort, value: Value) -> ModelCost {
        self.fold_enode_cost(self.observation.value(graph, sort, value), &[])
    }
    fn enode_cost(
        &self,
        graph: &EGraph,
        func: &egglog::Function,
        enode: &egglog::Enode<'_>,
    ) -> u32 {
        self.observation.enode(graph, func, enode)
    }
    fn container_cost(&self, graph: &EGraph, sort: &ArcSort, value: Value) -> u32 {
        self.observation.value(graph, sort, value)
    }
    fn fold_enode_cost(&self, node: u32, children: &[ModelCost]) -> ModelCost {
        let children = children
            .iter()
            .map(|cost| cost.object(&self.runtime))
            .collect::<Vec<_>>();
        ModelCost::Value {
            value: self.runtime.cost(node, &children),
            runtime: self.runtime.clone(),
        }
    }
    fn fold_container_cost(&self, node: u32, children: &[ModelCost]) -> ModelCost {
        // Both annotations name a typed observation node; native extraction
        // supplies the semantic container order and duplicate multiplicity.
        let children = children
            .iter()
            .map(|cost| cost.object(&self.runtime))
            .collect::<Vec<_>>();
        ModelCost::Value {
            value: self.runtime.cost(node, &children),
            runtime: self.runtime.clone(),
        }
    }
}

pub(super) struct MarginalModel(pub ObservedModel);
impl DagCostModel<ModelCost> for MarginalModel {
    fn base_value_cost(&self, graph: &EGraph, sort: &ArcSort, value: Value) -> ModelCost {
        TreeCostModel::base_value_cost(&self.0, graph, sort, value)
    }
    fn enode_cost(
        &self,
        graph: &EGraph,
        func: &egglog::Function,
        enode: &egglog::Enode<'_>,
    ) -> ModelCost {
        let node = self.0.observation.enode(graph, func, enode);
        self.0.fold_enode_cost(node, &[])
    }
    fn container_cost(&self, graph: &EGraph, sort: &ArcSort, value: Value) -> ModelCost {
        let node = self.0.observation.value(graph, sort, value);
        self.0.fold_container_cost(node, &[])
    }
}

impl Session {
    pub(super) fn resolve_cost_model(
        &self,
        name: &str,
        extractor: i32,
    ) -> Result<Arc<dyn NativeCostModel>, PreparationError> {
        let model = self.cost_models.get(name).cloned().ok_or_else(|| {
            PreparationError(Box::new(pb::Error {
                code: pb::ErrorCode::RuntimeFailure.into(),
                message: format!("unknown cost model {name}"),
                ..Default::default()
            }))
        })?;
        let contract = model.contract();
        let mut sorts = Vec::new();
        let expected = crate::builtin::import_sort(
            &contract.annotation.sorts,
            contract.annotation.root,
            &mut sorts,
        )?;
        let mut actual = Vec::new();
        let root = self
            .graph
            .export_sort(self.graph.get_sort_by_name("i64").unwrap(), &mut actual)?;
        let actual = crate::builtin::import_sort(&actual, root, &mut sorts)?;
        if actual != expected {
            return Err("cost model does not accept this graph's stored annotation sort".into());
        }
        if extractor == i32::from(pb::Extractor::GreedyDag) && !contract.additive {
            return Err("greedy-DAG extraction requires an additive marginal cost model".into());
        }
        // Validate D structurally before running any callback.
        let mut objective = Vec::new();
        let objective_root = crate::builtin::import_sort(
            &contract.objective.sorts,
            contract.objective.root,
            &mut objective,
        )?;
        if objective
            .iter()
            .any(|sort| matches!(sort.kind, Some(pb::sort::Kind::Var(_))))
        {
            return Err("cost model objective sort must be closed".into());
        }
        let objective_sort = &objective[objective_root as usize];
        if !matches!(&objective_sort.kind, Some(pb::sort::Kind::Application(family)) if family.args.is_empty())
        {
            return Err("host model objectives currently require a registered leaf sort".into());
        }
        self.graph
            .authoring_type_info()
            .portable_builtin_catalog()?;
        validate_nullary_family(self.graph.authoring_type_info(), objective_sort)?;
        Ok(model)
    }

    pub(super) fn extract_host_model(
        &mut self,
        program: &pb::Program,
        extract: &pb::Extract,
        response: &mut pb::RunProgramOutput,
        context: &RequestOccurrences,
    ) -> Result<pb::ExtractResult, egglog::Error> {
        let registration = self
            .resolve_cost_model(&extract.cost_model, extract.extractor)
            .map_err(|error| egglog::Error::ExtractError(error.0.message))?;
        let contract = registration.contract();
        let roots = extract
            .roots
            .iter()
            .map(|index| {
                eval_extract_root(
                    &mut self.graph,
                    program,
                    *index,
                    context.extraction_dags.get(index),
                    true,
                    &context.native_spans,
                )
                .map(|root| root.expect("executed extraction root"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let observation = Arc::new(freeze::observation(
            freeze::View {
                graph: &self.graph,
                names: &self.names,
                definitions: &self.definitions,
                mode: self.mode,
                extension: self.extension.as_ref(),
            },
            &roots,
        )?);
        let runtime = registration.start(&observation.program)?;
        let mut result = None;
        runtime.run(Box::new(|| {
            let model = ObservedModel {
                observation,
                runtime: runtime.clone(),
            };
            let mut encoded = HashMap::new();
            let observe =
                |terms: &TermDag, term: TermId, sort: &ArcSort, value: Value, children: &[u32]| {
                    encode_term(
                        self,
                        terms,
                        term,
                        sort,
                        value,
                        children,
                        response,
                        &mut encoded,
                    )
                };
            let variants = usize::try_from(extract.variants).map_err(|_| {
                egglog::Error::ExtractError("variant count exceeds native usize".into())
            })?;
            let (extracted, nodes) = if extract.extractor == i32::from(pb::Extractor::GreedyDag) {
                crate::greedy_dag_extract::extract_variants_greedy_dag_with_observer(
                    &self.graph,
                    roots,
                    variants,
                    MarginalModel(model),
                    observe,
                )?
            } else if contract.additive {
                self.graph.extract_variants_with_cost_model_and_observer(
                    roots,
                    variants,
                    egglog::extract::TreeCostModelFromDag(MarginalModel(model)),
                    observe,
                )?
            } else {
                self.graph.extract_variants_with_cost_model_and_observer(
                    roots, variants, model, observe,
                )?
            };
            let objective = crate::builtin::import_sort(
                &contract.objective.sorts,
                contract.objective.root,
                &mut response.sorts,
            )
            .map_err(egglog::Error::ExtractError)?;
            let mut output = pb::ExtractResult::default();
            for (variants, nodes) in extracted.variants.iter().zip(nodes) {
                let mut root = pb::ExtractedRoot::default();
                for (variant, term) in variants.iter().zip(nodes) {
                    let cost = if let Some(value) =
                        runtime.encode(&variant.cost.object(&runtime))?
                    {
                        // A first host codec encodes a leaf D. Never accept foreign
                        // arena references as if they belonged to this response.
                        use pb::primitive_value::Value as V;
                        if let Some(exact @ (V::BigInt(_) | V::BigRat(_) | V::Rational(_))) =
                            &value.value
                        {
                            validate_exact_number(exact).map_err(egglog::Error::ExtractError)?;
                        }
                        let family = match &response.sorts[objective as usize].kind {
                            Some(pb::sort::Kind::Application(family)) if family.args.is_empty() => {
                                &family.name
                            }
                            _ => {
                                return Err(egglog::Error::ExtractError(
                                    "host leaf objective has a non-leaf declared sort".into(),
                                ));
                            }
                        };
                        let sort_agrees = match (family.as_str(), &value.value) {
                            ("Unit", Some(V::Unit(_)))
                            | ("bool", Some(V::Bool(_)))
                            | ("i64", Some(V::I64(_)))
                            | ("f64", Some(V::F64Bits(_)))
                            | ("String", Some(V::String(_)))
                            | ("BigInt", Some(V::BigInt(_)))
                            | ("BigRat", Some(V::BigRat(_)))
                            | ("Rational", Some(V::Rational(_))) => true,
                            (
                                "Unit" | "bool" | "i64" | "f64" | "String" | "BigInt" | "BigRat"
                                | "Rational",
                                _,
                            ) => false,
                            (_, Some(V::Custom(custom))) => custom.args.is_empty(),
                            _ => false,
                        };
                        if !sort_agrees {
                            return Err(egglog::Error::ExtractError(
                                "host objective codec disagrees with its declared result sort"
                                    .into(),
                            ));
                        }
                        let index = u32::try_from(response.nodes.len()).map_err(|_| {
                            egglog::Error::ExtractError("objective arena exceeds u32".into())
                        })?;
                        response.nodes.push(pb::Node {
                            sort_id: objective,
                            kind: Some(pb::node::Kind::PrimitiveValue(value)),
                            ..Default::default()
                        });
                        Some(index)
                    } else {
                        None
                    };
                    root.variants.push(pb::ExtractedTerm { term, cost });
                }
                output.roots.push(root);
            }
            result = Some(output);
            Ok(())
        }))?;
        Ok(result.expect("provider completed the owned extraction operation"))
    }

    pub(super) fn keep_best_host_model(
        &mut self,
        keep: &pb::KeepBest,
    ) -> Result<(), egglog::Error> {
        let registration = self
            .resolve_cost_model(&keep.cost_model, keep.extractor)
            .map_err(|error| egglog::Error::ExtractError(error.0.message))?;
        let additive = registration.contract().additive;
        // Every retained table cell already belongs to this complete view.
        // All observation/codec failures precede the shared plan's clear step.
        let observation = Arc::new(freeze::observation(
            freeze::View {
                graph: &self.graph,
                names: &self.names,
                definitions: &self.definitions,
                mode: self.mode,
                extension: self.extension.as_ref(),
            },
            &[],
        )?);
        let runtime = registration.start(&observation.program)?;
        let model = ObservedModel {
            observation,
            runtime: runtime.clone(),
        };
        runtime.run(Box::new(|| {
            crate::keep_best::keep_best_with_selector(
                &mut self.graph,
                &keep.tables,
                |graph, roots, observe| {
                    let (extracted, _) = if keep.extractor == i32::from(pb::Extractor::GreedyDag) {
                        crate::greedy_dag_extract::extract_best_greedy_dag_with_observer(
                            graph,
                            roots,
                            MarginalModel(model),
                            observe,
                        )?
                    } else if additive {
                        graph.extract_best_with_cost_model_and_observer(
                            roots,
                            egglog::extract::TreeCostModelFromDag(MarginalModel(model)),
                            observe,
                        )?
                    } else {
                        graph.extract_best_with_cost_model_and_observer(roots, model, observe)?
                    };
                    if extracted.terms.iter().any(Option::is_none) {
                        return Err(egglog::Error::ExtractError(
                            "keep-best: could not extract a selected table cell".into(),
                        ));
                    }
                    Ok(())
                },
            )
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::protobuf::fixtures::Observed;

    struct InvalidObjective(&'static str);

    impl NativeCostModel for InvalidObjective {
        fn contract(&self) -> CostModelContract {
            let sorts = ["i64", self.0]
                .into_iter()
                .map(|name| pb::Sort {
                    kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                        name: name.into(),
                        args: vec![],
                    })),
                    ..Default::default()
                })
                .collect::<Vec<_>>();
            CostModelContract {
                annotation: ModelSort {
                    sorts: sorts.clone(),
                    root: 0,
                },
                objective: ModelSort { sorts, root: 1 },
                additive: false,
            }
        }

        fn start(&self, _: &pb::Program) -> Result<Arc<dyn CostModelRuntime>, egglog::Error> {
            panic!("invalid objective sort reached the model factory")
        }
    }

    #[test]
    fn invalid_objective_families_reject_before_model_start() {
        let mut engine = Engine::default();
        let response = engine
            .create(
                &pb::CreateEGraphRequest {
                    sorts: vec![pb::Sort {
                        kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                            name: "i64".into(),
                            args: vec![],
                        })),
                        ..Default::default()
                    }],
                    options: Some(pb::EGraphOptions {
                        cost_sort: Some(0),
                        execution_mode: pb::ExecutionMode::Normal.into(),
                        ..Default::default()
                    }),
                    ..Default::default()
                }
                .encode_to_vec(),
            )
            .unwrap();
        let handle = pb::CreateEGraphResponse::decode(response.as_slice())
            .unwrap()
            .egraph_id;
        for family in ["Vec", "missing-host-family"] {
            let name = engine
                .register_cost_model(handle, Arc::new(InvalidObjective(family)))
                .unwrap();
            let request = pb::RunProgramRequest {
                egraph_id: handle,
                diagnostics: false,
                program: Some(pb::Program {
                    sorts: vec![pb::Sort {
                        kind: Some(pb::sort::Kind::Application(pb::SortApplication {
                            name: "i64".into(),
                            args: vec![],
                        })),
                        ..Default::default()
                    }],
                    nodes: vec![pb::Node {
                        sort_id: 0,
                        kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                            value: Some(pb::primitive_value::Value::I64(1)),
                        })),
                        ..Default::default()
                    }],
                    commands: vec![pb::Command {
                        kind: Some(pb::command::Kind::Extract(pb::Extract {
                            roots: vec![0],
                            variants: 1,
                            extractor: pb::Extractor::Tree.into(),
                            cost_model: name.clone(),
                        })),
                        ..Default::default()
                    }],
                    ..Default::default()
                }),
            };
            let response = engine.run(&request.encode_to_vec()).unwrap();
            let error = Observed::from_frames(
                (response)
                    .iter()
                    .map(|bytes| pb::RunProgramResponse::decode(bytes.as_slice()).unwrap()),
            )
            .error
            .unwrap();
            assert_eq!(error.code, i32::from(pb::ErrorCode::InvalidProgram));
            assert!(error.message.contains(family), "{}", error.message);
            engine.release_cost_model(handle, &name).unwrap();
        }
    }
}
