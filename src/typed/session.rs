use super::{
    DefaultCost, EgglogValue, Fact, FreezeLimits, RunReport, Schedule, TypedError,
    decl::{CallKind, SortKind},
    expr::{Expr, NodeKind, ValueInput},
    lower::{Commit, Installed, Planner},
    program::IntoDefinitions,
    rule::{IntoActions, IntoFacts},
};
use egglog::{Term, ast::Command, prelude::Read};
use std::collections::HashMap;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typed::{
        builtins::I64,
        decl::{CallableDef, DefinitionSource},
        prelude::*,
    };
    use std::sync::OnceLock;

    #[test]
    fn borrowed_handles_and_extraction_share_expression_nodes() -> Result<(), TypedError> {
        #[sort]
        struct Shared;
        #[declarations]
        impl Shared {
            fn leaf(value: I64) -> Self;
            fn pair(left: Self, right: Self) -> Self;
        }

        let leaf = Shared::leaf(7);
        let pair = Shared::pair(&leaf, &leaf);
        let borrowed = Shared::from(&pair);
        assert_eq!(borrowed.expression().id(), pair.expression().id());

        let mut graph = EGraph::default();
        let forest = graph.extract_many(&[pair.clone(), leaf, pair])?;
        assert_eq!(forest[0].expression().id(), forest[2].expression().id());
        let (left, right) =
            get_args(&forest[0], |a: &Shared, b: &Shared| Shared::pair(a, b))?.unwrap();
        assert_eq!(left.expression().id(), forest[1].expression().id());
        assert_eq!(right.expression().id(), forest[1].expression().id());
        Ok(())
    }

    #[test]
    fn native_and_builtin_name_conflicts_reject_before_mutation() -> Result<(), TypedError> {
        #[sort]
        struct Value;
        #[sort(name = "i64")]
        struct WrongInteger;
        #[sort(name = "OccupiedSort")]
        struct OccupiedSort;
        #[sort(name = "OccupiedFunction")]
        struct OccupiedFunction;
        #[constructor]
        fn wrong_integer() -> WrongInteger;
        #[constructor]
        fn occupied_sort() -> OccupiedSort;
        #[constructor]
        fn occupied_function_sort() -> OccupiedFunction;
        #[constructor(name = "OccupiedSort")]
        fn sort_as_callable() -> Value;
        #[constructor(name = "OccupiedFunction")]
        fn occupied_function() -> Value;
        #[constructor(name = "+")]
        fn primitive() -> Value;
        #[constructor(name = "vec-of")]
        fn reserved_primitive() -> Value;
        #[constructor(name = "get-size!")]
        fn experimental_primitive() -> Value;
        #[constructor(name = "unstable-fresh!")]
        fn reserved_macro() -> Value;

        let mut graph = EGraph::default();
        graph
            .core
            .parse_and_run_program(
                None,
                "(sort OccupiedSort) (constructor OccupiedFunction () OccupiedSort)",
            )
            .unwrap();
        for action in [
            Action::from(wrong_integer()),
            Action::from(occupied_sort()),
            Action::from(occupied_function_sort()),
            Action::from(sort_as_callable()),
            Action::from(occupied_function()),
            Action::from(primitive()),
            Action::from(reserved_primitive()),
            Action::from(experimental_primitive()),
            Action::from(reserved_macro()),
        ] {
            let state = graph.core.extension_state::<Installed>().unwrap().clone();
            let names = graph.core.get_function_names();
            let sorts = graph.core.get_arcsorts_by(|_| true).len();
            let symbols = graph.core.parser.symbol_gen.clone();
            let tuples = graph.num_tuples()?;
            assert!(matches!(
                graph.register(action),
                Err(TypedError::Invalid(_))
            ));
            let after = graph.core.extension_state::<Installed>().unwrap();
            assert_eq!(after.sorts, state.sorts);
            assert_eq!(after.declarations, state.declarations);
            assert_eq!(graph.core.get_function_names(), names);
            assert_eq!(graph.core.get_arcsorts_by(|_| true).len(), sorts);
            assert_eq!(graph.core.parser.symbol_gen, symbols);
            assert_eq!(graph.num_tuples()?, tuples);
            assert!(!after.poisoned);
        }
        Ok(())
    }

    #[test]
    fn ruleset_name_conflicts_reject_before_mutation() -> Result<(), TypedError> {
        #[sort]
        struct Value;
        #[sort(name = "@$typed_group_anonymous_")]
        struct GroupName;
        #[sort(name = "@$typed_singleton_anonymous_")]
        struct SingletonName;
        #[constructor]
        fn group_sort() -> GroupName;
        #[constructor]
        fn singleton_sort() -> SingletonName;
        #[constructor(name = "@$typed_group_anonymous_")]
        fn group_callable() -> Value;
        #[constructor(name = "@$typed_singleton_anonymous_")]
        fn singleton_callable() -> Value;

        for action in [
            Action::from(group_sort()),
            Action::from(singleton_sort()),
            Action::from(group_callable()),
            Action::from(singleton_callable()),
        ] {
            for installed in [false, true] {
                let mut graph = EGraph::default();
                let existing = ruleset(rule((), ()));
                if installed {
                    graph.run(&existing)?;
                }
                let before = graph.core.extension_state::<Installed>().unwrap().clone();
                let names = graph.core.get_function_names();
                let sorts = graph.core.get_arcsorts_by(|_| true).len();
                let symbols = graph.core.parser.symbol_gen.clone();
                let tuples = graph.num_tuples()?;
                let result = if installed {
                    graph.register(&action)
                } else {
                    graph
                        .run(sequence([existing, ruleset(rule((), &action))]))
                        .map(|_| ())
                };
                assert!(matches!(result, Err(TypedError::Invalid(_))));
                let after = graph.core.extension_state::<Installed>().unwrap();
                assert_eq!(after.sorts, before.sorts);
                assert_eq!(after.declarations, before.declarations);
                assert_eq!(after.globals, before.globals);
                assert_eq!(after.rules, before.rules);
                assert_eq!(after.groups, before.groups);
                assert_eq!(graph.core.get_function_names(), names);
                assert_eq!(graph.core.get_arcsorts_by(|_| true).len(), sorts);
                assert_eq!(graph.core.parser.symbol_gen, symbols);
                assert_eq!(graph.num_tuples()?, tuples);
                assert!(!after.poisoned);
            }
        }
        Ok(())
    }

    #[test]
    fn frozen_preflight_preserves_names_installation_and_health() -> Result<(), TypedError> {
        static OBSERVED: OnceLock<I64> = OnceLock::new();
        fn definition() -> &'static CallableDef {
            static DEFINITION: OnceLock<CallableDef> = OnceLock::new();
            DEFINITION.get_or_init(|| CallableDef {
                callable: callable(),
                inputs: vec![],
                output: I64::sort_ref(),
                merge: Some(OBSERVED.get().unwrap().expression().clone()),
                cost: None,
                unextractable: false,
            })
        }
        fn callable() -> crate::typed::CallableRef {
            crate::typed::CallableRef::declared(
                "preflight::observed_merge",
                CallKind::Function,
                DefinitionSource {
                    token: std::any::TypeId::of::<OnceLock<I64>>(),
                    resolve: definition,
                },
                None,
            )
        }
        let mut graph = EGraph::new(EGraphOptions::default());
        let capture = let_("scalar", I64::from(7));
        graph.register(&capture)?;
        let frozen = graph.freeze()?;
        let observed = frozen.lookup(&capture)?;
        OBSERVED.set(observed.clone()).unwrap();
        let merge_call = I64::from_expression(Expr::call(I64::sort_ref(), callable(), vec![]));
        let symbol_gen = graph.core.parser.symbol_gen.clone();
        let state = graph.core.extension_state::<Installed>().unwrap().clone();
        let tuples = graph.num_tuples()?;
        let group = ruleset(Vec::<crate::typed::Rule>::new());
        let rejected = [
            graph.register(merge_call),
            graph.check(eq(&observed, 7)).map(|_| ()),
            graph.extract(&observed).map(|_| ()),
            graph.run(group.until(eq(&observed, 7))).map(|_| ()),
        ];
        for result in rejected {
            assert!(matches!(result, Err(TypedError::Invalid(_))));
        }
        assert_eq!(graph.core.parser.symbol_gen, symbol_gen);
        let after = graph.core.extension_state::<Installed>().unwrap();
        assert_eq!(after.sorts, state.sorts);
        assert_eq!(after.declarations, state.declarations);
        assert_eq!(after.captures, state.captures);
        assert_eq!(after.globals, state.globals);
        assert_eq!(after.rules, state.rules);
        assert_eq!(after.groups, state.groups);
        assert!(!after.poisoned);
        assert_eq!(graph.num_tuples()?, tuples);
        Ok(())
    }
}
#[derive(Clone, Debug)]
/// Bounds authoring traversal and native AST emission before destination execution.
///
/// These are safety ceilings, not a guarantee of linear backend runtime.
/// Raising them does not make recursive native passes stack-safe.
pub struct LoweringLimits {
    /// Maximum distinct authoring nodes examined by one collection pass.
    pub max_nodes: usize,
    /// Maximum outgoing edges, counting duplicate children.
    pub max_edges: usize,
    /// Maximum expanded occurrences in an expression, query, or rule action vector.
    pub max_expanded_nodes: usize,
    /// Maximum nesting of un-factored AST expressions and schedules.
    pub max_ast_depth: usize,
    /// Maximum emitted native commands in one method call.
    pub max_commands: usize,
}
impl Default for LoweringLimits {
    fn default() -> Self {
        Self {
            max_nodes: 100_000,
            max_edges: 1_000_000,
            max_expanded_nodes: 100_000,
            max_ast_depth: 128,
            max_commands: 100_000,
        }
    }
}
#[derive(Clone, Debug, Default)]
/// Configuration for the typed destination, with no mutable raw execution escape.
pub struct EGraphOptions {
    /// Authoring and native-lowering budgets.
    pub lowering_limits: LoweringLimits,
    /// Bounds for owned snapshot construction.
    pub freeze_limits: FreezeLimits,
}
/// A native experimental e-graph with scope-aware typed installation bookkeeping.
///
/// Methods execute constructed native AST commands in order. They are not
/// transactions: a core failure preserves its completed prefix and marks this
/// destination as needing a successful [`Self::pop`] to an earlier healthy scope.
pub struct EGraph {
    pub(crate) core: egglog::EGraph,
    pub(crate) options: EGraphOptions,
}
impl Default for EGraph {
    fn default() -> Self {
        Self::new(EGraphOptions::default())
    }
}
impl EGraph {
    /// Creates a destination through [`crate::new_experimental_egraph`].
    pub fn new(options: EGraphOptions) -> Self {
        let mut core = crate::new_experimental_egraph();
        core.extension_state_or_default::<Installed>();
        Self { core, options }
    }
    /// Consumes this wrapper and permanently ends typed lifecycle tracking.
    pub fn into_raw(self) -> egglog::EGraph {
        self.core
    }
    /// Records the actual native commands submitted while `operation` runs.
    /// Returns both its result (including a returned error) and the command record.
    /// Nested recordings are rejected without discarding the outer record.
    ///
    /// The record retains failed commands and popped scopes. A failed check is a
    /// failed native command even though [`Self::check`] returns `Ok(false)`.
    /// Preflight errors submit no commands. Extraction records its materialization
    /// commands, but not the direct native extractor or result decoding; `freeze`,
    /// `stats`, and `num_tuples` are also observations without commands.
    ///
    /// Recording an existing graph produces a fragment requiring its prior state.
    /// Even on a fresh graph, the record is an attempted program, not a snapshot
    /// or a guarantee that replay proceeds past previously failed commands.
    pub fn record<R>(
        &mut self,
        operation: impl FnOnce(&mut Self) -> R,
    ) -> Result<(R, egglog::program::CommandRecord), TypedError> {
        if !self.core.try_start_recording() {
            return Err(TypedError::Invalid(
                "a typed recording is already active".into(),
            ));
        }
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| operation(self)));
        let record = self
            .core
            .stop_recording()
            .expect("typed recording remains active");
        match result {
            Ok(result) => Ok((result, record)),
            Err(payload) => std::panic::resume_unwind(payload),
        }
    }
    fn ensure_healthy(&self) -> Result<(), TypedError> {
        if self
            .core
            .extension_state::<Installed>()
            .is_some_and(|s| s.poisoned)
        {
            return Err(TypedError::NeedsRestore);
        }
        Ok(())
    }
    /// Returns native tuple count for resource guards, requiring a healthy destination.
    pub fn num_tuples(&self) -> Result<usize, TypedError> {
        self.ensure_healthy()?;
        Ok(self.core.num_tuples())
    }
    /// Pushes native data and typed installation state together.
    pub fn push(&mut self) -> Result<(), TypedError> {
        self.ensure_healthy()?;
        let program = egglog::program::Program::new(vec![Command::Push(1)])?;
        self.core
            .run_shared_program(program)
            .map(|_| ())
            .map_err(|source| TypedError::Core {
                source,
                command: 0,
                completed: 0,
            })
    }
    /// Restores the most recent native scope, including capture identities and health.
    /// Fresh-name counters are intentionally not restored.
    pub fn pop(&mut self) -> Result<(), TypedError> {
        let program = egglog::program::Program::new(vec![Command::Pop(super::origin(), 1)])?;
        self.core
            .run_shared_program(program)
            .map(|_| ())
            .map_err(|source| TypedError::Core {
                source,
                command: 0,
                completed: 0,
            })
    }
    fn execute(
        &mut self,
        commands: Vec<(Command, Commit)>,
        symbol_gen: egglog::util::SymbolGen,
        check: bool,
    ) -> Result<(Vec<egglog::CommandOutput>, bool), TypedError> {
        if commands.len() > self.options.lowering_limits.max_commands {
            return Err(TypedError::LoweringLimit(
                "emitted command limit exceeded".into(),
            ));
        }
        let (commands, commits): (Vec<_>, Vec<_>) = commands.into_iter().unzip();
        let program = egglog::program::Program::new(commands)?;
        let mut output = vec![];
        self.core.parser.symbol_gen = symbol_gen;
        for (index, (command, commit)) in program.commands.into_iter().zip(commits).enumerate() {
            match self.core.run_shared_program(egglog::program::Program {
                format: program.format,
                commands: vec![command],
            }) {
                Ok(values) => {
                    commit.apply(self.core.extension_state_or_default::<Installed>());
                    output.extend(values);
                }
                Err(egglog::Error::CheckError(..)) if check => return Ok((output, false)),
                Err(source) => {
                    self.core.extension_state_or_default::<Installed>().poisoned = true;
                    return Err(TypedError::Core {
                        source,
                        command: index,
                        completed: index,
                    });
                }
            }
        }
        Ok((output, true))
    }
    /// Installs sorts, selected callables, rules, or rulesets without evaluating
    /// expressions or running rules. Accepts nested tuples and collections.
    ///
    /// Use `S::sort_ref()` for a sort and [`super::Definition::callable`] for an
    /// ordinary callable selector. Dependencies install in first-use order;
    /// compatible definitions and shared rule occurrences install only once.
    /// Installation state follows `push`/`pop`, just like implicit installation.
    pub fn install<T, M>(&mut self, definitions: T) -> Result<(), TypedError>
    where
        T: IntoDefinitions<M>,
    {
        self.ensure_healthy()?;
        let definitions = definitions.into_definitions();
        let mut planner = Planner::new(&mut self.core, self.options.lowering_limits.clone());
        planner.install(&definitions)?;
        let Planner {
            commands,
            symbol_gen,
            ..
        } = planner;
        self.execute(commands, symbol_gen, false)?;
        Ok(())
    }
    /// Materializes expressions and executes actions in caller order.
    ///
    /// Accepts owned or borrowed values, actions, relation rows, arrays, slices,
    /// vectors, and nested tuples through arity 32, using the same conversion as
    /// a rule's RHS. Borrowed collections are traversed without cloning them.
    /// Rules, rulesets, schedules and query facts are not registration inputs.
    /// Generated typed globals may add native command/rebuild boundaries in
    /// eligible setup regions. State-reading expressions are never reused across writes.
    /// A fresh capture nested inside an otherwise state-reading or fallible action
    /// is rejected before execution: register that capture first to make its
    /// evaluation boundary explicit. An established capture, a fresh capture in
    /// a pure surrounding tree, and a top-level capture of a fallible initializer
    /// remain supported.
    pub fn register<T, M>(&mut self, items: T) -> Result<(), TypedError>
    where
        T: IntoActions<M>,
    {
        self.ensure_healthy()?;
        let actions = items.into_actions();
        let mut planner = Planner::new(&mut self.core, self.options.lowering_limits.clone());
        planner.register(&actions)?;
        let Planner {
            commands,
            symbol_gen,
            ..
        } = planner;
        self.execute(commands, symbol_gen, false)?;
        Ok(())
    }
    /// Runs a native query without constructing its queried terms.
    /// Nonmatching queries return `false` and do not poison the destination.
    /// Expressions may be supplied directly: constructors/functions match rows,
    /// and primitives must evaluate successfully. A `Bool(false)` expression
    /// still succeeds; use `eq(boolean, true)` to require boolean truth.
    pub fn check<Q: IntoFacts>(&mut self, facts: Q) -> Result<bool, TypedError> {
        self.ensure_healthy()?;
        let facts = facts.into_facts();
        if facts.is_empty() {
            return Ok(true);
        }
        let mut planner = Planner::new(&mut self.core, self.options.lowering_limits.clone());
        planner.collect(facts.iter().flat_map(Fact::expressions).cloned(), [])?;
        let native = planner.query(&facts, false)?;
        planner.emit(Command::Check(super::origin(), native), Commit::None)?;
        let Planner {
            commands,
            symbol_gen,
            ..
        } = planner;
        Ok(self.execute(commands, symbol_gen, true)?.1)
    }
    /// Installs each reachable rule occurrence once and executes the native schedule.
    /// A ruleset is one run; borrowed schedules retain their shared tree.
    pub fn run(&mut self, schedule: impl Into<Schedule>) -> Result<RunReport, TypedError> {
        self.ensure_healthy()?;
        let schedule = schedule.into();
        let mut planner = Planner::new(&mut self.core, self.options.lowering_limits.clone());
        let native = planner.schedule(&schedule, 0)?;
        planner.emit(Command::RunSchedule(native), Commit::None)?;
        let Planner {
            commands,
            symbol_gen,
            ..
        } = planner;
        let (outputs, _) = self.execute(commands, symbol_gen, false)?;
        outputs
            .into_iter()
            .find_map(|x| match x {
                egglog::CommandOutput::RunSchedule(r) => Some(r),
                _ => None,
            })
            .ok_or_else(|| {
                self.core.extension_state_or_default::<Installed>().poisoned = true;
                TypedError::Decode("native run returned no report".into())
            })
    }
    /// Reads native accumulated reports, using first-installed diagnostic names.
    /// This immutable observation emits no commands and does not consume the
    /// lowering command budget. An unhealthy destination still needs restoration.
    pub fn stats(&self) -> Result<RunReport, TypedError> {
        self.ensure_healthy()?;
        Ok(self.core.get_overall_run_report().clone())
    }
    /// Evaluates a root and returns its native best-tree representative of exactly sort `S`.
    /// Uses the native default cost model and tie-breaking behavior.
    pub fn extract<S: EgglogValue>(&mut self, root: &S) -> Result<S, TypedError> {
        let mut terms = self.extract_costs(std::slice::from_ref(root))?;
        Ok(terms.pop().unwrap().0)
    }
    /// Returns the same representative with core's native default tree cost.
    pub fn extract_with_cost<S: EgglogValue>(
        &mut self,
        root: &S,
    ) -> Result<(S, DefaultCost), TypedError> {
        let mut terms = self.extract_costs(std::slice::from_ref(root))?;
        Ok(terms.pop().unwrap())
    }
    /// Evaluates ordered roots, then extracts them together into one shared portable DAG.
    /// Root order and duplicates are preserved; this is not joint DAG-cost optimization.
    pub fn extract_many<I: ValueInput>(
        &mut self,
        roots: &[I],
    ) -> Result<Vec<I::Owned>, TypedError> {
        Ok(self
            .extract_costs(roots)?
            .into_iter()
            .map(|(term, _)| term)
            .collect())
    }
    fn extract_costs<I: ValueInput>(
        &mut self,
        roots: &[I],
    ) -> Result<Vec<(I::Owned, DefaultCost)>, TypedError> {
        self.ensure_healthy()?;
        if roots.is_empty() {
            return Ok(vec![]);
        }
        let mut planner = Planner::new(&mut self.core, self.options.lowering_limits.clone());
        planner.collect(roots.iter().map(|r| r.borrow().expression().clone()), [])?;
        planner.prepare_setup(
            &roots
                .iter()
                .map(|r| r.borrow().expression())
                .collect::<Vec<_>>(),
        );
        let names = roots
            .iter()
            .map(|r| planner.materialize(r.borrow().expression()))
            .collect::<Result<Vec<_>, _>>()?;
        let Planner {
            commands,
            symbol_gen,
            ..
        } = planner;
        self.execute(commands, symbol_gen, false)?;
        let sort = self
            .core
            .get_sort_by_name(I::Owned::sort_ref().name())
            .unwrap()
            .clone();
        let values = self.core.read(|rs| {
            names
                .iter()
                .enumerate()
                .map(|(index, n)| {
                    rs.lookup(n, egglog::RawValues(vec![]))
                        .map_err(|source| TypedError::Core {
                            source,
                            command: 0,
                            completed: 0,
                        })?
                        .map(|value| (sort.clone(), value))
                        .ok_or_else(|| TypedError::UnresolvedRoot {
                            index: Some(index),
                            reason: "materialized root row is missing".into(),
                        })
                })
                .collect::<Result<Vec<_>, _>>()
        })?;
        let extracted = self.core.extract_best(values).map_err(|source| {
            self.core.extension_state_or_default::<Installed>().poisoned = true;
            TypedError::Core {
                source,
                command: 0,
                completed: 0,
            }
        })?;
        let result = (|| {
            let state = self.core.extension_state::<Installed>().unwrap();
            let mut memo = HashMap::new();
            let mut output = vec![];
            for (index, term) in extracted.terms.iter().enumerate() {
                let term = term.as_ref().ok_or_else(|| TypedError::UnresolvedRoot {
                    index: Some(index),
                    reason: "no finite extractable representative".into(),
                })?;
                let root = (term.term, I::Owned::sort_ref());
                let mut todo = vec![(root.clone(), false)];
                while let Some(((id, sort), done)) = todo.pop() {
                    if memo.contains_key(&(id, sort.clone())) {
                        continue;
                    }
                    match extracted.termdag.get(id) {
                        Term::Lit(l) => {
                            memo.insert(
                                (id, sort.clone()),
                                Expr::new(sort, NodeKind::Literal(l.clone()), super::origin()),
                            );
                        }
                        Term::Var(v) => {
                            return Err(TypedError::Decode(format!(
                                "unexpected extracted variable {v}"
                            )));
                        }
                        Term::App(name, children) => {
                            let (call, input) = if let Some(def) =
                                state.declarations.get(name.as_str())
                            {
                                (def.callable.clone(), def.inputs.clone())
                            } else {
                                let input = match (&sort.kind, name.as_str()) {
                                    (
                                        SortKind::Container { .. },
                                        "vec-empty" | "set-empty" | "map-empty",
                                    ) => vec![],
                                    (
                                        SortKind::Container {
                                            family: "Map",
                                            arguments,
                                        },
                                        "map-of",
                                    ) => children
                                        .iter()
                                        .enumerate()
                                        .map(|(i, _)| arguments[i % 2].clone())
                                        .collect(),
                                    (
                                        SortKind::Container { arguments, .. },
                                        "vec-of" | "set-of" | "multiset-of" | "pair",
                                    ) => {
                                        if arguments.len() == 1 {
                                            vec![arguments[0].clone(); children.len()]
                                        } else {
                                            arguments.clone()
                                        }
                                    }
                                    (_, "from-string") => vec![super::builtins::String::sort_ref()],
                                    (_, "bigint") => vec![super::builtins::I64::sort_ref()],
                                    (_, "bigrat") => vec![super::builtins::BigInt::sort_ref(); 2],
                                    (_, "rational") => vec![super::builtins::I64::sort_ref(); 2],
                                    _ => {
                                        return Err(TypedError::Decode(format!(
                                            "unsupported native reconstruction {name} for {}",
                                            sort.name()
                                        )));
                                    }
                                };
                                let portable_name = match name.as_str() {
                                    "vec-empty" => "vec-of",
                                    "set-empty" => "set-of",
                                    "map-empty" => "map-of",
                                    _ => name,
                                };
                                (
                                    super::CallableRef {
                                        name: portable_name.into(),
                                        kind: CallKind::Primitive { total: false },
                                        source: None,
                                        syntax: None,
                                    },
                                    input,
                                )
                            };
                            if input.len() != children.len() {
                                return Err(TypedError::Decode("extracted arity mismatch".into()));
                            }
                            if !done {
                                todo.push(((id, sort), true));
                                todo.extend(
                                    children
                                        .iter()
                                        .zip(input)
                                        .rev()
                                        .map(|(id, s)| ((*id, s), false)),
                                );
                            } else {
                                let args = children
                                    .iter()
                                    .zip(input)
                                    .map(|(id, s)| memo[&(*id, s)].clone())
                                    .collect();
                                memo.insert((id, sort.clone()), Expr::call(sort, call, args));
                            }
                        }
                    }
                }
                output.push((I::Owned::from_expression(memo[&root].clone()), term.cost));
            }
            Ok(output)
        })();
        if result.is_err() {
            self.core.extension_state_or_default::<Installed>().poisoned = true;
        }
        result
    }
}
