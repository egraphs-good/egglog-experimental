//! Offline lowering to the shared Egglog program, and explicit definitions.

use super::{
    Fact, LoweringLimits, Rule, Ruleset, Schedule, SortRef, TypedError,
    decl::CallKind,
    lower::{Commit, Installed, Planner},
    rule::{Direct, IntoActions, IntoFacts, Items},
    selector::SelectCall,
};
use egglog::{ast::Command, program::Program};

#[derive(Clone, Debug)]
/// A sort, selected callable, or ruleset to install without evaluating expressions.
///
/// Sort descriptions and rulesets can be passed directly to `install`. Use
/// [`Self::callable`] to select a declaration through its ordinary Rust callable.
/// This frontend description lowers to the same shared program as other inputs;
/// it is not a separate serialization format.
pub struct Definition(pub(crate) DefinitionKind);

#[derive(Clone, Debug)]
pub(crate) enum DefinitionKind {
    Sort(SortRef),
    Callable(super::CallableRef),
    Ruleset(Ruleset),
}

impl Definition {
    /// Selects one declared constructor, relation, or function without evaluating it.
    ///
    /// The callback constructs a direct symbolic call using every fresh argument
    /// exactly once in declaration order. Ordinary Rust callback code does run;
    /// no Egglog expression runs. Primitive operations are not declarations.
    ///
    /// ```
    /// use egglog_experimental::typed::{builtins::I64, prelude::*};
    /// #[relation]
    /// fn seen(value: I64);
    /// let mut graph = EGraph::default();
    /// graph.install(Definition::callable(|value: &I64| seen(value))?)?;
    /// assert_eq!(graph.num_tuples()?, 0);
    /// # Ok::<(), TypedError>(())
    /// ```
    pub fn callable<F, A>(selector: F) -> Result<Self, TypedError>
    where
        F: SelectCall<A>,
    {
        let selection = selector.select()?;
        if matches!(selection.callable.kind, CallKind::Primitive { .. })
            || selection.callable.source.is_none()
        {
            return Err(TypedError::Invalid(
                "installation requires a declared constructor, relation, or function".into(),
            ));
        }
        Ok(Self(DefinitionKind::Callable(selection.callable)))
    }
}

impl From<SortRef> for Definition {
    fn from(sort: SortRef) -> Self {
        Self(DefinitionKind::Sort(sort))
    }
}
impl From<&SortRef> for Definition {
    fn from(sort: &SortRef) -> Self {
        Self(DefinitionKind::Sort(sort.clone()))
    }
}
impl From<Ruleset> for Definition {
    fn from(rules: Ruleset) -> Self {
        Self(DefinitionKind::Ruleset(rules))
    }
}
impl From<&Ruleset> for Definition {
    fn from(rules: &Ruleset) -> Self {
        Self(DefinitionKind::Ruleset(rules.clone()))
    }
}
impl<F: FnOnce() -> Ruleset> From<&std::sync::LazyLock<Ruleset, F>> for Definition {
    fn from(rules: &std::sync::LazyLock<Ruleset, F>) -> Self {
        Self(DefinitionKind::Ruleset((**rules).clone()))
    }
}
impl From<Rule> for Definition {
    fn from(rule: Rule) -> Self {
        Self(DefinitionKind::Ruleset(super::ruleset(rule)))
    }
}
impl From<&Rule> for Definition {
    fn from(rule: &Rule) -> Self {
        Self(DefinitionKind::Ruleset(super::ruleset(rule)))
    }
}
impl From<&Definition> for Definition {
    fn from(definition: &Definition) -> Self {
        definition.clone()
    }
}

/// Adapts definitions, sort descriptions, rules, rulesets, and collections for installation.
#[doc(hidden)]
pub trait IntoDefinitions<M> {
    fn into_definitions(self) -> Vec<Definition>;
}
impl<T: Into<Definition>> IntoDefinitions<Direct> for T {
    fn into_definitions(self) -> Vec<Definition> {
        vec![self.into()]
    }
}
impl IntoDefinitions<Direct> for () {
    fn into_definitions(self) -> Vec<Definition> {
        vec![]
    }
}
impl<T: IntoDefinitions<M>, M> IntoDefinitions<Items<M>> for Vec<T> {
    fn into_definitions(self) -> Vec<Definition> {
        self.into_iter().flat_map(T::into_definitions).collect()
    }
}
impl<T: IntoDefinitions<M>, M, const N: usize> IntoDefinitions<Items<M>> for [T; N] {
    fn into_definitions(self) -> Vec<Definition> {
        self.into_iter().flat_map(T::into_definitions).collect()
    }
}
impl<'a, T, M> IntoDefinitions<Items<M>> for &'a [T]
where
    &'a T: IntoDefinitions<M>,
{
    fn into_definitions(self) -> Vec<Definition> {
        self.iter().flat_map(<&T>::into_definitions).collect()
    }
}
impl<'a, T, M, const N: usize> IntoDefinitions<Items<M>> for &'a [T; N]
where
    &'a T: IntoDefinitions<M>,
{
    fn into_definitions(self) -> Vec<Definition> {
        self.iter().flat_map(<&T>::into_definitions).collect()
    }
}
impl<'a, T, M> IntoDefinitions<Items<M>> for &'a Vec<T>
where
    &'a T: IntoDefinitions<M>,
{
    fn into_definitions(self) -> Vec<Definition> {
        self.iter().flat_map(<&T>::into_definitions).collect()
    }
}
macro_rules! definition_tuple {
    ($($a:ident:$marker:ident:$index:tt),+) => {
        impl<$($a: IntoDefinitions<$marker>, $marker),+> IntoDefinitions<($($marker,)+)> for ($($a,)+) {
            fn into_definitions(self) -> Vec<Definition> {
                let mut output = vec![];
                $(output.extend(self.$index.into_definitions());)+
                output
            }
        }
        impl<'a, $($a, $marker),+> IntoDefinitions<($($marker,)+)> for &'a ($($a,)+)
        where $(&'a $a: IntoDefinitions<$marker>),+ {
            fn into_definitions(self) -> Vec<Definition> {
                let mut output = vec![];
                $(output.extend((&self.$index).into_definitions());)+
                output
            }
        }
    };
}
for_arities!(definition_tuple);

/// Builds a shared program without running Egglog, resolving native names, or
/// evaluating expressions. Each successful method appends an ordered command batch.
///
/// Definitions, captures, and rule occurrences are remembered between methods.
/// A failed lowering leaves this builder unchanged. `push`/`pop` restore that
/// planned installation state while preserving fresh-name counters. The builder
/// assumes earlier commands succeed at execution time; `check` adds an assertion,
/// not a boolean observation. Native typechecking and runtime failures remain
/// possible when the resulting program is submitted.
///
/// ```
/// use egglog_experimental::typed::{builtins::I64, prelude::*};
/// #[relation]
/// fn seen(value: I64);
/// let mut program = ProgramBuilder::default();
/// program.install(Definition::callable(|value: &I64| seen(value))?)?;
/// program.register(seen(3))?;
/// program.check(seen(3))?;
/// let program = program.finish()?;
/// let json = program.to_json()?;
/// let restored = egglog::program::Program::from_json(&json)?;
/// let mut graph = egglog_experimental::new_experimental_egraph();
/// graph.run_shared_program(restored)?;
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub struct ProgramBuilder {
    commands: Vec<Command>,
    state: Installed,
    symbol_gen: egglog::util::SymbolGen,
    scopes: Vec<Installed>,
    limits: LoweringLimits,
}

impl Default for ProgramBuilder {
    fn default() -> Self {
        Self::new(LoweringLimits::default())
    }
}

impl ProgramBuilder {
    /// Creates an empty program with the same per-method lowering budgets as a live graph.
    pub fn new(limits: LoweringLimits) -> Self {
        let planner = Planner::empty(limits.clone());
        Self {
            commands: vec![],
            state: planner.state,
            symbol_gen: planner.symbol_gen,
            scopes: vec![],
            limits,
        }
    }

    // Plan against private copies so preflight failures cannot leak declarations,
    // captures, rule occurrences, or fresh-name reservations into later batches.
    fn append(
        &mut self,
        lower: impl FnOnce(&mut Planner<'_>) -> Result<(), TypedError>,
    ) -> Result<(), TypedError> {
        let mut planner = Planner::empty(self.limits.clone());
        planner.state = self.state.clone();
        planner.symbol_gen = self.symbol_gen.clone();
        lower(&mut planner)?;
        self.state = planner.state;
        self.symbol_gen = planner.symbol_gen;
        self.commands
            .extend(planner.commands.into_iter().map(|(command, _)| command));
        Ok(())
    }

    /// Appends definitions and their dependencies without a run or evaluation command.
    pub fn install<T, M>(&mut self, definitions: T) -> Result<(), TypedError>
    where
        T: IntoDefinitions<M>,
    {
        let definitions = definitions.into_definitions();
        self.append(|planner| planner.install(&definitions))
    }

    /// Appends expression materialization and ordered actions, as in [`super::EGraph::register`].
    pub fn register<T, M>(&mut self, items: T) -> Result<(), TypedError>
    where
        T: IntoActions<M>,
    {
        let actions = items.into_actions();
        self.append(|planner| planner.register(&actions))
    }

    /// Appends a native check assertion without constructing its queried terms.
    /// Unlike a live graph's boolean query, a false assertion stops program execution.
    pub fn check<Q: IntoFacts>(&mut self, facts: Q) -> Result<(), TypedError> {
        let facts = facts.into_facts();
        self.append(|planner| {
            if !facts.is_empty() {
                planner.collect(facts.iter().flat_map(Fact::expressions).cloned(), [])?;
                let native = planner.query(&facts, false)?;
                planner.emit(Command::Check(super::origin(), native), Commit::None)?;
            }
            Ok(())
        })
    }

    /// Appends reachable rules and their native schedule, without running them.
    pub fn run(&mut self, schedule: impl Into<Schedule>) -> Result<(), TypedError> {
        let schedule = schedule.into();
        self.append(|planner| {
            let native = planner.schedule(&schedule, 0)?;
            planner.emit(Command::RunSchedule(native), Commit::None)
        })
    }

    /// Appends a scope push and saves planned installation state.
    pub fn push(&mut self) -> Result<(), TypedError> {
        self.append(|planner| planner.emit(Command::Push(1), Commit::None))?;
        self.scopes.push(self.state.clone());
        Ok(())
    }

    /// Appends a scope pop and restores planned installations, retaining fresh names.
    /// An unmatched pop is rejected without changing the builder.
    pub fn pop(&mut self) -> Result<(), TypedError> {
        if self.scopes.is_empty() {
            return Err(TypedError::Invalid(
                "program has no pushed scope to restore".into(),
            ));
        }
        self.append(|planner| planner.emit(Command::Pop(super::origin(), 1), Commit::None))?;
        self.state = self.scopes.pop().unwrap();
        Ok(())
    }

    /// Validates and returns the shared core representation. Open pushed scopes
    /// are allowed, as in an ordinary Egglog program. This does not typecheck or execute it.
    pub fn finish(self) -> Result<Program, egglog::program::ProgramError> {
        Program::new(self.commands)
    }
}
