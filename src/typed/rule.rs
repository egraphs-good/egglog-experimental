use super::{
    CallableRef, EgglogValue, EqualitySort,
    expr::{Expr, Identity, NodeKind, ValueInput, variable},
};
use std::{
    collections::HashSet,
    sync::{Arc, LazyLock},
};
#[derive(Clone, Debug)]
/// A symbolic relation occurrence, usable as a fact or insertion but not as a value child.
pub struct Relation(pub(crate) Expr);
impl Relation {
    #[doc(hidden)]
    pub fn from_expression(expr: Expr) -> Self {
        Self(expr)
    }
    #[doc(hidden)]
    pub fn expression(&self) -> &Expr {
        &self.0
    }
    /// Returns the authored relation call's name for diagnostics.
    /// Use `get_args` for exact typed call inspection.
    pub fn call_name(&self) -> &str {
        match &self.0.node().kind {
            NodeKind::Call(f, _) => &f.name,
            _ => unreachable!(),
        }
    }
}
#[derive(Clone, Debug)]
/// A query proposition. Constructor and function expressions match existing
/// rows; primitive expressions must successfully evaluate. In particular, a
/// `Bool` expression matches either boolean value, not just `true`.
/// Querying does not insert missing constructor or function rows.
pub enum Fact {
    #[doc(hidden)]
    Eq(Expr, Expr),
    #[doc(hidden)]
    Expr(Expr),
}
#[derive(Clone, Debug)]
/// An ordered native mutation or expression evaluation, never an expression child.
pub enum Action {
    #[doc(hidden)]
    Expr(Expr),
    #[doc(hidden)]
    Effect(Expr),
    #[doc(hidden)]
    Set(CallableRef, Vec<Expr>, Expr),
    #[doc(hidden)]
    Union(Expr, Expr),
    #[doc(hidden)]
    Change(egglog::ast::Change, CallableRef, Vec<Expr>),
    #[doc(hidden)]
    Panic(String),
    #[doc(hidden)]
    Invalid(String),
}
impl From<Relation> for Fact {
    fn from(x: Relation) -> Self {
        Self::Expr(x.0)
    }
}
impl From<Relation> for Action {
    fn from(x: Relation) -> Self {
        Self::Effect(x.0)
    }
}
impl From<&Relation> for Fact {
    fn from(x: &Relation) -> Self {
        Self::Expr(x.0.clone())
    }
}
impl From<&Relation> for Action {
    fn from(x: &Relation) -> Self {
        Self::Effect(x.0.clone())
    }
}
impl From<&Action> for Action {
    fn from(x: &Action) -> Self {
        x.clone()
    }
}
impl<I: ValueInput> From<I> for Fact {
    fn from(x: I) -> Self {
        Self::Expr(x.borrow().expression().clone())
    }
}
impl<I: ValueInput> From<I> for Action {
    fn from(x: I) -> Self {
        Self::Expr(x.borrow().expression().clone())
    }
}
/// Matches two expressions of the same sort modulo native equality.
pub fn eq<I: ValueInput>(lhs: I, rhs: impl Into<I::Owned>) -> Fact {
    Fact::Eq(
        lhs.borrow().expression().clone(),
        rhs.into().expression().clone(),
    )
}
/// Builds the native disequality query; it is not Rust structural inequality.
pub fn ne<I: ValueInput>(lhs: I, rhs: impl Into<I::Owned>) -> Fact {
    Fact::Expr(Expr::call(
        super::builtins::Unit::sort_ref(),
        CallableRef::primitive("!=", false),
        vec![
            lhs.borrow().expression().clone(),
            rhs.into().expression().clone(),
        ],
    ))
}
/// Builds a native equality-sort union action.
pub fn union<I: ValueInput>(lhs: I, rhs: impl Into<I::Owned>) -> Action
where
    I::Owned: EqualitySort,
{
    Action::Union(
        lhs.borrow().expression().clone(),
        rhs.into().expression().clone(),
    )
}
/// Sets a declared function call without first evaluating the target call.
/// Invalid target kinds are reported when the action is submitted.
pub fn set<I: ValueInput>(call: I, value: impl Into<I::Owned>) -> Action {
    let value = value.into().expression().clone();
    match &call.borrow().expression().node().kind {
        NodeKind::Call(head, args) if head.kind == super::decl::CallKind::Function => {
            Action::Set(head.clone(), args.clone(), value)
        }
        _ => Action::Invalid("set target must be a direct declared function call".into()),
    }
}
/// Deletes a declared row. Native deletion semantics and restrictions are unchanged.
pub fn delete<C: super::selector::CallRoot>(call: C) -> Action {
    match &call.call_expression().node().kind {
        NodeKind::Call(head, args)
            if !matches!(head.kind, super::decl::CallKind::Primitive { .. }) =>
        {
            Action::Change(egglog::ast::Change::Delete, head.clone(), args.clone())
        }
        _ => Action::Invalid("delete target must be a direct declared row call".into()),
    }
}
/// Subsumes a declared row using native visibility and merge restrictions.
pub fn subsume<C: super::selector::CallRoot>(call: C) -> Action {
    match &call.call_expression().node().kind {
        NodeKind::Call(head, args)
            if !matches!(head.kind, super::decl::CallKind::Primitive { .. }) =>
        {
            Action::Change(egglog::ast::Change::Subsume, head.clone(), args.clone())
        }
        _ => Action::Invalid("subsume target must be a direct declared row call".into()),
    }
}
/// Builds a native failure action; this does not panic during Rust authoring.
/// Execution preserves effects completed before the failure. This is not an
/// assertion that another command is expected to fail.
pub fn panic(message: impl Into<String>) -> Action {
    Action::Panic(message.into())
}
#[doc(hidden)]
pub trait IntoFacts {
    fn into_facts(self) -> Vec<Fact>;
}
#[doc(hidden)]
pub trait IntoActions<M> {
    fn into_actions(self) -> Vec<Action>;
}
#[doc(hidden)]
pub struct Borrowed<M>(std::marker::PhantomData<M>);
#[doc(hidden)]
pub struct Items<M>(std::marker::PhantomData<M>);
#[doc(hidden)]
pub trait IntoRules<M = Direct> {
    fn into_rules(self) -> Vec<Rule>;
}
impl IntoFacts for Fact {
    fn into_facts(self) -> Vec<Fact> {
        vec![self]
    }
}
impl IntoFacts for Relation {
    fn into_facts(self) -> Vec<Fact> {
        vec![self.into()]
    }
}
impl IntoFacts for &Fact {
    fn into_facts(self) -> Vec<Fact> {
        vec![self.clone()]
    }
}
impl IntoFacts for &Relation {
    fn into_facts(self) -> Vec<Fact> {
        vec![self.into()]
    }
}
impl<I: ValueInput> IntoFacts for I {
    fn into_facts(self) -> Vec<Fact> {
        vec![self.into()]
    }
}
impl IntoActions<Direct> for Action {
    fn into_actions(self) -> Vec<Action> {
        vec![self]
    }
}
impl IntoActions<Direct> for Relation {
    fn into_actions(self) -> Vec<Action> {
        vec![self.into()]
    }
}
impl IntoActions<Direct> for &Action {
    fn into_actions(self) -> Vec<Action> {
        vec![self.clone()]
    }
}
impl IntoActions<Direct> for &Relation {
    fn into_actions(self) -> Vec<Action> {
        vec![self.into()]
    }
}
impl<I: ValueInput> IntoActions<Direct> for I {
    fn into_actions(self) -> Vec<Action> {
        vec![self.into()]
    }
}
impl<'a, T: ?Sized, M> IntoActions<Borrowed<M>> for &&'a T
where
    &'a T: IntoActions<M>,
{
    fn into_actions(self) -> Vec<Action> {
        (*self).into_actions()
    }
}
impl IntoActions<Direct> for () {
    fn into_actions(self) -> Vec<Action> {
        vec![]
    }
}
impl IntoActions<Direct> for &() {
    fn into_actions(self) -> Vec<Action> {
        vec![]
    }
}
impl<T: IntoActions<M>, M> IntoActions<Items<M>> for Vec<T> {
    fn into_actions(self) -> Vec<Action> {
        self.into_iter().flat_map(T::into_actions).collect()
    }
}
impl<T: IntoActions<M>, M, const N: usize> IntoActions<Items<M>> for [T; N] {
    fn into_actions(self) -> Vec<Action> {
        self.into_iter().flat_map(T::into_actions).collect()
    }
}
impl<'a, T, M> IntoActions<Items<M>> for &'a [T]
where
    &'a T: IntoActions<M>,
{
    fn into_actions(self) -> Vec<Action> {
        self.iter().flat_map(<&T>::into_actions).collect()
    }
}
impl<'a, T, M, const N: usize> IntoActions<Items<M>> for &'a [T; N]
where
    &'a T: IntoActions<M>,
{
    fn into_actions(self) -> Vec<Action> {
        self.iter().flat_map(<&T>::into_actions).collect()
    }
}
impl<'a, T, M> IntoActions<Items<M>> for &'a Vec<T>
where
    &'a T: IntoActions<M>,
{
    fn into_actions(self) -> Vec<Action> {
        self.iter().flat_map(<&T>::into_actions).collect()
    }
}
impl IntoRules for Rule {
    fn into_rules(self) -> Vec<Rule> {
        vec![self]
    }
}
impl IntoRules for &Rule {
    fn into_rules(self) -> Vec<Rule> {
        vec![self.clone()]
    }
}
impl IntoRules for Ruleset {
    fn into_rules(self) -> Vec<Rule> {
        Arc::unwrap_or_clone(self.rules)
    }
}
impl IntoRules for &Ruleset {
    fn into_rules(self) -> Vec<Rule> {
        self.rules.as_ref().clone()
    }
}
impl<F: FnOnce() -> Ruleset> IntoRules for &LazyLock<Ruleset, F> {
    fn into_rules(self) -> Vec<Rule> {
        self.rules.as_ref().clone()
    }
}
macro_rules! collections {
    ($trait:ident,$method:ident,$out:ty) => {
        impl $trait for () {
            fn $method(self) -> Vec<$out> {
                vec![]
            }
        }
        impl<T: $trait> $trait for Vec<T> {
            fn $method(self) -> Vec<$out> {
                self.into_iter().flat_map(T::$method).collect()
            }
        }
        impl<T: $trait, const N: usize> $trait for [T; N] {
            fn $method(self) -> Vec<$out> {
                self.into_iter().flat_map(T::$method).collect()
            }
        }
        impl<T: $trait + Clone> $trait for &[T] {
            fn $method(self) -> Vec<$out> {
                self.iter().cloned().flat_map(T::$method).collect()
            }
        }
        impl<T: $trait + Clone, const N: usize> $trait for &[T; N] {
            fn $method(self) -> Vec<$out> {
                self.iter().cloned().flat_map(T::$method).collect()
            }
        }
        impl<T: $trait + Clone> $trait for &Vec<T> {
            fn $method(self) -> Vec<$out> {
                self.iter().cloned().flat_map(T::$method).collect()
            }
        }
    };
}
collections!(IntoFacts, into_facts, Fact);
collections!(IntoRules, into_rules, Rule);
#[derive(Clone, Debug)]
/// One authored rule occurrence. Clones share its native installation and cursor.
/// Semantic options use copy-on-write so existing clones and installations stay unchanged.
/// Diagnostic labels do not change the occurrence.
pub struct Rule {
    pub(crate) data: Identity<RuleData>,
    pub(crate) label: Option<String>,
}
#[derive(Clone, Debug)]
pub(crate) struct RuleData {
    pub(crate) facts: Vec<Fact>,
    pub(crate) actions: Vec<Action>,
    pub(crate) naive: bool,
    pub(crate) no_decomp: bool,
    pub(crate) include_subsumed: bool,
}
impl Rule {
    /// Adds query conditions in call order, before any rule execution.
    ///
    /// Conditions may bind variables used by the actions. Submission validates
    /// the complete query; empty input preserves occurrence identity.
    pub fn when<Q: IntoFacts>(mut self, conditions: Q) -> Self {
        let facts = conditions.into_facts();
        if !facts.is_empty() {
            Arc::make_mut(&mut self.data.0).facts.extend(facts);
        }
        self
    }
    /// Selects native naive evaluation, including its permitted RHS read contexts.
    pub fn naive(mut self) -> Self {
        if !self.data.0.naive {
            Arc::make_mut(&mut self.data.0).naive = true;
        }
        self
    }
    /// Selects native seminaive evaluation and its RHS read restrictions.
    pub fn seminaive(mut self) -> Self {
        if self.data.0.naive {
            Arc::make_mut(&mut self.data.0).naive = false;
        }
        self
    }
    /// Disables native query decomposition for this rule occurrence.
    pub fn no_decomp(mut self) -> Self {
        if !self.data.0.no_decomp {
            Arc::make_mut(&mut self.data.0).no_decomp = true;
        }
        self
    }
    /// Includes subsumed rows in this rule's native matching.
    pub fn include_subsumed(mut self) -> Self {
        if !self.data.0.include_subsumed {
            Arc::make_mut(&mut self.data.0).include_subsumed = true;
        }
        self
    }
    /// Sets a diagnostic label without changing occurrence identity or cursors.
    /// First installation fixes the native diagnostic name; relabeling does not reinstall it.
    pub fn label(mut self, name: impl Into<String>) -> Self {
        self.label = Some(name.into());
        self
    }
}
impl Fact {
    pub(crate) fn expressions(&self) -> Vec<&Expr> {
        match self {
            Self::Eq(a, b) => vec![a, b],
            Self::Expr(a) => vec![a],
        }
    }
}
impl Action {
    pub(crate) fn expressions(&self) -> Vec<&Expr> {
        match self {
            Self::Expr(a) | Self::Effect(a) => vec![a],
            Self::Set(_, a, b) => a.iter().chain(std::iter::once(b)).collect(),
            Self::Union(a, b) => vec![a, b],
            Self::Change(_, _, a) => a.iter().collect(),
            Self::Panic(_) | Self::Invalid(_) => vec![],
        }
    }
}
/// Authors a query and ordered actions as one rule.
///
/// Introduce variables with [`super::var`] or a [`ruleset`] callback.
/// Submission rejects RHS-only variables and captures.
/// Inputs may be individual facts/actions or heterogeneous tuples and homogeneous collections.
///
/// ```
/// use egglog_experimental::typed::{builtins::I64, prelude::*};
/// #[relation]
/// pub fn edge(from: I64, to: I64);
/// #[ruleset]
/// fn paths(from: &I64, via: &I64, to: &I64) -> Vec<Rule> {
///     vec![rule((edge(from, via), edge(via, to)), edge(from, to))]
/// }
/// let mut graph = EGraph::default();
/// graph.register((edge(1, 2), edge(2, 3)))?;
/// graph.run(paths.saturate())?;
/// assert!(graph.check(edge(1, 3))?);
/// # Ok::<(), TypedError>(())
/// ```
pub fn rule<Q: IntoFacts, A: IntoActions<M>, M>(lhs: Q, rhs: A) -> Rule {
    Rule {
        data: Identity(Arc::new(RuleData {
            facts: lhs.into_facts(),
            actions: rhs.into_actions(),
            naive: false,
            no_decomp: false,
            include_subsumed: false,
        })),
        label: None,
    }
}
/// Authors an equality rewrite. Add optional query conditions with [`Rule::when`].
pub fn rewrite<I: ValueInput>(lhs: I, rhs: impl Into<I::Owned>) -> Rule
where
    I::Owned: EqualitySort,
{
    let expression = lhs.borrow().expression();
    rule(Fact::Expr(expression.clone()), union(lhs, rhs))
}
/// Authors both directions of an equality as independent rule occurrences.
///
/// Each direction has its own query and binding validation. Use array [`map`](array::map)
/// to add the same conditions to both rules, or customize each rule separately.
pub fn birewrite<I: ValueInput>(lhs: I, rhs: impl Into<I::Owned>) -> [Rule; 2]
where
    I::Owned: EqualitySort,
{
    let lhs = lhs.borrow().clone();
    let rhs = rhs.into();
    [rewrite(lhs.clone(), rhs.clone()), rewrite(rhs, lhs)]
}
#[derive(Clone, Debug)]
/// An immutable, ordered collection of rule occurrences.
pub struct Ruleset {
    pub(crate) rules: Arc<Vec<Rule>>,
    pub(crate) label: Option<String>,
}
impl Ruleset {
    /// Lowers this group to native AST commands for diagnostic inspection.
    ///
    /// Returns self-contained declarations, distinct rules in first-use order,
    /// and the combined group, without a run command or schedule. Uses submission
    /// lowering with fresh state and default [`super::LoweringLimits`], including
    /// its preflight errors. No execution, evaluation, parsing, or native
    /// resolution/typechecking is performed.
    ///
    /// Declaration names retain their exact nominal spelling. Local names preserve
    /// bindings and sharing, and are stable for the same ordered authoring structure.
    /// Spans retain Rust authoring locations. This is not canonical equivalence:
    /// aliases or first-use order can change the AST without changing semantics.
    /// Native `Display` is useful for inspection, not lossless source serialization.
    ///
    /// ```
    /// use egglog_experimental::typed::{builtins::I64, prelude::*};
    /// #[relation]
    /// fn seen(value: I64);
    /// let rules = ruleset(|value: &I64| rule(eq(value, 3), seen(value)));
    /// for command in rules.to_ast()? {
    ///     println!("{command}");
    /// }
    /// # Ok::<(), TypedError>(())
    /// ```
    pub fn to_ast(&self) -> Result<Vec<egglog::ast::Command>, super::TypedError> {
        let mut planner = super::lower::Planner::empty(super::LoweringLimits::default());
        planner.group(self)?;
        Ok(planner
            .commands
            .into_iter()
            .map(|(command, _)| command)
            .collect())
    }

    /// Repeats this group's native run using native stopping behavior.
    pub fn repeat(&self, times: usize) -> Schedule {
        Schedule(Arc::new(ScheduleNode::Repeat(times, self.into())))
    }
    /// Runs this group to native saturation.
    pub fn saturate(&self) -> Schedule {
        Schedule(Arc::new(ScheduleNode::Saturate(self.into())))
    }
    /// Adds a native stopping query to this group's run.
    pub fn until<Q: IntoFacts>(&self, facts: Q) -> Schedule {
        Schedule(Arc::new(ScheduleNode::Run(
            self.clone(),
            facts.into_facts(),
        )))
    }
    /// Sets a diagnostic label without changing occurrence identity or cursors.
    /// First installation fixes the native diagnostic name; relabeling does not reinstall it.
    pub fn label(mut self, name: impl Into<String>) -> Self {
        self.label = Some(name.into());
        self
    }
    /// Number of distinct rule occurrences in this immutable group.
    pub fn len(&self) -> usize {
        self.rules.len()
    }
    /// Whether this group has no rule occurrences.
    pub fn is_empty(&self) -> bool {
        self.rules.is_empty()
    }
}
#[doc(hidden)]
pub struct Direct;
#[doc(hidden)]
pub struct Callback<A>(std::marker::PhantomData<A>);
/// Builds an immutable group, deduplicating cloned rule occurrences in first-use order.
///
/// Pass existing rules/groups directly, or use a callback to introduce fresh typed
/// variables shared by the group's definitions, with up to 128 borrowed parameters.
/// Owned variable clones can also be reused outside the callback; submission
/// validates each rule's own query bindings.
pub fn ruleset<T, M>(input: T) -> Ruleset
where
    T: IntoRules<M>,
{
    let mut seen = HashSet::new();
    let rules = input
        .into_rules()
        .into_iter()
        .filter(|r| seen.insert(r.data.clone()))
        .collect();
    Ruleset {
        rules: Arc::new(rules),
        label: None,
    }
}
#[derive(Clone, Debug)]
/// A shared immutable native schedule. Clones retain the same schedule tree.
pub struct Schedule(pub(crate) Arc<ScheduleNode>);

#[derive(Debug)]
pub(crate) enum ScheduleNode {
    Run(Ruleset, Vec<Fact>),
    Repeat(usize, Schedule),
    Saturate(Schedule),
    Sequence(Vec<Schedule>),
    Invalid(String),
}
impl From<Ruleset> for Schedule {
    fn from(group: Ruleset) -> Self {
        Self(Arc::new(ScheduleNode::Run(group, Vec::new())))
    }
}
impl From<&Ruleset> for Schedule {
    fn from(group: &Ruleset) -> Self {
        Self(Arc::new(ScheduleNode::Run(group.clone(), Vec::new())))
    }
}
impl<F: FnOnce() -> Ruleset> From<&LazyLock<Ruleset, F>> for Schedule {
    fn from(group: &LazyLock<Ruleset, F>) -> Self {
        Self(Arc::new(ScheduleNode::Run((**group).clone(), Vec::new())))
    }
}
impl From<&Schedule> for Schedule {
    fn from(schedule: &Schedule) -> Self {
        schedule.clone()
    }
}
impl Schedule {
    /// Repeats this schedule using native stopping behavior.
    pub fn repeat(self, times: usize) -> Self {
        Self(Arc::new(ScheduleNode::Repeat(times, self)))
    }
    /// Runs this schedule to native saturation.
    pub fn saturate(self) -> Self {
        Self(Arc::new(ScheduleNode::Saturate(self)))
    }
    /// Adds a native stopping query to a direct run.
    /// Attaching it to a sequence, repeat, or saturation yields a preflight error.
    pub fn until<Q: IntoFacts>(self, facts: Q) -> Self {
        Self(Arc::new(match self.0.as_ref() {
            ScheduleNode::Run(g, _) => ScheduleNode::Run(g.clone(), facts.into_facts()),
            _ => ScheduleNode::Invalid("until may only be attached to a ruleset run".into()),
        }))
    }
}
#[doc(hidden)]
pub trait IntoSchedules {
    fn into_schedules(self) -> Vec<Schedule>;
}
impl<T: Into<Schedule>> IntoSchedules for T {
    fn into_schedules(self) -> Vec<Schedule> {
        vec![self.into()]
    }
}
collections!(IntoSchedules, into_schedules, Schedule);
/// Sequences schedules in caller order; each child retains its native run boundary.
pub fn sequence<S: IntoSchedules>(schedules: S) -> Schedule {
    Schedule(Arc::new(ScheduleNode::Sequence(schedules.into_schedules())))
}
macro_rules! tuple_adapter {
    ($trait:ident,$method:ident,$out:ty;$( $a:ident : $index:tt ),+) => {
        impl<$($a:$trait),+> $trait for ($($a,)+) {
            fn $method(self)->Vec<$out>{let mut output=Vec::new();$(output.extend(self.$index.$method());)+output}
        }
    };
}
macro_rules! callback_adapter {
    ($( $a:ident : $marker:ident : $index:tt ),*) => {
        impl<F,$($a:EgglogValue,)*R:IntoRules> IntoRules<Callback<($($a,)*)>> for F
        where F:for<'scope> FnOnce($(&'scope $a),*)->R{
            fn into_rules(self)->Vec<Rule>{
                let scope=Identity(Arc::new(()));let _=&scope;
                let variables=($(variable::<$a>(scope.clone(),$index),)*);
                let _=&variables;
                self($(&variables.$index),*).into_rules()
            }
        }
    };
}
macro_rules! arity {
    ($( $a:ident : $marker:ident : $index:tt ),+) => {
        tuple_adapter!(IntoFacts,into_facts,Fact;$($a:$index),+);
        tuple_adapter!(IntoRules,into_rules,Rule;$($a:$index),+);
        tuple_adapter!(IntoSchedules,into_schedules,Schedule;$($a:$index),+);
    };
}
callback_adapter!();
for_arities!(arity);
// Callback binders may be wider than the heterogeneous tuple input adapters.
for_arities!(callback_adapter;
    A32:M32:32,A33:M33:33,A34:M34:34,A35:M35:35,A36:M36:36,A37:M37:37,A38:M38:38,A39:M39:39,
    A40:M40:40,A41:M41:41,A42:M42:42,A43:M43:43,A44:M44:44,A45:M45:45,A46:M46:46,A47:M47:47,
    A48:M48:48,A49:M49:49,A50:M50:50,A51:M51:51,A52:M52:52,A53:M53:53,A54:M54:54,A55:M55:55,
    A56:M56:56,A57:M57:57,A58:M58:58,A59:M59:59,A60:M60:60,A61:M61:61,A62:M62:62,A63:M63:63,
    A64:M64:64,A65:M65:65,A66:M66:66,A67:M67:67,A68:M68:68,A69:M69:69,A70:M70:70,A71:M71:71,
    A72:M72:72,A73:M73:73,A74:M74:74,A75:M75:75,A76:M76:76,A77:M77:77,A78:M78:78,A79:M79:79,
    A80:M80:80,A81:M81:81,A82:M82:82,A83:M83:83,A84:M84:84,A85:M85:85,A86:M86:86,A87:M87:87,
    A88:M88:88,A89:M89:89,A90:M90:90,A91:M91:91,A92:M92:92,A93:M93:93,A94:M94:94,A95:M95:95,
    A96:M96:96,A97:M97:97,A98:M98:98,A99:M99:99,A100:M100:100,A101:M101:101,A102:M102:102,A103:M103:103,
    A104:M104:104,A105:M105:105,A106:M106:106,A107:M107:107,A108:M108:108,A109:M109:109,A110:M110:110,A111:M111:111,
    A112:M112:112,A113:M113:113,A114:M114:114,A115:M115:115,A116:M116:116,A117:M117:117,A118:M118:118,A119:M119:119,
    A120:M120:120,A121:M121:121,A122:M122:122,A123:M123:123,A124:M124:124,A125:M125:125,A126:M126:126,A127:M127:127
);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typed::{EGraph, EGraphOptions, TypedError, builtins::I64, origin, var};

    #[test]
    fn consuming_groups_moves_unique_storage_and_preserves_shared_occurrences() {
        let unique = ruleset(rule((), ()));
        let allocation = unique.rules.as_ptr();
        let occurrence = unique.rules[0].data.clone();
        let moved = unique.into_rules();
        assert_eq!(moved.as_ptr(), allocation);
        assert_eq!(moved[0].data, occurrence);

        let shared = ruleset(rule((), ()).label("retained"));
        let retained = shared.clone();
        let copied = shared.into_rules();
        assert_ne!(copied.as_ptr(), retained.rules.as_ptr());
        assert_eq!(copied[0].data, retained.rules[0].data);
        assert_eq!(copied[0].label, retained.rules[0].label);
    }

    #[test]
    fn schedules_share_nodes_and_lazy_groups_keep_labels_and_order() {
        let labelled = LazyLock::new(|| ruleset(rule((), ())).label("explicit"));
        let anonymous = LazyLock::new(|| ruleset(rule((), ())));

        assert_eq!(labelled.label.as_deref(), Some("explicit"));
        assert!(anonymous.label.is_none());
        let groups = ruleset((&anonymous, &labelled, &anonymous));
        assert_eq!(groups.rules[0].data, anonymous.rules[0].data);
        assert_eq!(groups.rules[1].data, labelled.rules[0].data);
        assert_eq!(groups.len(), 2);

        let shared = labelled.repeat(2).saturate();
        let cloned = shared.clone();
        assert!(Arc::ptr_eq(&shared.0, &cloned.0));
        let borrowed = Schedule::from(&shared);
        assert!(Arc::ptr_eq(&shared.0, &borrowed.0));
        let composed = sequence((&shared, &cloned, &anonymous, groups));
        let ScheduleNode::Sequence(children) = composed.0.as_ref() else {
            panic!()
        };
        assert!(Arc::ptr_eq(&children[0].0, &shared.0));
        assert!(Arc::ptr_eq(&children[1].0, &shared.0));
        let ScheduleNode::Run(group, _) = children[2].0.as_ref() else {
            panic!()
        };
        assert!(Arc::ptr_eq(&group.rules, &anonymous.rules));

        let direct = Schedule::from(&labelled);
        let stopped = direct.clone().until(eq(I64::from(1), 1));
        let ScheduleNode::Run(_, original_facts) = direct.0.as_ref() else {
            panic!()
        };
        let ScheduleNode::Run(_, stop_facts) = stopped.0.as_ref() else {
            panic!()
        };
        assert!(original_facts.is_empty());
        assert_eq!(stop_facts.len(), 1);
    }

    #[test]
    fn conditions_append_in_order_and_preserve_existing_metadata() {
        let x = var::<I64>("x");
        let original = rule(eq(&x, 1), ())
            .naive()
            .no_decomp()
            .include_subsumed()
            .label("source rule");
        let unchanged = original.clone().when(());
        assert_eq!(original.data, unchanged.data);
        let appended = original
            .clone()
            .when(eq(&x, 2))
            .when((eq(&x, 3), eq(&x, 4)));
        assert_ne!(original.data, appended.data);
        assert_eq!(original.data.0.facts.len(), 1);
        assert!(appended.data.0.naive);
        assert!(appended.data.0.no_decomp);
        assert!(appended.data.0.include_subsumed);
        assert_eq!(appended.label, original.label);
        let values: Vec<_> = appended
            .data
            .0
            .facts
            .iter()
            .map(|fact| {
                let Fact::Eq(_, rhs) = fact else {
                    unreachable!()
                };
                i64::try_from(I64::from_expression(rhs.clone())).unwrap()
            })
            .collect();
        assert_eq!(values, [1, 2, 3, 4]);
    }

    #[test]
    fn submission_rejects_escaped_merge_variables() {
        let old = I64::from_expression(Expr::new(
            I64::sort_ref(),
            NodeKind::MergeVariable("old"),
            origin(),
        ));
        let mut graph = EGraph::new(EGraphOptions::default());
        for step in [rule(&old, ()), rule(eq(&old, 0), ()), rule((), &old)] {
            assert!(matches!(
                graph.run(ruleset(step)),
                Err(TypedError::Invalid(_))
            ));
            assert_eq!(graph.num_tuples().unwrap(), 0);
            assert!(graph.check(()).unwrap());
        }
        assert!(matches!(graph.check(&old), Err(TypedError::Invalid(_))));
    }
}

macro_rules! action_tuple {
    ($( $a:ident : $m:ident : $index:tt ),+) => {
        impl<$($a:IntoActions<$m>,$m),+> IntoActions<($($m,)+)> for ($($a,)+) {
            fn into_actions(self)->Vec<Action>{let mut output=Vec::new();$(output.extend(self.$index.into_actions());)+output}
        }
        impl<'a,$($a,$m),+> IntoActions<($($m,)+)> for &'a ($($a,)+) where $(&'a $a:IntoActions<$m>),+ {
            fn into_actions(self)->Vec<Action>{let mut output=Vec::new();$(output.extend((&self.$index).into_actions());)+output}
        }
    };
}
for_arities!(action_tuple);
