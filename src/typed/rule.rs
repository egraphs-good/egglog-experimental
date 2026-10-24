use super::{
    EgglogValue, SortRef, TypedError,
    decl::Callable,
    expr::{Expr, ValueInput, fresh_scope, variable},
    pb,
    storage::{Arena, DeclarationKind, Record, Slot, publish, visit, visit_action},
};
use std::sync::LazyLock;

/// An owned canonical action, or a deferred authoring diagnostic.
/// Invalid targets are rejected at submission, before any actions execute.
#[derive(Clone)]
pub struct Action(Result<Record, String>);

impl<I: ValueInput> From<I> for Action {
    /// Retain an expression as an ordered term action in a heterogeneous list.
    /// This preserves its declarations, capture recipe and observation ownership;
    /// construction does not evaluate or materialize it.
    fn from(value: I) -> Self {
        let mut slots = std::array::from_fn(|_| vec![]);
        slots[Arena::Node as usize] = vec![Slot::External(value.borrow().expression().0.clone())];
        Self(
            publish(
                pb::Program {
                    commands: vec![pb::Command {
                        kind: Some(pb::command::Kind::Action(pb::Action {
                            kind: Some(pb::action::Kind::Term(0)),
                            ..Default::default()
                        })),
                        ..Default::default()
                    }],
                    ..Default::default()
                },
                slots,
                vec![],
                Arena::Command,
                0,
            )
            .map_err(|error| error.to_string()),
        )
    }
}

/// Write a direct function row without evaluating its target lookup.
/// With `no_merge`, assigning a different value to an existing row is an error.
pub fn set<I: ValueInput>(target: I, value: impl Into<I::Owned>) -> Action {
    row_action(
        target.borrow().expression(),
        pb::action::Kind::Set(pb::Set::default()),
        Some(value.into().expression().clone()),
    )
}

/// Delete a direct constructor, function or relation row without creating or reading it.
pub fn delete<I: ValueInput>(target: I) -> Action {
    row_action(
        target.borrow().expression(),
        pb::action::Kind::Delete(pb::Call::default()),
        None,
    )
}

/// Apply native constructor subsumption by row address, without a target lookup.
/// The native backend may create an absent row; this is not a deletion.
/// Function, primitive and capture targets are rejected at submission.
pub fn subsume<I: ValueInput>(target: I) -> Action {
    row_action(
        target.borrow().expression(),
        pb::action::Kind::Subsume(pb::Call::default()),
        None,
    )
}

// Preserve the target declaration and relocate its arguments, not the lookup
// node. The generated action arm determines admissible declaration kinds; no
// semantic action tree or name-to-target registry is retained.
fn row_action(target: &Expr, mut action: pb::action::Kind, value: Option<Expr>) -> Action {
    let build = || -> Result<Record, TypedError> {
        if target.0.owner.as_ref().unwrap().observed {
            return Err(TypedError::Invalid(
                "snapshot observations cannot be used as live row targets".into(),
            ));
        }
        if target.0.capture()?.is_some() {
            return Err(TypedError::Invalid(
                "capture storage is not an authored row target".into(),
            ));
        }
        let node = &target.0.owner.as_ref().unwrap().program.nodes[target.0.index as usize];
        let Some(pb::node::Kind::Call(call)) = &node.kind else {
            return Err(TypedError::Invalid(
                "row action requires a direct declared call".into(),
            ));
        };
        let declaration = target
            .0
            .declaration(&call.func, DeclarationKind::Callable)?;
        let kind = &declaration.owner.as_ref().unwrap().program.declarations
            [declaration.index as usize]
            .kind;
        if !matches!(
            (kind, &action),
            (
                Some(pb::declaration::Kind::Function(_)),
                pb::action::Kind::Set(_)
            ) | (
                Some(
                    pb::declaration::Kind::Function(_)
                        | pb::declaration::Kind::Constructor(_)
                        | pb::declaration::Kind::Relation(_)
                ),
                pb::action::Kind::Delete(_)
            ) | (
                Some(pb::declaration::Kind::Constructor(_)),
                pb::action::Kind::Subsume(_)
            )
        ) {
            return Err(TypedError::Invalid(
                "Set requires a function; Delete requires a constructor, function or relation; Subsume requires a constructor".into(),
            ));
        }
        let mut slots = std::array::from_fn(|_| vec![]);
        let mut call = call.clone();
        for arg in &mut call.args {
            let original = target.0.resolve(Arena::Node, *arg)?;
            *arg = u32::try_from(slots[Arena::Node as usize].len())
                .expect("protobuf arena exceeds u32");
            slots[Arena::Node as usize].push(Slot::External(original));
        }
        match &mut action {
            pb::action::Kind::Set(set) => {
                set.target = Some(call);
                set.value = Some(
                    u32::try_from(slots[Arena::Node as usize].len())
                        .expect("protobuf arena exceeds u32"),
                );
                slots[Arena::Node as usize].push(Slot::External(value.unwrap().0));
            }
            pb::action::Kind::Delete(target) | pb::action::Kind::Subsume(target) => *target = call,
            _ => unreachable!("row action kind"),
        }
        publish(
            pb::Program {
                commands: vec![pb::Command {
                    kind: Some(pb::command::Kind::Action(pb::Action {
                        kind: Some(action),
                        ..Default::default()
                    })),
                    ..Default::default()
                }],
                ..Default::default()
            },
            slots,
            vec![declaration],
            Arena::Command,
            0,
        )
    };
    Action(build().map_err(|error| error.to_string()))
}

/// A query fact backed by a generated Node.
#[derive(Clone, Debug)]
pub struct Fact(pub(super) Expr);

/// Match two expressions for equality in the same query binder.
pub fn eq<L: ValueInput>(left: L, right: impl Into<L::Owned>) -> Fact {
    Fact(equality_node(
        left.borrow().expression(),
        right.into().expression(),
    ))
}

/// Union two equality-sort values as an explicit ordered action.
/// Clones retain the Union occurrence. NORMAL direct actions support repeated
/// occurrences and nested Unions; generalized rule-head, deferred, query and
/// encoded-mode use remains unsupported. Fresh nested captures remain unsupported;
/// established captures may be used in top-level actions.
pub fn union<L: ValueInput>(left: L, right: impl Into<L::Owned>) -> Action
where
    L::Owned: super::EqualitySort,
{
    let node = equality_node(left.borrow().expression(), right.into().expression());
    let mut slots = std::array::from_fn(|_| vec![]);
    slots[Arena::Node as usize] = vec![Slot::External(node.0)];
    Action(
        publish(
            pb::Program {
                commands: vec![pb::Command {
                    kind: Some(pb::command::Kind::Action(pb::Action {
                        kind: Some(pb::action::Kind::Term(0)),
                        ..Default::default()
                    })),
                    ..Default::default()
                }],
                ..Default::default()
            },
            slots,
            vec![],
            Arena::Command,
            0,
        )
        .map_err(|error| error.to_string()),
    )
}

// Facts and explicit union actions share one fresh canonical node constructor,
// preserving ordered member ownership and the actual result-sort reference.
fn equality_node(left: &Expr, right: &Expr) -> Expr {
    let node = &left.0.owner.as_ref().unwrap().program.nodes[left.0.index as usize];
    let mut slots = std::array::from_fn(|_| vec![]);
    slots[Arena::Node as usize] = vec![
        Slot::External(left.0.clone()),
        Slot::External(right.0.clone()),
    ];
    slots[Arena::Sort as usize] = vec![Slot::External(
        left.0.resolve(Arena::Sort, node.sort_id).unwrap(),
    )];
    let program = pb::Program {
        nodes: vec![pb::Node {
            kind: Some(pb::node::Kind::Union(pb::Union {
                members: vec![0, 1],
            })),
            ..Default::default()
        }],
        ..Default::default()
    };
    Expr(publish(program, slots, vec![], Arena::Node, 0).unwrap())
}

/// An immutable authored rule value. Registration deduplicates rule content.
#[derive(Clone)]
pub struct Rule(pub(super) Record, pub(super) Option<String>);
/// An ordered collection of generated group additions, reusable across runs.
#[derive(Clone)]
pub struct Ruleset(pub(super) Vec<Record>, pub(super) Option<String>);

/// Match query facts and evaluate ordered expression actions for every match.
///
/// Facts and heads share one binder, but every head variable must be bound by
/// the query. Submission checks that obligation without executing the rule.
/// Equality facts are not actions; use `union` in a head or `rewrite` for an
/// equality rewrite.
pub fn rule(lhs: impl Facts, rhs: impl Actions) -> Rule {
    let mut query = vec![];
    lhs.append(&mut query);
    let mut slots = std::array::from_fn(|_| vec![]);
    slots[Arena::Node as usize] = query.into_iter().map(|e| Slot::External(e.0)).collect();
    let query = (0..slots[Arena::Node as usize].len())
        .map(|i| u32::try_from(i).expect("protobuf arena exceeds u32"))
        .collect();
    let mut head = vec![];
    let mut declarations = vec![];
    let error = rhs
        .append_actions(&mut head, &mut declarations, &mut |expr| {
            let index = slots[Arena::Node as usize].len();
            slots[Arena::Node as usize].push(Slot::External(expr.0));
            u32::try_from(index).expect("protobuf arena exceeds u32")
        })
        .err()
        .map(|error| error.to_string());
    Rule(
        publish(
            pb::Program {
                rules: vec![pb::Rule {
                    kind: Some(pb::rule::Kind::Rule(pb::RuleBody { query, head })),
                    eval_mode: pb::RuleEvalMode::Seminaive.into(),
                    ..Default::default()
                }],
                ..Default::default()
            },
            slots,
            declarations.into_iter().map(|d| d.0).collect(),
            Arena::Rule,
            0,
        )
        .unwrap(),
        error,
    )
}

impl Rule {
    /// Add an immutable diagnostic presentation, retaining the rule occurrence.
    pub fn label(self, label: impl Into<String>) -> Self {
        let label = label.into();
        let mut program = pb::Program {
            rules: vec![
                self.0.owner.as_ref().unwrap().program.rules[self.0.index as usize].clone(),
            ],
            ..Default::default()
        };
        let mut slots = std::array::from_fn(|_| vec![]);
        visit(&mut program, Arena::Rule, 0, |arena, index| {
            let position =
                u32::try_from(slots[arena as usize].len()).expect("protobuf arena exceeds u32");
            slots[arena as usize].push(Slot::External(self.0.resolve(arena, index)?));
            Ok(position)
        })
        .expect("published rule has valid references");
        program.rules[0].name = Some(label.clone());
        let error = self.1.or_else(|| {
            label
                .is_empty()
                .then(|| "rule label must not be empty".into())
        });
        let mut record = publish(
            program,
            slots,
            self.0.owner.as_ref().unwrap().declarations.clone(),
            Arena::Rule,
            0,
        )
        .unwrap();
        std::sync::Arc::get_mut(record.owner.as_mut().unwrap())
            .expect("unpublished label")
            .rule_origin = Some(self.0);
        Self(record, error)
    }

    /// Append query conditions, publishing a new immutable rule occurrence.
    /// Existing clones and groups keep the original rule. No conditions is a no-op.
    pub fn when(self, conditions: impl Facts) -> Self {
        let mut conditions_roots = vec![];
        conditions.append(&mut conditions_roots);
        if conditions_roots.is_empty() {
            return self;
        }
        let mut program = pb::Program {
            rules: vec![
                self.0.owner.as_ref().unwrap().program.rules[self.0.index as usize].clone(),
            ],
            ..Default::default()
        };
        let mut slots = std::array::from_fn(|_| vec![]);
        visit(&mut program, Arena::Rule, 0, |arena, index| {
            let relocated = slots[arena as usize].len();
            slots[arena as usize].push(Slot::External(self.0.resolve(arena, index)?));
            Ok(u32::try_from(relocated).expect("protobuf arena exceeds u32"))
        })
        .expect("published rule has valid references");
        let conditions = match program.rules[0].kind.as_mut().unwrap() {
            pb::rule::Kind::Rule(body) => &mut body.query,
            pb::rule::Kind::Rewrite(body) => &mut body.conditions,
            _ => unreachable!("unsupported published rule"),
        };
        for expr in conditions_roots {
            conditions.push(
                u32::try_from(slots[Arena::Node as usize].len())
                    .expect("protobuf arena exceeds u32"),
            );
            slots[Arena::Node as usize].push(Slot::External(expr.0));
        }
        let declarations = self.0.owner.as_ref().unwrap().declarations.clone();
        Self(
            publish(program, slots, declarations, Arena::Rule, 0).unwrap(),
            self.1,
        )
    }
}

/// Rewrite a matched expression to a value using the query's bindings.
pub fn rewrite<L: ValueInput>(left: L, right: impl Into<L::Owned>) -> Rule
where
    L::Owned: super::EqualitySort,
{
    let left = left.borrow().expression().clone();
    let right = right.into();
    let mut slots = std::array::from_fn(|_| vec![]);
    slots[Arena::Node as usize] = vec![
        Slot::External(left.0),
        Slot::External(right.expression().0.clone()),
    ];
    let program = pb::Program {
        rules: vec![pb::Rule {
            kind: Some(pb::rule::Kind::Rewrite(pb::Rewrite {
                lhs: 0,
                rhs: 1,
                ..Default::default()
            })),
            eval_mode: pb::RuleEvalMode::Seminaive.into(),
            ..Default::default()
        }],
        ..Default::default()
    };
    Rule(
        publish(program, slots, vec![], Arena::Rule, 0).unwrap(),
        None,
    )
}

#[doc(hidden)]
pub trait IntoRules<A> {
    fn append(self, rules: &mut Vec<Rule>, groups: &mut Vec<Ruleset>);
}
impl IntoRules<()> for Rule {
    fn append(self, rules: &mut Vec<Rule>, _: &mut Vec<Ruleset>) {
        rules.push(self);
    }
}
impl IntoRules<()> for &Rule {
    fn append(self, rules: &mut Vec<Rule>, _: &mut Vec<Ruleset>) {
        rules.push(self.clone());
    }
}
impl IntoRules<()> for Ruleset {
    fn append(self, rules: &mut Vec<Rule>, groups: &mut Vec<Ruleset>) {
        if !rules.is_empty() {
            groups.push(rule_list(std::mem::take(rules), None));
        }
        groups.push(self);
    }
}
impl IntoRules<()> for &Ruleset {
    fn append(self, rules: &mut Vec<Rule>, groups: &mut Vec<Ruleset>) {
        self.clone().append(rules, groups);
    }
}
impl<F: FnOnce() -> Ruleset> IntoRules<()> for &LazyLock<Ruleset, F> {
    fn append(self, rules: &mut Vec<Rule>, groups: &mut Vec<Ruleset>) {
        (&**self).append(rules, groups);
    }
}
impl IntoRules<()> for () {
    fn append(self, _: &mut Vec<Rule>, _: &mut Vec<Ruleset>) {}
}
impl<T: IntoRules<()>> IntoRules<()> for Vec<T> {
    fn append(self, rules: &mut Vec<Rule>, groups: &mut Vec<Ruleset>) {
        for item in self {
            item.append(rules, groups);
        }
    }
}
impl<T: IntoRules<()>, const N: usize> IntoRules<()> for [T; N] {
    fn append(self, rules: &mut Vec<Rule>, groups: &mut Vec<Ruleset>) {
        for item in self {
            item.append(rules, groups);
        }
    }
}
impl<'a, T> IntoRules<()> for &'a [T]
where
    &'a T: IntoRules<()>,
{
    fn append(self, rules: &mut Vec<Rule>, groups: &mut Vec<Ruleset>) {
        for item in self {
            item.append(rules, groups);
        }
    }
}

macro_rules! callbacks {
    ($($t:ident:$i:tt),*) => {
        impl<F, R, $($t: EgglogValue,)*> IntoRules<fn($($t),*)> for F
        where F: FnOnce($(&$t),*) -> R, R: IntoRules<()> {
            fn append(self, rules: &mut Vec<Rule>, groups: &mut Vec<Ruleset>) {
                let scope = fresh_scope();
                let _ = scope;
                self($(&variable::<$t>(scope, $i)),*).append(rules, groups);
            }
        }
    };
}
callbacks!();

/// Build a reusable selection from rules, groups or a fresh-variable callback.
/// Fresh arguments may escape the callback and keep their variable identity.
/// Collections preserve registration order; selected groups share equal rule content.
pub fn ruleset<A>(source: impl IntoRules<A>) -> Ruleset {
    named_ruleset(|| None, source)
}

// Evaluate the name after the authored body, matching the attribute's order.
#[doc(hidden)]
pub fn named_ruleset<A>(
    name: impl FnOnce() -> Option<String>,
    source: impl IntoRules<A>,
) -> Ruleset {
    let mut rules = vec![];
    let mut groups = vec![];
    source.append(&mut rules, &mut groups);
    let name = name();
    if groups.is_empty() {
        return rule_list(rules, name);
    }
    if !rules.is_empty() {
        groups.push(rule_list(rules, None));
    }
    let error = groups.iter().find_map(|g| g.1.clone());
    if let Some(name) = name {
        let mut captured = Vec::new();
        for group in groups {
            for addition in group.0 {
                let owner = addition.owner.as_ref().unwrap();
                let Some(pb::command::Kind::AddRules(add)) =
                    &owner.program.commands[addition.index as usize].kind
                else {
                    unreachable!("typed group addition")
                };
                for index in &add.rules {
                    captured.push(Rule(addition.resolve(Arena::Rule, *index).unwrap(), None));
                }
            }
        }
        let mut result = rule_list(captured, Some(name));
        result.1 = error;
        return result;
    }
    let mut seen = std::collections::HashSet::new();
    Ruleset(
        groups
            .into_iter()
            .flat_map(|g| g.0)
            .filter(|addition| seen.insert(addition.key()))
            .collect(),
        error,
    )
}

// A canonical AddRules command keeps registration order and its rule imports.
fn rule_list(rules: Vec<Rule>, name: Option<String>) -> Ruleset {
    let program = pb::Program {
        commands: vec![pb::Command {
            kind: Some(pb::command::Kind::AddRules(pb::AddRules {
                group: name.unwrap_or_else(|| format!("__typed_group_{}", fresh_scope())),
                rules: (0..rules.len())
                    .map(|i| u32::try_from(i).expect("protobuf arena exceeds u32"))
                    .collect(),
            })),
            ..Default::default()
        }],
        ..Default::default()
    };
    let mut slots = std::array::from_fn(|_| vec![]);
    let error = rules.iter().find_map(|r| r.1.clone());
    slots[Arena::Rule as usize] = rules.into_iter().map(|r| Slot::External(r.0)).collect();
    Ruleset(
        vec![publish(program, slots, vec![], Arena::Command, 0).unwrap()],
        error,
    )
}

#[doc(hidden)]
pub trait Facts {
    fn append(self, out: &mut Vec<Expr>);
}
impl<T: ValueInput> Facts for T {
    fn append(self, out: &mut Vec<Expr>) {
        out.push(self.borrow().expression().clone());
    }
}
impl Facts for Fact {
    fn append(self, out: &mut Vec<Expr>) {
        out.push(self.0);
    }
}
impl Facts for &Fact {
    fn append(self, out: &mut Vec<Expr>) {
        out.push(self.0.clone());
    }
}
impl Facts for () {
    fn append(self, _: &mut Vec<Expr>) {}
}
impl<T: Facts> Facts for Vec<T> {
    fn append(self, out: &mut Vec<Expr>) {
        for f in self {
            f.append(out);
        }
    }
}
impl<T: Facts, const N: usize> Facts for [T; N] {
    fn append(self, out: &mut Vec<Expr>) {
        for f in self {
            f.append(out);
        }
    }
}
impl<'a, T> Facts for &'a [T]
where
    &'a T: Facts,
{
    fn append(self, out: &mut Vec<Expr>) {
        for fact in self {
            fact.append(out);
        }
    }
}

/// Shared, sealed input conversion for registration and rule heads.
#[doc(hidden)]
pub trait Actions: action_input::Actions {}
impl<T: action_input::Actions> Actions for T {}

mod action_input {
    use super::super::EgglogValue;
    use super::{Action, Arena, Callable, Expr, TypedError, ValueInput, pb, visit_action};

    pub trait Actions {
        fn append_actions(
            self,
            out: &mut Vec<pb::Action>,
            declarations: &mut Vec<Callable>,
            node: &mut impl FnMut(Expr) -> u32,
        ) -> Result<(), TypedError>;
    }
    impl<T: ValueInput> Actions for T {
        fn append_actions(
            self,
            out: &mut Vec<pb::Action>,
            _: &mut Vec<Callable>,
            node: &mut impl FnMut(Expr) -> u32,
        ) -> Result<(), TypedError> {
            out.push(pb::Action {
                kind: Some(pb::action::Kind::Term(node(
                    self.borrow().expression().clone(),
                ))),
                ..Default::default()
            });
            Ok(())
        }
    }
    impl Actions for Action {
        fn append_actions(
            self,
            out: &mut Vec<pb::Action>,
            declarations: &mut Vec<Callable>,
            node: &mut impl FnMut(Expr) -> u32,
        ) -> Result<(), TypedError> {
            let record = self.0.map_err(TypedError::Invalid)?;
            let owner = record.owner.as_ref().unwrap();
            let Some(pb::command::Kind::Action(mut action)) =
                owner.program.commands[record.index as usize].kind.clone()
            else {
                unreachable!("owned action record")
            };
            visit_action(&mut action, |index| {
                Ok(node(Expr(record.resolve(Arena::Node, index)?)))
            })?;
            declarations.extend(owner.declarations.iter().cloned().map(Callable));
            out.push(action);
            Ok(())
        }
    }
    impl Actions for &Action {
        fn append_actions(
            self,
            out: &mut Vec<pb::Action>,
            declarations: &mut Vec<Callable>,
            node: &mut impl FnMut(Expr) -> u32,
        ) -> Result<(), TypedError> {
            self.clone().append_actions(out, declarations, node)
        }
    }
    impl Actions for () {
        fn append_actions(
            self,
            _: &mut Vec<pb::Action>,
            _: &mut Vec<Callable>,
            _: &mut impl FnMut(Expr) -> u32,
        ) -> Result<(), TypedError> {
            Ok(())
        }
    }
    impl<T: Actions> Actions for Vec<T> {
        fn append_actions(
            self,
            out: &mut Vec<pb::Action>,
            declarations: &mut Vec<Callable>,
            node: &mut impl FnMut(Expr) -> u32,
        ) -> Result<(), TypedError> {
            for value in self {
                value.append_actions(out, declarations, node)?;
            }
            Ok(())
        }
    }
    impl<T: Actions, const N: usize> Actions for [T; N] {
        fn append_actions(
            self,
            out: &mut Vec<pb::Action>,
            declarations: &mut Vec<Callable>,
            node: &mut impl FnMut(Expr) -> u32,
        ) -> Result<(), TypedError> {
            for value in self {
                value.append_actions(out, declarations, node)?;
            }
            Ok(())
        }
    }
    impl<'a, T> Actions for &'a [T]
    where
        &'a T: Actions,
    {
        fn append_actions(
            self,
            out: &mut Vec<pb::Action>,
            declarations: &mut Vec<Callable>,
            node: &mut impl FnMut(Expr) -> u32,
        ) -> Result<(), TypedError> {
            for value in self {
                value.append_actions(out, declarations, node)?;
            }
            Ok(())
        }
    }
}

macro_rules! tuples {
    ($($t:ident:$i:tt),*) => {
        impl<$($t: Facts),*> Facts for ($($t,)*) {
            fn append(self, out: &mut Vec<Expr>) { $(self.$i.append(out);)* }
        }
        impl<$($t: action_input::Actions),*> action_input::Actions for ($($t,)*) {
            fn append_actions(self, out: &mut Vec<pb::Action>, declarations: &mut Vec<Callable>, node: &mut impl FnMut(Expr) -> u32) -> Result<(), TypedError> {
                $(self.$i.append_actions(out, declarations, node)?;)*
                Ok(())
            }
        }
        impl<$($t: IntoRules<()>),*> IntoRules<()> for ($($t,)*) {
            fn append(self, rules: &mut Vec<Rule>, groups: &mut Vec<Ruleset>) {
                $(self.$i.append(rules, groups);)*
            }
        }
    };
}

macro_rules! arities {
    (@[$($done:ident:$j:tt,)*];) => {};
    (@[$($done:ident:$j:tt,)*]; $next:ident:$i:tt $(,$tail:ident:$k:tt)*) => {
        callbacks!($($done:$j,)* $next:$i);
        tuples!($($done:$j,)* $next:$i);
        arities!(@[$($done:$j,)* $next:$i,]; $($tail:$k),*);
    };
}
// Includes Luminal's observed binders up to 60 arguments, with a uniform
// 64-argument boundary for callbacks and ordered heterogeneous collections.
arities!(@[]; A0:0,A1:1,A2:2,A3:3,A4:4,A5:5,A6:6,A7:7,A8:8,A9:9,
    A10:10,A11:11,A12:12,A13:13,A14:14,A15:15,A16:16,A17:17,A18:18,A19:19,
    A20:20,A21:21,A22:22,A23:23,A24:24,A25:25,A26:26,A27:27,A28:28,A29:29,
    A30:30,A31:31,A32:32,A33:33,A34:34,A35:35,A36:36,A37:37,A38:38,A39:39,
    A40:40,A41:41,A42:42,A43:43,A44:44,A45:45,A46:46,A47:47,A48:48,A49:49,
    A50:50,A51:51,A52:52,A53:53,A54:54,A55:55,A56:56,A57:57,A58:58,A59:59,
    A60:60,A61:61,A62:62,A63:63);

pub(super) fn ensure_sort<S: EgglogValue>(expr: Expr) -> Result<S, TypedError> {
    let node = &expr.0.owner.as_ref().unwrap().program.nodes[expr.0.index as usize];
    if SortRef(expr.0.resolve(Arena::Sort, node.sort_id)?) != S::sort_ref() {
        return Err(TypedError::Decode(
            "decoded expression has another sort".into(),
        ));
    }
    Ok(S::from_expression(expr))
}
