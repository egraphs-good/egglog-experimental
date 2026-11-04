//! Typed composition of ordered actions, Run and capped Loop forms.
use super::rule::action_input::Actions;
use super::{
    Action, Rule, Ruleset, TypedError,
    expr::Expr,
    pb,
    storage::{Record, visit_command},
};

/// An ordered schedule retaining the rule values used by each Run.
#[derive(Clone)]
pub struct Schedule {
    pub(super) commands: Vec<pb::Command>,
    pub(super) rulesets: Vec<Ruleset>,
    pub(super) operands: Vec<Record>,
    pub(super) declarations: Vec<Record>,
    pub(super) error: Option<String>,
}

impl From<&Ruleset> for Schedule {
    fn from(ruleset: &Ruleset) -> Self {
        Self {
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Run(pb::Run::default())),
                ..Default::default()
            }],
            rulesets: vec![ruleset.clone()],
            operands: vec![],
            declarations: vec![],
            error: None,
        }
    }
}
impl From<Action> for Schedule {
    fn from(action: Action) -> Self {
        let mut commands = vec![];
        let mut operands = vec![];
        let mut declarations = vec![];
        let error = action
            .append_commands(&mut commands, &mut declarations, &mut |Expr(record)| {
                let index = u32::try_from(operands.len()).expect("protobuf arena exceeds u32");
                operands.push(record);
                index
            })
            .err()
            .map(|error| error.to_string());
        Self {
            commands,
            rulesets: vec![],
            operands,
            declarations: declarations.into_iter().map(|d| d.0).collect(),
            error,
        }
    }
}
impl From<&Action> for Schedule {
    fn from(action: &Action) -> Self {
        Self::from(action.clone())
    }
}

impl From<Ruleset> for Schedule {
    fn from(ruleset: Ruleset) -> Self {
        Self::from(&ruleset)
    }
}
impl From<Rule> for Schedule {
    fn from(rule: Rule) -> Self {
        Self::from(super::ruleset(rule))
    }
}
impl From<&Rule> for Schedule {
    fn from(rule: &Rule) -> Self {
        Self::from(super::ruleset(rule))
    }
}
impl From<&std::sync::LazyLock<Ruleset>> for Schedule {
    fn from(ruleset: &std::sync::LazyLock<Ruleset>) -> Self {
        Self::from(&**ruleset)
    }
}
impl From<&Schedule> for Schedule {
    fn from(schedule: &Schedule) -> Self {
        schedule.clone()
    }
}

impl Schedule {
    /// Observe one owned snapshot after this entire schedule. Place this
    /// composition inside repeat/saturate to choose an observation per iteration.
    pub fn with_snapshots(mut self) -> Self {
        self.commands.push(pb::Command {
            kind: Some(pb::command::Kind::Freeze(pb::Freeze {})),
            ..Default::default()
        });
        self
    }

    /// Execute at most this many iterations, stopping when the body can stop.
    /// Zero still prepares the schedule's rules and publishes named bindings.
    pub fn repeat(self, max_iterations: u64) -> Self {
        Self {
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Loop(pb::Loop {
                    body: self.commands,
                    max_iterations: Some(max_iterations),
                    ..Default::default()
                })),
                ..Default::default()
            }],
            rulesets: self.rulesets,
            operands: self.operands,
            declarations: self.declarations,
            error: self.error,
        }
    }
    /// Repeat until a complete body iteration makes no changes and may stop.
    pub fn saturate(self) -> Self {
        Self {
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Loop(pb::Loop {
                    body: self.commands,
                    ..Default::default()
                })),
                ..Default::default()
            }],
            rulesets: self.rulesets,
            operands: self.operands,
            declarations: self.declarations,
            error: self.error,
        }
    }
}

impl Ruleset {
    /// Repeat this selection without resetting existing rule state.
    pub fn repeat(&self, max_iterations: u64) -> Schedule {
        Schedule::from(self).repeat(max_iterations)
    }
    /// Saturate this rule selection.
    pub fn saturate(&self) -> Schedule {
        Schedule::from(self).saturate()
    }
    /// Whether this collection contains no rules.
    pub fn is_empty(&self) -> bool {
        self.rules.is_empty()
    }
}

/// Collections accepted by ordered schedule composition.
pub trait Schedules {
    #[doc(hidden)]
    fn append(self, target: &mut Vec<Schedule>);
}
macro_rules! single {
    ($($ty:ty),*) => { $(impl Schedules for $ty {
        fn append(self, target: &mut Vec<Schedule>) { target.push(self.into()); }
    })* };
}
single!(
    Action,
    &Action,
    Rule,
    &Rule,
    Ruleset,
    &Ruleset,
    &std::sync::LazyLock<Ruleset>,
    Schedule,
    &Schedule
);
impl<T: Schedules> Schedules for Vec<T> {
    fn append(self, target: &mut Vec<Schedule>) {
        for schedule in self {
            schedule.append(target);
        }
    }
}
impl<T: Schedules, const N: usize> Schedules for [T; N] {
    fn append(self, target: &mut Vec<Schedule>) {
        for schedule in self {
            schedule.append(target);
        }
    }
}
macro_rules! tuples {
    ($($ty:ident:$index:tt),*) => {
        impl<$($ty: Schedules),*> Schedules for ($($ty,)*) {
            fn append(self, target: &mut Vec<Schedule>) { $(self.$index.append(target);)* }
        }
    };
}
tuples!(A:0);
tuples!(A:0,B:1);
tuples!(A:0,B:1,C:2);
tuples!(A:0,B:1,C:2,D:3);
tuples!(A:0,B:1,C:2,D:3,E:4);
tuples!(A:0,B:1,C:2,D:3,E:4,F:5);
tuples!(A:0,B:1,C:2,D:3,E:4,F:5,G:6);
tuples!(A:0,B:1,C:2,D:3,E:4,F:5,G:6,H:7);
tuples!(A:0,B:1,C:2,D:3,E:4,F:5,G:6,H:7,I:8);
tuples!(A:0,B:1,C:2,D:3,E:4,F:5,G:6,H:7,I:8,J:9);

/// Compose phases in their supplied order, retaining repeated occurrences.
pub fn sequence(source: impl Schedules) -> Schedule {
    let mut schedules = Vec::new();
    source.append(&mut schedules);
    let mut commands = Vec::new();
    let mut rulesets = Vec::new();
    let mut operands = Vec::new();
    let mut declarations = Vec::new();
    let mut error = None;
    for mut schedule in schedules {
        let base = u32::try_from(operands.len()).expect("protobuf arena exceeds u32");
        if let Err(problem) = visit_operands(&mut schedule.commands, |index| Ok(base + index)) {
            error = Some(problem.to_string());
        }
        error = error.or(schedule.error);
        commands.extend(schedule.commands);
        rulesets.extend(schedule.rulesets);
        operands.extend(schedule.operands);
        declarations.extend(schedule.declarations);
    }
    Schedule {
        commands,
        rulesets,
        operands,
        declarations,
        error,
    }
}

// Traverse control structure while preserving node references in dead bodies.
// Importing these operands declares slots but never executes their recipes.
pub(super) fn visit_operands(
    commands: &mut [pb::Command],
    mut node: impl FnMut(u32) -> Result<u32, TypedError>,
) -> Result<(), TypedError> {
    let mut pending = commands.iter_mut().rev().collect::<Vec<_>>();
    while let Some(command) = pending.pop() {
        if matches!(
            command.kind,
            Some(pb::command::Kind::Action(_) | pb::command::Kind::Let(_))
        ) {
            visit_command(command, &mut node)?;
        } else {
            match &mut command.kind {
                Some(pb::command::Kind::Loop(body)) => pending.extend(body.body.iter_mut().rev()),
                Some(pb::command::Kind::Run(_) | pb::command::Kind::Freeze(_)) => (),
                _ => {
                    return Err(TypedError::Invalid(
                        "unsupported typed schedule command".into(),
                    ));
                }
            }
        }
    }
    Ok(())
}
