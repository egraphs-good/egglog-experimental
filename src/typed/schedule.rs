//! Typed composition of the protocol's Run and capped Loop forms.
use super::{Ruleset, pb};
use std::collections::HashSet;

/// An ordered schedule retaining the generated additions needed by its groups.
#[derive(Clone)]
pub struct Schedule {
    pub(super) commands: Vec<pb::Command>,
    pub(super) rulesets: Vec<Ruleset>,
}

impl From<&Ruleset> for Schedule {
    fn from(ruleset: &Ruleset) -> Self {
        let mut seen = HashSet::new();
        let groups = ruleset
            .0
            .iter()
            .filter_map(|record| {
                let owner = record.owner.as_ref().unwrap();
                let Some(pb::command::Kind::AddRules(add)) =
                    &owner.program().unwrap().commands[record.index as usize].kind
                else {
                    unreachable!("typed group addition")
                };
                seen.insert(add.group.clone()).then(|| add.group.clone())
            })
            .collect();
        Self {
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Run(pb::Run {
                    groups,
                    ..Default::default()
                })),
                ..Default::default()
            }],
            rulesets: vec![ruleset.clone()],
        }
    }
}
impl From<Ruleset> for Schedule {
    fn from(ruleset: Ruleset) -> Self {
        Self::from(&ruleset)
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
    /// Zero still registers the schedule's rules.
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
        }
    }
}

impl Ruleset {
    /// Repeat this group selection without resetting registered rule state.
    pub fn repeat(&self, max_iterations: u64) -> Schedule {
        Schedule::from(self).repeat(max_iterations)
    }
    /// Saturate this selection of groups.
    pub fn saturate(&self) -> Schedule {
        Schedule::from(self).saturate()
    }
    /// Whether the retained additions contain no rules.
    pub fn is_empty(&self) -> bool {
        for record in &self.0 {
            let owner = record.owner.as_ref().unwrap();
            if let Some(pb::command::Kind::AddRules(add)) =
                &owner.program().unwrap().commands[record.index as usize].kind
                && !add.rules.is_empty()
            {
                return false;
            }
        }
        self.1.is_none()
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
    for schedule in schedules {
        commands.extend(schedule.commands);
        rulesets.extend(schedule.rulesets);
    }
    Schedule { commands, rulesets }
}
