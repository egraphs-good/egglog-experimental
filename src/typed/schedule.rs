//! Typed composition of the protocol's existing Run, Repeat and Saturate forms.
use super::{Ruleset, pb, storage::Arena};
use std::collections::HashSet;

/// An ordered schedule with location-only imports of authored rulesets.
#[derive(Clone)]
pub struct Schedule {
    pub(super) commands: Vec<pb::Command>,
    pub(super) rulesets: Vec<Ruleset>,
}

impl From<&Ruleset> for Schedule {
    fn from(ruleset: &Ruleset) -> Self {
        Self {
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Run(pb::Run {
                    ruleset: Some(pb::RulesetRef {
                        kind: Some(pb::ruleset_ref::Kind::Index(0)),
                    }),
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
    /// Execute the body exactly this many times; zero still publishes its theory.
    pub fn repeat(self, times: u64) -> Self {
        Self {
            commands: vec![pb::Command {
                kind: Some(pb::command::Kind::Repeat(pb::Repeat {
                    body: self.commands,
                    times: Some(times),
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
                kind: Some(pb::command::Kind::Saturate(pb::Saturate {
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
    /// Repeat this ruleset without changing its rule occurrence identities.
    pub fn repeat(&self, times: u64) -> Schedule {
        Schedule::from(self).repeat(times)
    }
    /// Saturate this exact ruleset occurrence closure.
    pub fn saturate(&self) -> Schedule {
        Schedule::from(self).saturate()
    }
    /// Whether the retained group closure contains no rule occurrences.
    pub fn is_empty(&self) -> bool {
        let mut pending = vec![self.0.clone()];
        let mut seen = HashSet::new();
        while let Some(record) = pending.pop() {
            let owner = record.owner.as_ref().unwrap();
            if !seen.insert((owner.id, record.index)) {
                continue;
            }
            match &owner.program.rulesets[record.index as usize].kind {
                Some(pb::ruleset::Kind::Rules(rules)) if !rules.rules.is_empty() => return false,
                Some(pb::ruleset::Kind::Combined(group)) => {
                    for child in &group.rulesets {
                        let Some(pb::ruleset_ref::Kind::Index(index)) = child.kind else {
                            return false;
                        };
                        let Ok(child) = record.resolve(Arena::Ruleset, index) else {
                            return false;
                        };
                        pending.push(child);
                    }
                }
                _ => (),
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
    for mut schedule in schedules {
        let offset = u32::try_from(rulesets.len()).expect("ruleset arena exceeds u32");
        relocate(&mut schedule.commands, |index| {
            pb::ruleset_ref::Kind::Index(
                index
                    .checked_add(offset)
                    .expect("ruleset arena exceeds u32"),
            )
        });
        commands.extend(schedule.commands);
        rulesets.extend(schedule.rulesets);
    }
    Schedule { commands, rulesets }
}

// Only Runs carry imports; loops retain the exact generated command structure.
pub(super) fn relocate(
    commands: &mut [pb::Command],
    mut index: impl FnMut(u32) -> pb::ruleset_ref::Kind,
) {
    let mut pending: Vec<_> = commands.iter_mut().collect();
    while let Some(command) = pending.pop() {
        match command.kind.as_mut().expect("typed schedule command") {
            pb::command::Kind::Run(run) => {
                let Some(pb::ruleset_ref::Kind::Index(old)) = run.ruleset.as_ref().unwrap().kind
                else {
                    unreachable!()
                };
                run.ruleset.as_mut().unwrap().kind = Some(index(old));
            }
            pb::command::Kind::Repeat(repeat) => pending.extend(repeat.body.iter_mut()),
            pb::command::Kind::Saturate(saturate) => pending.extend(saturate.body.iter_mut()),
            _ => unreachable!("typed schedule form"),
        }
    }
}
