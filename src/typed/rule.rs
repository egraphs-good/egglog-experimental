use super::{
    EgglogValue, SortRef, TypedError,
    expr::{Expr, ValueInput, fresh_scope, variable},
    pb,
    storage::{Arena, Record, Slot, publish},
};

/// A query fact backed by a generated Node.
#[derive(Clone, Debug)]
pub struct Fact(pub(super) Expr);

/// Match two expressions for equality in the same query binder.
pub fn eq<L: ValueInput>(left: L, right: impl Into<L::Owned>) -> Fact {
    let left = left.borrow().expression();
    let right = right.into();
    let node = &left.0.owner.as_ref().unwrap().program.nodes[left.0.index as usize];
    let mut slots = std::array::from_fn(|_| vec![]);
    slots[Arena::Node as usize] = vec![
        Slot::External(left.0.clone()),
        Slot::External(right.expression().0.clone()),
    ];
    slots[Arena::Sort as usize] = vec![Slot::External(
        left.0.resolve(Arena::Sort, node.sort_id).unwrap(),
    )];
    let program = pb::Program {
        ir_version: 1,
        nodes: vec![pb::Node {
            kind: Some(pb::node::Kind::Union(pb::Union {
                members: vec![0, 1],
            })),
            ..Default::default()
        }],
        ..Default::default()
    };
    Fact(Expr(
        publish(program, slots, vec![], Arena::Node, 0).unwrap(),
    ))
}

/// Each wrapper owns one generated RuleDecl occurrence. Clones retain it.
#[derive(Clone)]
pub struct Rule(pub(super) Record);
/// An immutable generated flat ruleset; cloning preserves its occurrence.
#[derive(Clone)]
pub struct Ruleset(pub(super) Record);

/// Rewrite a matched expression to a value using the query's bindings.
pub fn rewrite<L: ValueInput>(left: L, right: impl Into<L::Owned>) -> Rule {
    let left = left.borrow().expression().clone();
    let right = right.into();
    let mut slots = std::array::from_fn(|_| vec![]);
    slots[Arena::Node as usize] = vec![
        Slot::External(left.0),
        Slot::External(right.expression().0.clone()),
    ];
    let program = pb::Program {
        ir_version: 1,
        rules: vec![pb::RuleDecl {
            kind: Some(pb::rule_decl::Kind::Rewrite(pb::Rewrite {
                lhs: 0,
                rhs: 1,
                ..Default::default()
            })),
            eval_mode: pb::RuleEvalMode::Seminaive.into(),
            ..Default::default()
        }],
        ..Default::default()
    };
    Rule(publish(program, slots, vec![], Arena::Rule, 0).unwrap())
}

#[doc(hidden)]
pub trait IntoRules<A> {
    fn build(self) -> Vec<Rule>;
}
impl IntoRules<()> for Rule {
    fn build(self) -> Vec<Rule> {
        vec![self]
    }
}
impl IntoRules<()> for () {
    fn build(self) -> Vec<Rule> {
        vec![]
    }
}
impl IntoRules<()> for Vec<Rule> {
    fn build(self) -> Vec<Rule> {
        self
    }
}

macro_rules! callbacks {
    ($($t:ident:$i:tt),*) => {
        impl<F, R, $($t: EgglogValue,)*> IntoRules<fn($($t),*)> for F
        where F: FnOnce($(&$t),*) -> R, R: IntoRules<()> {
            fn build(self) -> Vec<Rule> {
                let scope = fresh_scope();
                let _ = scope;
                self($(&variable::<$t>(scope, $i)),*).build()
            }
        }
    };
}
callbacks!();
callbacks!(A:0);
callbacks!(A:0,B:1);
callbacks!(A:0,B:1,C:2);
callbacks!(A:0,B:1,C:2,D:3);

/// Build a flat group from rules or a callback with up to four fresh arguments.
/// Fresh arguments may escape the callback and keep their variable identity.
pub fn ruleset<A>(source: impl IntoRules<A>) -> Ruleset {
    let rules = source.build();
    let program = pb::Program {
        ir_version: 1,
        rulesets: vec![pb::Ruleset {
            kind: Some(pb::ruleset::Kind::Rules(pb::RuleList {
                rules: (0..rules.len() as u32).collect(),
            })),
            ..Default::default()
        }],
        ..Default::default()
    };
    let mut slots = std::array::from_fn(|_| vec![]);
    slots[Arena::Rule as usize] = rules.into_iter().map(|r| Slot::External(r.0)).collect();
    Ruleset(publish(program, slots, vec![], Arena::Ruleset, 0).unwrap())
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
macro_rules! tuples {
    ($($t:ident:$i:tt),*) => { impl<$($t: Facts),*> Facts for ($($t,)*) { fn append(self, out: &mut Vec<Expr>) { $(self.$i.append(out);)* } } };
}
tuples!(A:0,B:1);
tuples!(A:0,B:1,C:2);
tuples!(A:0,B:1,C:2,D:3);

pub(super) fn ensure_sort<S: EgglogValue>(expr: Expr) -> Result<S, TypedError> {
    let node = &expr.0.owner.as_ref().unwrap().program.nodes[expr.0.index as usize];
    if SortRef(expr.0.resolve(Arena::Sort, node.sort_id)?) != S::sort_ref() {
        return Err(TypedError::Decode(
            "decoded expression has another sort".into(),
        ));
    }
    Ok(S::from_expression(expr))
}
