// Core web-demo/list.egg: demand-driven tables over an equality-sort list.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct List;

#[declarations]
impl List {
    pub fn nil() -> List;
    pub fn cons(head: egg::I64, tail: List) -> List;
}
#[function(no_merge)]
pub fn length(list: List) -> egg::I64;
#[relation]
pub fn length_demand(list: List);
#[function(no_merge)]
pub fn get(list: List, index: egg::I64) -> egg::I64;
#[relation]
pub fn get_demand(list: List, index: egg::I64);
#[constructor]
pub fn append(left: List, right: List) -> List;
#[constructor]
pub fn replace(list: List, index: egg::I64, value: egg::I64) -> List;

#[ruleset]
fn rules(
    head: &egg::I64,
    tail: &List,
    tail_length: &egg::I64,
    n: &egg::I64,
    item: &egg::I64,
    list: &List,
    i: &egg::I64,
) -> Vec<Rule> {
    let cons = List::cons(head, tail);
    vec![
        rule(length_demand(List::nil()), set(length(List::nil()), 0)),
        rule(length_demand(&cons), length_demand(tail)),
        rule(
            (length_demand(&cons), eq(length(tail), tail_length)),
            set(length(&cons), tail_length + 1),
        ),
        rule(get_demand(&cons, 0), set(get(&cons, 0), head)),
        rule((get_demand(&cons, n), n.gt(0)), get_demand(tail, n - 1)),
        rule(
            (get_demand(&cons, n), eq(get(tail, n - 1), item)),
            set(get(&cons, n), item),
        ),
        rewrite(append(List::nil(), list), list),
        rewrite(append(&cons, list), List::cons(head, append(tail, list))),
        rewrite(replace(&cons, 0, item), List::cons(item, tail)),
        rewrite(
            replace(cons, i, item),
            List::cons(head, replace(tail, i - 1, item)),
        )
        .when(i.gt(0)),
    ]
}

pub fn main() -> Result<(), TypedError> {
    let nil = List::nil();
    let a = List::cons(1, List::cons(2, &nil));
    let b = List::cons(3, &nil);
    let c = List::cons(1, List::cons(2, &b));
    let d = List::cons(1, List::cons(4, nil));
    let e = let_("append", append(&a, &b));
    let f = let_("replace", replace(&a, 1, 4));
    let mut egraph = EGraph::default();
    egraph.register((
        &a,
        &b,
        &c,
        &d,
        &e,
        &f,
        length_demand(&c),
        get_demand(&b, 0),
        get_demand(&a, 1),
    ))?;
    egraph.run(rules.saturate())?;
    assert!(egraph.check((
        eq(e, &c),
        eq(length(c), 3),
        eq(get(b, 0), 3),
        eq(get(a, 1), 2),
        eq(f, d)
    ))?);
    Ok(())
}
