use super::*;
use crate::effsafe_extract::checks::is_valid_statewalk;
use crate::effsafe_extract::term_graph::{ENode, NodeKind};

fn node(cost: Cost, children: Vec<EClassId>) -> ENode {
    ENode {
        kind: NodeKind::Placeholder,
        cost,
        arity: children.len(),
        children,
        regions: Vec::new(),
        region_positions: Vec::new(),
        boundary: None,
    }
}

fn add_class(g: &mut TermGraph, effectful: bool, enodes: Vec<ENode>) -> EClassId {
    let id = g.len();
    g.classes.push(EClass {
        enodes,
        is_effectful: effectful,
        sort: 0,
    });
    id
}

struct Satellites {
    g: TermGraph,
    states: Vec<EClassId>,
    reads: Vec<EClassId>,
    root: EClassId,
}

impl Satellites {
    fn new(count: usize) -> Self {
        let mut g = TermGraph::default();
        add_class(&mut g, true, vec![node(1, vec![])]);
        let mut states = Vec::new();
        let mut reads = Vec::new();
        for _ in 0..count {
            let state = add_class(&mut g, true, vec![node(1, vec![0])]);
            states.push(state);
            reads.push(add_class(&mut g, false, vec![node(1, vec![state])]));
            g.classes[0].enodes.push(node(1, vec![state]));
        }
        let children = std::iter::once(0).chain(reads.iter().copied()).collect();
        let root = add_class(&mut g, true, vec![node(1, children)]);
        Self {
            g,
            states,
            reads,
            root,
        }
    }
}

fn walk_cost(g: &TermGraph, root: EClassId, opts: StatewalkOptions) -> Option<Cost> {
    let costs: Vec<Vec<Cost>> = g
        .classes
        .iter()
        .map(|c| c.enodes.iter().map(|n| n.cost).collect())
        .collect();
    statewalk_dp(g, root, &costs, opts).ok().map(|walk| {
        assert!(is_valid_statewalk(g, root, &walk));
        walk.iter()
            .fold(0, |cost: Cost, &(c, n)| cost.saturating_add(costs[c][n]))
    })
}

// Exhaustive Dijkstra search over (current state, all extractable e-classes),
// without hashes, liveness, or satellite pruning.
fn exhaustive_cost(g: &TermGraph, root: EClassId) -> Option<Cost> {
    assert!(g.len() < 64);
    let saturate = |mut available: u64| {
        loop {
            let before = available;
            for c in g.class_ids().filter(|&c| !g.is_effectful(c)) {
                if g.classes[c].enodes.iter().any(|n| {
                    n.children
                        .iter()
                        .all(|&child| available & (1 << child) != 0)
                }) {
                    available |= 1 << c;
                }
            }
            if before == available {
                return available;
            }
        }
    };
    let initial = (0, saturate(1));
    let cost = g.enode(0, 0).cost;
    let mut best = FxHashMap::from_iter([(initial, cost)]);
    let mut heap = BinaryHeap::from([(Reverse(cost), initial)]);
    while let Some((Reverse(cost), (u, available))) = heap.pop() {
        if best[&(u, available)] != cost {
            continue;
        }
        if u == root {
            return Some(cost);
        }
        for (v, n) in g.enode_ids().filter(|&(v, _)| g.is_effectful(v)) {
            let enode = g.enode(v, n);
            if g.state_child(enode) != Some(u)
                || !enode.children.iter().all(|&c| available & (1 << c) != 0)
            {
                continue;
            }
            let next = (v, saturate(available | (1 << v)));
            let next_cost = cost.saturating_add(enode.cost);
            if best.get(&next).is_none_or(|&old| next_cost < old) {
                best.insert(next, next_cost);
                heap.push((Reverse(next_cost), next));
            }
        }
    }
    None
}

fn check_options(g: &TermGraph, root: EClassId, expected: Option<Cost>) {
    for liveness in [false, true] {
        for satellite in [false, true] {
            let opts = StatewalkOptions {
                liveness,
                satellite,
            };
            assert_eq!(walk_cost(g, root, opts), expected, "{opts:?}");
        }
    }
}

#[test]
fn entry_alternatives_compete_on_cost() {
    let mut fixture = Satellites::new(0);
    fixture.g.classes[0].enodes = vec![node(10, vec![]), node(2, vec![])];
    check_options(&fixture.g, fixture.root, Some(3));
}

#[test]
fn an_entry_cannot_read_its_own_state() {
    let mut fixture = Satellites::new(0);
    let read = add_class(&mut fixture.g, false, vec![node(0, vec![0])]);
    fixture.g.classes[0].enodes = vec![node(0, vec![read]), node(2, vec![])];
    check_options(&fixture.g, fixture.root, Some(3));
}

#[test]
fn satellite_root_has_the_shortest_walk() {
    let fixture = Satellites::new(7);
    check_options(&fixture.g, fixture.states[6], Some(2));
}

#[test]
fn satellite_enodes_compete_on_cost() {
    let mut fixture = Satellites::new(7);
    fixture.g.classes[fixture.states[0]].enodes = vec![node(10, vec![0]), node(1, vec![0])];
    check_options(&fixture.g, fixture.root, Some(16));
}

#[test]
fn unnecessary_satellites_are_not_forced_into_the_walk() {
    let mut fixture = Satellites::new(7);
    let needed = fixture.reads[6];
    fixture.g.classes[fixture.root].enodes = vec![node(1, vec![0, needed])];
    for (i, &read) in fixture.reads[..6].iter().enumerate() {
        // Keep the other reads live without requiring them on the cheap walk.
        fixture.g.classes[fixture.root]
            .enodes
            .push(node(100 + i as Cost, vec![0, read]));
    }
    check_options(&fixture.g, fixture.root, Some(4));
}

#[test]
fn a_required_satellite_can_be_cheaper_after_another_visit() {
    let mut fixture = Satellites::new(7);
    fixture.g.classes[fixture.states[0]].enodes =
        vec![node(10, vec![0]), node(1, vec![0, fixture.reads[6]])];
    check_options(&fixture.g, fixture.root, Some(16));
}

#[test]
fn a_required_satellite_can_return_more_cheaply_after_another_visit() {
    let mut fixture = Satellites::new(7);
    fixture.g.classes[0].enodes[1].cost = 10;
    fixture.g.classes[0]
        .enodes
        .push(node(1, vec![fixture.states[0], fixture.reads[6]]));
    check_options(&fixture.g, fixture.root, Some(16));
}

#[test]
fn required_satellites_can_have_mutually_blocked_cheapest_entries() {
    let mut fixture = Satellites::new(7);
    for i in 0..2 {
        fixture.g.classes[fixture.states[i]].enodes =
            vec![node(10, vec![0]), node(1, vec![0, fixture.reads[1 - i]])];
    }
    check_options(&fixture.g, fixture.root, Some(25));
}

#[test]
fn alternative_pure_terms_do_not_make_each_satellite_required() {
    let mut fixture = Satellites::new(7);
    let read = add_class(
        &mut fixture.g,
        false,
        fixture.reads.iter().map(|&c| node(0, vec![c])).collect(),
    );
    fixture.g.classes[fixture.states[0]].enodes[0].cost = 10;
    fixture.g.classes[fixture.root].enodes = vec![node(1, vec![0, read])];
    check_options(&fixture.g, fixture.root, Some(4));
}

#[test]
fn satellites_match_exhaustive_search() {
    for seed in 0..1024 {
        let mut rng = Mt64::new(seed);
        let mut next = |bound| (rng.next_u64() % bound) as usize;
        let mut fixture = Satellites::new(6 + next(3));
        let count = fixture.states.len();
        for (i, &state) in fixture.states.iter().enumerate() {
            let mut children = vec![0];
            if next(3) == 0 {
                children.push(fixture.reads[next(count as u64)]);
            }
            let enodes = &mut fixture.g.classes[state].enodes;
            *enodes = vec![node(next(5) as Cost, children)];
            if next(2) == 0 {
                enodes.push(node(next(5) as Cost, vec![0]));
            }
            let mut children = vec![state];
            if next(2) == 0 {
                children.push(fixture.reads[next(count as u64)]);
            }
            fixture.g.classes[0].enodes[i + 1] = node(next(5) as Cost, children);
        }
        let mut children = vec![0];
        children.extend(fixture.reads.iter().filter(|_| next(2) == 0).copied());
        fixture.g.classes[fixture.root].enodes = vec![node(next(5) as Cost, children)];
        let root = if seed % 4 == 0 {
            fixture.states[next(count as u64)]
        } else {
            fixture.root
        };
        let expected = exhaustive_cost(&fixture.g, root);
        for liveness in [false, true] {
            for satellite in [false, true] {
                let opts = StatewalkOptions {
                    liveness,
                    satellite,
                };
                assert_eq!(
                    walk_cost(&fixture.g, root, opts),
                    expected,
                    "seed={seed}, {opts:?}, graph={:?}",
                    fixture.g
                );
            }
        }
    }
}
