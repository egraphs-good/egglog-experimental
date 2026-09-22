// Core web-demo/prims.egg: the imperative schedule and both supplied graphs.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;
#[sort]
pub struct Edge;

#[declarations]
impl Edge {
    pub fn new(source: egg::I64, target: egg::I64, weight: egg::I64) -> Edge;
}
#[relation]
pub fn edge_exists(edge: Edge);
#[relation]
pub fn start();
#[relation]
pub fn in_mst(edge: Edge);
#[relation]
pub fn solution(source: egg::I64, target: egg::I64, weight: egg::I64);
#[function(merge = |old: egg::I64, new: egg::I64| old.max(new))]
// A 0/1 membership flag: max prevents initialization from undoing an inclusion.
pub fn included(vertex: egg::I64) -> egg::I64;
#[function(merge = |old: egg::I64, new: egg::I64| old.max(new))]
pub fn iteration() -> egg::I64;
#[function(merge = |_old: Edge, new: Edge| new)]
pub fn best_edge(iteration: egg::I64) -> Edge;
#[function(merge = |_old: egg::I64, new: egg::I64| new)]
pub fn best_weight(iteration: egg::I64) -> egg::I64;

#[ruleset]
fn init(x: &egg::I64, y: &egg::I64, w: &egg::I64, e: &Edge) -> Vec<Rule> {
    vec![
        // Treat each input edge as undirected, then initialize its vertices.
        rule(eq(e, Edge::new(x, y, w)), union(e, Edge::new(y, x, w))),
        rule(edge_exists(Edge::new(x, y, w)), set(included(x), 0)),
        rule(
            start(),
            (
                set(included(1), 1),
                set(iteration(), 0),
                set(best_weight(0), 99_999_999),
            ),
        ),
    ]
}

#[ruleset]
fn choose(i: &egg::I64, x: &egg::I64, y: &egg::I64, w: &egg::I64) -> Vec<Rule> {
    vec![rule(
        (
            eq(i, iteration()),
            edge_exists(Edge::new(x, y, w)),
            eq(included(x), 1),
            eq(included(y), 0),
            w.lt(best_weight(i)),
        ),
        (
            set(best_weight(i), w),
            set(best_edge(i), Edge::new(x, y, w)),
        ),
    )]
}

#[ruleset]
fn finish(i: &egg::I64, x: &egg::I64, y: &egg::I64, w: &egg::I64) -> Vec<Rule> {
    vec![rule(
        (eq(i, iteration()), eq(Edge::new(x, y, w), best_edge(i))),
        (
            in_mst(Edge::new(x, y, w)),
            set(included(x), 1),
            set(included(y), 1),
            set(iteration(), i + 1),
            set(best_weight(i + 1), 99_999_999),
        ),
    )]
}

#[ruleset]
fn finalize(x: &egg::I64, y: &egg::I64, w: &egg::I64) -> Vec<Rule> {
    // Emit just one canonical orientation of each undirected solution edge.
    vec![rule(
        (in_mst(Edge::new(x, y, w)), x.lt(y)),
        solution(x, y, w),
    )]
}

pub fn main() -> Result<(), TypedError> {
    let cases = [
        (vec![(1, 2, 2), (1, 4, 1), (2, 4, 2), (3, 4, 3)], 3, 6),
        (
            vec![
                (1, 2, 1),
                (1, 4, 5),
                (1, 5, 3),
                (2, 4, 5),
                (2, 5, 2),
                (3, 5, 4),
                (3, 6, 5),
                (4, 5, 4),
                (5, 6, 7),
            ],
            5,
            16,
        ),
    ];
    for (edges, count, total) in cases {
        // Graph facts remain a source ruleset, not an out-of-band MST solver.
        let graph = ruleset(rule(
            start(),
            edges
                .iter()
                .map(|&(x, y, w)| edge_exists(Edge::new(x, y, w)))
                .collect::<Vec<_>>(),
        ));
        let mut egraph = EGraph::default();
        egraph.register(start())?;
        egraph.run(sequence((
            sequence((&init, &graph)).saturate(),
            sequence((choose.saturate(), &finish)).saturate(),
            finalize.saturate(),
        )))?;
        assert!(egraph.check(eq(iteration(), count))?);
        let mut found = 0;
        let mut weight = 0;
        for (x, y, w) in edges {
            if egraph.check(solution(x, y, w))? {
                found += 1;
                weight += w;
            }
        }
        assert_eq!((found, weight), (count, total));
    }
    Ok(())
}
