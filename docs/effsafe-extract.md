# Effect-Safe Extraction

This document describes `effsafe-extract` in `src/effsafe_extract/`. It is an
extractor for languages whose terms thread an explicit *state* (memory, I/O, a
heap) through their expressions, and whose e-graphs therefore contain terms
that are individually valid but cannot be combined: two e-nodes that both
consume the same state cannot both appear in one program.

The algorithm is *statewalk DP* from

> Oliver Flatt, Anjali Pal, Yihong Zhang, Ryan Tjoa, Kirsten Graham, Alex
> Fischman, Chandrakana Nandi, Eli Rosenthal, Zachary Tatlock, and Haobin Ni.
> 2026. *Efficient Extraction for Effectful E-graphs.* Proc. ACM Program. Lang.
> 10, OOPSLA2, Article 398. <https://doi.org/10.1145/3839530>

which defines effect-safe extraction (Section 4), shows that finding any
effect-safe extraction is NP-complete (Section 5), and gives the dynamic
program, tractable in *statewalk width* (Section 6). It was developed for the
[eggcc](https://github.com/egraphs-good/eggcc) compiler, where it is known as
*tiger*. This document covers the interface; see the paper for the algorithm.

## The problem

Consider a language where `Print` takes a value and the current state and
returns the new state:

```lisp
(let $s0 (Arg))
(let $p1 (Print (Num 1) $s0))
(let $p2 (Print (Add (Num 1) (Num 0)) $s0))
(union $p1 $p2)
(let $p3 (Print (Add (Num 2) (Num 3)) $p1))
```

`$p1` and `$p2` are equal, so a tree extractor is free to choose either when
extracting `$p3`. But a *pure* term that reads the state must read the state
the extracted program actually produces. Once the extractor commits to one
chain of effectful e-nodes (the *statewalk*), every pure term in the program
has to be built from that chain alone. Extracting one e-node per e-class is
not enough; the extractor needs a global view of which state each term uses.

`effsafe-extract` chooses the statewalk and the pure terms together.

## Language annotations

Three things tell the extractor about the language.

### `set-effectful`

`(set-effectful Expr e)` marks the e-class of `e` as carrying the state. It is an
action, so rules can use it:

```lisp
(rule ((= e (Print v s))) ((set-effectful Expr e)))
```

The first argument must name an existing eq sort; `e` must have that sort.
The action also works at top level and on values bound by earlier actions.
The explicit sort can resolve overloaded expressions.

Effectfulness is a property of e-classes, not constructors: an `If` is
effectful only when its result carries the state. A container (`Vec`, `Set`,
...) holding an effectful element is effectful without being marked.

### `:regions`

An effectful e-node may have one effectful child that continues its region's
statewalk (the state it consumes) plus any number of effectful children that
start *subregions*: a conditional's branches, a loop's body. Subregions are
extracted on their own, from their own copy of the state. The `:regions`
option on a `constructor` or `datatype` variant lists the zero-based argument
positions that start subregions:

```lisp
(datatype Expr
  (If Expr Expr Expr Expr :regions (2 3))   ; predicate, state, then, else
  (Loop Expr Expr :regions (1)))            ; inputs, body
```

The annotation lowers to the command `(effsafe-regions If 2 3)`, which
programs can also write directly if the declaration cannot be changed.

Pure e-nodes can also start effectful subregions at annotated positions.
Those subregions have their own statewalks; other effectful dependencies of
the pure e-node must belong to the enclosing statewalk.

An effectful e-node with two effectful children outside its `:regions`
positions has no single state input. Such e-nodes are skipped (the extraction
fails with a message naming them only if a root has no other term).

### Placeholders (Rust only)

Some sorts should not be extracted at all. eggcc attaches a *context* to every
leaf that refers back to the region the leaf is in, which makes the terms
cyclic. An embedder can name a constructor of such a sort that stands in for
every value of it, in `EffsafeConfig::placeholders`:

```rust
effsafe_state(&mut egraph)
    .config
    .placeholders
    .insert("Assumption".into(), Expr::Call(span!(), "NoContext".into(), vec![]));
```

The extractor does not descend into the sort and emits the placeholder for
every child of that sort instead; the replacement must be a well-typed
constructor application of the sort, with literal or nested constructor
arguments. Invalid replacements cause an extraction error. Placeholders can
produce a term outside the requested e-class; the embedder must restore any
information needed to preserve meaning.

## Regions

Regions follow Section 7.1 of the paper. A *region* is reachable from an
effectful root through state children and pure children, excluding subregions. Every
region must have exactly one *entry e-class*, containing an effectful e-node
with no state child outside `:regions` positions (a function argument, say).
Multiple entry e-nodes in that class are allowed: extraction chooses the
cheapest whose pure children need no state. Distinct entry e-classes are
rejected. Within a region, the extractor:

1. chooses a chain from root to entry using estimated costs, requiring every
   pure dependency of the chain to be extractable from it;
2. linearizes the region along that chain; and
3. extracts the pure terms greedily, charging a pure e-class once per region.

Subregions are extracted the same way and placed below the e-nodes that use
them. Search costs are heuristic; the result need not have the lowest possible
DAG cost.

## Costs

Costs are a DAG within each region and a tree across region boundaries, using
egglog's two cost model traits:

| Where | Trait | Role |
| --- | --- | --- |
| Within a region | `DagCostModel` | Marginal e-node, base value and container costs; a pure e-class shared within a region is charged once. |
| At a region boundary | `TreeCostModel` | Combines the costs of an e-node's subregions with its own: sum, branch weighting, loop multiplication, ... |

In the egglog frontend the `DagCostModel` is the dynamic cost model, so
`:cost` annotations and `set-cost` apply, and the boundary model is
`TreeCostModelFromDag` of the same model, which adds the subregions' costs to
the e-node's own cost.

The boundary model applies to e-nodes with `:regions` children. Its
`fold_enode_cost` receives costs at those argument positions and `0` elsewhere.
The result must include the node's own cost. Ordinary children, including
predicates and state inputs, are charged separately in the enclosing region.

Each annotated child is charged per occurrence, even when two arguments
share the same subregion. Pure children at `:regions` positions remain in
the enclosing region but are priced independently through the same fold.
Search uses their estimated costs; reported costs use the selected terms.

A compiler embedding egglog installs its own models with
`set_effsafe_cost_models`. eggcc, for instance, charges both branches of an
`If` (the cheaper one at a quarter) and multiplies a loop body by an iteration
estimate:

```rust
struct Heuristics;
impl TreeCostModel<DefaultCost> for Heuristics {
    type EnodeCost = (String, DefaultCost);     // constructor name, own cost
    type ContainerCost = DefaultCost;
    fn enode_cost(&self, egraph: &EGraph, func: &Function, enode: &Enode<'_>) -> Self::EnodeCost {
        (func.name().to_string(), DagCostModel::enode_cost(&MyNodeCosts, egraph, func, enode))
    }
    fn fold_enode_cost(&self, (name, own): Self::EnodeCost, child_costs: &[DefaultCost]) -> DefaultCost {
        match (name.as_str(), child_costs) {
            ("If", &[_, _, then, els]) => own.saturating_add(then.max(els)).saturating_add(then.min(els) / 4),
            ("Loop", &[_, body]) => own.saturating_add(body.saturating_mul(100)),
            _ => child_costs.iter().fold(own, |acc, c| acc.saturating_add(*c)),
        }
    }
    // base_value_cost, container_cost, fold_container_cost as usual
}
let mut egraph = new_experimental_egraph();
set_effsafe_cost_models(&mut egraph, MyNodeCosts, Heuristics);
```

The reported cost of an extraction is the extracted program's cost under the
same models. With the default sum, an `If` of cost 1 whose branches cost 10
each reports `1 + 10 + 10 = 21` (plus its predicate and state) even though the
two branches are the same shared region.

The annotations and cost models live in the e-graph's extension state
(`EffsafeState`), so they are cloned and snapshotted with it.

Costs are `u64`s. The extractor uses saturating addition; custom cost models
should also use saturating arithmetic.

## Checking

Every extraction is checked for effect safety before it is returned, including
in release builds. A failed final check returns an extraction error. The
extractor's internal invariants (well-formed region graphs, mappings,
statewalks) are checked in debug builds, or in any build when the
`EFFSAFE_VALIDATE` environment variable is set, e.g.
`EFFSAFE_VALIDATE=1 cargo test --release`. `EFFSAFE_DEBUG` adds detail to
"no finite term" errors.

## Commands

```lisp
(extract <expr> :extractor effsafe [:include-subsumed])
(print-function <constructor> [n] :extractor effsafe [:include-subsumed])
(set-effectful <Sort> <expr>)
(effsafe-regions <constructor> <position>...)   ; what :regions lowers to
```

`extract ... :extractor effsafe` extracts the expression's e-class, which must be
effectful, and reports it like any `extract` (see Costs).
`print-function ... :extractor effsafe` prints one term for each e-class
holding an e-node of the constructor, in e-class order. Variants (`extract e n`), `multi-extract` and `keep-best` do not support
`:extractor effsafe`.

An optional row limit on `print-function` selects the roots before extraction.
Unselected roots need not be effectful or extractable.

`:include-subsumed` is an error with the other extractors.

From Rust, `extract_effsafe` runs the same extraction with an explicit
`EffsafeConfig`, `effsafe_state` gives access to the configuration stored on
an e-graph (placeholders included), and `set_effsafe_cost_models` installs
custom cost models. Programmatic callers read the terms from the
`CommandOutput::ExtractBest` or `CommandOutput::PrintFunction` the commands
return.

`EffsafeConfig::regions` accepts positions in any order and ignores duplicates.
`EffsafeConfig::statewalk` controls liveness and satellite pruning; both are
enabled by default.

## Subsumed e-nodes

Like egglog's other extractors, effect-safe extraction skips subsumed e-nodes.
A program whose rules subsume e-nodes for other reasons (to stop rewrites
from firing again, say) can include them with `:include-subsumed`:

```lisp
(print-function Func :extractor effsafe :include-subsumed)
```

## Limitations

- Outside explicit subregions, pure e-nodes must not use effectful e-nodes
  that are not on their region's statewalk; rewrites must preserve this (it holds for
  languages in which the state is linear).
- A container holding two states is skipped, like other effectful e-nodes
  with multiple state inputs outside `:regions`.
- Roots must be effectful. Pure roots are rejected; use `extract` without
  `:extractor effsafe` for ordinary tree extraction.
