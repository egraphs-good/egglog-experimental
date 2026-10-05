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

### The effectful relation

A unary relation marks the e-classes whose terms carry the state. The program
populates it with ordinary rules:

```lisp
(relation Effectful (Expr))
(rule ((= e (Print v s))) ((Effectful e)))
```

Effectfulness is a property of e-classes, not constructors: in eggcc an `If`
is effectful only when its type contains the state. The relation is passed to
the extraction commands by name, so a program can keep several.

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

The same declaration can be made separately, for example when the datatype is
declared in another file:

```lisp
(effsafe-regions If 2 3)
```

An effectful e-node with two effectful children outside its `:regions`
positions is an error.

### `effsafe-placeholder`

Some sorts should not be extracted at all. eggcc attaches a *context* to every
leaf that refers back to the region the leaf is in, which makes the terms
cyclic. `effsafe-placeholder` tells the extractor not to descend into a sort
and to emit a fixed term for every child of that sort instead:

```lisp
(effsafe-placeholder Assumption (NoContext))
```

## Regions

Regions follow Section 7.1 of the paper. A *region* is the part of the e-graph reachable from an effectful root
through state children and pure children, but not through subregions. Every
region has exactly one *entry*: an effectful e-node with no effectful children
(a function argument, say). Within a region, the extractor:

1. finds the cheapest chain of effectful e-nodes from the root down to the
   entry such that every pure term the chain needs is extractable from it (a
   dynamic program over the set of extractable pure e-classes, hashed and
   shared between states);
2. linearizes the region along that chain; and
3. extracts the pure terms greedily, charging a pure e-class once per region.

Subregions are extracted the same way and placed below the e-nodes that use
them. A subregion used from several places is extracted once.

## Costs

E-node costs come from a `DagCostModel`: in the egglog frontend this is the
dynamic cost model, so `:cost` annotations and `set-cost` apply. Base values
and containers are priced by the same model.

The cost of an e-node is its own cost, plus the cost of its non-region
children, plus whatever its subregions add. The last part is decided by a
`RegionCostModel`. The default, `SumRegions`, adds the subregions' costs. A
compiler can implement the trait to express heuristics such as charging only
the more expensive branch of a conditional or weighting a loop body by an
iteration estimate:

```rust
struct MyRegions;
impl RegionCostModel for MyRegions {
    fn fold_regions(&self, _: &EGraph, constructor: &str, costs: &[Cost]) -> Cost {
        match constructor {
            "If" => costs.iter().copied().max().unwrap_or(0),
            "Loop" => costs[0].saturating_mul(100),
            _ => costs.iter().sum(),
        }
    }
}
let egraph = new_experimental_egraph_with_effsafe(DynamicCostModel, Arc::new(MyRegions));
```

Costs are `u64`s with saturating arithmetic.

## Commands

```lisp
(effsafe-extract <effectful-relation> <expr>...)
(effsafe-extract-all <effectful-relation> <constructor>)
(effsafe-regions <constructor> <position>...)
(effsafe-placeholder <sort> <expr>)
```

`effsafe-extract` extracts each expression's e-class; the roots must be
effectful. `effsafe-extract-all` extracts every e-class that holds an e-node
of the given constructor, in e-class order, sharing regions between them.
Both return an `EffsafeExtractOutput` (a `TermDag` and one root term per
extracted e-class) through `CommandOutput::UserDefined`; the CLI prints the
terms.

From Rust, `extract_effsafe` runs the same extraction with an explicit
`EffsafeConfig`, and `new_experimental_egraph_with_effsafe` registers the
commands with custom cost models.

## Subsumed e-nodes

Like egglog's other extractors, `effsafe-extract` skips subsumed e-nodes.
A program whose rules subsume e-nodes for other reasons (to stop rewrites
from firing again, say) can include them with a trailing `:include-subsumed`:

```lisp
(effsafe-extract-all Effectful Func :include-subsumed)
```

## Limitations

- Pure e-nodes must not use effectful e-nodes that are not on their region's
  statewalk; the language's rewrites must preserve this (it holds for
  languages in which the state is linear).
- `:regions` is accepted on `constructor` and on `datatype` variants, not yet
  inside `datatype*`.
- Containers are extracted element by element; a container holding an
  effectful e-class is treated as a pure node.
- Roots must be effectful. Extracting a pure root is a plain tree extraction,
  which `extract` already provides.
