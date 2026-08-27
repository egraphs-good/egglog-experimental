# Greedy DAG Extractor

This document describes the greedy DAG extractor in `src/greedy_dag_extract.rs`.
The implementation is experimental. It complements egglog's default tree
extractor by charging a shared dependency once within each extracted root or
variant.

The extractor is available through `:extractor greedy-dag` on `extract`,
`multi-extract`, and `keep-best`, and through the Rust functions
`extract_best_greedy_dag` and `extract_variants_greedy_dag`.

## Goals

The extractor is designed to:

- account for sharing without requiring subtraction or inspecting a concrete
  cost type;
- support marginal costs for enodes, containers, and base values through
  egglog's `DagCostModel` interface;
- limit discovery and propagation to values reachable from the requested
  roots;
- reject cyclic selections and keep a candidate's score consistent with the
  term reconstructed from it;
- support multiple roots and root-level variants without forcing one global
  representative choice across all returned terms; and
- remain fast enough for extraction-heavy egglog programs.

It is not intended to provide:

- globally optimal DAG extraction;
- a joint minimum-cost DAG across multiple requested roots;
- full k-best DAG extraction below the root e-class;
- cost functions that depend on the selected child extraction costs; or
- extraction through proof and term-encoding view tables.

## Cost Semantics

The extractor accepts a `DagCostModel<C>`, where `C` implements `MonoidCost`.
The model assigns an intrinsic marginal cost to each selected item:

- `enode_cost` costs a constructor row, excluding its children;
- `container_cost` costs a container value, excluding its elements; and
- `base_value_cost` costs a primitive value.

Each reachable dependency is identified by `(sort, value)`. The sort is part of
the key because egglog values are only meaningful within a sort, and a model may
assign different costs to the same raw value under different sorts.

For one candidate DAG, each dependency's marginal cost is combined at most
once. `MonoidCost::identity` supplies the empty cost and `MonoidCost::combine`
combines distinct marginal costs. The algorithm relies on the laws documented
by `MonoidCost`: combination must be associative, commutative, deterministic,
non-panicking, and monotone with respect to the cost order. Commutativity is
needed because merge order is chosen for performance rather than semantics.

The cost model is evaluated once for each reachable producer row and once for
each distinct reachable primitive or container value. Propagation, conflict
resolution, variants, and multiple roots reuse this frozen cost snapshot.

An objective that computes a node's cost from the selected child costs does not
fit this interface. Such an objective has tree-style context and should use a
`TreeCostModel`; it cannot generally be decomposed into once-paid marginal
costs.

## Result Semantics

Each returned root or variant has its own complete producer-choice snapshot.
That snapshot determines both its reported cost and its reconstructed term.
Separate roots may therefore use different representatives for a shared
e-class. Their terms share storage in the returned `TermDag`, but the extractor
does not minimize the union of all requested roots as one joint DAG.

This choice avoids the non-local representation problem described in
[extraction-gym issue 36](https://github.com/egraphs-good/extraction-gym/issues/36):
one globally selected node per e-class is not always sufficient for several
roots with conflicting finite choices.

Variant extraction ranks the requested root e-class's producer rows. It does
not enumerate every alternative producer combination in descendants. A
primitive or container root has one structural extraction, even when more than
one variant is requested. Requesting zero variants returns empty result lists
without discovering roots or evaluating the cost model.

## Algorithm

The implementation has five stages.

### 1. Discover the root-reachable problem

Discovery starts from every requested `(sort, value)` root and uses an explicit
worklist, so deeply nested constructor chains do not consume the Rust call
stack.

For an eq-sort value, discovery finds every visible, extractable, non-subsumed
normal constructor row that produces the value. It records the row and then
schedules its children. Containers are expanded structurally. Any eq-sort
values nested inside containers are recorded as dependencies of the enclosing
producer row, not only as independently reachable nodes.

Discovery deliberately excludes hidden functions, unextractable functions,
subsumed rows, and proof or term-encoding view tables. The latter have a
special row representation that this experimental extractor does not expose as
part of its contract.

The resulting problem contains:

- all reachable producer rows;
- all reachable primitive and container values;
- a reverse index from each eq-sort dependency to producer rows that use it;
  and
- optionally, an index from each target e-class to its producer rows for
  variant extraction.

This root-aware discovery differs from extraction-gym implementations that
ignore their root argument, as tracked by
[issue 49](https://github.com/egraphs-good/extraction-gym/issues/49).

### 2. Freeze IDs and marginal costs

During discovery, `InternerBuilder` assigns typed dense IDs to sort names and
reachable `(sort, value)` keys. Once discovery finishes, both interners are
frozen. Dense secondary maps and bitsets can then be sized once and cannot be
invalidated by later interning.

The extractor next evaluates all reachable `DagCostModel` callbacks and stores
their results on producer rows or structural nodes. No callback runs from the
fixed-point hot loop.

### 3. Propagate greedy improvements

Every reachable producer row is evaluated once to seed the fixed point. When a
new candidate strictly improves the best known cost for its target e-class,
that target is added to a queue. The reverse dependency index then revisits only
producer rows whose candidate may have changed.

This is a root-aware adaptation of the worklist in
[`faster_greedy_dag.rs`](https://github.com/egraphs-good/extraction-gym/blob/903ba0f818b50608fe20ae9e0f03c35cb27bc50a/src/extract/faster_greedy_dag.rs#L91-L135).
A debug-only final scan asserts that no discovered producer row can still
improve, guarding the completeness of the dependency index.

### 4. Build and reconcile candidates

A `DagCandidate` stores two related closures:

- `paid_costs` contains every reachable dependency whose marginal cost has
  already been charged; and
- `producer_choices` contains the exact constructor row chosen for every
  reachable eq-sort dependency.

Candidate construction unions the child paid-cost sets and inserts the current
node's marginal cost if it has not already been paid. It starts from the largest
child set, following
[`faster_greedy_dag.rs`](https://github.com/egraphs-good/extraction-gym/blob/903ba0f818b50608fe20ae9e0f03c35cb27bc50a/src/extract/faster_greedy_dag.rs#L57-L62),
so that set is cloned once instead of replayed entry by entry.

If a child closure already reaches the candidate's target and no producer
choices conflict, the candidate is cyclic and is rejected. When child snapshots
select different producers for the same e-class, simply unioning their costs
would make the score disagree with reconstruction. The implementation instead
chooses one closed producer plan, installs the candidate's root producer, and
rescans that exact plan to:

- remove dependencies reachable only through losing choices;
- recompute the once-paid cost closure;
- reject cycles in the reconciled plan; and
- retain only producer choices actually reachable from the root.

This snapshot-and-rescore step addresses the correctness risks reported for
other greedy DAG representations in
[extraction-gym issue 28](https://github.com/egraphs-good/extraction-gym/issues/28).

### 5. Reconstruct terms and variants

Reconstruction follows the selected producer snapshot, using a per-result memo
and visiting set. Repeated dependencies become shared `TermId`s in a single
`TermDag`; a visiting-set hit is treated as an extraction cycle.

Best extraction reconstructs the fixed-point winner for each requested root.
Variant extraction evaluates only producer rows indexed under the requested
root e-class, ranks finite candidates by cost and producer ID, and reconstructs
up to the requested count. Each variant retains its own immutable candidate
snapshot.

## Data Structures

### Frozen interners and secondary collections

`src/secondary_map.rs` provides extraction-local indexed collections:

- `InternerBuilder<K>` grows while reachable keys are discovered;
- `Interner<K>` is the frozen key universe;
- `InternId<K>` is a typed dense index tied to its key type;
- `SecondaryMap<K, V>` stores optional per-ID values in a dense vector; and
- `SecondarySet<K>` stores membership in a `FixedBitSet`.

Freezing before creating secondary collections makes their length stable. The
typed IDs prevent accidentally mixing sort IDs, cost-key IDs, and producer-row
IDs.

### Once-paid cost sets

`AggregatedSparseSecondaryMap<DagCostKey, C>` represents one candidate's
once-paid dependency set. It contains:

- a compact insertion-ordered vector of `(key ID, marginal cost)` entries;
- a bitset that answers membership queries in constant time; and
- the cached monoid aggregate of all entries.

The vector is needed to iterate and merge only present entries. The bitset is
needed because candidate construction performs many membership checks; scanning
the vector for each insert is substantially slower. The cached total avoids
recombining every entry each time candidates are compared and, unlike a running
delta, does not require subtraction from `C`.

`union_by_cloning_largest` clones the largest input and inserts unique entries
from smaller inputs. Duplicate IDs keep the existing marginal cost. After
producer-plan reconciliation, cost-model stability makes those duplicate
payloads equivalent; commutativity makes the aggregate independent of merge
order.

### Producer rows and indexes

Backend row callbacks borrow their data, but propagation must revisit rows after
discovery. `ProducerRows` therefore owns a compact arena of reachable rows and
uses typed `ProducerRowId`s to refer to it.

The always-built dependency index supports fixed-point propagation. The target
index is built only for variants because best extraction never reads it, and
measuring an eager index found a small but repeatable best-extraction
regression.

## Complexity

Let `R` be the number of reachable producer rows, `D` the number of reverse
dependency edges, and `S` the size of a candidate's selected dependency
closure.

- Discovery explores each reachable eq-sort value's constructors once, stores
  each reachable producer row once, and records each distinct dependency edge
  once per row. Primitive and container cost records are deduplicated, although
  a container reached along multiple paths may have its elements traversed more
  than once. Finding constructors for an eq-sort value still filters the
  e-graph's function metadata by output sort before using the backend's e-class
  row lookup.
- Fixed-point seeding evaluates `R` rows. Later improvements revisit only rows
  named by the `D`-edge reverse index instead of rescanning all rows.
- Candidate scoring is not scalar like additive tree extraction. It must merge
  selected closures, so its work is proportional to entries visited from child
  sets, bounded by the relevant `S` values.
- Exact rescoring traverses the reconciled producer plan when child snapshots
  conflict. Variant ranking rebuilds each root producer candidate and therefore
  invokes exact rescoring only for variants with such a conflict.
- Candidate snapshots can consume substantially more memory than one scalar
  cost and parent edge per e-class. This is the main cost of preserving exact
  score-to-term consistency.

The algorithm is a heuristic. Greedy improvements do not provide an optimality
guarantee, and extraction-gym has examples where related greedy variants differ
in quality ([issue 19](https://github.com/egraphs-good/extraction-gym/issues/19)).

## Validation

Focused integration tests cover the semantic boundaries:

- `test_greedy_dag_extract_prefers_shared_subterms` distinguishes tree cost
  from once-paid DAG cost.
- `test_greedy_dag_cost_and_term_use_the_same_producer_snapshot` checks that
  the reported score and reconstructed producer choices agree.
- `test_greedy_dag_reconciles_conflicting_child_snapshots` exercises exact
  conflict rescoring, independent roots, variants, and callback caching.
- `test_greedy_dag_extract_avoids_cycle_from_python_issue_387` and
  `test_greedy_dag_multi_extract_avoids_combined_root_cycle` cover finite
  extraction in the presence of cyclic alternatives.
- `test_greedy_dag_tracks_eq_dependencies_nested_in_containers` checks the
  reverse index for nested eq-sort dependencies.
- `test_greedy_dag_accepts_non_additive_monoid_cost` verifies that aggregation
  uses `MonoidCost::combine`, not hard-coded addition.
- `test_greedy_dag_costs_each_reachable_node_once_for_variants` verifies that
  variants and repeated roots reuse the frozen marginal-cost snapshot.
- `test_greedy_dag_extract_zero_variants_returns_empty_for_all_root_kinds`
  verifies the zero-work fast path.

The file-test harness also runs the opposite extractor for every recognized
`extract` command from an equivalent cloned e-graph state. It converts each
returned term back into an expression, evaluates it, and checks that its sort
and value equal the requested root. This validates both tree and greedy DAG
results across the checked-in experimental program corpus.

## Performance Decisions

The following measurements used release builds on an Apple M4 Mac. The vector
canary was a temporary copy of egglog's `tests/extract-vec-bench.egg` with its
extraction switched to greedy DAG. Its rows report local before/after
comparisons made as the implementation evolved and should not be compared to
one another as a single benchmark series. The final comparison uses the
checked-in Taylor 51 program. These measurements justify implementation choices
but are not general performance guarantees.

| Decision | Evidence |
| --- | --- |
| Intern reachable keys and use a vector plus bitset for paid costs | Replacing hash-table-backed cost sets reduced the vector canary by about 55%. Replacing the bitset with linear entry scans later regressed it by roughly 65-70%. |
| Clone the largest child cost set before union | Reduced the vector canary from 20.79 ms to 18.41 ms, about 11%. This strategy comes from extraction-gym's `faster_greedy_dag`. |
| Index exact producer dependencies, including values nested in containers | Removed the fixed-point safety scan and reduced the vector canary from 13.62 ms to 9.29-9.44 ms, about 31-32%. |
| Cache every reachable cost-model callback during preparation | Changed Taylor 51 greedy DAG time from 207.4 ms to 206.9 ms; the 95% confidence interval of -0.98% to +0.53% is consistent with no regression. Callback-count tests establish the semantic benefit. |
| Build the producer target index only for variants | Always building it regressed best extraction by 2.32% (95% CI +0.11% to +4.53%). |
| Reserve the merged producer-plan capacity | Removing the reserve regressed variant extraction by 2.72% (95% CI +0.90% to +4.54%); the best-extraction result was inconclusive. |
| Use `hashbrown::HashMap` in hot maps | A complete replacement with `std::collections::HashMap` regressed Taylor 51 by 1.90% across 120 alternating pairs (95% CI +1.04% to +2.76%). The experiment did not isolate the hasher from other implementation details. |
| Keep the sparse entries, membership bitset, and aggregate in one type | Flattening a one-use nested wrapper removed roughly 30 lines and was performance-neutral on best and variant workloads. |

The final Taylor 51 comparison used experimental commit `4c5e7922` with egglog
commit `e264c37a`, `hyperfine --warmup 5 --runs 20`, and redirected stdout. The
same release binary ran the original tree workload in `1.026 s +/- 0.012 s` and
a copy with its 324 extraction commands changed to `:extractor greedy-dag` in
`207.8 ms +/- 2.2 ms`. Greedy DAG was `4.93 +/- 0.08` times faster on this
particular workload. This is a whole-program comparison of two extractors that
may select different terms, not a general claim that greedy DAG extraction is
faster than tree extraction.

## Alternatives Tried

Several plausible simplifications or optimizations were measured and rejected:

- Returning owned candidates to reduce `Arc` traffic produced noisy results and
  no clear improvement over the bitset baseline.
- Replacing the pending queue's keys with dense IDs did not beat the simpler
  exact-dependency worklist.
- Omitting a child closure when its root was already paid can change extraction
  quality when two paths select different sub-DAGs, so it is not a
  behavior-preserving optimization.
- Removing the producer-plan capacity reservation made variants measurably
  slower.
- Building the variant target index eagerly and replacing `hashbrown` with the
  standard `HashMap` both made best extraction measurably slower.

Quality-changing pruning, parallel heuristics, and initialized exact solving
are intentionally deferred to separate extractor modes. They should not be
hidden inside the semantics of `greedy-dag`. Relevant future directions include
[e-boost](https://arxiv.org/abs/2508.13020) and
[optimal extraction parameterized by treewidth](https://arxiv.org/abs/2408.17042).

## Primary References

- [extraction-gym `faster_greedy_dag.rs`](https://github.com/egraphs-good/extraction-gym/blob/903ba0f818b50608fe20ae9e0f03c35cb27bc50a/src/extract/faster_greedy_dag.rs)
- [extraction-gym `greedy_dag.rs`](https://github.com/egraphs-good/extraction-gym/blob/903ba0f818b50608fe20ae9e0f03c35cb27bc50a/src/extract/greedy_dag.rs)
- [Root handling in DAG extractors, issue 49](https://github.com/egraphs-good/extraction-gym/issues/49)
- [Greedy heuristic quality differences, issue 19](https://github.com/egraphs-good/extraction-gym/issues/19)
- [Global greedy correctness problems, issue 28](https://github.com/egraphs-good/extraction-gym/issues/28)
- [Non-local multi-root extraction, issue 36](https://github.com/egraphs-good/extraction-gym/issues/36)
