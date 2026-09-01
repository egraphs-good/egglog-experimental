# `unstable-subst`: a substitution primitive

Status: exploration. Lives in `egglog-experimental`; the general e-graph
introspection it uses lives in `egglog` (see "What egglog had to expose").

## Interface

```text
(unstable-subst root map) : R × Map<K, K> → R
```

`root` is an e-class of any eq-sort `R`. `map` has one eq-sort `K` for both
keys and values; `R` and `K` may differ because traversal can reach `K`-sorted
children beneath an `R`-sorted root. Exactly one map is accepted, so a single
call cannot substitute keys of several different sorts.

The entries form one simultaneous substitution. For example, a map containing
`x -> y` and `y -> x` swaps `x` and `y`; it does not substitute `x := y` and
then `y := x`. A mapped value is spliced in as supplied and is not itself
traversed. With an empty map, the primitive returns the exact root value and
writes nothing.

The primitive walks the sub-e-graph reachable from `root`, copies only the part
affected by the substitution, and returns the copied root. Reachability follows
constructor rows (term structure), not `function` rows (analyses over that
structure). It also follows e-classes inside containers such as `Vec`, `Map`,
and `Set`, rebuilding affected containers around their substituted contents.

## Semantics and safety

Let `σ` map each key e-class to its mapped value.

* A reachable e-class is **affected** if it is a key or if one of its
  e-nodes, including through a container child, refers to an affected e-class.
* `σ(v)` is the mapped value for a key, the original `v` for an
  unaffected value, and the rebuilt value for an affected container.
* For an affected non-key e-class `e`, every non-subsumed e-node
  `f(c1..cn) -> e` in the snapshot is copied as `f(σ(c1)..σ(cn))`. Those
  copies are unioned, and their class is `σ(e)`.
* The result is `σ(root)`. If no key is reachable, the original root is
  returned and nothing is copied.

Copying every e-node carries the region's equations into the copy. If the
original e-class contains both `t1` and `t2`, the copy asserts
`σ(t1) = σ(t2)`. This is sound only when substitution preserves a derivation
of that equality, including every premise on which it depends. The primitive
does not inspect provenance or prove that condition for the caller.

For example, an equality such as `a * 0 = 0` derived by an unconditional
rewrite is preserved by substituting for `a`. A ground union such as
`x + 1 = 5` is not preserved by arbitrarily replacing `x`: copying it under
`x := 9` would assert `9 + 1 = 5`. Equations from conditional or
analysis-dependent rules are likewise not generally safe, because substitution
can invalidate the condition or analysis fact that justified them. Being a
singleton e-class is neither necessary nor sufficient; what matters is whether
the copied derivations remain valid.

## Operational constraints

* **If traversal is required, `root` must already have committed rows.** An
  action's writes are staged until the action finishes. A root built by that
  same action is therefore invisible to the walk and returns unchanged, without
  an error. A root that is itself a key instead returns its mapped value
  directly and needs no rows. Otherwise, pass a root bound by the rule query or
  created by an earlier command. Replacements may be built in the current
  action because they are spliced in rather than walked.
* **No e-class id is invented.** Every copied e-node is inserted through the
  ordinary constructor path. A cycle is copyable only if some e-node can first
  name each copied class. If every e-node in a cycle depends on an as-yet
  unnamed copy, substitution reports an ungrounded-cycle error before writing.
* **Subsumed e-nodes are skipped.** They are excluded from extraction and must
  not be resurrected as ordinary rows in a copy.
* **Live reads require `Context::Full`.** The primitive is available in
  top-level actions and `:naive` rule heads, not ordinary seminaive rule heads,
  which would not re-fire when the live state they read grows.
* It is registered by `new_experimental_egraph`; `EGraph::default` does not
  include it.

## Implementation

Substitution separates all copyability decisions from mutation: one read-only
phase followed by two write passes.

1. **Collect and preflight, read-only.** Build a snapshot of reachable
   constructor rows and container contents, mark the affected region, and
   compute an order in which every copied e-class can be named. If no such
   order exists, report the ungrounded cycle before substitution writes a copy.
   Values built as arguments to the primitive have already been staged by the
   enclosing action, so this guarantee does not roll those argument writes back.
2. **Name copied classes.** In the computed order, insert one ready e-node per
   affected non-key e-class to obtain its image.
3. **Complete their equations.** With every image named, insert the remaining
   e-nodes and union each result into the image of its original class.

Container rebuilding waits until every e-class inside has an image, so an
ungrounded cycle cannot leave a half-substituted container behind. E-class
traversal uses explicit stacks; only descent through nested container values
recurses, bounded by the program's container-sort nesting.

### Cost

Collection uses indexed output lookups rather than whole-table scans, but its
cost is not proportional only to returned rows. When a traversal is needed, it
scans table-size metadata and asks for the schema of every nonempty table to
catalog the current nonempty constructors. Let `C` be the number with an eq-sort
output, `C_s` the number outputting sort `s`, and `R_s` the reached non-root
e-classes of sort `s`. Collection then makes exactly
`C + sum_s(R_s * C_s)` indexed row probes: the root's sort is unknown, while
every child's sort is known. Each probe uses that table's cached output-column
index; there is no cross-table e-class index.

After those probes, snapshot construction and affected marking are linear in
the reached e-classes, returned rows, dependency edges, and container contents.
The copyability fixpoint can rescan the affected snapshot while it finds a
naming order, so its worst case is superlinear (quadratic when progress reveals
only one of linearly many classes per scan). Apart from backend insertion and
union costs, the two write passes process each planned e-node at most twice.
Snapshot memory is proportional to the reached e-classes, rows, edges, and
container contents; there is no configured snapshot-size bound.

### What egglog had to expose

Nothing substitution-specific: a small set of general e-graph operations makes
the primitive implementable out of tree.

* `Read::constructor_enodes_for_eclass` performs an indexed lookup of
  constructor rows whose output is one e-class. The lookup was developed in
  [PR #934](https://github.com/egraphs-good/egglog/pull/934), cherry-picked
  upstream in [PR #986](https://github.com/egraphs-good/egglog/pull/986), and
  renamed to the pinned method by
  [PR #1003](https://github.com/egraphs-good/egglog/pull/1003). The Cargo
  dependency pins that earliest suitable official upstream merge.
* `Read::constructor_schema`, together with `Read::table_sizes`, lets a
  primitive enumerate the current nonempty constructors and group them by
  output sort. The e-graph supplies its `TypeInfo` as an `ExternalContext` for
  the duration of the operation.
* `Core::map_container` rebuilds and interns a container value through the
  existing `ContainerValues::rebuild_val_with` machinery.

## Known limitations

* Values are assumed canonical. That holds after top-level rebuilds and in a
  `:naive` rule head, the supported contexts.
* A custom `ContainerValue` must invoke its rebuild callback only for
  eq-sort or eq-container fields, as egglog's built-in containers do. The
  callback carries raw values rather than their sorts, so presenting an opaque
  base field whose raw id collides with an e-class id could remap that field.
* Proof mode is unsupported because copied rows carry no justification. The
  primitive has no proof validator, so proof or term-encoding execution is
  refused rather than silently producing an invalid proof.
* A primitive-level failure reaches an egglog program as a generic primitive
  panic, with the specific reason in the log.
* `tests/subst-basics.egg` pins language semantics,
  `tests/unstable-subst.egg` demonstrates beta reduction, and `tests/subst.rs`
  covers e-class identity, table sizes, and failure behavior. The file harness
  does not add egglog's desugar, term-encoding, or multi-thread variants.
