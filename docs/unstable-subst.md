# `unstable-subst`: a substitution primitive

Status: exploration. Lives in `egglog-experimental`; the e-graph introspection
it needs lives in `egglog` (see "What egglog had to expose" below).

## What it does

```text
(unstable-subst root map) : (R, Map<K, K>) -> R
```

`root` is an e-class of any eq-sort `R`; `map` is a `Map` whose key and value
sorts are the same eq-sort `K`. The primitive walks the sub-e-graph reachable
from `root`, copies the part of it that the substitution actually touches while
replacing every occurrence of a key e-class with its mapped value, and returns
the e-class of the copied root.

Reachability follows **constructor** rows only (the term structure), never
`function` rows (those are analyses over the structure, not part of it).
Container-valued children (`Vec`, `Map`, `Set`, ...) are followed into and
rebuilt with substituted contents.

## Semantics

Let `σ` be the resulting map on values.

* An e-class is **affected** if it is a key of `map`, or if one of its e-nodes
  has an affected child (least fixpoint over the reachable subgraph).
  Container values are affected if any of their contents are.
* `σ(v) = map[v]` for keys, `σ(v) = v` for unaffected `v`.
* For an affected non-key e-class `e`, every e-node `f(c1..cn) -> e` in the
  snapshot is copied as `f(σ(c1)..σ(cn))`; all the copies are unioned together
  and `σ(e)` is that class. Copying every e-node, not just the ones that change,
  is what carries the region's equations over to the copy — see below.
* The return value is `σ(root)`.

Consequences worth stating out loud:

* **Nothing is copied when nothing changes.** An unaffected sub-e-graph is
  shared with the original, so `(unstable-subst e (map-empty))` is exactly `e`
  and allocates nothing.
* **The region's equations are substituted too, not just its terms.** An
  e-class is a set of terms known equal, so copying it copies every one of its
  e-nodes: if the e-graph knows `t1 = t2` and both are reachable, the copy
  asserts `σ(t1) = σ(t2)`. An e-node with no substituted children copies to
  itself, so `lookup_or_insert` finds the original row and the copy merges back
  into the original class.

  That is what you want when the equations come from rewrite rules, which hold
  for every value of the substituted classes. With
  `(rewrite (Mul a (Num 0)) (Num 0))`, the class of `(Mul x (Num 0))` also holds
  `(Num 0)`; substituting `x := 5` merges the copy back into that class and
  returns it, and `5 * 0` really is `0`.

  It is wrong when the e-graph holds a **ground** equation pinning a substituted
  class down. `(union (Add x (Num 1)) (Num 5))` asserts `x = 4`; substituting
  `x := 9` copies the untouched `(Num 5)` unchanged, merges, and thereby asserts
  `9 + 1 = 5`. So only substitute classes that behave like universally
  quantified variables — being singleton is neither necessary nor sufficient.
  (`tests/subst.rs` pins both directions.)

  Copying every e-node rather than only the ones that change is deliberate.
  Copying only the changed e-nodes would never merge back into the original
  class, but it would also drop the region's equations from the copy: the
  `x * 0` result above would come back as a bare `(Mul (Num 5) (Num 0))` not
  known to equal `0`. A running rule set would re-derive that; a one-shot
  substitution would not.
* **`root` must already exist.** The walk reads tables, and an action's writes
  stay staged until the action finishes. A root the enclosing action just built
  has no rows yet, so the walk finds nothing under it and returns it *unchanged
  and without an error* — `(unstable-subst (Mul x y) m)`, building its own
  argument, silently does nothing. Pass a root the rule's query bound, or one
  from an earlier command; that is what the `:naive` beta-reduction shape does.
  Replacements are exempt: a map's values are spliced into the copy without
  being walked, so those can be built in the same action.
* **No e-class id is ever invented.** Every copied e-node goes in through
  `lookup_or_insert`, exactly as `(Add a b)` in an action does, so egglog names
  the copy. The consequence is the cycle rule below.
* **Grounded cycles are copied; ungrounded ones error.** A cyclic e-class can
  only be copied if one of its e-nodes has all its children outside the cycle:
  that e-node's insert names the copy, and the cyclic e-node then unions into
  it. `x = {Var "x", Add x (Num 0)}` qualifies and works. A cycle in which every
  e-node points back into the cycle has no such starting point, and naming its
  copy would mean inventing an e-class id — so it reports that
  (`egglog_experimental::subst` returns an error naming the e-class; the
  primitive panics, since a primitive cannot return one) rather than producing
  a partial copy.
* **Subsumed e-nodes are skipped** — they are excluded from extraction, so
  resurrecting them un-subsumed in a copy would be wrong.
* Registered by `new_experimental_egraph`, so a plain `EGraph::default` does not
  have it.
* The snapshot is taken from live table contents, so `unstable-subst` is only
  available where reads *and* writes are legal: top-level actions (`let`,
  `eval`, action-mode `run-schedule`) and the head of a `:naive` rule. This is
  the `Context::Full` capability, enforced by the typechecker. It is not
  available in an ordinary seminaive rule head, because a rule that read live
  state would not re-fire when the state it read grows.

## Implementation

Three passes over the reachable subgraph. The two that walk e-classes use an
explicit stack, so term depth is bounded by the heap rather than by Rust's
stack; only the descent into nested containers recurses, and that is bounded by
how deeply the program's sorts nest containers.

1. **Collect** — DFS from `root` gathering, per reachable e-class, its e-nodes
   (table name + child values), and per reachable container value, its
   contents. The root's sort is not known at runtime (the primitive is shared
   across all call sites), so the walk probes every eq-sorted constructor for
   the root e-class and then uses the matched constructor's declared input
   sorts for everything below it. E-class ids come from one global counter, so
   probing the wrong sort's table simply finds nothing.
2. **Mark** — worklist propagation from the map keys up the parent relation
   built in pass 1.
3. **Build** — a sweep over the affected e-classes in postorder, copying every
   e-node whose children already have copies (`lookup_or_insert` per e-node;
   the first copy of a class names it, later ones union into it). One sweep
   finishes the acyclic case; the sweep repeats while it makes progress, which
   is what lets a grounded cycle close. Anything still uncopied when progress
   stops is an ungrounded cycle and is reported. Containers are rebuilt through
   `ContainerValues::rebuild_val_with` with a remap table, and nothing is
   interned until every value inside the container resolves, so a blocked
   container leaves no half-substituted copy behind.

### What egglog had to expose

Nothing substitution-specific: three general pieces of e-graph introspection,
after which the whole primitive is ordinary out-of-tree code.

* `Read::enodes_for_eclass` — indexed lookup of the constructor rows whose
  output column is a given e-class, instead of scanning the table. Cherry-picked
  from <https://github.com/egraphs-good/egglog/pull/934> (still open), together
  with the `core-relations` `ExecutionState::for_each_matching_col` and
  `egglog-bridge` `TableAction::for_each_output_value` it rests on.
* `Read::constructor_schema` / `Read::function_schema` / `Read::table_subtype` —
  a table's declared signature and subtype, from inside a primitive body.
  `EGraph::functions_iter` already exposes this from `&EGraph`, but a primitive
  only sees the state wrapper, and those carried no sort information at all.
  The e-graph passes its `&TypeInfo` into each execution as an
  `ExternalContext`, so the borrow lasts exactly that operation.
* `Core::map_container` — map a container value's contents and intern the
  result, over the existing `ContainerValues::rebuild_val_with`. Out-of-tree
  code cannot go through `Core::register_container`, which needs to name the
  container's Rust type.

Two things it did **not** need to expose, worth recording because they were the
expected blockers: `TypeInfo::get_arcsorts_by` is already public, so the type
constraint can enumerate the declared `Map` and eq-sorts itself; and a sort's
kind is recoverable from the public `Sort::value_type` and `Sort::inner_sorts`,
so a `Map` sort can be identified without downcasting to `MapSort` (whose
`ContainerSort` impl sits behind a private wrapper type).

### Known limitations

* `R` and `K` must be eq-sorts, and the map's key and value sorts must be
  identical: a substitution that replaced a `K`-sorted child with a value of a
  different sort would produce an ill-typed row.
* A cycle in the substituted region with no grounded e-node is rejected rather
  than copied, as described above.
* No bound on snapshot size — a root that reaches the whole e-graph copies as
  much of it as the substitution affects.
* Values are assumed canonical, which holds at the top level (egglog rebuilds
  after every command) and in a `:naive` rule head. Term-encoding mode, where
  canonicalization goes through a per-sort union-find table rather than the
  backend's, is untested.
* Proof mode is unsupported: the copied rows carry no justification. This is
  rejected rather than silently wrong — `egglog_experimental::subst` errors with
  `ProofsIncompatibleApi` (from `EGraph::update`), and the primitive is
  registered without a proof validator, so a program that uses it under
  `--proofs` or `--term-encoding` is refused with "primitive operation lacks a
  validator function".
* Tests live in `tests/subst.rs` rather than a `tests/*.egg` file, so they skip
  the `files` harness's desugar / term-encoding / multi-thread variants.
* A failing substitution reaches an egglog program as the generic
  "primitive panicked", with the reason in the log. Registering a custom panic
  message needs `egglog_bridge::EGraph::new_panic`, and egglog exposes no
  accessor for its backend; a `Write::panic_with(message)` would fix it.
* The constructor list is rebuilt from the table schemas on every call, which is
  O(tables) per substitution. Fine at the scale of a typical program, and it is
  what keeps the primitive correct as an e-graph gains constructors.
