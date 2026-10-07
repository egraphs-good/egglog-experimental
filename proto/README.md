# Protobuf IR draft

This is a work-in-progress design for a shared Egglog IR that text, Python,
Rust, and other frontends could produce directly. It is being shared for
feedback, not as a finished API. The wire format may change during review.

Start with [egglog.proto](egglog/v1/egglog.proto). Its validation annotations
and comments are the specification. The main pieces are:

- Flat expression, sort, and ruleset arenas, with explicit shared references.
- Immutable declarations and rulesets, separate from ordered commands.
- Native scalar, container, and function values. Custom values carry opaque
  bytes and explicit child references; symbolic computation remains a call.
- Complete current-state export as an ordinary `Program`, including definitions,
  logical data, cycles, and empty e-classes. This is not an engine checkpoint.

There is no engine lowering, runtime, or service implementation yet. CEL checks
directly expressible constraints, not full typing, binding, effects, or cycle
validity. The remaining requirements are normative comments. CEL can exhaust
its evaluation budget on large valid inputs; that is inconclusive, not proof
that a program is invalid. Frontend parity has not been demonstrated end to end.

## Design decisions and open questions

Decisions are marked below; the other questions remain open. The schema's
comments and annotations remain the normative contract.

### Shared builtin definitions and type checking

Proposed discovery model: builtins are implicitly available, and an EGraph
query exports their portable declarations with optional language metadata.
Export generic families and all overloads, not just instantiated sorts/tables
or a map keyed only by name. A saved export can drive binding generation
without a live EGraph at import time. The query and descriptor format remain
to be designed; declaring a signature does not supply its native implementation.

Today `Container` and `FuncSort` describe concrete types, each node supplies its
resolved sort, and host primitives are ambient. `Primitive` declares a computed
body, not a host signature. There are no declaration-level type variables or
generic signatures.

Python already separates generic declarations from concrete expression types.
Its [signatures](https://github.com/egraphs-good/egglog-python/blob/ff72f601a972ca1eb7cb0a1d299813f5d65b1a14/python/egglog/declarations.py#L752-L791)
support type variables and a repeated argument type. Useful test cases are:

```text
map-get<K,V>(Map<K,V>, K) -> V
map-empty<K,V>() -> Map<K,V>
vec-of<T>(T...) -> Vec<T>
unstable-vec-map<T,U>((T) -> U, Vec<T>) -> Vec<U>
```

Specify type-constructor arities, type-variable scope, substitution, overload
resolution, and how empty containers obtain their types. The relationship
between exported host definitions and submitted declarations remains open.
Separate frontend inference/conversions from checking the resolved IR. This
need not introduce generic user-defined equality sorts.

**Decided:** use ordinary generic signatures, including homogeneous varargs,
with a dedicated typing rule for function application: arguments match the
function's parameter sorts, and the call has its result sort. Do not add
heterogeneous type packs to the signature language. This follows Python's
[application special case](https://github.com/egraphs-good/egglog-python/blob/ff72f601a972ca1eb7cb0a1d299813f5d65b1a14/python/egglog/runtime.py#L522-L538).
`Lambda` and `PartialCall` retain their structural typing rules. Binding
generation remains a goal; the decision does not choose a Rust arity strategy.

### High-level bindings and language metadata

Protobuf codegen produces message classes, not ergonomic Egglog APIs. Could
builtin and user declarations also generate Python classes, Rust methods, and
Egglog source? For example, one signature might be presented
as Python `m[k]` and Rust `m.get(k)`, with the same underlying call.

**Decided:** start with typed metadata for Rust, Python, and Egglog source only;
defer arbitrary extension payloads and other languages. Egglog presentation
metadata is where datatype grouping and related surface syntax belong, rather
than adding a second semantic datatype declaration. This describes how to
present definitions, not original formatting or source round-tripping.

Python's [declarations](https://github.com/egraphs-good/egglog-python/blob/ff72f601a972ca1eb7cb0a1d299813f5d65b1a14/python/egglog/declarations.py#L311-L324)
distinguish constructors, methods, class methods, properties, and preserved host
methods. Potential metadata includes module/type names, receiver placement,
operators, argument order, defaults, and conversions. Exact fields, attachment
points (including datatype groups), validation, and treatment in declaration
identity remain to be designed. This is separate from the existing diagnostic
locations/documentation; it does not add another copy of those fields.

**Decided:** initially generate the symbolic declarations and expression-building
API. Host methods such as `Map.value` and host conversions remain ordinary
handwritten Python. Descriptors do not transport native implementations or
arbitrary method bodies. A useful end-to-end test: export Luminal's Rust-defined
IR, generate its Python API, author a Python rewrite, and consume that rule in
Rust without duplicating the IR declarations.

### Unnamed rulesets and declaration reuse

- **Ruleset identity — decided:** immutable rulesets have optional names and
  share state by occurrence identity. The current provisional wire layout uses
  `Program.rulesets`, with a rule-list or composition body. Runs and composition
  children use an arena index or an installed name. An absent name is anonymous;
  a present empty name retains the default ruleset. Named roots retain their
  reachable anonymous children and rule state across requests. Compatible
  presentations of the same name compare internal sharing before identifying
  corresponding occurrences. Resends must then preserve sharing across all
  named roots.
  Conflicting identity requirements are errors. A matched index reuses the
  retained occurrence everywhere it is referenced.
  Other anonymous entries are fresh per submission, even when their bodies
  are equal. Repeated references and loop iterations within one submission
  share state. Composition cycles are invalid. These contracts are specified
  in the schema; runtime enforcement remains unimplemented.

  ```text
  request 1: rulesets[0] = unnamed rule list
             rulesets[1] = name "opt", composition [index 0]
             run(index 1)
  request 2: run(name "opt")  # retains the same unnamed child and rule state
  request 3: rulesets[0] = equal unnamed rule list; run(index 0)  # fresh
  ```

  This is the same indirection principle as a persistent top-level capture:
  its name survives while arena indices remain local. Existing captures lower
  to nullary functions and sets; this does not add general expression bindings.
  Whether resending a named parent can give a new name to its retained
  anonymous child remains open.
- **Once per Run — decided:** flatten transitive inclusion in order, considering
  each rule occurrence only at its first inclusion. Distinct equal rules remain
  independent. Separate Runs and loop iterations select independently; this
  does not limit firings from query matches or override the scheduler.
- **Rule-level sharing — proposed:** a rule arena would let multiple rulesets
  reference the same rule occurrence directly, without copying it. This is a
  layout proposal only; the current schema still requires `RuleDecl` names and
  assigns each rule occurrence to a leaf ruleset. No rule arena is implemented.
- **Declaration reuse — decided:** programs may refer to definitions already
  installed on the same e-graph handle without resending them. Builtin calls
  resolve against implicitly available host primitives without requiring
  builtin declarations. Calls resolve by name and argument/result
  sorts; missing or ambiguous matches are errors. Full definition resends are
  optional compatibility checks: identical definitions are no-ops, conflicts
  are errors. There are no signature-only imports. This is specified in the
  schema comments; runtime enforcement remains unimplemented. Each payload
  still includes every referenced node/sort arena entry; indices are local to
  that message. An `EqSort` entry also idempotently declares its name. Standalone
  exports retain all installed definitions and their dependencies. Host catalog
  discovery and its descriptor format remain open.

### Current-state export and optional recording

**Decided:** `Freeze` returns one complete current-state `Program`, with no
filtering and no separate snapshot message or loading instruction. Include all
installed declarations and sorts, named rulesets and their retained anonymous
children, and builtin descriptors, even when unused. Preserve occurrence sharing.
The commands reconstruct all logical data, including empty/unreachable classes,
constructor alternatives, function and relation rows, subsumption, captures, and
assigned row costs. Historical commands, scheduler instances, seminaive cursors,
reports, caches, and host resources are not part of this export.

The export is an ordered list of ordinary actions: one direct `Action.term` for
each canonical equality class (a unique Union containing its constructor rows),
relation insertions, function `Set`s including Unit outputs, `SetCost`s, then
constructor subsumption. It contains no queries, runs, loops, or other commands.
Values use exact payloads and shared class references;
function rows are writes, not calls to evaluate or extraction alternatives.
There is no need to extract a finite representative to construct a cyclic or
empty equality class. Every canonical function/cost key is written once, so
restoration into empty data does not depend on replaying conflict merges.
This normalized shape can be inspected without running its commands or decoding
opaque custom payloads.

**Action identity — decided:** direct actions in one execution of a command list
share their `Union` identity mapping, including across intervening observations
or other commands. Each loop-body iteration has its own mapping; nested lists
do not inherit the outer mapping, which resumes afterward. Each rule firing,
primitive/lambda invocation, and other command's evaluated inputs has its own
scope. Retained references follow canonical identity through intervening unions,
rebuilds, and runs. Queries neither read nor populate this mapping. Ordinary call
nodes remain shared syntax, not memoized values.

```text
nodes[0] = E: Union[]
commands = [Set(f(), index 0), Set(g(), index 0)]
# Both rows reference the same empty class in this execution.
# A new execution or a loop-body iteration allocates a fresh class.
```

An exported `Program.cost_sort` records the handle's immutable cost sort C;
normal requests may omit it. When present it is a compatibility precondition,
checked before installing definitions or running commands, not reconfiguration.
Restore by executing the export on a fresh, data-empty
handle with the same C and compatible host capabilities. Rules start with fresh
execution state. Against existing data the Program still uses ordinary action
semantics, without a restoration-equivalence guarantee.

This contract is not implemented. Complete builtin descriptors still need the
generic catalog layout discussed above; `Primitive` cannot stand in for a host
signature. The proposed rule arena also remains a separate layout question.
Custom value reconstruction requires trusted codecs, and pure non-equality value
cycles have no selected ordinary-action construction. These are explicit support
gaps, not permission to silently omit definitions or values or to claim a
complete export. `Freeze` must fail when required state cannot be represented.

**Recording — decided:** an adapter may opt into recording original `Program`
requests, handle creation/configuration, and their outcomes in order. Recording
is off by default and separate from current-state export; no runtime recorder or
new RPC is supplied here. Preserve request boundaries and request-local arenas;
naively concatenating Programs changes references and action identity scopes.
Record failures and completed outputs as well as successes. Earlier effects can
survive failure, so this is an execution record, not a promise of exact replay
or an engine checkpoint.

### Reporting and timing attribution

Reconsider reporting separately, including timings, ruleset/rule attribution,
nested loops, repeated placements, and command-output association. The current
flat outputs and name-based report/error fields are provisional and cannot
identify anonymous ruleset occurrences. No reporting representation is chosen
by the ruleset-arena decision; do not invent occurrence names or discard data
to fit those fields. Execution progress and loop termination remain as specified.

### Shared Python/Rust memory

Should Python use independent generated messages and pass bytes, convert them
to Rust objects, or expose one Rust-owned arena through PyO3? The wire format
does not choose an in-process representation. Sharing ownership could avoid
rebuilding the same graph, but needs explicit mutation, lifetime, and threading
rules; no zero-copy or performance claim has been established.

[PyO3 supports Rust-backed Python classes and shared ownership](https://pyo3.rs/main/class.html#no-lifetime-parameters).
That is a possible implementation route, not something the current generators
provide automatically. Compare construction, traversal, crossing the boundary,
and memory use on the same graph before choosing.

### Remaining review work

- **Host catalog:** how do both sides discover compatible primitive signatures,
  execution capabilities, value codecs, and cost models? Descriptions do not
  transport executable host code. Include custom values with explicit e-class
  children in encoding/remapping/rebuild tests; generic inspection stays inert.
- **Semantic conformance:** implement and test the checks beyond CEL: types,
  binding, contexts/effects, cycles, and declaration equivalence. In particular,
  equivalent resends may change ordinary syntax sharing but must preserve
  `Union` identity topology. The contract is specified; enforcement is not yet
  implemented. This does not propose another Python-only validator.
- **Frontend coverage:** exercise text, Python, and Rust producers against the
  same cases. Document which file-I/O, expected-failure, and printing/statistics
  commands are frontend/test-harness conveniences versus shared operations.
  Keep the selected literal extraction-count restriction explicit.
- **Deferred:** proofs. Current-state export/restoration and optional recording
  are specified above but have no runtime implementation.

A small next experiment: describe `Vec`/`Map` and the signatures above once,
generate Python and Rust expression APIs, and compare their resolved IR and
type errors. Treat function application and the Luminal roundtrip as additional
coverage, not evidence already established by wire roundtrip tests.

## Generated previews and checks

[Python](../gen/python/egglog/v1/egglog_pb.py) and
[Rust](../gen/rust/egglog/v1/egglog.v1.rs) message sources are checked in for
inspection. They are not an installable SDK or an integrated Rust crate.
Python uses `protobuf-py`, with `protovalidate` for validation; versions are
locked in `uv.lock`. The Rust messages use `prost` (tested with 0.14.4).
Imported Rust validation definitions also require `prost-types`. No gRPC
transport is generated or required.

To regenerate, install Buf (tested with 1.73.0), uv, and Rust/Cargo, then run
from the repository root:

```sh
cargo install --locked protoc-gen-prost --version 0.5.0
make proto-gen
make proto-lint
```

These use local generator plugins. Initial tool/dependency downloads may need
network access. Commit generated sources together with schema changes.
On a clean checkout, `make proto-drift` regenerates and detects tracked changes.

A Python wire/validation smoke check, after `uv sync --locked`:

```sh
uv run python - <<'PY'
from gen.python.egglog.v1 import egglog_pb as ir
from protobuf import Oneof
from protovalidate import validate

program = ir.Program(
    ir_version=1,
    sorts=[ir.Sort(kind=Oneof("prim", ir.PrimSort(name="i64")))],
    nodes=[ir.Node(sort_id=0, kind=Oneof("primitive_value",
        ir.PrimitiveValue(value=Oneof("i64", 42))))],
)
validate(program)
assert ir.Program.from_binary(program.to_binary()) == program
PY
```

This checks encoding and annotated constraints, not Egglog execution. With no
commands, the example does not request any evaluation.

The imported `buf.validate` sources are generated from Protovalidate, pinned in
`buf.lock`. Copyright 2023–2026 Buf Technologies, Inc.; distributed under the
[Apache-2.0 license](LICENSE.protovalidate).
