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

**Decided:** generic definitions are limited to host primitive signatures and
host sort families. Tables, computed `Primitive` bodies, and user equality
sorts remain concrete; frontends may specialize generic user code before this
boundary. Host descriptors assert an available compatible implementation;
they do not supply native code. Builtins remain implicitly available, so calls
do not have to resend their descriptors.

`Declaration` has `HostSortFamily` and `HostPrimitive` arms, sharing the existing
documentation and provenance fields. A family records its name and arity:
nullary families such as `i64` use `PrimSort`, while positive-arity families
such as `Vec` and `Map` use `Container` with exactly that many arguments.
Function types remain structural `FuncSort`s. Family names share the sort
namespace with `EqSort`; callable names occupy a separate namespace.

`HostPrimitive` selects an ordinary `GenericSignature` or the dedicated
`FunctionApplication` typing form. A signature has an ordered type-parameter
binder, fixed inputs, a required output, and an optional homogeneous varargs
tail. It uses the existing sort arena with signature-only `Sort.var` indices.
Parameter labels are diagnostic: changing their spelling does not change the
definition. A shared pattern is interpreted independently in each signature's
binder; neither arena sharing nor export combines binders or substitutions.
Compatibility compares ordered binder positions and structural signatures.

Python already separates generic declarations from concrete expression types.
Its [signatures](https://github.com/egraphs-good/egglog-python/blob/ff72f601a972ca1eb7cb0a1d299813f5d65b1a14/python/egglog/declarations.py#L752-L791)
support type variables and a repeated argument type. Useful test cases are:

```text
map-get<K,V>(Map<K,V>, K) -> V
map-empty<K,V>() -> Map<K,V>
vec-of<T>(T...) -> Vec<T>
vec-map<T,U>((T) -> U, Vec<T>) -> Vec<U>
```

Each actual call supplies concrete argument and result sorts. Matching all of
them must determine every parameter consistently, including parameters found
only in the result: `map-empty() : Map<i64,String>` determines both parameters,
and `vec-of() : Vec<String>` determines its element type. In contrast,
`count<T>(...T) -> i64` with zero arguments leaves `T` undetermined and is
rejected. There is no call-level type-argument list, implicit conversion,
subtyping, or overload search.

Node/value sorts, lambda parameter sorts, cost sorts, and concrete declaration
signatures must be recursively closed. Creation and ordinary response sort
arenas contain no variables; a nested exported `Program` may include signature
patterns. CEL checks direct bounds, variable roots, and declared family uses.
Recursive closedness, binder scope, signature matching, family resolution, and
compatible descriptor resends remain semantic checks, not implemented yet.

**Decided:** each core callable has one unique name across user and host
definitions; the core does not select from same-name overloads. Frontends lower
overloaded syntax such as `+` to the appropriate unique callable name and make
conversions explicit before this boundary. Generics remain: a call instantiates
one named generic definition, rather than choosing an overload. No concrete
naming convention is chosen here.

`FunctionApplication` describes a named primitive called through normal `Call`:
the first argument has a concrete function type, remaining arguments match its
parameter sorts, and the call has its result sort. It needs no heterogeneous
type packs. This follows Python's
[application special case](https://github.com/egraphs-good/egglog-python/blob/ff72f601a972ca1eb7cb0a1d299813f5d65b1a14/python/egglog/runtime.py#L522-L538).
For `PartialCall`, captured argument sorts plus the resulting `FuncSort.params`
form the effective complete argument list; `FuncSort.result` supplies its result.
Apply the target's typing form to that complete call, including varargs or
function application, and require every generic parameter to be determined.
The existing relation-capability restriction still applies.

Complete `Freeze` exports include these descriptors and their signature patterns,
even when unused; freezing a fresh empty handle therefore exposes its ambient
catalog. Definitions-only filtering is deferred. Saved catalogs can support
binding generation, but native implementation, codec, and execution-capability
compatibility must be established by the host; matching descriptors alone cannot
establish it.
No runtime catalog adapter or generated high-level bindings are implemented.

### High-level bindings and language metadata

Protobuf codegen produces message classes, not ergonomic Egglog APIs. Planned
high-level generators use builtin and user declarations to produce Python/Rust
symbolic APIs and Egglog source. For example, one signature might be presented
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
points (including datatype groups), and validation remain to be designed.
This is separate from existing diagnostic locations/documentation; it does not
add another copy of those fields.

**Decided:** freeze each language's metadata block when first supplied for a
definition. An absent language on a later compatible redeclaration makes no
assertion and removes nothing; another language may first be supplied later.
A subsequent block for an already-supplied language must match the fixed block.
Adding or changing a same-language alias after that first block is rejected.
Presentation metadata is independent of semantic definition identity.
No metadata wire layout or runtime implementation is chosen yet; matching and
normalization details remain to be specified.

**Decided:** without a Python/Rust presentation block for a definition, generate
plain symbolic types and free functions with API identifiers derived from core
names. Behind those identifiers, preserve exact core names, signatures, and
argument order; do not infer operators or receivers. Cross-declaration Python/Rust
binding collisions (explicit/explicit, explicit/derived, or derived/derived) are
target-language generation errors, not declaration-installation errors. Generators
must error, not fall back, overwrite, or rename bindings. Engine installation still
rejects malformed individual metadata and conflicting resupply of one declaration's
fixed language block. These defaults are derived output, not supplied metadata:
they install or freeze no block, so later explicit metadata
remains that language's first supply. The exact naming/normalization algorithm
is undecided; high-level generators and metadata wire layout are unimplemented.

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
  children use an arena index or an installed name. An absent name adds no
  binding; an unmatched entry without a name is anonymous. A present empty name
  retains the default ruleset. Named roots retain their
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
  Resending an already-installed named parent may give a matched anonymous
  child its first name, preserving that occurrence and its rule state. Match
  bodies and sharing before applying the new binding. Each occurrence may have
  only one name: renaming it, assigning two different names to one occurrence,
  or reusing a name bound to another occurrence is an error. An omitted name
  does not remove an existing binding. Equal anonymous bodies alone never
  establish a match; complete export preserves each occurrence's assigned name.
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
  builtin declarations. A call's unique name selects its definition; argument
  and result sorts check that signature, including any generic instantiation.
  Missing names and signature mismatches are errors. Full definition resends are
  optional compatibility checks: identical definitions are no-ops, conflicts
  are errors. User definitions have no signature-only imports; host descriptors
  are complete compatibility assertions about external implementations.
  This is specified in the schema comments; runtime enforcement remains
  unimplemented. Each payload still includes every referenced node/sort arena
  entry; indices are local to that message. An `EqSort` entry also idempotently
  declares its name. Standalone
  exports retain all installed definitions and their dependencies. Host binding
  remains unimplemented.

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

This contract is not implemented. `HostSortFamily` and `HostPrimitive` provide
the generic catalog layout; host binding, semantic validation, and full export
still need implementation. The proposed rule arena remains a separate layout
question. Custom value reconstruction requires trusted codecs. No ordinary
native pure non-equality self-cycle has been established; arbitrary host-codec
cycles remain unproven. `Freeze` must fail when required state cannot be
represented, not silently omit it or claim a complete export.

**Recording — decided:** an adapter may opt into recording original `Program`
requests, handle creation/configuration, and their outcomes in order. Recording
is off by default and separate from current-state export; no runtime recorder or
new RPC is supplied here. Preserve request boundaries and request-local arenas;
naively concatenating Programs changes references and action identity scopes.
Record failures and completed outputs as well as successes. Earlier effects can
survive failure, so this is an execution record, not a promise of exact replay
or an engine checkpoint.

### Reporting and timing attribution

**Decided:** `RunProgramRequest.profile` is off by default. Off disables optional
diagnostic collection and retention, not just output; scheduler-required counters,
progress, and stopping checks are unchanged. This is a schema contract, not an
implemented collection-off path or a performance claim.

Each completed top-level `Run` returns `RunOutcome` (`updated`, `can_stop`);
`Repeat` and `Saturate` return `LoopOutcome` (any update, body-execution count,
termination reason). Nested control outcomes are folded into their enclosing
loop, not emitted separately. Zero-iteration loops still have an outcome.
Historical `can_stop` values are not ANDed into a loop's stopping status.

All requested observations remain in completion order, including inside loops
and with profiling off. Each output has a `CommandLocation`: a static command
path plus one zero-based iteration coordinate per enclosing loop. Errors locate
the innermost active command independently of their most specific source span.
A failed loop has no outcome, but its completed observations and earlier effects
remain; execution and termination semantics are unchanged.

Opt-in `ProfileSummary` aggregates by static `Run` site and response-local rule
occurrence. It counts entered invocations and retains no per-iteration history.
Run sites own search/apply, merge, and rebuild totals; group membership does not
duplicate work. Rule metrics are breakdowns, not additional elapsed time.
Present metrics cover all observed work in their aggregate; an unavailable total
is absent, not a known subset or zero. A failed request has an explicitly
incomplete summary, including observed work from a failing Run; a successful
empty summary is complete. Completeness does not promise every optional metric.

`RunProgramResponse.rules` gives each attributed occurrence one local index,
shared by profile rows and errors even with profiling off. A `RuleAttribution`
routes from a request-local ruleset or installed named root, through composition
child positions to a leaf rule ordinal. This covers retained anonymous leaves
without invented names or a new rule arena. Names and spans are diagnostic;
distinct equal occurrences stay distinct, and both directions of an authored
`BiRewrite` share one entry. Path resolution and identity checks remain normative
semantic requirements. Detailed traces and runtime implementation are deferred.
Only referenced catalog entries are returned; profiling off without a rule error
returns none.

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

- **Host binding:** implement catalog discovery and compatibility checks for
  native implementations, execution capabilities, value codecs, and cost models.
  Descriptions do not transport executable host code. Include custom values
  with explicit e-class children in encoding/remapping/rebuild tests; generic
  inspection stays inert.
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
