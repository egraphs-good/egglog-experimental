# Protobuf IR draft

This is a work-in-progress design for a shared Egglog IR that text, Python,
Rust, and other frontends could produce directly. It is being shared for
feedback, not as a finished API. The wire format may change during review.

Start with [egglog.proto](egglog/v1/egglog.proto). Its validation annotations
and comments are the specification. The main pieces are:

- Flat expression, sort, rule, and ruleset arenas, with shared references.
- Immutable declarations and rulesets, separate from ordered commands.
- Native scalar, container, and function values. Custom values carry opaque
  bytes and explicit child references; symbolic computation remains a call.
- Complete current-state export as a snapshot of logical options and an ordinary
  `Program`, including definitions, logical data, cycles, and empty e-classes.
  This is not an engine checkpoint.
- Existing proof requests and structured results from the current proof engine,
  with proof enablement selected in `EGraphOptions`.

An initial in-process bytes adapter lives in
[`src/protobuf.rs`](../src/protobuf.rs); its supported slice is described below.
It is not frontend conformance or a complete service implementation. CEL checks
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

`Declaration` has `EqSort`, `HostSortFamily`, and `HostPrimitive` arms, sharing
documentation and provenance fields. `Sort.eq` references an equality-sort name;
`Sort.family` applies a host family through `HostSort{name,args}`, with exactly
its declared arity, including zero for `i64` or `Unit`. References never declare
definitions. Builtin families and installed sorts need not be redeclared.
Function types remain structural `FuncSort`s. Family names share the sort
namespace with equality sorts; callable names occupy a separate namespace.
Type-use spans may remain on `Sort`, but docs and bindings belong to definitions.

`HostPrimitive` selects an ordinary `GenericSignature` or the dedicated
`FunctionApplication` typing form. A signature has an ordered type-parameter
binder, fixed inputs, a required output, and an ordered `varargs` pattern.
An empty pattern means no tail; a one-element pattern means homogeneous varargs;
a wider pattern repeats as an ordered group. The flat argument count after the
fixed prefix must be a multiple of the nonempty pattern's width. Width and order
are semantic, including `[T, T]`; there is no tuple/group expression node.
It uses the existing sort arena with signature-bound `Sort.var` indices.
Parameter labels are diagnostic: changing their spelling does not change the
definition. A shared pattern is interpreted independently in each signature's
binder; neither arena sharing nor export combines binders or substitutions.
Compatibility compares ordered binder positions and structural signatures.

This draft changes field 4 from a singular `Arg` to `repeated Arg`, with
coordinated immutable schema, engine, and frontend pins, not a deployed stable
old-wire guarantee. Canonical zero/one-tail binary encodings are unchanged.
Generated Rust changes `Option<Arg>` to `Vec<Arg>`, Python changes `Arg | None`
to `list[Arg]`, and ProtoJSON changes the tail object to an array. Old receivers
are unsafe for wider patterns: they collapse or merge repeated field occurrences
and lose the pattern width. Previously duplicated singular-field encodings also
change meaning. `ir_version = 1` does not detect this draft incompatibility;
all consumers must migrate together. The schema can describe grouped tails;
native matching, Map registration, and frontend generation are separate gates.

Python already separates generic declarations from concrete expression types.
Its [signatures](https://github.com/egraphs-good/egglog-python/blob/ff72f601a972ca1eb7cb0a1d299813f5d65b1a14/python/egglog/declarations.py#L752-L791)
support type variables and a repeated argument type. Useful test cases are:

```text
map-get<K,V>(Map<K,V>, K) -> V
map-empty<K,V>() -> Map<K,V>
map-of<K,V>((K,V)...) -> Map<K,V>  # flat key,value arguments, not tuple values
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
compatible descriptor resends are semantic checks. The executable subset below
implements these for its supported scalar/Vec signatures and declarations.

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
For `PrimitiveValue.partial_call`, captured argument sorts plus the resulting
`FuncSort.params` form the effective complete argument list; `FuncSort.result`
supplies its result.
Apply the target's typing form to that complete call, including varargs or
function application, and require every generic parameter to be determined.
The existing relation-capability restriction still applies. A `Lambda` stores only
captures and its body; its enclosing `FuncSort` supplies parameter and result sorts.

Complete `Freeze` exports include these descriptors and their signature patterns,
even when unused; freezing a fresh empty handle therefore exposes its ambient
catalog. Definitions-only filtering is deferred. Saved catalogs can support
binding generation, but native implementation, codec, and execution-capability
compatibility must be established by the host; matching descriptors alone cannot
establish it.
The initial engine-owned scalar catalog path below is implemented; complete
catalog export, generic families and generated high-level bindings are not.

### High-level language bindings

Protobuf codegen produces message classes, not ergonomic Egglog APIs. Planned
high-level generators use builtin and user declarations to produce Python/Rust
symbolic APIs and Egglog source. For example, one signature might be presented
as Python `m[k]` and Rust `m.get(k)`, with the same underlying call.

**Decided:** start with typed bindings for Rust, Python, and Egglog source only;
defer arbitrary extension payloads and other languages. Egglog presentation
bindings are where datatype grouping and related surface syntax belong, rather
than adding a second semantic datatype declaration. This describes how to
present definitions, not original formatting or source round-tripping.

Python's [declarations](https://github.com/egraphs-good/egglog-python/blob/ff72f601a972ca1eb7cb0a1d299813f5d65b1a14/python/egglog/declarations.py#L311-L324)
distinguish constructors, methods, class methods, properties, and preserved host
methods. `SortBindings` now attaches to `EqSort` and `HostSortFamily`;
`CallableBindings` attaches to callable `Declaration` arms through `bindings`.
Both have optional Python, Rust, and Egglog blocks, without duplicating
locations/documentation.
Type bindings carry qualified display paths and optional parameter labels in
core family order. Callable views carry explicit surface-to-core input mappings;
owner sort patterns identify semantic types, not their display paths.

**Decided:** freeze each language's bindings block when first supplied for a
definition. An absent language on a later compatible redeclaration makes no
assertion and removes nothing; another language may first be supplied later.
A subsequent block for an already-supplied language must match the fixed block.
Adding or changing a same-language alias after that first block is rejected.
Presentation bindings are independent of semantic definition identity.
Repeated same-name supplies in one Program are reconciled before interning;
agreeing blocks are allowed. Compare referenced sort/default structures after
arena remapping, without recursively comparing their presentation bindings.
Default-root comparison preserves shared versus distinct `Union` occurrences.
The supported adapter declarations implement this runtime matching;
target-language generation and name normalization remain frontend work.

**Decided:** without a Python/Rust presentation block for a definition, generate
plain symbolic types and free functions with API identifiers derived from core
names. Missing bindings never hide a definition; explicit hiding is outside
this draft's scope, with no special meaning assigned to an empty block.
Behind those identifiers, preserve exact core names, signatures, and
argument order; do not infer operators or receivers. Cross-declaration Python/Rust
binding collisions (explicit/explicit, explicit/derived, or derived/derived) are
target-language generation errors, not declaration-installation errors. Generators
must error, not fall back, overwrite, or rename bindings. Engine installation still
rejects malformed individual bindings and conflicting resupply of one declaration's
fixed language block. These defaults are derived output, not supplied bindings:
they install or freeze no block, so later explicit bindings
remain that language's first supply. The exact naming/normalization algorithm
is undecided; high-level generation remains frontend work. Runtime checks for
the bounded executable declaration/default subset are implemented below.

Python views distinguish free functions, initializers, methods, class methods,
properties, class variables, and ownerless constants. A `CONSTANT` view names a
nullary concrete expression (`C`), with a qualified path and no owner, receiver,
parameters or mutated input. Its path is nonempty, but the final component may
be empty to preserve an empty constant name; preceding components stay nonempty.
It does not evaluate a body during installation or
export. A nullary `FUNCTION` remains callable (`C()`); arity never implies a
constant view. The bounded runtime acceptance below does not establish frontend
generation.
Ordered parameter records give core-input
positions, names, and optional default expressions. Initializers derive `__init__`
without storing a path. Receivers are mapped inputs; initializers/class methods
introduce no core `self`/`cls` argument. Only an
initializer requires its result to match its owner. An optional mutated-input
index also supports free functions: replace that wrapper with the core result
and return Python `None`, without changing the core signature or effects.

**Decided:** defaults are closed symbolic expressions, not captured runtime
values: calls and lambda-bound variables are allowed, but free/query variables
are not. Never evaluate defaults during installation or export. Their node sorts
are concrete and may constrain generic call substitution when used. Expand an
emitted call's omitted defaults together, with fresh `Union` identities and
preserved internal sharing; then check the actual use's binding/effect rules.

Rust views distinguish free/associated/receiver/trait forms through their fields.
Borrowed impl `Self` and receiver borrowing are separate: `impl Add for &T` with
`self` differs from `impl Trait for T` with `&self`. Parameters and trait arguments
record wrapper ownership; an optional associated output name such as `Output`
maps to the core result. Arbitrary associated types, lifetimes, const generics,
mutable borrowing, and executable host bodies are outside this limited layout.

Ordinary varargs use one final logical parameter slot for the whole flat tail,
regardless of pattern width, with no default, receiver, or redundant varargs flag.
`FunctionApplication` instead has a function input and a heterogeneous tail
derived from its concrete `FuncSort`.
A structural-function owner marker represents `__call__` without a fake family
or new type-pack binder. Other owner/trait patterns use only the enclosing
callable's existing generic binder; bindings cannot introduce generic nodes.
Egglog views carry symbols and constructor datatype membership, grouped by the
existing output equality sort, without new datatype or text-overload semantics.

`Freeze` retains supplied blocks and their bindings-only dependencies, remapping
arenas without executing defaults or freezing derived wrapper choices. CEL checks
direct shapes, positions and bounds. Recursive default closure, owner/receiver
typing, bindings compatibility, and target-language generation remain normative
requirements, not implemented semantic checks.

**Decided:** initially generate the symbolic declarations and expression-building
API. Host methods such as `Map.value` and host conversions remain ordinary
handwritten Python. Descriptors do not transport native implementations or
arbitrary method bodies. A useful end-to-end test: export Luminal's Rust-defined
IR, generate its Python API, author a Python rewrite, and consume that rule in
Rust without duplicating the IR declarations.

### Unnamed rulesets and declaration reuse

- **Ruleset identity — decided:** immutable rulesets have optional names and
  share state by occurrence identity. The wire layout uses
  `Program.rulesets`, with a rule-list or composition body. Runs and composition
  children use an arena index or an installed name. An absent name adds no
  binding; an unmatched entry without a name is anonymous. A present empty name
  retains the default ruleset. Named roots retain their
  reachable anonymous children and rule state across requests. Compatible
  presentations of the same name compare internal sharing before identifying
  corresponding occurrences. Resends must then preserve both rule and ruleset
  sharing across all named roots, without merging distinct occurrences or
  splitting shared ones. Rule labels do not participate in matching.
  Duplicate named-root presentations cannot collapse distinct rule-arena entries.
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
  bodies and sharing before applying the new binding. Each ruleset occurrence may have
  only one name: renaming it, assigning two different names to one occurrence,
  or reusing a name bound to another occurrence is an error. An omitted name
  does not remove an existing binding. Equal anonymous bodies alone never
  establish a match; complete export preserves each occurrence's assigned name.
- **Once per Run — decided:** flatten transitive inclusion in order, considering
  each rule occurrence only at its first inclusion. Distinct equal rules remain
  independent. Separate Runs and loop iterations select independently; this
  does not limit firings from query matches or override the scheduler.
- **Rule-level sharing — decided:** `Program.rules` holds `RuleDecl` occurrences;
  each `RuleList.rules` is an ordered list of arena indices. Different leaves
  and repeated positions may reference the same occurrence; equal separate
  entries remain distinct. Names are optional diagnostic labels, may repeat,
  and provide no rule lookup or identity. A rule matched through an installed
  named root is reused even in a newly added leaf that references its index.
  A wholly unanchored resubmission remains fresh. References share the rule and
  its rule-owned state across groups/Run sites; distinct scheduler instances and
  their scheduler-owned state remain separate. CEL checks direct indices;
  matching and execution are unimplemented.
  Only named roots retain rules across requests; unretained entries are omitted
  from `Freeze`, and arena membership alone never executes a rule.
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
  entry; indices are local to that message. Equality sorts are defined by
  `Declaration.eq_sort`, not by arena references. Standalone
  exports retain all installed definitions and their dependencies. Host binding
  remains unimplemented.

### Current-state export and optional recording

**Decided:** `Freeze` returns one `EGraphSnapshot{options,program}`, with complete
logical settings and an ordinary reconstruction `Program`, without filtering
or a special loading instruction. Include all
installed declarations and sorts, named rulesets and their retained anonymous
children and rules, and builtin descriptors, even when unused. Emit each retained
rule/ruleset occurrence once, remapping leaf indices and preserving sharing.
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

`EGraphOptions` records the immutable cost sort C, indexing creation's `sorts`
or the snapshot's `program.sorts`. C may be any supported closed sort, including
a custom equality sort. Ordinary Programs have no configuration precondition.
Creation accepts only sort declarations, resolves them and the closed type arena
before allocating a handle, and executes no Program. Its optional `threads` is a
resource request: absent selects receiver policy, zero requests automatic
parallelism, positive requests that count; unsupported requests fail creation.
Resources are not exported.

The current byte adapter honors this thread request using the native per-egraph
configuration API; clones retain that configuration. Wasm rejects counts above
one. An absent field leaves the native default unchanged. Creation's existing
i64 cost-sort and no-declaration limits still apply; native thread-pool resource
allocation behavior is unchanged.

`ConfigureEGraphResources` specifies live resource query/update over the same
bytes boundary. Its required operation selects an inert query or a thread-count
update (zero means auto, positive means exact). Success returns the effective
positive native count as uint64, not a requested value or frontend CPU estimate.
Unsupported updates fail before mutation; updates must preserve existing rule
cursors and logical state. Clone inherits the effective count, later updates are
handle-local, and resources remain outside snapshots. The protocol is specified
and implemented by `Engine::configure_resources`, using the native getter/setter
without cloning execution state. Invalid handles, missing/unknown operations and
unsupported requests fail explicitly. Immutable logical
options, future-rule defaults and report-policy controls are not resource fields.

Restore by remapping C's reachable closed sort graph and needed sort declarations
into a creation request, then executing the exported Program on that fresh handle
with compatible host capabilities. Unrelated generic signature patterns may stay
in the snapshot; do not copy its entire sort arena into the closed creation arena.
Rules start with fresh execution state. Against an existing handle the Program
still uses ordinary action semantics; callers must check options for any
restoration-equivalence guarantee.

This contract is not implemented. `HostSortFamily` and `HostPrimitive` provide
the generic catalog layout; host binding, semantic validation, and full export
still need implementation. Custom value reconstruction requires trusted codecs.
No ordinary native pure non-equality self-cycle has been established; arbitrary host-codec
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
Source fallback is expression, action, rule, then active command.
A failed loop has no outcome, but its completed observations and earlier effects
remain; execution and termination semantics are unchanged.

`PrintedFunction.table` identifies rows whose argument/output cells are ordinary
extracted values; relation outputs are Unit. Any cell without finite extraction
fails the whole command. Table statistics pair each exact response sort reference
with its distinct-value count, in input order followed by output.

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
child positions to a leaf rule ordinal, not a `Program.rules` index. The selected
list entry identifies the rule, including retained rules absent from the request.
Shared rules have one response catalog entry regardless of route. Names and spans
are diagnostic; distinct equal occurrences stay distinct, and both directions of
an authored `BiRewrite` share one entry. Path resolution and identity checks remain normative
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

### Existing proof engine

`EGraphOptions.execution_mode` selects ordinary execution (the default), term
encoding, proofs, or proof testing. Clone retains the mode and proof state.
The current byte adapter accepts only NORMAL; other or unknown mode values fail
creation before allocating a handle. Prove/ProveExists fail Program preparation
before any actions execute until native proof integration is implemented.
Snapshots retain the mode, but logical reconstruction does not preserve original
derivations. `Prove` uses the same conjunctive facts as `Check`; `ProveExists`
targets a constructor name without inserting a witness. Proof testing executes
checks as proof requests. Preserve native ordering: `Prove` can complete a helper
run and its effects before proof extraction fails. Successful proof requests
return the proof at the originating command location, including inside loops.

This draft leaves native maintenance `Run` emission, output locations, and
optional profiling attribution unresolved. CEL accepts nested `Run` payloads
as wire capacity only; it does not require their emission or select a reporting
policy. The authored-command reporting rules above do not settle this question.

`ProofResult` contains separate, inert term and proof arenas. Terms have no sort:
native proof propositions can describe a function row with inputs and output as
children. All eight native justifications are represented, including explicit
substitutions, shared premises, container normalization, and the `Eval` side
condition placeholder. Native IDs are remapped to result-local indices, so
inspection does not require a live e-graph. A native proof failure carries a
structured reason, independently of its diagnostic text.

CEL checks required fields, oneofs, direct reference bounds, unique substitution
names, and error-detail consistency. Shared decoders must additionally check
acyclicity and reachability with bounded-stack traversal. This is transport for
the existing checked/simplified proof, not a new proof engine or a standalone
checker; rule context and compatible host validators remain external. The
schema tests establish wire/CEL behavior only. Native execution and the existing
desugar/proof-checker-context treatment still require adapter integration and
conformance tests.

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
- **Frontend boundaries:** datatype/include/operator/default syntax lowers in
  the producer. Frontend CSV input decodes to ordinary declarations/actions;
  file and pretty output render structured observations. `function_size` and
  `function_values` use `PrintSize` and `PrintFunction` results respectively.
  Standalone `Check` responses support `check_bool`/`check_fail`: distinguish
  success from `CHECK_FAILED` and propagate other failures. General `fail`
  remains external test-harness logic, not a catch or rollback inside a Program.
  Frontend `push`/`pop` can use a `CloneEGraph` handle stack. Native extraction's
  best-count zero lowers to `variants = 1`; this IR accepts literal counts only.
  Exact graph-owned `lookup_function_value` results and values passed to custom
  cost callbacks are not `PrintFunction`'s extracted representatives; those
  remain host-adapter work, not a new RPC or a claim of full Python parity.
  These adapters and shared text/Python/Rust producer conformance tests remain
  unimplemented.
- Current-state export/restoration and optional recording are specified above
  but have no runtime implementation.

A small next experiment: describe `Vec`/`Map` and the signatures above once,
generate Python and Rust expression APIs, and compare their resolved IR and
type errors. Treat function application and the Luminal roundtrip as additional
coverage, not evidence already established by wire roundtrip tests.

## Generated previews and checks

[Python](../gen/python/egglog/v1/egglog_pb.py) and
[Rust](../gen/rust/egglog/v1/egglog.v1.rs) message sources are checked in for
inspection. The Rust messages are also the reusable `egglog-proto` crate at
`gen/rust`; its handwritten `Cargo.toml` and `lib.rs` include the generated
message file directly. Core pins a published revision of this leaf and exposes
it as `egglog::proto`; experimental consumes that re-export, not a second local
leaf dependency. Schema updates follow schema/leaf revision S → core revision C
→ experimental revision E, preserving one Rust message package identity.
Python packaging remains a later migration step.
Python uses `protobuf-py`, with `protovalidate` for validation; versions are
locked in `uv.lock`. The Rust messages use `prost` (tested with 0.14.4).
Imported Rust validation definitions also require `prost-types`. No gRPC
transport is generated or required.

### Initial executable Rust slice

`egglog_experimental::protobuf::Engine` exposes `create`, `clone_egraph`,
`destroy`, `configure_resources`, and `run`. Every method accepts encoded request
bytes and returns encoded response bytes. Decode failures and unknown handles are transport
errors; program failures are `RunProgramResponse.error`. Whole-program
validation occurs before installation, while runtime errors preserve completed
effects and observations. Native ASTs are transient lowering products.

The current executable subset is deliberately limited:

- Equality sorts, the five scalar host sorts and nested Vec applications; explicit constructor/function
  declarations with scalar static costs and merge bodies using values,
  old/new variables, and constructors.
- Ordered actions and persistent captures expressed as nullary function sets.
- Query equality groups, flat named seminaive rulesets, rewrites, and checks.
- Tree extraction with costs, duplicate roots and shared result nodes; extracted
  table rows; native e-graph clone and destruction.
- Profile-enabled execution with command locations and compact run summaries.
- Catalog-backed i64/f64 addition through distinct host definition keys.
- Generic Vec empty/of/get, ordered Vec value payloads and extracted Vec data.
- Compatible EqSort/Constructor/Function resupply, with canonical protobuf
  declaration/default closures retained across requests and clones. Each
  language block is fixed on its first supply; absent later blocks do not erase
  it. References compare structurally, including shared Union default topology.
- Python/Rust scalar type and addition views and Rust Vec type/empty/of/get
  views supplied by native registration; intact user sort/callable views,
  including ownerless Python CONSTANT views on nullary constructors/functions
  and closed scalar/Vec initializer defaults.
  Default calls are checked, never evaluated during installation/export. Actual
  omitted-argument expansion remains the frontend's responsibility.

Unsupported forms fail explicitly. These include profile-off (the native engine
still collects timing data), action/nested/empty Union identities, other complex values
and codecs, other primitive catalog mappings, relations, ruleset
resupply, anonymous/combined/shared rulesets, nondefault rule modes, schedulers,
loops, snapshots, proof requests, merge table reads, and custom cost models.
Expressions deeper than 256 nodes or requiring more than 65,536 native tree
nodes are currently rejected. This is a checkpoint, not a narrowing of
the conformance goal. Full source coverage, generated frontend APIs, exact
snapshots, and Python/Rust/Luminal migration remain unimplemented.

The focused regression is `cargo test --test protobuf`. It compares the native
fixture with decoded results and checks invalid-byte controls and post-failure
state. No frontend suite is counted as migrated by these tests.

`cargo run --example export_builtin_catalog -- catalog.pb` constructs the normal
provider-registered native engine at generation time and writes its canonical
`Program` bytes. It prints the existing incomplete-registration inventory to
stderr. Frontend packages can ship that resource and decode it without creating
an EGraph during authoring. Pin the generating core/experimental/leaf revisions;
the resource can be checked against the runtime provider by submitting its
declarations in an empty-command request. This is a partial catalog, not Freeze.
Lambda/partial-call defaults, other value codecs and unsupported execution forms
remain explicit gaps; scalar/Vec default checking does not establish their
compatibility. Native text rendering preserves executable semantics, not Python
or Rust presentation metadata.

### Initial source producer

`protobuf::source::Source` parses once and yields ordered protobuf `Program`
phases using the existing native desugarer and typechecker, before global removal
or proof instrumentation. Submit each phase through `Engine::run` using encoded
requests and decode its response **before advancing the iterator**. Stop on any
transport, source-resolution, or decoded execution error. This preserves effects
of earlier successful phases when a later source command fails. The producer
executes no user actions; previously submitted source/AST is never an execution
fallback. Start with a fresh, compatible handle; importing an existing handle's
authoring catalog is not implemented.

The first source slice supports datatypes, scalar/equality-sort functions,
ordered top-level lets, ordinary rules and directional rewrites, fixed named
theories, one-step runs, checks, and static tree extraction. Lets become nullary
function sets at their source positions. Rulesets are emitted when first run;
adding rules afterward is explicitly rejected until occurrence-preserving
immutable versions are implemented. Future rules are never hoisted into earlier
runs. Rewrite provenance is retained through native resolution so its typed
components can populate the existing `Rewrite` message, without treating an
arbitrary union rule as a rewrite.

Rules retain their source labels and spans. Query-local variables are renamed
after native source-position validation into a namespace disjoint from parsed
declarations/bindings, so later declarations cannot change delayed rule
publication. Global references remain distinct captured-function calls.

Experimental `extract` is an extension command. This producer explicitly
resolves only its static tree form; dynamic costs and extractor options remain
unsupported. Relations, program-defined primitives and uncatalogued primitive
calls, proof modes, local lets,
globals in rule heads, bidirectional rewrites, general unions/schedules,
includes, multi-command command macros and other extension commands are separate
gates.

`protobuf::source::render` converts the producer's decoded Programs back to
native source, reusing the adapter's expression/action/rule lowering. User sorts
and callables use deterministic private native symbols, so a logical callable
named `panic` is still rendered as a call rather than a native Panic action.
Identifiers outside the projected namespaces (such as ruleset names) must still
be valid native source atoms. Rendering preserves execution semantics, not
logical declaration names or presentation metadata when the text is reimported.
The tests execute that rendered source after reparsing and compare observations with
the byte-adapter path. They also cover ordered captures, failure prefixes and
mutated/corrupt byte controls. Run `cargo test --test protobuf source_`; this is a
small semantic roundtrip checkpoint, not migration of the source corpus.

Container phases use `protobuf::source::Renderer::default()` and its `render`
method, retaining the type/definition state across phases. Compatible declaration
resupplies are checked but not emitted as duplicate native declarations. It emits each closed
structural Vec sort once, including children before parents; rendering executes
no user actions. The stateless `render` entrypoint retains the scalar subset
and explicitly rejects container phases. Native source resolution remains
nominal, so two source aliases for Vec<i64> do not become interchangeable before
export; after resolution both map to one structural wire sort.

The wire sort and callable namespaces remain separate even for the same logical
name and across requests. All user equality sorts and constructor/function names
are projected with distinct namespace tags and UTF-8 hex encoding; host
definition keys retain exact-key dispatch. Query variables are renamed at their
binder use, independently of merge `old`/`new`. Canonical declarations and binding
defaults retain their logical names. Extraction, nested returned sorts and table
results reverse only adapter-owned names before wire interning. Foreign occupied
native symbols reject preparation instead of being reused or overwritten.

The adapter currently reserves `__egglog_proto_` and `__egglog_instance_` for
derived native sort/callable/variable/instance names. Authored equality-sort and callable
declarations using those prefixes fail before installation or effects. This is
a temporary valid-name conformance gap, not a final naming policy; removing this
restriction remains required. Native diagnostic prose may expose private names;
structured diagnostic name translation is also unfinished. Do not rely on an
unlikely prefix to avoid collisions. Reordered wire sort arenas, declaration
arrival order and cloned sessions do not change derived native identity.

### Initial engine-owned builtin definitions

Core's primitive macro accepts an optional `[id = "provider.definition"]` next
to the existing source alias. The same type annotations produce a canonical
protobuf signature; migrated native constraints are compiled from that record,
not another signature table. The native body, validator and allowed-context
entrypoints are unchanged. i64 `+` uses `egglog.core.i64.add`, while f64 `+` uses
`egglog.core.f64.add`. Source still uses the overloaded `+`; source resolution
selects the registration before exporting its exact wire key. A decoded call
cannot substitute a source alias or switch overloads through inference.

`TypeInfo::builtin_catalog()` returns the migrated protobuf definitions and
explicit lists of undescribed primitive registrations, presort factories and
installed non-equality sorts. Reserved but undescribed family operations are
also inventoried before any instances exist. Export performs no application or validation of
values. Conflicting registration keys fail catalog export/lookup while existing
unrelated native aliases keep their behavior. Compatible host descriptor resends
are assertions, not implementation replacement. Rendering retains exact keys,
which the native registry recognizes as the same registration identities.

Vec's three canonical generic definitions are registered with its presort before
instantiation. The `[instance = binding]` primitive macro derives constraints
from those same protobuf patterns and checks runtime conversion/arity agreement;
there is no handwritten native signature beside the record. Native nominal
instances share one wire definition key. Decoded calls validate all argument
and result sorts before selecting a derived native instance lookup key, pointing
to the same implementation, validator and context IDs. This preserves output-only
typing of an empty Vec even with several concrete shapes installed. These
compiler lookup keys never become wire declarations or exported sort names.
Rust presentation names the family `egglog_experimental::typed::builtins::Vec<T>`:
`empty`/`of` are associated views, `of` maps the variadic tail, and `get` borrows
its receiver. Python Vec views remain absent; neither language's frontend
generation is inferred from registration alone.

This checkpoint does not implement complete `Freeze`, other Vec operations,
generic Map/Fn definitions, wrapper generation, custom
codecs or capability/proof metadata export. The generic signature/family records
remain the compiler input; opaque constraints are never scraped into a
second signature registry. In core, run
`cargo test --no-default-features --test builtin_catalog`; in this repository,
run `cargo test --test protobuf`.

To regenerate, install Buf (tested with 1.73.0), uv, and Rust/Cargo, then run
from the repository root:

```sh
cargo install --locked protoc-gen-prost --version 0.5.0
make proto-gen
make proto-lint
make proto-test
```

These use local generator plugins. Initial tool/dependency downloads may need
network access. Commit generated sources together with schema changes.
On a clean checkout, `make proto-drift` regenerates and detects tracked changes.
`make proto-test` runs focused presentation/proof/resource wire validation with
the generated Python messages; it does not run Egglog or independently check a proof.

A Python wire/validation smoke check, after `uv sync --locked`:

```sh
uv run python - <<'PY'
from gen.python.egglog.v1 import egglog_pb as ir
from protobuf import Oneof
from protovalidate import validate

program = ir.Program(
    ir_version=1,
    sorts=[ir.Sort(kind=Oneof("family", ir.HostSort(name="i64")))],
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
