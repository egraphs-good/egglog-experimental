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

An experimental in-process bytes adapter lives in
`src/protobuf.rs`; current limits are described below.
It is not a complete service implementation. CEL checks
directly expressible constraints, not full typing, binding, effects, or cycle
validity. The remaining requirements are normative comments. CEL can exhaust
its evaluation budget on large valid inputs; that is inconclusive, not proof
that a program is invalid. Complete frontend parity is not yet established.

## Design decisions and open questions

Decisions are marked below; the other questions remain open. The schema's
comments and annotations remain the normative contract.

### Schema revision and rule names

**Decided:** `Program` has no application version field. Generated SDKs, engines,
and frontends select the same schema revision; incompatible draft changes migrate
together. The `egglog.v1` package and service names identify this API, but are not
carried in raw protobuf bytes and do not negotiate a schema. Unknown-field
handling alone cannot establish semantic compatibility. Removed Program tag 1
and its old name are reserved to avoid reinterpreting existing draft artifacts.

`Rule` is an authored rule or rewrite occurrence, including its options and
diagnostic metadata. Its `rule` arm contains a `RuleBody`: the query and ordered
actions. `RuleList` references occurrences by index; a label is never identity.

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
Function types remain structural `FuncSort`s. Nominal equality-sort names,
host-family names and callable names occupy three distinct namespaces, selected
by their existing oneof tags. Thus EqSort `Pair`, HostSortFamily `Pair` and a
callable `Pair` may coexist without changing their names. `Sort.eq` resolves only
an EqSort; `Sort.family` resolves only a HostSortFamily, never a same-spelled
definition of another kind. Missing definitions remain errors checked against
local, installed and ambient definitions. Same-family resends and applications
must still agree on arity; all callable kinds still share one namespace.
Type-use spans and optional `egglog_aliases` may remain on `Sort`; neither affects
type identity. Equal applications collect their text aliases, so `A` and `Z` can
both name `Maybe<i64>`. Other frontends may omit them. Text frontends handle name
collisions; docs and family/nominal bindings belong to definitions.
Text rendering chooses one stable alias; binary records retain all aliases.

CEL checks local family arity; installed-name resolution and compatible resupply
remain semantic checks.

Evaluated ordinary expression nodes retain their lazy first-demand result within
one Action command execution, including inside loops, or one rule firing's
ordered head. Each execution gets a fresh memo; writes commit in command order.
No evaluation is hoisted before its first demand, and failed evaluations preserve
the completed mutation prefix. Query patterns and Union's
separate identity scopes are unchanged. Host callback invocation counts are
not a protocol guarantee.

`Declaration.doc` preserves absence, explicitly empty text, and nonempty text.
It is excluded from semantic identity; compatible resupply retains the first
stored documentation. Rust uses `Option<String>`. Python accepts `None` as unset
but its scalar getter returns `""` when absent: use `has_field("doc")`, not
truthiness, to recover absence. ProtoJSON distinguishes omission from `"doc":""`.
Rule and ruleset docs retain ordinary implicit-string semantics.

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
compatible descriptor resends are semantic checks.

**Decided:** each wire callable has one unique name across user and host
definitions; the wire IR does not select from same-name overloads. Frontends lower
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

### High-level language bindings

Protobuf codegen produces message classes, not ergonomic Egglog APIs. Planned
high-level generators use builtin and user declarations to produce Python/Rust
symbolic APIs and Egglog source. For example, one signature might be presented
as Python `m[k]` and Rust `m.get(k)`, with the same underlying call.

Public Python APIs must be statically checkable with MyPy; typed Rust APIs must
enforce their types at compilation. Test accepted calls and rejected wrong-sort
or arity cases, not only runtime validation. A wire signature need not dictate
the public argument shape. Current Python uses `Map.empty`, `insert`, and
indexing; Rust's existing `Map::of` accepts typed key/value tuples. The shared bulk
wire interface is one `Vec<Pair<K, V>>`; frontends may accept typed host tuple
collections or lower flat text arguments while preserving that core shape.
Default generated bindings must also preserve static types: report unsupported
generation rather than weakening types to expose a primitive.

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
is undecided; high-level generation remains frontend work.

Python views distinguish free functions, initializers, methods, class methods,
properties, class variables, and ownerless constants. Free functions and constants
have nonempty qualified paths whose final component may be empty; preceding
components stay nonempty. A `CONSTANT` view names a nullary concrete expression
(`C`), with no owner, receiver, parameters or mutated input.
It does not evaluate a body during installation or
export. A nullary `FUNCTION` remains callable (`C()`); arity never implies a
constant view.
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
An optional `tail_repetitions` on a Python/Rust view instead gives a
`HostPrimitive` signature with N fixed inputs and a nonempty width-W tail
exactly N + R*W fixed view slots. Slot i derives its sort from fixed input i
or tail position (i-N) % W. There is no remaining logical tail slot. Receivers
and parameters cover all slots once, with matching sorts; defaults and Python
mutation remain limited to original fixed inputs. CEL checks the count against
the supplied mappings by division, without multiplying or expanding R, and
checks direct receiver/owner sort roots. Recursive structural typing still
requires the semantic verifier. Python currently admits this field only on
FUNCTION and METHOD; unused specialized property/constant and other forms
are explicitly unsupported. The canonical signature/provider and emitted Call
are unchanged, and ordinary canonical call checking still applies.

Presence matters: absent retains the logical-tail convention, while present
zero maps only the fixed prefix. Python's scalar getter returns zero in both
cases; use `has_field("tail_repetitions")`, not truthiness. New consumers preserve
all valid absent-field encodings and meanings. This is not an old-reader guarantee for new views:
discarding the field can widen a fixed-arity view back to a variadic surface.
Preserving these views requires a coordinated schema/consumer epoch; generated
message bindings and schema validation alone do not establish frontend support.

`FunctionApplication` instead has a function input and a heterogeneous tail
derived from its concrete `FuncSort`, and cannot use `tail_repetitions`.
A structural-function owner marker represents `__call__` without a fake family
or new type-pack binder. Other owner/trait patterns use only the enclosing
callable's existing generic binder; bindings cannot introduce generic nodes.
Egglog views carry symbols and constructor datatype membership, grouped by the
existing output equality sort, without new datatype or text-overload semantics.

`Freeze` retains supplied blocks and their bindings-only dependencies, remapping
arenas without executing defaults or freezing derived wrapper choices. CEL checks
direct shapes, positions and bounds. Recursive default closure, owner/receiver
typing, bindings compatibility, and target-language generation are additional
semantic requirements.

**Decided:** initially generate the symbolic declarations and expression-building
API. Host methods such as `Map.value` and host conversions remain ordinary
handwritten Python. Descriptors do not transport native implementations or
arbitrary method bodies. A useful end-to-end test: export Luminal's Rust-defined
IR, generate its Python API, author a Python rewrite, and consume that rule in
Rust without duplicating the IR declarations.

### Unnamed rulesets and declaration reuse

`RunProgramResponse.ruleset_publication` is required independently of profiling
and errors. Its unique names confirm exactly the submitted compatible ruleset
presentations whose bindings are retained, including old compatible resupplies
and completed first naming; `""` denotes the explicit default name. Preparation
failure confirms none; success or completed definitions followed by command
error confirms every submitted name. Failure omissions neither revoke earlier
confirmation nor establish global absence. Readers must also check membership
against the exact request; response-only validation checks presence/uniqueness.
Legacy absence means unavailable/unknown, never an empty confirmation, and
fails this draft's new response contract. This observation is not a state export.

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
  share state. Composition cycles are invalid.

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
- **Rule-level sharing — decided:** `Program.rules` holds `Rule` occurrences;
  each `RuleList.rules` is an ordered list of arena indices. Different leaves
  and repeated positions may reference the same occurrence; equal separate
  entries remain distinct. Names are optional diagnostic labels, may repeat,
  and provide no rule lookup or identity. A rule matched through an installed
  named root is reused even in a newly added leaf that references its index.
  A wholly unanchored resubmission remains fresh. References share the rule and
  its rule-owned state across groups/Run sites; distinct scheduler instances and
  their scheduler-owned state remain separate. CEL checks direct indices.
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
  Each payload still includes every referenced node/sort arena
  entry; indices are local to that message. Equality sorts are defined by
  `Declaration.eq_sort`, not by arena references. Standalone
  exports retain all installed definitions and their dependencies.

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
rebuilds, and runs. Queries neither read nor populate this identity mapping.
Ordinary call results instead use the shorter first-demand memo of one
Action command execution (including inside loops) or one rule firing's ordered
head; each such execution starts a fresh memo.

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

`ConfigureEGraphResources` queries the effective thread count and `no_decomp`, or
updates threads, future-rule decomposition policy, or native report detail through
`report_level`. Zero threads requests automatic parallelism; a positive count is
exact. Updates preserve logical state and rule cursors. Clone inherits resources,
later changes are handle-local, and Freeze omits them. Invalid or unsupported
requests fail explicitly; the native thread-pool allocation boundary is unchanged.

Restore by remapping C's reachable closed sort graph and needed sort declarations
into a creation request, then executing the exported Program on that fresh handle
with compatible host capabilities. Unrelated generic signature patterns may stay
in the snapshot; do not copy its entire sort arena into the closed creation arena.
Rules start with fresh execution state. Against an existing handle the Program
still uses ordinary action semantics; callers must check options for any
restoration-equivalence guarantee.

Custom value reconstruction requires trusted codecs.
No ordinary native pure non-equality self-cycle has been established; arbitrary host-codec
cycles remain unproven. `Freeze` must fail when required state cannot be
represented, not silently omit it or claim a complete export.

**Execution history:** set `CreateEGraphRequest.record_history=true` at creation
and retrieve `GetHistoryResponse` through `GetHistory` (`Engine::get_history`).
Recording is off by default; disabled retrieval errors and retains no growing
request log. History keeps known fields of decoded typed requests before
normalization and actual responses, including preparation errors, completed-prefix
outputs, resource queries and Freeze.
Transport errors and interrupted/no-response operations are distinct outcomes.
Audit requests may be invalid inputs; inspecting them does not authorize execution.
This is not a raw-byte record: decoders may discard unknown protobuf fields.
Retrieval itself adds nothing to history.

Clone shares its recorded past and then diverges independently. Successful
`ReturnToEGraph` restores the saved logical scope while joining both ordered
audits in service submission order, counting shared exchanges once. Destroyed or
consumed handles retain a closed audit until the Engine is dropped. Enabled
recording is unbounded; native callbacks/codecs remain external. Keep each
Program's local arenas separate:
concatenation changes references and Union identity scopes. History is neither
a checkpoint nor a promise of deterministic or side-effect-free replay.

The typed Rust API offers the same creation-time choice:

```rust
let mut graph = egglog_experimental::typed::EGraph::with_recording(true)?;
graph.stats()?;
let history = graph.history()?; // Create and Stats; retrieval adds no entry.
assert_eq!(history.entries.len(), 2);
```

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
Native helper/maintenance Runs do not become public outcomes. A requested native
result completed before trailing maintenance fails remains in the output prefix.
RunOutcome keeps the requested native schedule's `updated`/`can_stop`, including
inline helper work; exclusive profiling does not redefine those flags.

`PrintFunction.max_rows` is optional: absent selects all rows, present zero
selects none, and a positive value bounds the native scan prefix. The target
must exist even for zero rows. `PrintedFunction.table` identifies rows whose
argument/output `TableCell`s contain either an ordinary extracted node reference
or an `unavailable_sort` response-sort reference when no finite representative
exists. Positions, multiplicity and subsumed flags remain intact; relation
outputs are Unit. Unavailability is not a dummy term and does not fail the
command. Actual extraction/encoding errors still fail without partial output;
earlier effects/outputs remain and later commands do not run. Table statistics
pair each exact response sort reference with its distinct-value count, in input
order followed by output.

Rust represents `PrintFunction.max_rows` as `Option<u64>`. Python readers must
use `has_field("max_rows")`, since the scalar getter returns zero when absent.
The byte adapter observes admitted Constructor, Function and Relation tables in
all four execution modes. Encoded observations return logical live rows; native
raw term-table dumps can retain historical or deleted rows and therefore differ.
This does not establish full Source text parity. CSV/file output and
Fail-observation remain separate required conformance gates.

`ProfileSummary` provides exclusive phase attribution: authored Run sites are
separate from internal maintenance attributed to its command or installation
cause. Failing invocations and completed prefixes remain visible; missing metrics
are unknown, not zero. These measurements do not partition wall time.

`include_run_reports` additionally returns native `NativeRunReport` detail at
completed requested control sites; `Stats` observes the cumulative native report.
This backend-oriented view and the authored exclusive summary have different
meanings. `report_level` selects future native collection detail. Both views use
the response's `rules` catalog for occurrence attribution, also used by errors.
Labels remain diagnostic; shared occurrences stay shared and distinct equal
occurrences stay distinct. The schema specifies paths, completeness and metrics.

### Message ownership

Arenas are local to each message. The wire contract does not prescribe transport
or shared-memory ownership.

### Existing proof engine

`EGraphOptions.execution_mode` selects ordinary execution (the default), term
encoding, proofs, or proof testing. Clone retains the mode and proof state.
The local byte adapter supports all four modes with `profile=true`; unknown
mode values fail creation before allocating a handle. Flat Prove/ProveExists
requests use the current native engine and return owned proof bytes.
Snapshots retain the mode, but logical reconstruction does not preserve original
derivations. `Prove` uses the same conjunctive facts as `Check`; `ProveExists`
targets a constructor name without inserting a witness. Proof testing executes
checks as proof requests. Preserve native ordering: `Prove` can complete a helper
run and its effects before proof extraction fails. Successful proof requests
return the proof at the originating command location, including inside loops.

**Decided:** proof mode returns requested results only. Helper Runs remain native
execution and contribute only to optional profiling, with the exclusive
attribution described above. CEL rejects nested Run/Loop outcomes and permits
nested proof/observation results; matching them to the requested command remains
an adapter check. Flat byte execution implements requested-only results and
exclusive authored/maintenance leaf summaries.
The current adapter still requires `profile=true`; it cannot yet
satisfy the collection-off contract.

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
schema tests establish wire/CEL behavior only. The bounded native/adapter proof
fixtures do not establish full frontend or desugar/proof-checker-context conformance.

### Conformance work

The schema is the contract; the current-engine adapters are experiments for
finding missing semantics and unnecessary concepts. Text, Python and Rust/Luminal
tests exercise encoded requests and responses. Complete source, application and
cross-mode conformance is still in progress; a wire roundtrip alone establishes
none of these.

Host implementations, codecs and cost models remain registered outside the
messages. Native capability checks still apply. Declarations are not Commands.
Source handles expected declaration/rule-installation failures during authoring,
preserving successful definition prefixes. These assertions and rejected bodies
produce no protobuf operations or validation obligations; replay in another
namespace or mode does not repeat the assertions.

## Generated messages and checks

[Python](../gen/python/egglog/v1/egglog_pb.py) and
[Rust](../gen/rust/egglog/v1/egglog.v1.rs) message sources are checked in. The Rust
SDK is the `egglog-proto` crate in `gen/rust`, consumed and re-exported by
Experimental as `egglog_experimental::proto`. Core has no protobuf dependency:
it supplies the native descriptions, checking and execution facilities that
Experimental projects into these messages. Keep the schema, generated SDKs and
selected native provider revisions coherent when running integration tests.

Python uses `protobuf-py` and `protovalidate`; the compiled Rust SDK uses `prost`.
Separately generated imported validation definitions also need `prost-types`.
No gRPC transport is generated or required.

The implementation subsections below describe the separate integration
branch/worktree. The schema-only review includes the specification and generated
SDKs, without these runtime implementations.

### Byte adapter

`protobuf::Engine` (`src/protobuf.rs`) accepts encoded requests for creation,
cloning, destruction, scope return, resource configuration, program execution and
`GetHistory` retrieval.
Decode failures and unknown handles are transport errors; program failures are
returned in `RunProgramResponse.error`. Preparation validates on disposable
native state without running user actions. Installation and execution retain
their actual completed prefix on failure, not an atomic rollback guarantee.
All supplied rules, including unused rules, are compile-validated.

Canonical records retain logical identities and optional metadata. Compatible
resupply asserts the installed definition; it does not replace a host
implementation. Defaults are checked without evaluation; omitted-argument
expansion belongs to the frontend.

Current limits include requests requiring `profile=true`, Normal-only
Extract/Freeze, native proof-mode restrictions on non-global
no-merge functions, and context-specific lowering/expansion budgets. Evaluated
action graphs use lazy first-demand native locals, including ordinary primitive
calls and exact numeric values, in all four modes. Ordered rule heads share one
memo per firing; extraction roots evaluate independently in Normal mode.
Query patterns and rewrite left-hand sides use shallow facts with shared query
binders; native query normalization and matching retain their own costs.
Rendering oversized extraction roots to Source remains tree-limited.
Unsupported modes, values and codecs fail explicitly. These are adapter limits,
not changes to the schema contract.

### Source production and rendering

`protobuf::source::Source` (`src/protobuf/source.rs`) resolves native source
into ordered submissions. Before producing the first submission, use
`with_execution_mode` once to select the target handle's execution mode; the
selection is immutable. Omission uses Normal lowering. Native source admission
and capture semantics follow the selected mode; this does not broaden ordinary
wire Function admission or enable encoded-mode Extract.
Includes are parsed when reached. Use `next_submission`, submit its Program or
scope operation, and decode a successful response **before advancing**. Stop on
source, transport or execution errors. Earlier completed phases remain visible;
source/AST execution is never a fallback. The producer requires a fresh,
compatible target handle.

File/CSV prints are host-only `Submission::PrintFunction` values. Call their
`run` method with the ordinary Program submission callback: it opens the file
before submission, formats structured rows, and writes or returns host stdout.
Stop on presentation errors too. The flat Program iterator rejects these
submissions; filenames never enter protobuf. Predicate rows have inputs only;
ordinary Unit-valued functions retain their output. Cells use the existing
bounded Source renderer and fail explicitly for unsupported values.

Captures keep their ordered write positions. Rules retain labels and spans;
publication uses immutable versions without hoisting future rules into earlier
runs. The first publication binds the authored ruleset name; later publications
use generated names. Source resolves its current alias when producing each Run.
A raw `RulesetRef{name: "r"}` continues to select the first immutable publication
of `r`; use the emitted Run's actual reference to select a later publication.
Query locals remain distinct from persistent captures and later
declarations. Proof requests retain the authored facts, leaving proof execution
to the receiving mode. Source extraction counts are literal and bounded;
aggregate extraction preserves its ordered result groups.

Source rejects authored `let` bindings inside `fail`, including nested wrappers;
evaluate an expression or action directly instead. Fail retains completed
effects and catches the supported operation's evaluation, not preparation errors.

Reuse one stateful `Renderer` across the stream; `render_submission` handles
scope submissions too. Compatible declarations are not emitted twice. Core and
Experimental renderings have different native naming constraints and reject
unrepresentable forms explicitly. Reparsed text is an execution comparison, not
an export of the original logical keys or language presentation metadata.
Derived native aliases are reversed through exact owned mappings, never by
recognizing a prefix. Private-looking spellings remain valid logical names;
free-form diagnostic prose may still expose implementation names.

### Native builtin registry

Core owns each primitive's signature, implementation, contexts and validator.
`TypeInfo::builtin_catalog()` describes those registrations; Experimental's
`portable_builtin_catalog()` projects them without a second signature table.
Generic instances select the same native implementation after checking exact
argument/result sorts. Optional Python/Rust presentation records describe
wrappers, not executable host code or proof certificates.

Surface overloads are resolved before protobuf: i64 and f64 addition select
distinct keys such as `egglog.core.i64.add` and `egglog.core.f64.add`. Today's
text adapter may render overloaded spellings; the protocol does not require
native overloads. Provider export recipes also lower legacy forms such as flat
`map-of` into the canonical `Vec<Pair<K,V>>` constructor without recognizing
arbitrary user calls by spelling. Canonical records stay intact; the adapter
adds no sorting or deduplication policy.

`cargo run --example export_builtin_catalog -- catalog.pb` exports the configured
native provider's canonical definitions and reports any undescribed
registrations. Frontends can ship that resource for offline authoring and check
it against the runtime provider. Pin its provider revisions; it is not Freeze.

Focused checks are `cargo test --test protobuf` and
`cargo test --test builtin_catalog`. Source-corpus trials live in `tests/files.rs`;
these focused checks are not a complete frontend/application acceptance run.

To regenerate, install Buf, uv and Rust/Cargo, then run from the repository root:

```sh
cargo install --locked protoc-gen-prost --version 0.5.0
make proto-gen
make proto-lint
make proto-test
```

Commit generated sources with schema changes. `make proto-drift` detects
regeneration drift. `make proto-test` checks wire constraints with the generated
Python messages; it does not execute Egglog or independently check proofs.

A wire/validation smoke check, after `uv sync --locked`:

```sh
uv run python - <<'PY'
from gen.python.egglog.v1 import egglog_pb as ir
from protobuf import Oneof
from protovalidate import validate

program = ir.Program(
    sorts=[ir.Sort(kind=Oneof("family", ir.HostSort(name="i64")))],
    nodes=[ir.Node(sort_id=0, kind=Oneof("primitive_value",
        ir.PrimitiveValue(value=Oneof("i64", 42))))],
)
validate(program)
assert ir.Program.from_binary(program.to_binary()) == program
PY
```

With no commands, this example requests no evaluation.

The imported `buf.validate` sources are generated from Protovalidate, pinned in
`buf.lock`. Copyright 2023–2026 Buf Technologies, Inc.; distributed under the
[Apache-2.0 license](LICENSE.protovalidate).
