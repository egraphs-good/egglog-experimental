# Protobuf IR draft

This is a work-in-progress design for a shared Egglog IR that text, Python,
Rust, and other frontends could produce directly. It is being shared for
feedback, not as a finished API. The wire format may change during review.

Start with [egglog.proto](egglog/v1/egglog.proto). Its validation annotations
and comments are the specification. The main pieces are:

- Flat expression, sort, and rule arenas, with shared references.
- Immutable declarations and rule values; ordered commands add rules to groups.
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
handling alone cannot establish semantic compatibility. This unpublished draft
has no backward-compatibility reservations.

`Rule` is an authored rule or rewrite value, including its options and
diagnostic metadata. Its `rule` arm contains a `RuleBody`: the query and ordered
actions. `AddRules` references values by index; labels are diagnostic.

### Shared builtin definitions and type checking

**Decided:** `GetBuiltins` returns a separate, read-only `BuiltinCatalog` for
the configured backend, without an EGraph handle. It describes primitive sorts
and primitive signatures, including generics; it does not supply implementation
code. Clients can fetch/cache it independently of graph state.

Programs declare only user entities: equality sorts, constructors, functions,
relations and `UserDefinedPrimitive` bodies. These remain concrete; frontends
may specialize generic user code before this boundary. Builtin descriptions
are neither input declarations nor snapshot/history contents. Calls reference
their available canonical names without importing descriptors.

`Sort.eq` references a user equality-sort name. `Sort.application` applies a
`PrimitiveSort` through `SortApplication{name,args}`, with its declared arity,
including zero for `i64` or `Unit`. Function types are structural `FuncSort`s.
Equality-sort, primitive-sort and callable names occupy distinct namespaces;
all callable kinds share one namespace. References do not declare definitions.
Missing names and incompatible signatures remain errors. Type-use spans do not
affect identity. Transparent aliases such as two names for `Maybe<i64>` belong
to the text frontend; documentation belongs to definitions.

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
Rule docs retain ordinary implicit-string semantics.

`Primitive.signature` contains ordinary structural typing: a type-parameter
count, fixed inputs, a required output, and an ordered `varargs` pattern.
An empty pattern means no tail; a one-element pattern means homogeneous varargs;
a wider pattern repeats as an ordered group. The flat argument count after the
fixed prefix must be a multiple of the nonempty pattern's width. Width and order
are semantic, including `[T, T]`; there is no tuple/group expression node.
Signature-bound `Sort.var` indices are below `type_param_count`. Frontends supply
their own diagnostic parameter names. Native primitive-specific sort and domain
restrictions are checked at submission before execution; a structural signature
does not promise support for every substitution.

Examples of shared signatures:

```text
map-get<K,V>(Map<K,V>, K) -> V
map-empty<K,V>() -> Map<K,V>
map-from-pairs<K,V>(Vec<Pair<K,V>>) -> Map<K,V>
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
signatures must be recursively closed. Only the separate builtin catalog
contains signature-bound sort variables. CEL checks direct bounds and variable roots.
Recursive closedness, binder scope, signature matching, family resolution, and
installed definition compatibility are semantic checks.

**Decided:** each wire callable has one unique name across user and host
definitions; the wire IR does not select from same-name overloads. Frontends lower
overloaded syntax such as `+` to the appropriate unique callable name and make
conversions explicit before this boundary. Generics remain: a call instantiates
one named generic definition, rather than choosing an overload. No concrete
naming convention is chosen here.

`Apply{function,args}` invokes a function value. Its concrete `FuncSort` supplies
the exact argument and result sorts; evaluate the function first, then arguments
left-to-right. Application has no public builtin callable identity. Frontends can
close a concrete application operation in a program-defined primitive when it is
used as a first-class callback, retaining ordinary named partial application.
For `PrimitiveValue.partial_call`, captured argument sorts plus the resulting
`FuncSort.params` form the named target's complete argument list, and
`FuncSort.result` supplies its result. Match its signature, including varargs,
and determine every generic parameter. Relations cannot be partially applied.
A `Lambda` stores captures and its body; its enclosing `FuncSort` supplies its
parameter and result sorts. Apply is executable code, never inert value data;
deferred bodies may contain it.

`Freeze` does not repeat the backend catalog. Typed inspection or reconstruction
uses the matching catalog fetched separately. Saved catalogs can support binding
generation, but matching descriptions do not establish implementation, codec or
execution-capability compatibility.

### Frontend APIs and generation

The shared catalog describes canonical identities, sort families, generic
signatures. Frontends own names, operators, methods/properties,
keyword parameters, defaults and host conversions. None of that presentation is
installed in the engine or included in Freeze/history.

Generators combine the catalog with local frontend mappings. For example,
`egglog.core.i64.add` has signature `(i64, i64) -> i64`; Python may expose
`i64.__add__`, Rust `core::ops::Add`, and text `+`. Their types come from the same
native description. Borrowing and language argument shapes are frontend policy,
not another copy of the signature.

Protobuf message codegen alone does not create those ergonomic APIs. Python
APIs must remain statically checkable with MyPy, and Rust APIs at compilation.
A generator must report unsupported generation instead of weakening types.
A missing local mapping does not hide a semantic declaration; a frontend may
provide a generic wrapper or require an explicit mapping for its public API.
Identifier and surface-name collisions are frontend errors, not engine
redefinition conflicts.

The shared bulk Map constructor takes one `Vec<Pair<K,V>>`. Python/Rust may
accept typed host tuple collections; text may lower flat `map-of` arguments.
These choices emit the same concrete calls.

Defaults are closed symbolic expressions owned by the frontend. Free/query
variables are invalid; lambda-bound variables are allowed. Do not evaluate a
default while defining a wrapper. Import omitted default roots together when
building the call, preserving internal sharing and fresh Union identities
between calls. Their required semantic declarations enter the request when used;
unused default templates are not graph state. Local owner/default references
must retain their expression/type graph, not rely on another message's indices.

Builtin catalog exports and logical snapshots contain semantic definitions,
not enough information to reproduce an author's exact language API. Recreating
that API requires its frontend mapping. A Rust-defined Luminal IR can still be
used from generated Python wrappers to author rules consumed in Rust, sharing
the same semantic declarations throughout. Literal/container codecs, `.value`
accessors and preserved host methods remain frontend behavior; native provider
implementations are registered separately.

### Additive rule groups and declaration reuse

Ordered `AddRules{group,rules}` commands contain immutable typed rule values
inline and add them to a graph-owned group. There is no rule arena or separate
group declaration. Frontends may retain reusable owned rule values locally.

```text
commands = [AddRules("opt", [fold_zero]), Run(["opt"]),
            AddRules("opt", [fold_constants]), Run(["opt", "cleanup"])]
```

Content establishes rule identity across groups and submissions: resolved typed
body, ordered query/actions, execution options and represented sharing, with
normalized query binders. Labels, documentation, source locations and arena
indices do not identify rules. Re-adding the same content is a no-op and never
resets its native cursor. `Run.groups` selects the ordered union of group
members, considering shared content once. Separate Runs and loop iterations
select independently; query matches and schedulers retain their normal meaning.
Unknown groups are empty, `[]` selects nothing, and `[""]` selects the default
group. Compatible additions may be retried after a partial installation failure.

Programs may reference definitions already installed on the same handle without
resending them. Builtins are implicitly available. A call's unique name selects
its definition; exact argument/result sorts check the signature. Missing names
and mismatches are errors. Full definition resends are optional compatibility
checks: compatible definitions are no-ops and conflicts are errors.
Every referenced node/sort arena entry remains message-local. Equality sorts
are defined by `Declaration.eq_sort`, not by arena references.

### Current-state export and optional recording

**Decided:** `Freeze` returns one `EGraphSnapshot{options,program}`, with complete
logical settings and an ordinary reconstruction `Program`, without filtering
or a special loading instruction. Include all
installed user declarations and their sorts, even when unused, plus
registered rule values and group membership through `AddRules`. Emit each shared
rule once and remap its group references.
The commands reconstruct all logical data, including empty/unreachable classes,
constructor alternatives, function and relation rows, subsumption, captures, and
assigned row costs. Builtin descriptions, historical commands, scheduler instances,
seminaive cursors, reports, caches and host resources are not part of this export.

Its data commands are ordered ordinary actions: one direct `Action.term` for
each canonical equality class (a unique Union containing its constructor rows),
relation insertions, function `Set`s including Unit outputs, `SetCost`s, then
constructor subsumption. Aside from rule-registration commands, it contains no queries, runs or loops.
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
or the snapshot's `program.sorts`. C may be a supported closed backend-provided sort or composition. Ordinary Programs have no configuration precondition.
Creation resolves its closed type arena before allocating a handle and executes
no Program. User equality sorts are unavailable at creation. Its optional `threads` is a
resource request: absent selects receiver policy, zero requests automatic
parallelism, positive requests that count; unsupported requests fail creation.
Resources are not exported.

The current byte adapter honors this thread request using the native per-egraph
configuration API; clones retain that configuration. Wasm rejects counts above
one. An absent field leaves the native default unchanged. The adapter currently requires the
i64 cost sort; native thread-pool resource
allocation behavior is unchanged.

Threads and `no_decomp` are creation-time choices.
`CreateEGraphResponse.threads` acknowledges the effective positive thread count.
Clone inherits resources; Freeze omits them. There is no resource-configuration
RPC or Python live setter in this interface.

Restore by remapping C's reachable closed backend sort graph into a creation request, then executing the exported Program on that fresh handle
with compatible primitive implementations/codecs and the matching builtin catalog.
Rules start with fresh execution state. Against an existing handle the Program
still uses ordinary action semantics; callers must check options for any
restoration-equivalence guarantee.

Custom value reconstruction requires trusted codecs.
No ordinary native pure non-equality self-cycle has been established; arbitrary host-codec
cycles remain unproven. `Freeze` must fail when required state cannot be
represented, not silently omit it or claim a complete export.

**Input history:** set `CreateEGraphRequest.record_history=true` and call
`GetHistory` (`Engine::get_history`) to obtain one accumulated `Program`.
Recording is off by default; disabled retrieval errors and retains no growing
log. Inputs rejected during validation/preparation are omitted. Accepted inputs
are retained before installation/execution, including those that subsequently
fail. Outcomes, resource/lifecycle requests and retrieval itself are not recorded.
This records decoded known fields, not raw bytes.

Export remaps local arenas while preserving command order, sharing and distinct
Union locations. Declarations are cumulative: an earlier recorded Freeze may
observe later declaration metadata. Logical data remains ordered. History is
neither a checkpoint nor an exact-replay guarantee after failures.

Clone shares its recorded prefix and then diverges. Scope pop destroys the
active branch and resumes the saved graph with its recorded prefix.
Destroy releases that graph's history; live clones retain their own past.
Recording is unbounded during the graph's lifetime. Host capabilities and
creation settings remain external.

The typed Rust API exposes the same opt-in choice:

```rust
let mut graph = egglog_experimental::typed::EGraph::with_recording(true)?;
graph.stats()?;
let history = graph.history()?;
assert_eq!(history.commands.len(), 1); // Stats; retrieval adds nothing.
```

### Execution results, diagnostics and streaming

Ordinary `Run` and compound loops return the same small `RunResult`:
`updated` reports any database change; scheduler-aware `can_stop` preserves the
backend's existing conservative aggregation across compound schedules. A bounded
run finishing does not itself prove saturation. Readiness is computed during
execution, never by calling the scheduler again from a client.

`Loop` repeats a body until it can stop, an `until` pre-check matches, or its
optional maximum is reached. No maximum means unbounded; zero does nothing.
Text repetition uses this capped behavior too, rather than forcing quiet
iterations solely to reach a count. With zero iterations, `updated` is false
and `can_stop` is true.

`RunProgramRequest.diagnostics` defaults to false. Off skips optional timers,
per-rule metric maps and retained iteration reports while leaving scheduler
counts and decisions intact. Opting in emits one `Diagnostic` output immediately
after a completed top-level control result at the same `CommandLocation`.
`Stats` uses the same document type for previously collected cumulative detail;
it does not retroactively collect runs executed with diagnostics off.

`Diagnostic` contains a format identifier and opaque bytes. The current native
format is `application/vnd.egglog.run-report+json`. Its JSON
contains `iterations` and the native `search_and_apply_time_per_rule`,
`num_matches_per_rule`, `search_and_apply_time_per_ruleset`,
`merge_time_per_ruleset` and `rebuild_time_per_ruleset` maps. Native durations are
`{secs,nanos}`. The document omits the duplicate `updated`/`can_stop` fields.
Names and physical plans are backend diagnostics, with no portable attribution
or operator model. A plan's `stages` are `[kind, optional_stats, next_indices]`
tuples; unavailable stage counters remain absent.
Decomposed/materialized plans use an opaque `text` presentation with their symbol
mapping; unavailable structured `stages` are omitted, rather than shown as empty.
`Explain.groups` inspects
current selected rule query plans without executing or advancing their cursors,
returning `application/vnd.egglog.query-plan+json` as native `[name,plan]` pairs.

`RunProgram` is canonically streaming. Each response contains either an output
payload or a terminal error, with its own source files. `Engine::run_stream`
synchronously delivers owned frames in observation order, including inside loops.
Output frames own their node/sort arenas; Freeze Programs and proof arenas remain
independent. Completion emits an empty success frame; failure emits an error
after any completed observations. `Engine::run` buffers this same frame sequence.

One `Error` carries its class (invalid program, failed check or runtime failure),
human message, optional source span and command location. It does not duplicate
the failing rule or successful proof records. Completed effects remain committed.

The synchronous callback supplies backpressure without a growing queue. Returning
`ControlFlow::Break(())` on an observation chunk cancels at a safe boundary and returns a
transport cancellation error; completed effects remain. A failed or cancelled
loop has no fabricated completed result. Earlier observations remain usable,
and the live state need not equal the last received snapshot. `Fail` does not
catch cancellation. Same-engine callback reentry is rejected while execution is
active. The final callback's return value cannot cancel already completed work
or replace its actual error. Input history records only the accepted input Program, independently of
streamed outputs.

The typed Rust API offers `run(schedule) -> RunResult`,
`run_with_diagnostics(schedule) -> (RunResult, Diagnostic)` and
`stats() -> Diagnostic`. `Schedule::with_snapshots()` appends one Freeze after
the chosen schedule. `schedule.with_snapshots().repeat(3)` observes each body;
`schedule.repeat(3).with_snapshots()` observes once after the loop.
`run_stream(schedule, |snapshot| ...)` delivers only explicitly requested owned
snapshots while execution proceeds; those snapshots outlive the graph.

Outputs carry a command path and one zero-based iteration coordinate per enclosing
loop. Errors locate the innermost active command independently of their source
span. Native helper Runs emit no requested control result. A requested result
completed before trailing maintenance fails remains in the output prefix.

`GetTableRows.max_rows` is optional: absent selects all rows, present zero
selects none, and a positive value bounds the native scan prefix. The target
must exist even for zero rows. `TableRows.table` identifies rows whose
argument/output `TableCell`s contain either an ordinary extracted node reference
or an `unavailable_sort` response-sort reference when no finite representative
exists. Positions, multiplicity and subsumed flags remain intact; relation
outputs are Unit. Unavailability is not a dummy term and does not fail the
command. Actual extraction/encoding errors still fail without partial output;
earlier effects/outputs remain and later commands do not run. Table statistics
pair each exact response sort reference with its distinct-value count, in input
order followed by output.

Rust represents `GetTableRows.max_rows` as `Option<u64>`. Python readers must
use `has_field("max_rows")`, since the scalar getter returns zero when absent.
The byte adapter observes admitted Constructor, Function and Relation tables in
all four execution modes. Encoded observations return logical live rows; native
raw term-table dumps can retain historical or deleted rows and therefore differ.
This does not establish full Source text parity. CSV/file output and
Fail-observation remain separate required conformance gates.

### Message ownership

Arenas are local to each message. The wire contract does not prescribe transport
or shared-memory ownership.

### Existing proof engine

`EGraphOptions.execution_mode` selects ordinary execution (the default), term
encoding, proofs, or proof testing. Clone retains the mode and proof state.
The local byte adapter supports all four modes; unknown
mode values fail creation before allocating a handle. Flat Prove/ProveExists
requests use the current native engine and return owned proof bytes.
Snapshots retain the mode, but logical reconstruction does not preserve original
derivations. `Prove` uses the same conjunctive facts as `Check`; `ProveExists`
targets a constructor name without inserting a witness. Proof testing executes
checks as proof requests. Preserve native ordering: `Prove` can complete a helper
run and its effects before proof extraction fails. Successful proof requests
return the proof at the originating command location, including inside loops.

**Decided:** proof mode returns requested results only. Helper Runs remain native
execution and can appear in explicitly collected backend diagnostics. CEL rejects
nested control results and permits nested proof/observation results; matching them
to requested commands remains an adapter check.

`ProofResult` contains separate, inert term and proof arenas. Terms have no sort:
native proof propositions can describe a function row with inputs and output as
children. All eight native justifications are represented, including explicit
substitutions, shared premises, container normalization, and the `Eval` side
condition placeholder. Native IDs are remapped to result-local indices, so
inspection does not require a live e-graph. Proof failures use the ordinary Error.

CEL checks required fields, oneofs, direct reference bounds and unique substitution
names. Shared decoders must additionally check
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
cloning, destruction, program execution, `GetHistory` and `GetBuiltins` retrieval.
`run_stream` is the canonical execution path; `run`
collects its owned response chunks.
Decode failures and unknown handles are transport errors; program failures are
returned in the error arm of `RunProgramResponse`. Preparation validates on disposable
native state without running user actions. Installation and execution retain
their actual completed prefix on failure, not an atomic rollback guarantee.
All supplied rules, including unused rules, are compile-validated.

Canonical records retain logical identities, documentation and origins.
Compatible resupply asserts the installed semantic definition; it does not
replace a native implementation. Wrapper defaults and presentation validation
belong to the frontend.

Current limits include Normal-only Extract/Freeze, native proof-mode restrictions on non-global
no-merge functions, and context-specific lowering/expansion budgets. Evaluated
action graphs use lazy first-demand native locals, including ordinary primitive
calls and exact numeric values, in all four modes. Ordered rule heads share one
memo per firing; extraction roots evaluate independently in Normal mode.
Query patterns and rewrite left-hand sides use shallow facts with shared query
binders; native query normalization and matching retain their own costs.
Rendering oversized extraction roots to Source remains tree-limited.
Rule keys normalize outer query names and duplicate Var records. Saved-code and
shared query/lambda binders retain conservative spelling/sharing distinctions;
the adapter does not identify every alpha-equivalent graph.
History export reports a compatibility error if accepted inputs contain
conflicting declarations after a partial installation failure; it does not
rewrite either submitted definition to force them into one Program.
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
source additions emit `AddRules` at the authored position. Combined source
selections expand to ordered group names. Later additions become visible to
later Runs without membership versions or publication receipts.
Query locals remain distinct from persistent captures and later
declarations. Proof requests retain the authored facts, leaving proof execution
to the receiving mode. Source extraction counts are literal and bounded;
aggregate extraction preserves its ordered result groups.

Source rejects authored `let` bindings inside `fail`, including nested wrappers;
evaluate an expression or action directly instead. Fail retains completed
effects and catches the supported operation's evaluation, not preparation errors.

The renderer supports fixed rule-addition preludes and one-time wrappers.
Dynamic `AddRules` inside a genuinely repeated schedule is not representable in
the current text schedule syntax and fails explicitly. High-level fixed theories
place their additions before repeated execution.

Reuse one stateful `Renderer` across the stream; `render_submission` handles
scope submissions too. Compatible declarations are not emitted twice. Core and
Experimental renderings have different native naming constraints and reject
unrepresentable forms explicitly. Reparsed text is an execution comparison, not
a guarantee of the original logical spellings or source formatting. Text
frontends retain their own scoped aliases; detached Programs use canonical valid
syntax without transporting those hints.
Derived native aliases are reversed through exact owned mappings, never by
recognizing a prefix. Private-looking spellings remain valid logical names;
free-form diagnostic prose may still expose implementation names.

### Native builtin registry

Core owns each primitive's signature, implementation, contexts and validator.
`TypeInfo::builtin_catalog()` describes those registrations; Experimental's
`portable_builtin_catalog()` projects them into a separate `BuiltinCatalog`
without a second signature table.
Generic instances select the same native implementation after checking exact
argument/result sorts. Python/Rust/text mappings remain local to their
frontends and generators; exported descriptors contain no language view.

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
    sorts=[ir.Sort(kind=Oneof("application", ir.SortApplication(name="i64")))],
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
