# Protobuf IR draft

This directory proposes a typed, language-neutral Egglog interface for text,
Python, Rust and other frontends. It is an unpublished draft for design review;
the wire format may change.

[egglog.proto](egglog/v1/egglog.proto) is the reference: its comments and validation
annotations define the contract. This overview explains the model. Execution
prototypes are being tested separately; this PR contains the schema, generation
tooling and wire-validation tests.

## Programs, definitions and execution

A `Program` contains expression and sort arenas, declarations, ordered commands,
and optional source files. Arena indices are local to the owning message;
references from an earlier request cannot be reused without importing them.

| Record | Purpose |
| --- | --- |
| `Sort`, `Node` | Explicit types and shared expression graphs |
| `Declaration` | Immutable equality-sort, constructor, function, relation or program-defined primitive definitions |
| `Rule`, `AddRules` | Inline rule values added to named groups |
| `Command`, `Action`, `Loop` | Ordered execution and repeated command bodies |
| `BuiltinCatalog` | Backend-provided primitive sorts and signatures |
| `EGraphSnapshot` | Logical creation options and a reconstruction Program |

Declarations establish the vocabulary for the whole Program. They are installed
before commands, without executing their bodies, and cannot occur in `Loop`.
Recursive references between definitions are resolved during linking. Commands
say what executes and in what order; unused arena nodes do not execute.
Declaration timing between operations can be expressed using separate Programs.

Definitions have canonical names and exact signatures. Compatible resubmission
is harmless; conflicting definitions do not replace installed ones. A later
Program can use an installed definition without resending it. Callables share
one namespace; equality sorts and primitive sorts have distinct namespaces.

`AddRules{group,rules}` contains rules directly, with no rule arena or separate
group declaration:

```text
AddRules("opt", [fold_zero])
Run(["opt"])
AddRules("opt", [fold_constants])
Run(["opt", "cleanup"])
```

Groups grow by content identity. The same rule in several groups shares compiled
state; re-adding it does not reset its cursor. Labels, documentation and source
locations are diagnostic metadata. Unknown groups are empty.

## Typed expression graphs

Each node carries its resolved sort. Calls name one exact definition; the IR
does not perform overload selection or implicit conversion. Frontends resolve
surface syntax such as `+` and retain their own language presentation mappings.

`GetBuiltins` returns the configured backend's graph-independent catalog.
Programs, snapshots and history do not include builtin descriptions. The catalog
supports offline authoring and binding generation, but does not ship primitive
implementations or codecs.

Primitive sorts include scalars and containers. `SortApplication` represents
compositions such as `Vec<i64>`; function types use structural `FuncSort` values.
Generic signatures specify a parameter count, fixed inputs, output and an
optional repeating argument pattern. Actual calls are concrete. Native
primitive-specific applicability checks remain necessary even when the
structural signature matches.

`PrimitiveValue` stores exact scalar, container and function data. Custom values
carry opaque bytes and explicit child references. Computation uses `Call` or
intrinsic `Apply{function,args}`. There is no public application primitive;
frontends can wrap Apply in deferred code for first-class callbacks.

Ordinary shared nodes retain their first-demand result within one Action
execution or one rule firing's ordered head. `Union` also carries class identity:
reusing an empty equality-sort Union can make two actions refer to one fresh
class. Its identity lasts for the enclosing command-list execution; each loop
iteration has a fresh mapping. Queries instead use Union as an equality pattern.
The reference specifies the other evaluation and identity scopes.

Union references also represent cyclic and empty classes in exported data.
This avoids extracting a finite tree merely to inspect the graph. Variable,
effect and cycle validity depend on use context; arena membership alone grants
no permission to evaluate a node.

## Results and observations

`RunProgram` streams output frames followed by completion, or a terminal error.
Each frame owns its source files; output frames also own their node/sort arenas.
Completed outputs and effects remain visible if a later operation fails.
Preparation checks precede execution; execution is not an atomic transaction.

`Run` performs one round. `Loop` repeats commands until an iteration can stop,
its `until` query matches, or its optional maximum is reached. A count is a cap,
not a request to force quiet iterations. Completed top-level Run/Loop commands
emit `RunResult{updated,can_stop}`; nested controls do not emit separate results.
Detailed diagnostics are opt-in format-tagged bytes; backend profiling and query
plans are not a second portable report model.

Extraction returns finite representatives. `GetTableRows`, `GetTableSizes` and
`GetTableStats` return structured observations. A table cell without a finite
representative is explicitly unavailable rather than a fabricated expression.
`Freeze` preserves the complete logical graph instead.

Stored constructor cost annotations have a creation-selected type C. Registered
extraction models can return a separate result type D. Model implementations
and ordering remain outside the protocol; requests select a registered model.

Proof requests use the existing proof engine and return structured certificates.
Internal helper work does not produce extra requested Run results. Logical
reconstruction preserves the selected execution mode, not original derivations.

## Logical state and input history

`Freeze` returns `EGraphSnapshot{options,program}`. Its Program includes installed
user declarations, inline rule additions, and ordinary actions reconstructing
classes, rows, captures, costs and subsumption. Shared rule values are repeated
in each relevant group's addition; content identity preserves sharing of their
compiled rule. No special loading instruction is needed.

Reconstruction on a fresh compatible engine uses all snapshot logical options,
including `execution_mode` and `seminaive`, with `cost_sort` remapped into the
creation sort arena, then executes the Program. Builtin catalogs, primitive
implementations and custom codecs must be compatible. Resources such as thread
count are chosen by the receiver. Scheduler instances, incremental cursors,
reports and caches are not restored: this is logical state, not a checkpoint.

Input recording is separately enabled at creation. `GetHistory` returns one
accumulated Program of accepted inputs, including inputs that later failed during
execution. It omits outcomes and validation-rejected inputs. Declaration metadata
is cumulative, so it is not an exact replay guarantee. Clones retain their
prefix and then diverge; destroying a handle releases its history.

## Prototype integrations

The separate execution prototypes use an in-process `protobuf::Engine` for
encoded requests, a stateful Source producer/renderer for the text frontend,
and high-level Python/Rust APIs that emit the same records. Source yields
Programs or scope operations; callers submit each one and decode its successful
response before advancing, stopping on errors. Text-only formatting and file
output stay in the frontend.

Current adapter limits include i64 cost annotations, Normal-only Extract/Freeze,
native proof-mode restrictions and context-specific expansion budgets. These are
prototype limits, not additional restrictions on the schema. Wire validation or
a binary roundtrip alone does not establish frontend or execution conformance.

## Generated messages and checks

Generated Python messages use `protobuf-py`; Rust uses `prost` in the
`egglog-proto` crate. Message sources are ignored build outputs under
`gen/python` and `gen/rust`; package manifests, root modules and licenses remain
versioned. Run `make proto-gen` before building either SDK. No gRPC transport is
generated or required. Consumers must
select matching schema revisions: the `egglog.v1` package name is not a version
handshake in raw bytes.

CEL annotations check directly expressible constraints. Normative comments
cover remaining typing, binding, effect and graph obligations. CEL budget
exhaustion on a large input is inconclusive; implementations may use equivalent
scalable checks.

With Buf, uv and Rust/Cargo installed, regenerate and check from the repository
root:

```sh
cargo install --locked protoc-gen-prost --version 0.5.0
make proto-gen
make proto-lint
make proto-test
```

`make proto-test` regenerates its inputs before validating wire/CEL behavior;
it does not execute Egglog or independently check proofs. `make proto-clean`
removes generated sources while preserving the package scaffolding. The protobuf
CI job generates from a fresh checkout, runs validation tests and compiles the
Rust SDK.

A wire-validation example, after `make proto-gen`:

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

Imported `buf.validate` sources are pinned in `buf.lock`. Copyright 2023–2026 Buf
Technologies, Inc.; [Apache-2.0](LICENSE.protovalidate).
