# Protobuf IR draft

This is a work-in-progress design for a shared Egglog IR that text, Python,
Rust, and other frontends could produce directly. It is being shared for
feedback, not as a finished API. The wire format may change during review.

Start with [egglog.proto](egglog/v1/egglog.proto). Its validation annotations
and comments are the specification. The main pieces are:

- Flat expression and sort arenas, with explicit types and shared references.
- Immutable declarations and rulesets, separate from ordered commands.
- Native scalar, container, and function values. Custom values carry opaque
  bytes and explicit child references; symbolic computation remains a call.
- Lossless logical snapshots with declarations, cycles, and empty e-classes.
  A snapshot is not an engine checkpoint; restoration is deferred.

There is no engine lowering, runtime, or service implementation yet. CEL checks
directly expressible constraints, not full typing, binding, effects, or cycle
validity. The remaining requirements are normative comments. CEL can exhaust
its evaluation budget on large valid inputs; that is inconclusive, not proof
that a program is invalid. Frontend parity has not been demonstrated end to end.

## Open questions

These are directions to explore, not changes already made to the schema.

### Shared builtin definitions and type checking

Could a standard-library setup program describe all host primitives and type
constructors, so frontends can generate bindings and agree on type checking?
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

Should these live in program declarations, or in a separate builtin catalog
that generates/checks concrete programs? Specify type-constructor arities,
type-variable scope, substitution, overload resolution, and how empty containers
obtain their types. Separate frontend inference/conversions from checking the
resolved IR. This need not introduce generic user-defined equality sorts.

Functions need a separate check: applying `Fn<(A...), R>` takes a heterogeneous
argument list, not repetitions of one type. Python still has special cases for
[application](https://github.com/egraphs-good/egglog-python/blob/ff72f601a972ca1eb7cb0a1d299813f5d65b1a14/python/egglog/runtime.py#L522-L538)
and [partial application](https://github.com/egraphs-good/egglog-python/blob/ff72f601a972ca1eb7cb0a1d299813f5d65b1a14/python/egglog/egraph.py#L548-L553).
Can the signature language express those, or should they remain explicitly special?

### High-level bindings and language metadata

Protobuf codegen produces message classes, not ergonomic Egglog APIs. Could
builtin and user declarations also generate Python classes, Rust methods, and
bindings for other languages? For example, one signature might be presented
as Python `m[k]` and Rust `m.get(k)`, with the same underlying call.

Python's [declarations](https://github.com/egraphs-good/egglog-python/blob/ff72f601a972ca1eb7cb0a1d299813f5d65b1a14/python/egglog/declarations.py#L311-L324)
distinguish constructors, methods, class methods, properties, and preserved host
methods. Potential metadata includes module/type names, receiver placement,
operators, argument order, defaults, and conversions. Should this be an open,
namespaced annotation on definitions or a separate binding manifest? How are
unknown annotations preserved, and can they be ignored without changing the
Egglog definition? This is separate from the existing locations/documentation.

Generating expression builders does not generate native primitive implementations,
arbitrary preserved methods, or value codecs. Decide which conveniences are
declarative and which remain handwritten. A useful end-to-end test: export
Luminal's Rust-defined IR, generate its Python API, author a Python rewrite,
and consume that rule in Rust without duplicating the IR declarations.

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
- **Deferred:** snapshot restoration and proofs. Restoration would recover
  logical data/schema, not scheduler history or an engine checkpoint.

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
