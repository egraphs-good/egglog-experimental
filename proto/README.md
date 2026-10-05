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
