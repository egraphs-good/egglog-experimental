# Constant-folding conformance

The three authoring examples execute through their actual frontends. The shared
runner compares public input history after the final Freeze against one reviewed
`constant-folding.expected.textproto`. Source's host submits Freeze separately;
Freeze is an observation command, not source syntax. Request batching can differ.
Python and Rust each expose one command function receiving an existing graph.
Their standalone entry points use ordinary graphs; the capture harness supplies
recording graphs and owns Freeze, snapshot inspection and history serialization.
The authoring statements are shared, without source rewriting or duplicate bodies.

`normalizer.py` only reorders declarations, bindings and arena entries, remapping
their references. It preserves all records, names, metadata, field presence and
graph sharing. Unsupported kinds and unanchored identity graphs fail explicitly.
TextProto formatting comes from the generated schema descriptors.

Run the normalizer tests from the experimental checkout with a Python environment
containing the generated SDK dependencies:

```sh
PYTHONPATH=. "$PYTHON" -B -m unittest discover -s proto/conformance -p 'test_*.py'
```

For integration, install matching native and SDK builds into the selected Python
environment, and build the isolated Rust example against this checkout:

The end-to-end check requires the matching Python and experimental integration
branches; the schema-only branch supports the normalizer tests on its own.

```sh
cargo run --manifest-path proto/conformance/rust/Cargo.toml \
  --bin constant-folding-example
cargo build --manifest-path proto/conformance/rust/Cargo.toml \
  --bin constant-folding-conformance
"$PYTHON" -B proto/conformance/run.py \
  --rust-binary "$RUST_BINARY" --output "$CAPTURE_DIRECTORY"
```

Supply the actual built binary and a disposable capture directory explicitly.
The integration runner never invokes Cargo or installs dependencies. Capture
files retain original wire bytes and readable views; they are not repaired inputs.
`--update-expected` intentionally updates the single expected file only after all
three real recorded Programs match. Ordinary test runs never update it.
