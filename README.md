# egglog-experimental

This repo implements several experimental extensions to the core [`egglog`](https://github.com/egraphs-good/egglog).
Currently, this can be thought of as a standard library to `egglog`.

You can use the egglog [Zulip](https://egraphs.zulipchat.com/#narrow/stream/375765-egglog) to ask questions and suggest improvements to this repo.

## Trying it out

The easiest way to try out `egglog-experimental` is to use the [web demo](https://egraphs-good.github.io/egglog-demo), which builds on top of latest egglog-experimental.

To install egglog-experimental binary locally, you need to install `cargo` and run

```
git clone git@github.com:egraphs-good/egglog-experimental.git
cargo install --path=egglog-experimental
```

To use it in a Rust project, you can add it as a dependency in a `Cargo.toml` file.

```
egglog-experimental = "3.0"
```

## Documentation

Check out the crate documentation (built locally) for the current list of implemented extensions, API details, and demo links.
Releases are coordinated with compatible releases of egglog.

The [protobuf IR draft](proto/README.md) explores a shared representation for
text, Python, and Rust frontends. A bounded in-process byte adapter and source
producer are implemented; complete frontend conformance remains unfinished.
Wire sort/callable namespaces and logical result names are preserved through
derived native names; rendered source uses those private implementation names.
`cargo run --example export_builtin_catalog -- catalog.pb` exports native-owned
definitions and scalar presentation records for frontend generation, with the
remaining catalog gaps printed separately. It is not a Freeze snapshot.
