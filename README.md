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
egglog-experimental = "1.0"
```

## Documentation

Check out the [crate documentation on docs.rs](https://docs.rs/egglog-experimental/latest/egglog_experimental/) for the current list of implemented extensions, API details, and demo links.
