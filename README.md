# egglog-experimental

This repo implements several experimental extensions to the core [`egglog`](https://github.com/egraphs-good/egglog).
Currently, this can be thought of as a standard library to `egglog`.

You can use the egglog Zulip [Zulip](https://egraphs.zulipchat.com/#narrow/stream/375765-egglog) to ask questions and suggest improvements to this repo.

## Trying it out

The easiest way to try out `egglog-experimental` is to use the [web demo](https://egraphs-good.github.io/egglog-demo), which builsd on top of latest egglog-experimental.

To install egglog-experimental binary locally, you need to install `cargo` and run

```
git clone git@github.com:egraphs-good/egglog-experimental.git
cargo install --path=egglog-experimental
```

To use it in a Rust project, you can add it as a dependency in a `Cargo.toml` file.

```
egglog-experimental = "1.0"
```

## Implemented extensions

* `for`-loops ([demo](https://egraphs-good.github.io/egglog-demo/?example=for))
* `with-ruleset` ([demo](https://egraphs-good.github.io/egglog-demo/?example=with-ruleset))
* Rationals ([demo](https://egraphs-good.github.io/egglog-demo/?example=rational), see `src/rational.rs` for supported primitives)
* Dynamic cost model with `set-cost` ([demo](https://egraphs-good.github.io/egglog-demo/?example=05-cost-model-and-extraction))
* Running custom schedulers with `run-with` ([demo](https://egraphs-good.github.io/egglog-demo/?example=math-backoff))
