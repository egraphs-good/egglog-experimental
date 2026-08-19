# egglog-experimental

Experimental extensions to the core [`egglog`](https://github.com/egraphs-good/egglog)
language and runtime. The crate can be used as a standard library for egglog
programs that want to try features before they move into core.

Questions and feature ideas are welcome on the egglog
[Zulip](https://egraphs.zulipchat.com/#narrow/stream/375765-egglog).

## Try it

The quickest option is the [web demo](https://egraphs-good.github.io/egglog-demo),
which includes egglog-experimental. To install the command-line program locally:

```sh
cargo install egglog-experimental
egglog-experimental path/to/program.egg
```

To use all extensions from Rust:

```toml
[dependencies]
egglog-experimental = "3.0"
```

```rust
let mut egraph = egglog_experimental::new_experimental_egraph();
egraph.parse_and_run_program(None, program)?;
```

`new_experimental_egraph` registers every extension below. Releases use the
same major version as the compatible egglog release.

## Features

### Language and values

| Extension | Syntax and behavior |
| --- | --- |
| [Exact rationals](https://egraphs-good.github.io/egglog-demo/?example=rational) | `Rational` values are built with `(rational numerator denominator)` and support arithmetic, comparisons, rounding, partial power/root operations, and numeric conversions. |
| [`for`](https://egraphs-good.github.io/egglog-demo/?example=for) | `(for (fact...) (action...))` runs a generated rule once, which is useful for applying an action to every current match. |
| [`with-ruleset`](https://egraphs-good.github.io/egglog-demo/?example=with-ruleset) | `(with-ruleset name rule-or-rewrite...)` assigns a group of rules, rewrites, and birewrites to one ruleset. |
| Body-defined primitives | `(primitive name (InputSort...) OutputSort body)` defines a primitive using positional arguments `_0`, `_1`, and so on. Bodies may call existing primitives, functions, and globals. |
| Fresh values | `(unstable-fresh! Sort [:cost N] [:unextractable])` creates a fresh value in a rule action for each match. |

### Scheduling and extraction

| Extension | Syntax and behavior |
| --- | --- |
| [Extended schedules](https://egraphs-good.github.io/egglog-demo/?example=math-backoff) | `(run-schedule step...)` supports `run`, `seq`, `saturate`, `repeat`, `eval`, and commands. `(let-scheduler name (back-off ...))` and `(run-with name ruleset)` add reusable custom schedulers. See the [`scheduling` module](https://docs.rs/egglog-experimental/latest/egglog_experimental/scheduling/) for the complete grammar. |
| [Dynamic extraction costs](https://egraphs-good.github.io/egglog-demo/?example=05-cost-model-and-extraction) | Wrap datatype or constructor declarations in `(with-dynamic-cost ...)`, then use `(set-cost (Constructor args...) cost)` to change the cost used by `extract` and `multi-extract`. |
| [Multiple extraction](https://egraphs-good.github.io/egglog-demo/?example=multi-extract) | `(multi-extract n term...)` returns the `n` lowest-cost variants of every term using one extractor pass. |
| Best-term compaction | `(keep-best "table"...)` extracts the best representation of every value in the named tables, clears the e-graph, and reinserts only those compacted tables. |

### Inspection

| Extension | Syntax and behavior |
| --- | --- |
| [Table size](https://github.com/egraphs-good/egglog-experimental/blob/main/tests/web-demo/get-size.egg) | `(get-size!)` returns the total number of tuples; `(get-size! "table"...)` sums only the named tables. It can be used in schedule guards. |
| Table statistics | `(print-table-stats)` reports every visible function table; `(print-table-stats Table)` reports one. Output includes row counts, distinct values per column, and out-degree distributions. |

See the [crate documentation](https://docs.rs/egglog-experimental) for Rust APIs
and the [`tests/web-demo`](https://github.com/egraphs-good/egglog-experimental/tree/main/tests/web-demo)
directory for runnable examples. User-facing changes are recorded in the
[changelog](CHANGELOG.md).
