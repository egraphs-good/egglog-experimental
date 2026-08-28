# Changelog

This file records notable user-facing changes to egglog-experimental.

## [Unreleased]

### Added

- A `:node-limit N` option for the `back-off` scheduler: once an observed count
  reaches this soft threshold, further rules are delayed. Each check sees
  earlier rule actions, but one rule may add any number of nodes and the
  deferred rebuild may change the count again.
- The `(get-node-size!)` primitive: the visible constructor-row count of an
  ordinary experimental e-graph, excluding relations, analysis functions,
  global aliases, hidden declarations, and internal-prefixed implementation
  tables. This is the same measure `:node-limit` uses there.
- A `:dag` option for `multi-extract` that let-binds subterms shared across
  the extracted variants instead of expanding every variant to a tree.

### Changed

- The `back-off` scheduler now rejects unknown option tags instead of silently
  ignoring misspellings or removed options.

## [3.0.0] - 2026-08-20

This is the first crates.io release of egglog-experimental. Its major version
matches egglog 3, with which it is compatible.

### Added

- An extended scheduling language with named back-off schedulers, sequencing,
  saturation, repetition, full-context expression evaluation, and command steps.
- Dynamic extraction costs, multi-term/multi-variant extraction, and `keep-best`
  compaction.
- Body-defined primitives, one-shot `for` rules, grouped `with-ruleset`
  declarations, and fresh values in rule actions.
- Exact rational values and their arithmetic, comparison, rounding, partial
  power/root, and conversion primitives.
- E-graph table-size queries and per-table column and out-degree statistics.
- The `egglog-experimental` command-line program and
  `new_experimental_egraph` Rust entry point.

[Unreleased]: https://github.com/egraphs-good/egglog-experimental/compare/v3.0.0...HEAD
[3.0.0]: https://github.com/egraphs-good/egglog-experimental/tree/v3.0.0
