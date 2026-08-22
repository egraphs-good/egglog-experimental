# Changelog

This file records notable user-facing changes to egglog-experimental.

## [Unreleased]

### Added

- A `Maybe[T]` sort with construction, partial unwrapping, defaulting,
  undefined-result capture, and higher-order branching. When more than one
  nominal `Maybe` alias is compatible, `maybe-none` requires type context.
- `map-fold-kv` for folding Map entries in opaque, EGraph-local stored `Value`
  order. Callbacks should be order-insensitive; an undefined callback makes the
  whole fold undefined.
- `f64-is-finite`, a predicate for guarding computations that may produce NaN
  or infinite values.

`Maybe` operations and `map-fold-kv` are not currently supported in proof mode.

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
