# Changelog

This file records notable user-facing changes to egglog-experimental.

## [Unreleased]

### Added

- `(unstable-subst root map)`, which copies the affected portion of the
  constructor sub-e-graph reachable from `root` with each key e-class replaced
  by its mapped value, preserving subsumed rows and making subsumption dominant
  on copy collisions. Available in top-level actions and `:naive` rule heads;
  anchorless affected cycles fail before copy writes.

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
