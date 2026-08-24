# Changelog

This file records notable user-facing changes to egglog-experimental.

## [Unreleased]

### Added

- `:node-limit` and `:eager-apply` options for the `back-off` scheduler:
  `:node-limit N` keeps the e-graph within `N` e-nodes while choosing matches;
  with `:eager-apply`, each rule's chosen matches are applied before the next
  rule is consulted, so the limit is checked against the live e-graph size.
- The `(get-node-size!)` primitive: the e-node count of the e-graph (rows of
  eq-sort tables), the same measure `:node-limit` uses.
- A `:dag` option for `multi-extract` that let-binds subterms shared across
  the extracted variants instead of expanding every variant to a tree, plus
  the underlying `dag_print` printing functions.

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
