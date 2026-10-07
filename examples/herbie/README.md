# Herbie rewrite examples

These five standalone dumps were supplied from [Herbie](https://github.com/herbie-fp/herbie)'s `dump-egglog` workload as representative rewrite problems. `rewrite16.egg` is the optimization target; `rewrite15.egg`, `rewrite17.egg`, `rewrite66.egg`, and `rewrite88.egg` exercise additional inputs. The Herbie copyright and MIT license notice are preserved in [LICENSE](LICENSE).

Run a dump with normal experimental, proofs off and one engine thread:

```sh
cargo build --locked --release --bin egglog-experimental
RUST_LOG=error target/release/egglog-experimental --mode normal -j 1 examples/herbie/rewrite16.egg
```

The dumps retain their original rules, schedules, extraction requests and rollback checks. Compatibility edits replace obsolete `(set (constN) expression)` assignments to nullary constructors with `(union (constN) expression)`. There are 2, 7, 24, 97 and 4 such edits in dumps 15, 16, 17, 66 and 88 respectively. The checked-in files are byte-identical to the modernized benchmark inputs; original/modern SHA-256 hashes are recorded in [the benchmark metadata](../../benchmarks/herbie/results.json).

In rewrite17, the last bad-merge flag is intentionally `true`, followed by rollback. Expected behavior includes that flag, extraction variant multiplicity and table sizes.

See [before/after benchmarks and further optimization opportunities](../../benchmarks/herbie/README.md), including raw measurements and a portable comparison command. These examples are run explicitly, keeping ordinary test-suite runtime unchanged.
