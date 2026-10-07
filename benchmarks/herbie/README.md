# Herbie before/after performance

The paired egglog and egglog-experimental changes reduce whole-process time and peak memory on all five [Herbie rewrite examples](../../examples/herbie). They remove repeated AST/query cloning, unnecessary retained syntax, fresh-name tables, temporary lowering buffers and borrowed-key copies; eligible inactive rules defer planning until activation. Results below measure the combined changes in both repositories. They do not isolate the contribution of either PR.

The workload is **normal experimental, proofs off, one engine thread** (`--mode normal -j 1`, `RUST_LOG=error`). Rules, schedules, extraction requests, output generation and stopping conditions are fixed. All five outputs match the baseline byte for byte, including extracted multisets with multiplicity, table sizes and bad-merge flags. Rewrite17's final true bad-merge flag followed by rollback is expected.

Measured source endpoints:

| Endpoint | egglog | egglog-experimental |
| --- | --- | --- |
| Before | [`4821547d`](https://github.com/egraphs-good/egglog/commit/4821547da08c1a8e5a2f530625f1648f13b058a3) | [`b14ef1d`](https://github.com/egraphs-good/egglog-experimental/commit/b14ef1d7f68fc7b893b3fd83c6a6b3cd9e303085), repinned to that egglog revision |
| After | [`b7aa0886`](https://github.com/egraphs-good/egglog/commit/b7aa0886ba79d24548327d923646aad7f32e6a57) | [`b70dcde`](https://github.com/egraphs-good/egglog-experimental/commit/b70dcde3b82f5c59d66db53a31fa5b22d1c531c8) |

The before engine is egglog's main at the start of the campaign, rather than the older egglog pin originally in experimental main. Both recorded builds used local path dependencies at the listed revisions. This PR replaces those local paths with a git pin to the same after source; it also adds examples and benchmark artifacts. The recorded figures are reused measurements of those engine sources, not a new timing claim for the packaging commit. Compiler paths and git/path package identities can change rebuilt binary hashes.

The measurements were collected on Apple Silicon macOS 26.6 with Rust 1.91.0, release builds, on 6 October 2026 local time (7 October UTC). Each dump has ten ABBA blocks and twenty observations per endpoint, plus one warmup per endpoint. Timing covers the entire child process, including startup, parsing, execution, extraction and normal output captured to temporary files. Peak RSS is per child from `wait4`. The CLI's existing shutdown behavior is unchanged. No builds or profiles ran concurrently. All observations succeeded and are retained; no samples were appended to reach a threshold.

Mean whole-process runtime, with **after/before ratios** and independent 95% Fieller intervals (Student t, 19 degrees of freedom):

| Dump | Before (ms) | After (ms) | Reduction | After / before, 95% CI |
| --- | ---: | ---: | ---: | --- |
| rewrite16 | 70.64 | 56.97 | 19.4% | 0.8065 [0.7941, 0.8189] |
| rewrite15 | 41.79 | 27.60 | 34.0% | 0.6604 [0.6553, 0.6655] |
| rewrite17 | 109.01 | 94.77 | 13.1% | 0.8694 [0.8660, 0.8729] |
| rewrite66 | 311.69 | 302.29 | 3.0% | 0.9698 [0.9655, 0.9742] |
| rewrite88 | 88.80 | 72.10 | 18.8% | 0.8119 [0.8090, 0.8149] |

Peak resident memory (MiB = 2²⁰ bytes):

| Dump | Before (MiB) | After (MiB) | Reduction | After / before, 95% CI |
| --- | ---: | ---: | ---: | --- |
| rewrite16 | 65.98 | 41.37 | 37.3% | 0.6269 [0.6252, 0.6287] |
| rewrite15 | 41.13 | 24.11 | 41.4% | 0.5862 [0.5832, 0.5891] |
| rewrite17 | 74.56 | 49.19 | 34.0% | 0.6597 [0.6574, 0.6620] |
| rewrite66 | 72.07 | 51.47 | 28.6% | 0.7141 [0.7117, 0.7166] |
| rewrite88 | 92.80 | 57.56 | 38.0% | 0.6203 [0.6188, 0.6219] |

Every ratio's upper bound is below one. No aggregate across dumps is reported. These measurements do **not** establish performance relative to native egg or integrated Herbie.

[samples.csv](samples.csv) contains the original 400 observations and 20 warmups from the cumulative and incremental comparisons, exported without machine-local paths. The tables above use only the cumulative cohort. The separate incremental cohort compares the earlier optimized checkpoint (`c628da74` core with `4f390ad` experimental) to the final source: rewrite16's additional runtime reduction was 12.7%, and its additional RSS reduction was 23.0%. Do not pool these cohorts or add percentages from separate pilots. [results.json](results.json) contains per-dump summaries, endpoint/compiler identities, binary and input hashes, original collection hashes, and diagnostic profile metadata. CSV endpoint `A` means before and `B` means after in the identified cohort. Blank block/order fields identify warmups.

To run a new comparison, build separate executables and give their paths to [benchmark.py](benchmark.py). It follows the same timing and statistical conventions, checks semantic witnesses, records failed runs, refuses to overwrite an existing collection and checks input/executable hashes before marking it complete. The original campaign used frozen helpers from egglog-encoding; this portable script is a smaller reproduction entrypoint, and its statistics have been checked against every archived interval. Its own runs identify its script hash separately.

For the same before source, from this checkout:

```sh
git worktree add --detach ../egglog-experimental-herbie-before b14ef1d7f68fc7b893b3fd83c6a6b3cd9e303085
python3 - <<'PY'
from pathlib import Path
p = Path('../egglog-experimental-herbie-before/Cargo.toml')
text = p.read_text()
old = '90635860397ce710f8c0a4eeb04154a8ebc3ac05'
assert text.count(old) == 3
p.write_text(text.replace(old, '4821547da08c1a8e5a2f530625f1648f13b058a3'))
PY
CARGO_TARGET_DIR="$PWD/../egglog-experimental-herbie-before/target" cargo build \
  --manifest-path ../egglog-experimental-herbie-before/Cargo.toml \
  --release --bin egglog-experimental
CARGO_TARGET_DIR="$PWD/target" cargo build --locked --release --bin egglog-experimental
uv run benchmarks/herbie/benchmark.py collect \
  --before ../egglog-experimental-herbie-before/target/release/egglog-experimental \
  --after target/release/egglog-experimental \
  --output benchmarks/local/herbie-before-after.jsonl
```

The first baseline build updates its lockfile for the explicit git repin. The current checkout uses its committed lockfile. Keep the two binaries separate and finish all builds before timing. The default comparison covers all five examples with ten blocks; use `--files 16 --blocks 3` for a small exploratory run, keeping it separate from final comparisons. The PEP 723 script declares its SciPy dependency for `uv`; it can also run with Python 3.11+ and SciPy installed. Collection supports macOS and Linux. To recompute a summary without collecting new samples:

```sh
uv run benchmarks/herbie/benchmark.py summarize benchmarks/local/herbie-before-after.jsonl
```

Further improvements are possible, with larger changes to the engine. A late profile after the frontend/query changes and before the final hasher adjustment found the following inclusive CPU shares; they overlap and are not additive savings estimates. The profile sampled 140 complete rewrite16 commands and had some unresolved symbols.

| Opportunity | Evidence and useful next experiment | Main correctness boundary |
| --- | --- | --- |
| Rule execution and joins | About 38% inclusive CPU in `run_rules`. Identify expensive rules and repeated indexing/rebuild work before changing their plans. | Preserve callback/match multiplicity, seminaive timestamps, pending writes and reports. A broad Gj→MinCover switch produced 8 callbacks/matches instead of 2 with identical output rows; it cannot be treated as an equivalent default. |
| Shared checked frontend representation | Typechecking is about 15%, canonicalized lowering 10%. Measure the redundant part of the typed AST→core conversion, then try a bounded shared representation. | Preserve type/groundedness checks, globals, macro behavior and meaningful errors. Those phase shares also contain necessary work; eliminating a small discarded correspondence alone previously had only about a 1.7% ceiling. |
| Broader inactive-rule deferral | Planning remains visible. Instrument which additional empty queries cost enough to justify deferred construction. | Live-empty tables can retain physical tombstones. Zero-match plans may still flush pending writes and contribute reports; a blanket emptiness test changes behavior. The retained optimization only defers variants already guaranteed to be pruned. |
| Snapshot tables and indexes | Snapshots are about 3.3% after sharing immutable rules/queries. Investigate copy-on-write only if real Herbie snapshot frequency justifies it. | Mutable rows, indexes, counters and graph-specific history must remain independent after clone and pop. |
| Prepared extraction cost lookup | Extraction is about 9.4%, with roughly 2.4% in dynamic cost lookup. An extraction-scoped prepared lookup may avoid repeated names and registry access. | Preserve cost updates, declarations, unions, requested variants and push/pop; the whole extraction share is not removable lookup overhead. |

Validation used focused snapshot, deferred-planning/tombstone, lowering, fresh-name, macro, extraction and type-inference checks. Formatting and Clippy with `-D warnings` passed. The complete suite was not rerun after each optimization; this campaign did not optimize or benchmark proofs or multiple engine threads. Some individual runtime pilots were inconclusive and were retained for clear memory reductions; final performance claims come from the balanced endpoint comparisons above.
