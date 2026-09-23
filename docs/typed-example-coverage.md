# Typed example coverage

The executable corpus is pinned to core `e264c37a3332453eb0b6486c82c8766dd1af17df`
and Python `433542b4e7e5a4263566b166d849856a7e20aa5e`. It includes the 40 public
core web demos, the 12 Python package gallery scripts, and the seven Python
tutorials. It does not include the complete core regression suite or external
compiler exercise projects. The admitted portions map to 45 Rust ports; the
46th example demonstrates typed frozen traversal and table observation, and
the 47th exports a complete shared program for cross-frontend execution.

Every listed Rust file is independently runnable with
`cargo run --no-default-features --features typed --example typed_NAME`.
The `typed_examples` integration target includes and executes these same files.
The six introductory lessons also appear verbatim in `typed::tutorial` rustdoc;
lesson 3 first displays and tests their shared arithmetic theory.
No example uses generated Egglog source or a parser fallback.

## Authoring and review

The [RFC](typed-rust-api-rfc.md#authoring-contract) owns the common declaration,
conversion, rule, execution, and observation contracts.
The [design aims](typed-rust-api-rfc.md#design-aims) target source-like size and
ordinary Rust composition, without weakening source semantics to save lines.
The source pins above identify the corpus being ported, not the current core
dependency, which is pinned in the [Cargo manifest](../Cargo.toml).

Examples follow their source theory structure, retaining meaningful explanations,
helpers, generation loops and separately scheduled stages. Keep rule families in
their source order; factor genuine generation without moving rules across theory
sections. Pair test expressions with
their expected results rather than maintaining parallel arrays. Explicit constructors remain
for query-field binding, callable selection, ambiguous conversions, and symbolic
left operands. The tables below own the exact source coverage and exclusions.
Declarations use their default qualified Rust names, not aliases retaining old
descriptor spellings. The `typed_program_export` interchange example explicitly
names its sort and constructors to give other frontends stable shared identities.
Simple merge policies are written directly in attributes;
costs, extractability, and explicit duplicate-output policies are preserved.
Application sorts use `#[sort]` and `#[declarations] impl` only. Bodyless
constructors and relations need no redundant attribute. Unary constructors opt
into generated concrete conversions with `#[constructor(from(...))]` when real
call sites use the shorter literal operands or need native interop; unused
conversion boilerplate is not an example requirement. Functions and methods,
including constructors, use ordinary Rust snake_case names. Prefer standard
arithmetic/bitwise operators where the trait contract matches symbolic results.
The native-value tutorial also uses `#[constructor(try_from(i64))]` for reverse
inspection through standard `TryFrom`/`TryInto`, keeping evaluation explicit.
API-only conversion, selector and ruleset-length assertions live in integration
tests; examples retain the source program's actual computational checks.
Fixed theories use module-level `#[ruleset]` declarations with ordinary Rust bodies; their
names refer to lazy immutable values. Rulesets are direct schedule inputs, so
one run needs no `.run()` conversion. Runtime-dependent generation remains
ordinary functions and callbacks. `EGraph::default()` needs no empty options
argument. `birewrite(lhs, rhs)` returns the two ordinary rules directly.
Declare a fixed theory's variables once as borrowed parameters, reusing them
across independently bound rules, and return `Vec<Rule>` directly. Do not repeat
named-variable declarations per rule; retain distinct variables within each
query. Keep `Ruleset` composition when it actually combines reusable groups.
Shared theories are imported as Rust modules, not inserted with expression-level
`include!`.
An example's private captures use names such as `"output"`, without redundant
module prefixes. A shared destination or public integration may need qualified
capture names; this differs from automatically qualified declaration identities.
Ruleset names default to their qualified Rust paths. Expression operations use
receiver methods where natural; straightforward math arguments are positional.
Single-use symbolic aliases are inlined, while shared expressions and meaningful
generation/execution stages retain names. Put pure shared expressions before the
rule list instead of repeating nested blocks per rule. Prefer direct literal
inputs wherever an existing conversion and the surrounding symbolic type make
the meaning exact; keep explicit anchors for symbolic arithmetic and pattern
field binding.

Opt-in named records are for patterns or updates that actually become clearer:
`..Args::fresh()` supplies independent variables for omitted fields, while
`..matched_args` retains already-matched fields. This can remove irrelevant
ruleset parameters without removing constraints. Small positional calls stay
positional; adding a record for a unary or binary call is usually more ceremony.
Keep private relations beside their rules and use automatic declaration names
unless an independent producer must share the same nominal identity.

## Core web demos

The source path for every row is `tests/web-demo/NAME.egg` at the core revision
above. Hyphens in source names become underscores in Rust target names.
Computational checks and source scopes are retained; diagnostic printing is
replaced with assertions rather than introducing a table-printing API.
The subsumption example uses an explicit `saved_root` relation to bind the source's
captured global in its later rule. This preserves that e-class after the original
initializer contains a subsumed node; it does not inline the initializer or add
capture expressions to typed rule bodies. An additional scoped matching case
checks this adaptation in `tests/typed_example_regressions.rs`, not in the port.

Full-file physical line counts include blank lines, comments, Rust declarations,
imports and executable checks. The 38 mapped core sources total 4,021 lines;
their Rust files total 5,279. This is not an identical-work ratio: the exclusions
below still apply, and some Rust files include separate Python cases. Sources are
counted at the pinned core revision above; Rust counts are this review's formatted
working files.

Array read-through/overwrite rules retain their source ordering, as do the rule
families in read/write analysis, fusion, lambda and type inference. Lambda keeps
its core/Python parameterization; a shared array of fixed rules preserves
occurrence identity when those rules are inserted at their source positions.

| Source | Cargo example | Admitted scope | .egg lines | .rs lines |
| --- | --- | --- | ---: | ---: |
| `antiunify.egg` | `typed_antiunify` | Full computational program | 26 | 47 |
| `array.egg` | `typed_array` | Full computational program | 77 | 125 |
| `bdd.egg` | `typed_bdd` | Full computational program | 107 | 123 |
| `bignum.egg` | `typed_bignum` | Full computational program | 13 | 26 |
| `birewrite.egg` | `typed_birewrite` | Full computational program | 18 | 33 |
| `combinators.egg` | `typed_combinators` | Full computational program | 102 | 208 |
| `cyk.egg` | `typed_cyk` | All grammar/input cases; excludes 10-variant extraction at lines 94 and 113 | 115 | 157 |
| `datatypes.egg` | `typed_datatypes` | Full computational program | 11 | 52 |
| `eqsat-basic.egg` | `typed_eqsat_basic` | Full computational program | 25 | 47 |
| `eqsolve.egg` | `typed_eqsolve` | Full computational program | 45 | 90 |
| `fibonacci.egg` | `typed_fibonacci` | Full computational program | 11 | 25 |
| `fusion.egg` | `typed_fusion` | Full computational program | 152 | 259 |
| `herbie.egg` | `typed_herbie` | Full computational program | 570 | 618 |
| `herbie-tutorial.egg` | `typed_herbie_tutorial` | Full computational program | 144 | 215 |
| `knapsack.egg` | `typed_knapsack` | Full computational program | 46 | 93 |
| `lambda.egg` | `typed_lambda` | Full computational program | 242 | 451 |
| `levenshtein-distance.egg` | `typed_levenshtein_distance` | Full computational program | 71 | 114 |
| `list.egg` | `typed_list` | Full computational program | 73 | 90 |
| `math.egg` | `typed_math` | Full computational program | 337 | 342 |
| `matrix.egg` | `typed_matrix` | Full computational program | 98 | 159 |
| `multiset.egg` | `typed_multiset` | Lines 1–79, 108–118, 132–141, 177–181; see exclusions | 210 | 112 |
| `naturals.egg` | `typed_naturals` | Full computational program | 32 | 63 |
| `path.egg` | `typed_path` | Full computational program | 19 | 27 |
| `path-union.egg` | `typed_path_union` | Full computational program | 21 | 33 |
| `pathproof.egg` | `typed_pathproof` | Full computational program | 30 | 45 |
| `points-to.egg` | `typed_points_to` | Full computational program | 63 | 100 |
| `prims.egg` | `typed_prims` | Full computational program | 124 | 133 |
| `push-pop.egg` | `typed_push_pop` | Full computational program | 11 | 18 |
| `resolution.egg` | `typed_resolution` | Full computational program | 100 | 103 |
| `rw-analysis.egg` | `typed_rw_analysis` | Full computational program | 284 | 292 |
| `schedule-demo.egg` | `typed_schedule_demo` | Full computational program | 28 | 30 |
| `set.egg` | `typed_set` | Full computational program | 40 | 61 |
| `subsume.egg` | `typed_subsume` | Full computational program | 30 | 68 |
| `towers-of-hanoi.egg` | `typed_towers_of_hanoi` | Full computational program | 39 | 54 |
| `typecheck.egg` | `typed_typecheck` | Full computational program | 102 | 123 |
| `typeinfer.egg` | `typed_typeinfer` | Full computational program | 336 | 406 |
| `unification-points-to.egg` | `typed_unification_points_to` | Full analysis/checks; both roots retained, excludes final 100-variant displays | 243 | 297 |
| `unify.egg` | `typed_unify` | Full computational program | 26 | 40 |

## Python gallery and tutorials

| Python source | Cargo example | Admitted scope |
| --- | --- | --- |
| `examples/bignum.py` | `typed_bignum` | BigInt/BigRat arithmetic and table checks |
| `examples/eqsat_basic.py` | `typed_eqsat_basic` | Both expressions and equality proof |
| `examples/fib.py` | `typed_fibonacci` | Separate Python 1,1 initial-value case alongside core 0,1 case |
| `examples/lambda_.py` | `typed_lambda` | Separate Python theory: constructor evaluation, its distinct freer(Let) formula, all positive/negative cases and compose-presence rule |
| `examples/matrix.py` | `typed_matrix` | Dimension and Kronecker-product checks |
| `examples/resolution.py` | `typed_resolution` | Separate final clause with negative p1; core has positive p1 and an additional unit-propagation occurrence |
| `examples/schedule_demo.py` | `typed_schedule_demo` | Alternating steps, including negative checks |
| `examples/bool.py` | `typed_bool` | Boolean primitives and function-valued rule result |
| `examples/ndarrays.py` | `typed_ndarrays` | Every symbolic shape/index/string-generation case |
| `docs/tutorials/getting-started.ipynb` | `typed_matrix` | Explicit dimension, identity and matrix subcases; no notebook renderer |
| `docs/tutorials/tut_1_basics.py` | `typed_tutorial_basics` | Full computational lesson |
| `docs/tutorials/tut_2_datalog.py` | `typed_tutorial_datalog` | Reachability, shortest paths and equality-sort graph cases |
| `docs/tutorials/tut_3_analysis.py` | `typed_tutorial_analysis` | Lines 1–199 |
| `docs/tutorials/tut_4_scheduling.py` | `typed_tutorial_scheduling` | Lines 1–198 |
| `docs/tutorials/tut_5_extraction.py` | `typed_tutorial_extraction` | Lines 1–99 |
| Typed Rust RFC | `typed_freeze` | Exact rootless snapshots, retained typed captures, selected nodes, scalar decoding, typed table rows, duplicate roots and cyclic traversal |
| Shared program interchange | `typed_program_export` | Offline declarations, captured addition, folding schedule, and equality assertion exported as versioned JSON |

## Explicit deferred portions

- Core `unstable-fn.egg` and `eqsat-basic-multiset.egg`: central computations
  need higher-order function containers and runtime application.
- Core `multiset.egg` lines 81–105, 121–130, 143–175 and 184–210: higher-order
  map, flat-map, index fill/clear, reduce and filter. The admitted sum subsection
  is independent of the excluded map setup; its Rust scopes remain balanced.
- Core `cyk.egg` lines 94 and 113: enumeration of ten variants, not the grammar
  cases themselves. Single-best-tree extraction is not claimed as variant parity.
- Core `unification-points-to.egg` final two extraction commands: enumeration of
  100 variants for each allocation root. Both roots are extracted with the
  single-best API; the full swap/f database and both alias checks are retained.
- Python `examples/higher_order_functions.py` and `examples/multiset.py`:
  their central computation needs higher-order map/application.
- Python `examples/jointree.py`: dynamic per-node costs are essential.
- Python `docs/tutorials/sklearn.ipynb`: sklearn/array API/Numba/Python-object
  integration and benchmarking are outside the typed v1 boundary.
- Python analysis lesson lines 201–219: table debugging/row APIs and variants.
- Python scheduling lesson lines 200–248: table-size/custom scheduler section.
- Python extraction lesson lines 100–151: dynamic per-node cost section.

`pathproof` uses ordinary proof terms, not proof mode. The lambda example's
host closures author syntax rather than run as native callbacks. The ndarray
example is symbolic and has no NumPy runtime dependency. Both Herbie programs
use ordinary table analyses rather than custom extraction callbacks.

The core language-reference recipes in `src/ast/mod.rs` and
`egglog-ast/src/generic_ast.rs` map to the basics, Datalog, scheduling,
extraction and subsumption examples. Stale schematic `:on_merge` syntax,
mutable named-group late-add semantics, table/CSV printing and advanced
extraction do not introduce new typed v1 capabilities. Extraction ties remain
native ties; examples do not promise a particular equal-cost representative.

## Validation

Run the source-aligned examples and regressions with:

```sh
cargo test --no-default-features --features typed --test typed_examples --test typed_example_regressions
cargo test --no-default-features --features typed --doc
```

Source-specific API regressions live in `tests/typed_example_regressions.rs`,
including rational-only symbolic arithmetic that must still require its domain
rules. The complete typed test suite also checks declarations, binders, lowering,
observation, and compile-fail contracts.
