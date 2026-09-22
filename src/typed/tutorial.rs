//! # Learn the typed Rust API
//!
//! These six lessons are an entry point into the full 46-example corpus. Each
//! lesson's complete program is the standalone Cargo example also executed by
//! the `typed_examples` integration tests. Run one using, for example,
//! `cargo run --no-default-features --features typed --example typed_tutorial_basics`.
//!
//! See `docs/typed-example-coverage.md` in the source package for the complete
//! source-to-example map and precise v1 exclusions. The examples supplement,
//! rather than replace, the Luminal ReferenceRuntime CPU acceptance gate.
//!
//! A `#[ruleset]` function declares a fixed, lazy theory. Its borrowed typed
//! parameters, such as `x: &Num`, introduce fresh query variables when the
//! definitions are first built. Both the attribute and ordinary callbacks accept
//! up to 128 borrowed parameters; each rule binds its variables independently.
//! Its diagnostic name defaults to `module::function`;
//! use `#[ruleset(name = ...)]` only when an explicit name is needed.
//! Keep fixed theories at module scope. Return `Vec<Rule>` when authoring rules;
//! return a `Ruleset` when composing existing groups and retaining their occurrences.
//! Start an ordinary session with `EGraph::default()`; pass `EGraphOptions` to
//! `EGraph::new(options)` only when changing the configuration.
//! Reuse rulesets directly; ordinary calls and builtins retain owned,
//! shared expression nodes. Ordinary local expression values can be borrowed
//! when reused without adding a lifetime to the resulting expression graph.
//! Bind pure shared patterns before the rule list, then write its rules directly.
//! Keep loop-dependent expressions and runtime choices in their authoring scope.
//! Use `var::<Num>("x")` for named variables, or an ordinary `ruleset(|x: &Num| ...)`
//! callback for local or parameterized definitions with fresh variables.
//! Owned variables can be reused across callbacks, rules, checks, and
//! stopping queries; each query binds them independently.
//! For a query pattern, give each unconstrained argument a distinct named
//! variable or borrowed callback parameter, or use a fresh named argument record
//! for a large call. A matched expression can be reused
//! in rule actions; every variable must be query-bound before RHS use.
//! Use an expression directly as a fact when only its existence matters:
//! `rule(&pattern, actions)` or `egraph.check(&pattern)`. Keep `eq` for an actual
//! equality constraint or a result variable used elsewhere. Primitive expression
//! facts require successful evaluation, not boolean truth; use `eq(value, true)`
//! for a boolean condition. Queries do not materialize missing constructor rows.
//! `rule(lhs, rhs)` authors queries and ordered actions; `rewrite(lhs, rhs)`
//! authors equality rewrites with optional `.when(facts)` conditions.
//! `birewrite(lhs, rhs)` returns an ordinary `[Rule; 2]`, one per direction;
//! customize their conditions with `.map(|rule| rule.when(facts))`.
//! Definitions are infallible values; individual rules and groups need no `Ok` or `?`
//! wrappers. Submission validates and executes them; `Ruleset::to_ast()` lowers a
//! group for diagnostic inspection without executing it.
//! `register(items)` accepts precisely the same expression, relation, and action
//! inputs as a rule's RHS, including nested borrowed tuples and collections.
//! Query facts belong in `check`; submit rules and rulesets through a schedule.
//! Declare a named `#[sort]` struct, then methods and standard operators with
//! `#[declarations]`. A bodyless method with an equality-sort output declares a
//! constructor; one without a return type declares a relation. Primitive outputs
//! require `#[function(no_merge)]` or an explicit merge policy. Methods with bodies
//! remain ordinary Rust. Calls accept borrowed values and supported literals.
//! Declaration names default to their qualified Rust paths, including the owner
//! for methods and the trait for trait methods. Reexports preserve identity.
//! Add callable attributes only for meaningful options; reserve `name = ...` for
//! intentional shared identities, not old spellings or capitalization.
//! Simple merge policies belong directly in the attribute as typed closures,
//! such as `merge = |old: I64, new: I64| old.max(new)`; `no_merge` stays explicit.
//! On a unary free or associated constructor without a receiver,
//! `#[constructor(from)]` generates concrete `From` implementations for its input
//! type and a borrowed input. List additional inputs explicitly, such as
//! `#[constructor(from(i32, i64))]`. These conversions
//! choose application constructors; typed call parameters and operator RHSs accept
//! those values through `Into`. Keep nontrivial conversions in ordinary Rust.
//! Use literals where the receiving sort is known, for example `ne(name, "RELU")`,
//! `set(count(expr), 0)`, or `rewrite(x + 0, x)`. Keep an explicit symbolic value
//! where it determines the operation's sort or a homogeneous collection's type.
//! Add conversion routes when real call sites use them. Prefer a named constructor
//! for a standalone value, such as `Num::constant(2)` or `Num::var("x")`.
//! For example, `Num::constant(2) * (&x * 3)` retains the same ordered syntax as
//! explicit constant constructors. Keep the symbolic left operand and original
//! parentheses: native arithmetic and reverse operators are not inferred.
//! `Num::from("x")` creates a named application node, not `var::<Num>("x")`.
//! Keep constructors explicit when binding their fields in a query or selecting
//! a callable. Conversions never evaluate a symbolic value or import an observed
//! frozen reference; `TryFrom` inspection remains an explicit fallible boundary.
//! Inspect a call with `get_args(&expr, |x: &Num, y: &Num| x + y)?`.
//! The selector runs once on fresh inputs and must return a direct call over
//! every input exactly once in order. It identifies a callable, not a partial
//! pattern: constants, nested expressions, reordered inputs, and omissions are
//! errors. The result is an optional tuple of typed arguments.
//! Submit a ruleset directly with `egraph.run(&group)?`, or build a schedule
//! with `group.saturate()`, `group.repeat(3)`, or `group.until(facts)`.
//! A sequence can mix rulesets and schedules: `sequence((&first, second.saturate()))`.
//! Submit a temporary directly, as in `egraph.run(group.saturate())?`, or borrow
//! a reusable schedule with `egraph.run(&schedule)?`. These forms do not create
//! new rule occurrences or reset their incremental cursors.
//!
//! ## Partial patterns and matched field updates
//!
//! Keep small calls positional. For a call with many fields, opt into one record
//! with `args = Name`. Its owned fields have the declaration's exact symbolic
//! types. `Name::fresh()` creates a distinct query variable for every field;
//! ordinary struct update can constrain just the fields that matter.
//! Reuse that record on the RHS to preserve its other matched fields:
//!
//! ```rust
//! use egglog_experimental::typed::{prelude::*, builtins as egg};
//!
//! #[sort]
//! struct Matrix;
//! #[constructor]
//! fn input(name: egg::String) -> Matrix;
//! #[constructor]
//! fn relu(value: Matrix) -> Matrix;
//! #[constructor(args = MatmulArgs)]
//! fn matmul(left: Matrix, right: Matrix, rows: egg::I64, cols: egg::I64,
//!           inner: egg::I64, epilogue: egg::String) -> Matrix;
//!
//! #[ruleset]
//! fn fuse_relu() -> Rule {
//!     let args = MatmulArgs {
//!         epilogue: "NONE".into(),
//!         ..MatmulArgs::fresh()
//!     };
//!     rewrite(relu(args.clone()), MatmulArgs { epilogue: "RELU".into(), ..args })
//! }
//!
//! let original = relu(matmul(input("a"), input("b"), 2, 3, 4, "NONE"));
//! let mut graph = EGraph::default();
//! graph.register(&original)?;
//! graph.run(&fuse_relu)?;
//! assert!(graph.check(eq(original, matmul(input("a"), input("b"), 2, 3, 4, "RELU")))?);
//! # Ok::<(), TypedError>(())
//! ```
//!
//! Fresh fields are not defaults and do not inherit from another call. A second
//! `fresh()` has independent variables; cloning or `..args` retains their identity.
//! Use `..args.clone()` when the same matched fields are needed again. Explicitly
//! share fields when two patterns must agree, such as `rows: first.rows.clone()`.
//! New variables appearing only on the RHS are rejected when submitting the rule.
//! Field literals and borrowed values require `.into()` because struct fields
//! have concrete owned types; ordinary calls still accept them directly.
//! Struct update requires the same record type, not a different constructor's.
//! `From<Record>` constructs the original call; use `Matrix::from(args.clone())`
//! when an explicit sort anchor is needed, such as a direct rewrite LHS. Records
//! also support functions and relations; use `Relation::from(args)` for a relation
//! fact. `Name::get_args(&call)` inspects an exact existing call, not an unknown
//! query variable or an unselected frozen class. It never evaluates the fields.
//!
//! ## Native values and reverse conversions
//!
//! Use `From` to construct symbolic expressions and `TryFrom` to read concrete
//! values. A unary constructor can generate both directions. Bare `try_from`
//! unwraps its input sort; `try_from(T, U)` also converts the field using those
//! types' existing `TryFrom<Input>` implementations. Both owned and borrowed
//! expressions are supported. This is inspection, not evaluation or extraction.
//!
//! ```rust
//! use egglog_experimental::typed::{prelude::*, builtins as egg};
//!
//! #[sort]
//! struct Number;
//!
//! #[declarations]
//! impl Number {
//!     #[constructor(from(i64), try_from(i64))]
//!     fn constant(value: egg::I64) -> Number;
//! }
//!
//! let number = Number::from(5_i64);
//! assert_eq!(i64::try_from(&number)?, 5);
//! let value: i64 = number.try_into()?;
//! assert_eq!(value, 5);
//! let expression = Number::constant(egg::I64::from(2) + 3);
//! assert!(i64::try_from(&expression).is_err()); // The field is not a literal.
//! assert_eq!(egg::I64::try_from(&expression)?, egg::I64::from(2) + 3);
//! let mut egraph = EGraph::default();
//! assert_eq!(i64::try_from(egraph.extract(&expression)?)?, 5);
//! # Ok::<(), TypedError>(())
//! ```
//!
//! Reverse conversions are opt-in and require the annotated constructor, not
//! another call returning the same sort. Each claims a Rust conversion to its
//! input sort and listed targets; overlapping claims are compile errors. Listed
//! targets must be owned, with conversion errors implementing `Display` (their
//! messages become `TypedError::Decode`). Container conversions keep immediate
//! symbolic children; they do not recursively convert or evaluate them. Write
//! substantive conversions as ordinary Rust `TryFrom` implementations instead.
//! Methods with bodies remain ordinary Rust; no "preserve" annotation is needed.
//!
//! Python's builtin `.value` has this inspection role; the experimental array
//! API's `.eval()` additionally runs its domain rules and extracts. In Rust,
//! keep domain schedules explicit with `run`, then extract and convert. Frozen
//! equality classes require an explicit producer choice before call inspection;
//! conversion never picks another alternative or makes an observed value live again.
#![doc = concat!(
    "\n## 1. Values, queries, and equality saturation\n\nStart with a named sort, associated constructors, and standard operators.\nOrdinary Rust values author syntax; explicit captures retain installed results.\nQueries do not insert terms, and rules do not run until a schedule is submitted.\n\n```rust\n",
    include_str!("../../examples/typed_tutorial_basics.rs"),
    "\n```\n"
)]
#![doc = concat!(
    "\n## 2. Relations and functional tables\n\nA relation records a fact. A table has an explicit duplicate-output policy.\nThe three cases connect reachability, shortest paths and equality-sort vertices.\n\n```rust\n",
    include_str!("../../examples/typed_tutorial_datalog.rs"),
    "\n```\n"
)]
#![doc = concat!(
    "\n## 3. Let analyses inform rewriting\n\nThe same table/rule interface expresses inequalities and interval bounds.\nFirst, the shared theory from `examples/typed_support/arithmetic.rs`: each\n`#[ruleset]` function declares an immutable theory constructed once on first use.\nRefer to its name as a value, without calling it. Its ordinary Rust body authors\ndefinitions without creating or running an EGraph.\n\n```rust\n",
    include_str!("../../examples/typed_support/arithmetic.rs"),
    "\n```\n\nNow compose those groups and use the analysis to guard rewriting. The next\nlesson imports the same theory; it is not a separate execution backend.\n\n```rust\n",
    "# #[path = \"../../examples/typed_support/arithmetic.rs\"]\n# mod theory;\n# #[cfg(any())]\n",
    include_str!("../../examples/typed_tutorial_analysis.rs"),
    "\n```\n"
)]
#![doc = concat!(
    "\n## 4. Control when rules run\n\nReuse the arithmetic theory shown in lesson 3. Immutable groups retain rule\noccurrences. A sequence creates separate runs, and saturation/repetition preserve\nnative stopping behavior. Explicit push/pop makes the one-round and two-round\ncomparisons independent.\n\n```rust\n",
    "# #[path = \"../../examples/typed_support/arithmetic.rs\"]\n# mod theory;\n# #[cfg(any())]\n",
    include_str!("../../examples/typed_tutorial_scheduling.rs"),
    "\n```\n"
)]
#![doc = concat!(
    "\n## 5. Extract a representative with a known cost\n\nStatic constructor costs participate in native best-tree extraction. Ordered\nmulti-root extraction shares reconstruction, not a joint optimization objective.\n\n```rust\n",
    include_str!("../../examples/typed_tutorial_extraction.rs"),
    "\n```\n"
)]
#![doc = concat!(
    "\n## 6. Keep an exact snapshot and traverse its values\n\nFreeze takes no roots and owns its data. Look up retained captures as the same\ntyped sort wrappers, choose an ordered output list later, and traverse cycles\nwithout expanding them. Select a constructor with `nodes(&class)?` before\ninspecting its arguments; a stored class is not a selected call. Scalar `TryFrom`\nreads exact native payloads, and container decoding retains immediate observed\nchildren. Typed tables include installed empty tables and function outputs, which\nare not constructor alternatives. No observation invokes primitives or extraction.\nObserved wrappers retain their snapshot after the graph is mutated or dropped,\nand cannot be submitted to live execution.\n\n```rust\n",
    include_str!("../../examples/typed_freeze.rs"),
    "\n```\n"
)]
