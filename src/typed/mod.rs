//! Ordinary Rust authoring backed directly by generated protobuf records.
//!
//! This initial subset supports equality sorts/constructors, merged functions, relation predicates, exact selectors,
//! callback rules/rewrites, immutable groups, ordered Run/Repeat/Saturate
//! schedules and byte-backed register/check/extract/freeze observations.
//! Flat and composed groups lower to ordered AddRules and union Run selections.
//! Equal rule content shares native registration and cursor state across groups.
//! An undecodable or malformed reply makes that handle unusable; ordinary engine
//! failures retain completed prefixes and permit compatible retries.
//! `EGraph::try_clone` clones native state/cursors and binding observations;
//! subsequent mutations are independent. No definitions or commands are replayed.
//! `push`/`pop` explicitly save/restore native data, cursors and typed bindings.
//! Pop retains collected cumulative diagnostics and fresh-name state, and can recover
//! an uncertain current transport state from its known healthy saved scope.
//! A clone starts with an empty scope stack, even inside a scope. Dropping a graph
//! discards its owned handles; it does not pop or merge work into another graph.
//! `run` returns the backend's `updated` and scheduler-aware `can_stop` flags.
//! `run_with_diagnostics` also returns an opaque backend diagnostic; `stats`
//! observes cumulative diagnostics. Detailed collection is opt-in.
//! `Schedule::with_snapshots` chooses the observation cadence; `run_stream`
//! delivers those owned snapshots during execution and supports cancellation.
//! I64/F64 arithmetic, String/Bool operations, Unit literals and generic
//! Vec/Pair/Map operations use engine-owned metadata.
//! Ordered container decoding retains child expression ownership. Foreign open
//! binders, arbitrary declarations and schedule forms beyond Run/Repeat/Saturate
//! are not accepted; no source/AST execution fallback exists. `Snapshot` retains
//! exported classes, producers and table rows without evaluating roots. Its
//! typed observations cannot be submitted as live expressions, even transitively.
//!
//! Scalar conversions and constructor arguments are checked by Rust. Calls
//! author symbolic expressions; they do not evaluate those expressions.
//!
//! `#[relation]` declares an input-only predicate, including an inherent `&self`
//! receiver in the first input position. Its existing `builtins::Unit` expression
//! is a query or row-insertion term, not a decoded native row value. Registering
//! it inserts a row; checking it only tests existence. `delete` addresses the row
//! without evaluating/inserting it. Set, subsumption, extraction, captures and
//! nested value uses and relation equality fail before effects.
//! `Snapshot::rows` exposes retained function/relation rows with shallow typed
//! input/output views; these rows are distinct from constructor producers.
//!
//! ```
//! use egglog_experimental::typed::{builtins::Unit, prelude::*};
//! #[sort] struct List;
//! #[constructor] fn empty() -> List;
//! #[declarations]
//! impl List {
//!     #[relation(name = "marked")]
//!     pub fn marked(&self);
//! }
//! let list = empty();
//! let predicate: Unit = list.marked();
//! let mut graph = EGraph::new()?;
//! assert!(!graph.check(&predicate)?);
//! graph.register(&predicate)?;
//! assert!(graph.check(&predicate)?);
//! graph.register(delete(&predicate))?;
//! assert!(!graph.check(&predicate)?);
//! # Ok::<_, TypedError>(())
//! ```
//! ```compile_fail
//! use egglog_experimental::typed::{builtins::I64, prelude::*};
//! #[relation] fn row(value: I64) -> I64;
//! ```
//! ```compile_fail
//! use egglog_experimental::typed::prelude::*;
//! #[sort] struct List;
//! #[declarations]
//! impl List { #[relation] fn row(&mut self); }
//! ```
//!
//! Ordinary Vec/Map methods retain their element/key types. Vec union is
//! available only for equality-sort elements, not equality-containing containers.
//!
//! ```
//! use egglog_experimental::typed::{builtins::{I64, Vec}, prelude::*};
//! fn append<T: EgglogValue>(xs: &Vec<T>, ys: &Vec<T>) -> Vec<T> { xs.append([ys]) }
//! fn merge<T: EqualitySort>(xs: &Vec<T>, ys: &Vec<T>) -> Vec<T> { xs.union(ys) }
//! let xs = Vec::<I64>::of([1_i64]);
//! let _ = append(&xs, &xs).append(std::iter::empty::<Vec<I64>>()).push(2_i64).set(0_i64, 3_i64).remove(0_i64).pop();
//! ```
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{I64, F64, Vec};
//! let xs = Vec::<I64>::empty();
//! let _ = xs.append([Vec::<F64>::empty()]);
//! ```
//! ```compile_fail,E0599
//! use egglog_experimental::typed::builtins::{I64, Vec};
//! let xs = Vec::<I64>::empty();
//! let _ = xs.union(&xs);
//! ```
//! ```compile_fail,E0599
//! use egglog_experimental::typed::{builtins::Vec, prelude::*};
//! #[sort] struct Atom;
//! let xs = Vec::<Vec<Atom>>::empty();
//! let _ = xs.union(&xs);
//! ```
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{I64, F64, Vec};
//! let _ = Vec::<I64>::empty().push(F64::from(1.0));
//! ```
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{I64, F64, Map};
//! let _ = Map::<I64, I64>::empty().remove(F64::from(1.0));
//! ```
//!
//! `ne(left, right)` is a catalog-generated same-sort Unit fact. The left
//! symbolic value determines the sort; either wrapper may be borrowed and the
//! right operand accepts that wrapper's existing conversions. Inequality is
//! evaluated by the engine, including equality-class merges, not by Rust Eq.
//!
//! Constructor `cost` metadata must be a nonnegative inert `I64` value (Rust
//! integer expressions are converted once when the declaration is initialized).
//! Symbolic calls, variables and captures are rejected on submission rather than
//! evaluated. `unextractable` retains the constructor but excludes it from
//! extraction. Both options are constructor-only.
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::{builtins::F64, prelude::*};
//! #[sort] struct Term;
//! #[constructor(cost = F64::from(1.0))]
//! fn term() -> Term;
//! ```
//! ```compile_fail
//! use egglog_experimental::typed::{builtins::I64, prelude::*};
//! #[function(no_merge, cost = 0)]
//! fn value() -> I64;
//! ```
//! ```compile_fail
//! use egglog_experimental::typed::prelude::*;
//! #[relation(unextractable)]
//! fn predicate();
//! ```
//!
//! ```
//! use egglog_experimental::typed::{builtins::I64, prelude::*};
//! let value = I64::from(7);
//! let mut graph = EGraph::new()?;
//! assert!(graph.check(ne(&value, 0))?);
//! assert!(!graph.check(ne(&value, &value))?);
//! # Ok::<_, TypedError>(())
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::{builtins::{I64, F64}, ne};
//! let _ = ne(&I64::from(1), F64::from(1.0));
//! ```
//! ```compile_fail,E0277
//! use egglog_experimental::typed::prelude::*;
//! #[sort] struct Left;
//! #[sort] struct Right;
//! let _ = ne(var::<Left>("left"), var::<Right>("right"));
//! ```
//! ```compile_fail,E0277
//! use egglog_experimental::typed::{builtins::{I64, F64, Vec}, ne};
//! let _ = ne(Vec::<I64>::of([1]), Vec::<F64>::of([1.0]));
//! ```
//! ```compile_fail,E0308
//! use egglog_experimental::typed::{builtins::I64, ne};
//! let _: I64 = ne(I64::from(1), 2);
//! ```
//! ```compile_fail,E0061
//! use egglog_experimental::typed::{builtins::I64, ne};
//! let _ = ne(I64::from(1));
//! ```
//! ```compile_fail,E0061
//! use egglog_experimental::typed::{builtins::I64, ne};
//! let _ = ne(I64::from(1), 2, 3);
//! ```
//!
//! `Maybe<T>` stores no child or exactly one symbolic child. Its generated
//! `none`, `some`, `unwrap`, and eager `unwrap_or` methods retain the exact T.
//! `Option<T>::try_from(&value)` inspects direct construction or extracted data
//! without evaluating a present child. Some(None) is distinct from outer None.
//!
//! ```
//! use egglog_experimental::typed::{builtins::{I64, Maybe}, prelude::*};
//! let none = Maybe::<I64>::none();
//! let child = I64::from(7);
//! let some = Maybe::<I64>::some(&child);
//! assert_eq!(Option::<I64>::try_from(&some)?, Some(child));
//! assert_eq!(Option::<I64>::try_from(&none)?, None);
//! let nested = Maybe::<Maybe<I64>>::some(&none);
//! assert_eq!(Option::<Maybe<I64>>::try_from(&nested)?, Some(none));
//! let mut graph = EGraph::default();
//! assert_eq!(i64::try_from(&graph.extract(some.unwrap_or(2_i64))?)?, 7);
//! # Ok::<_, TypedError>(())
//! ```
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64, Maybe};
//! let _ = Maybe::<I64>::some(F64::from(1.0));
//! ```
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64, Maybe};
//! let _ = Maybe::<I64>::none().unwrap_or(&F64::from(1.0));
//! ```
//! ```compile_fail,E0061
//! use egglog_experimental::typed::builtins::{I64, Maybe};
//! let _ = Maybe::<I64>::none(1_i64);
//! ```
//! ```compile_fail,E0061
//! use egglog_experimental::typed::builtins::{I64, Maybe};
//! let _ = Maybe::<I64>::some();
//! ```
//! ```compile_fail,E0308
//! use egglog_experimental::typed::builtins::{F64, I64, Maybe};
//! let _: F64 = Maybe::<I64>::some(1_i64).unwrap();
//! ```
//!
//! Rule queries accept facts; registration and ordered rule heads share one
//! canonical action input conversion, including `union`, `set`, `delete` and
//! `subsume` actions.
//! A fact is never an implicit union action.
//! Conditions append to the query of a new immutable rule; existing clones keep
//! their original body. Each rule closes its whole binder once at submission.
//!
//! `#[ruleset]` turns a monomorphic, safe Rust function into one lazily initialized
//! immutable group. Its ordinary body and concrete or inferred output author
//! rules through the existing callback, with up to 64 immutable borrowed inputs.
//! The default native binding name is the module-qualified function name;
//! `#[ruleset(name = expression)]` uses that exact name expression once, after
//! the body. Named composition captures the explicitly authored rule values
//! into that group; later runtime additions to child groups do not change the
//! captured membership. Anonymous composition selects the union of its groups.
//! Cloning or composing `&LazyLock<Ruleset>` inputs preserves rule content and
//! native cursors. A second graph registers that content in independent state.
//! The generated item is a static, so normal Rust restrictions on shadowing its
//! name with a parameter or local binding still apply. Opaque `impl Trait`
//! callback inputs/outputs are not supported; concrete and inferred outputs are.
//!
//! ```
//! use egglog_experimental::typed::prelude::*;
//! #[sort] struct LazyItem;
//! #[declarations] impl LazyItem { fn Before() -> Self; fn After() -> Self; }
//! #[ruleset(name = "example::copy")]
//! fn copy() -> Rule { rule(LazyItem::Before(), LazyItem::After()) }
//! let group = ruleset((&copy, &copy));
//! let mut graph = EGraph::new()?;
//! graph.register(LazyItem::Before())?;
//! graph.run(&group)?;
//! assert!(graph.check(LazyItem::After())?);
//! # Ok::<_, TypedError>(())
//! ```
//! ```compile_fail
//! use egglog_experimental::typed::prelude::*;
//! #[ruleset]
//! fn generic<T>(value: &T) {}
//! ```
//! ```compile_fail,E0530
//! use egglog_experimental::typed::{builtins::I64, prelude::*};
//! #[ruleset]
//! fn parameter(parameter: &I64) {}
//! #[ruleset]
//! fn local() { let local = (); }
//! ```
//!
//! Functions are table reads, not constructor data. `set` addresses a direct
//! function call without reading its row; `delete` addresses a function or
//! constructor row without creating it. Invalid targets return a submission
//! error, not an authoring panic. Actions and nested collections preserve order.
//! `union` explicitly joins same-sort equality values; `subsume` applies native
//! constructor subsumption by row address, without an authored target lookup.
//! Unlike Delete, native subsumption may create an absent constructor row.
//! Observe an established root to avoid reauthoring the subsumed constructor.
//! A cloned union action retains its occurrence: repeating it in one submission
//! or one rule head rejects; independently authored unions stay distinct.
//! Nested Union values are not supported. Captures remain forbidden in rules.
//!
//! ```
//! use egglog_experimental::typed::prelude::*;
//! #[sort] struct Item;
//! #[declarations] impl Item { fn Before() -> Self; fn After() -> Self; }
//! let before = Item::Before();
//! let after = Item::After();
//! let root = let_("root", &before);
//! let mut graph = EGraph::new()?;
//! graph.register(&root)?;
//! graph.register((union(&before, &after), subsume(&before)))?;
//! assert_eq!(graph.extract(&root)?, after);
//! # Ok::<_, TypedError>(())
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::prelude::*;
//! #[sort] struct Left;
//! #[sort] struct Right;
//! let _ = union(var::<Left>("x"), var::<Right>("y"));
//! ```
//! ```compile_fail,E0277
//! use egglog_experimental::typed::{builtins::I64, union};
//! let _ = union(I64::from(1), 2);
//! ```
//! ```compile_fail,E0061
//! use egglog_experimental::typed::prelude::*;
//! #[sort] struct Item;
//! let _ = union(var::<Item>("x"));
//! ```
//! ```compile_fail,E0061
//! use egglog_experimental::typed::prelude::*;
//! #[sort] struct Item;
//! let x = var::<Item>("x");
//! let _ = union(&x, &x, &x);
//! ```
//!
//! Named argument records inspect exact call syntax without querying an engine:
//!
//! ```
//! use egglog_experimental::typed::{builtins::I64, prelude::*};
//! #[function(no_merge, args = ReadArgs)]
//! fn read(key: I64) -> I64;
//! let call = read(1);
//! assert_eq!(ReadArgs::get_args(&call)?.unwrap().key, I64::from(1));
//! let mut graph = EGraph::new()?;
//! graph.register(set(&call, 10))?;
//! assert_eq!(i64::try_from(&graph.extract(&call)?)?, 10);
//! graph.register((delete(&call), set(&call, 20)))?;
//! assert_eq!(i64::try_from(&graph.extract(&call)?)?, 20);
//! # Ok::<_, TypedError>(())
//! ```
//!
//! `let_(label, initializer)` is an inert, structurally comparable capture recipe.
//! Registering or extracting a fresh capture initializes it once at that ordered
//! evaluation point; subsequent uses read its saved value. The same label in a
//! live scope must retain the same sort and initializer. Empty and UTF-8 labels
//! are supported. Captures are opaque to call selectors and cannot be row targets.
//! Check requires captures already established; rules, rewrites and conditions
//! reject them. Clone copies observations, and pop restores the saved captures
//! without recycling private names. Failed commands confirm only earlier completed
//! initializers; uncertain receipts require recovery through a saved scope.
//!
//! ```
//! use egglog_experimental::typed::{builtins::I64, prelude::*};
//! #[function(no_merge)] fn read(key: I64) -> I64;
//! let before = let_("before", read(1));
//! let after = let_("after", read(1));
//! let mut graph = EGraph::new()?;
//! graph.register((set(read(1), 10), &before, delete(read(1)), set(read(1), 20), &after))?;
//! assert_eq!(i64::try_from(&graph.extract(&before)?)?, 10);
//! assert_eq!(i64::try_from(&graph.extract(&after)?)?, 20);
//! # Ok::<_, TypedError>(())
//! ```
//!
//! This Normal-mode capture subset admits direct fallible/table-read initializers
//! and fresh captures nested in constructor/value-only surrounding syntax. Fresh
//! capture nesting beside a table read, Union or host call is rejected before
//! execution. Established captures are closed leaves. Full nested-host support
//! awaits authoritative totality/effect metadata; no local builtin-name list or
//! evaluated-value cache substitutes for it.
//!
//! Binary constructor declarations for qualified `std::ops`/`core::ops`
//! `Add`, `Sub`, `Mul`, `Div` and `Rem` share one definition across owned and
//! borrowed left operands and right operands convertible to the declared sort.
//! They construct Calls, not host arithmetic. The original Rust signature must
//! still agree with the declared trait RHS and associated output.
//! Operator names are evaluated once in a nongeneric definition context, not
//! in an owned/borrowed operator call. Literals and module-level function calls
//! are supported; generated `Self` and operand-dependent names are not.
//!
//! ```compile_fail,E0411
//! use egglog_experimental::typed::prelude::*;
//! #[sort] struct Term;
//! #[declarations]
//! impl std::ops::Add<&Term> for &Term {
//!     type Output = Term;
//!     #[constructor(name = std::any::type_name::<Self>())]
//!     fn add(self, rhs: &Term) -> Term;
//! }
//! ```
//! ```compile_fail,E0425
//! use egglog_experimental::typed::prelude::*;
//! #[sort] struct Term;
//! #[declarations]
//! impl std::ops::Add<&Term> for &Term {
//!     type Output = Term;
//!     #[constructor(name = std::any::type_name_of_val(&rhs))]
//!     fn add(self, rhs: &Term) -> Term;
//! }
//! ```
//!
//! ```compile_fail,E0053
//! use egglog_experimental::typed::{builtins::I64, prelude::*};
//! #[sort] struct Term;
//! #[declarations]
//! impl Term { #[constructor(from)] fn Num(value: I64) -> Self; }
//! #[declarations]
//! impl std::ops::Add<I64> for &Term {
//!     type Output = Term;
//!     #[constructor] fn add(self, rhs: &Term) -> Term;
//! }
//! ```
//! ```compile_fail,E0053
//! use egglog_experimental::typed::prelude::*;
//! #[sort] struct Term;
//! #[sort] struct Other;
//! #[declarations]
//! impl std::ops::Add<&Term> for &Term {
//!     type Output = Other;
//!     #[constructor] fn add(self, rhs: &Term) -> Term;
//! }
//! ```
//! ```compile_fail
//! use egglog_experimental::typed::prelude::*;
//! #[sort] struct Term;
//! #[declarations]
//! impl std::ops::Sub<&Term> for &Term {
//!     type Output = Term;
//!     #[constructor] fn add(self, rhs: &Term) -> Term;
//! }
//! ```
//! ```compile_fail
//! use egglog_experimental::typed::prelude::*;
//! #[sort] struct Term;
//! #[declarations]
//! impl std::ops::Add<&Term> for &Term {
//!     type Output = Term;
//!     #[constructor] fn add(&mut self, rhs: &Term) -> Term;
//! }
//! ```
//! ```compile_fail,E0119
//! use egglog_experimental::typed::prelude::*;
//! #[sort] struct Term;
//! #[declarations]
//! impl std::ops::Add<&Term> for &Term {
//!     type Output = Term;
//!     #[constructor] fn add(self, rhs: &Term) -> Term;
//! }
//! impl std::ops::Add<&Term> for &Term {
//!     type Output = Term;
//!     fn add(self, _: &Term) -> Term { self.clone() }
//! }
//! ```
//! Ordinary body-bearing trait implementations are left unchanged; they do not
//! silently gain owned-left or conversion-based operator implementations.
//!
//! ```compile_fail,E0369
//! use egglog_experimental::typed::prelude::*;
//! struct Term;
//! #[declarations]
//! impl std::ops::Add<&Term> for &Term {
//!     type Output = Term;
//!     fn add(self, _: &Term) -> Term { Term }
//! }
//! let _ = Term + &Term;
//! ```
//!
//! Key, named field and assigned value sorts remain statically checked:
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::{builtins::{I64, F64}, prelude::*};
//! #[function(no_merge)] fn read(key: I64) -> I64;
//! let _ = read(F64::from(1.0));
//! ```
//! ```compile_fail,E0277
//! use egglog_experimental::typed::{builtins::{I64, F64}, prelude::*};
//! #[function(no_merge)] fn read(key: I64) -> I64;
//! let _ = set(read(1), F64::from(1.0));
//! ```
//! ```compile_fail,E0308
//! use egglog_experimental::typed::{builtins::{I64, F64}, prelude::*};
//! #[function(no_merge, args = ReadArgs)] fn read(key: I64) -> I64;
//! let _ = ReadArgs { key: F64::from(1.0) };
//! ```
//!
//! Functions explicitly select exactly one of `no_merge` or a two-argument
//! `merge` closure. `no_merge` asserts equality on conflicting writes; it is
//! not keep-new. A merge closure authors immutable deferred syntax once per
//! definition, over owned output-sort `old` and `new` values. Only those two
//! variables are bound; captures and other free variables are rejected before
//! execution. Native write-context validation retains each callee's actual
//! capabilities. Table callees require installed backends: acyclic declarations
//! install in dependency order, while unsupported dependency cycles reject
//! before publication or actions. Implicit defaults remain absent.
//! Merge variables must be that definition's own old/new parameters, not ones
//! retained from another callback. Same-thread recursive or mutually recursive
//! merge initialization panics during authoring, before waiting on its definition;
//! ordinary concurrent initialization and retries after callback panics retain
//! OnceLock behavior. Cross-thread initialization cycles are not detected.
//! Wire-native merge validation still returns submission errors.
//! Inherent functions support `&self`; named argument records still require
//! explicit owned arguments. `from`/`try_from` remain constructor-only.
//!
//! ```
//! use egglog_experimental::typed::{builtins::I64, prelude::*};
//! #[sort] struct Dim;
//! #[declarations]
//! impl Dim {
//!     fn Num(value: I64) -> Self;
//!     #[function(merge = |old: I64, new: I64| old.max(new))]
//!     fn lower(&self) -> I64;
//! }
//! let value = Dim::Num(1);
//! let mut graph = EGraph::new()?;
//! graph.register((set(value.lower(), 10), set(value.lower(), 30), set(value.lower(), 20)))?;
//! assert_eq!(i64::try_from(&graph.extract(value.lower())?)?, 30);
//! # Ok::<_, TypedError>(())
//! ```
//!
//! ```compile_fail
//! use egglog_experimental::typed::{builtins::I64, prelude::*};
//! #[function(no_merge, merge = |old: I64, new: I64| old.max(new))]
//! fn read(key: I64) -> I64;
//! ```
//! ```compile_fail,E0308
//! use egglog_experimental::typed::{builtins::{I64, F64}, prelude::*};
//! #[function(merge = |_: I64, _: I64| F64::from(1.0))]
//! fn read(key: I64) -> I64;
//! ```
//!
//! ```compile_fail
//! use egglog_experimental::typed::{builtins::I64, prelude::*};
//! #[function(no_merge, from)] fn read(key: I64) -> I64;
//! ```
//! ```compile_fail
//! use egglog_experimental::typed::{builtins::I64, prelude::*};
//! #[function(no_merge, try_from)] fn read(key: I64) -> I64;
//! ```
//! ```compile_fail
//! use egglog_experimental::typed::{builtins::I64, prelude::*};
//! #[function] fn read(key: I64) -> I64;
//! ```
//! ```compile_fail
//! use egglog_experimental::typed::{builtins::I64, prelude::*};
//! #[function(no_merge, args = "NotARecord")] fn read(key: I64) -> I64;
//! ```
//! ```compile_fail,E0277
//! use egglog_experimental::typed::{builtins::I64, prelude::*};
//! #[function(no_merge)] fn read(key: I64) -> I64;
//! let _ = read(set(read(1), 2)); // an action is not an expression value
//! ```
//!
//! ```
//! use egglog_experimental::typed::{builtins::I64, prelude::*};
//! #[sort]
//! struct Term;
//! #[declarations]
//! impl Term {
//!     fn Input(value: I64) -> Self;
//!     fn Seen(value: I64) -> Self;
//! }
//! let marks = ruleset(|x: &I64| rule(Term::Input(x), Term::Seen(x)).when(eq(x, 7)));
//! let mut graph = EGraph::default();
//! graph.register([Term::Input(7), Term::Input(8)])?;
//! graph.run(&marks)?;
//! assert!(graph.check(Term::Seen(7))?);
//! assert!(!graph.check(Term::Seen(8))?);
//! let stats = graph.stats()?;
//! assert!(!stats.content.is_empty());
//! let shared = ruleset((&marks, &marks)); // canonical composition, no rule copies
//! graph.run(&shared)?;
//! let mut snapshots = Vec::new();
//! graph.run_stream(Schedule::from(&shared).with_snapshots().repeat(2), |snapshot| {
//!     snapshots.push(snapshot);
//!     std::ops::ControlFlow::Continue(())
//! })?;
//! assert_eq!(snapshots.len(), 2);
//! graph.push()?;
//! graph.register(Term::Input(9))?;
//! assert!(graph.check(Term::Input(9))?);
//! graph.pop()?;
//! assert!(!graph.check(Term::Input(9))?);
//! # Ok::<(), TypedError>(())
//! ```
//!
//! Query equalities cannot be registered or used as a rule head:
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::{builtins::I64, prelude::*};
//! let _ = rule((), eq(I64::from(1), 1));
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::{builtins::I64, prelude::*};
//! let _ = EGraph::default().register(eq(I64::from(1), 1));
//! ```
//!
//! Rule records are not values, and collections must contain rules or groups:
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::prelude::*;
//! let _ = EGraph::default().register(rule((), ()));
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::prelude::*;
//! let _ = ruleset(vec![7_i64]);
//! ```
//!
//! Callbacks borrow fresh variables; an owned callback parameter is not admitted:
//!
//! ```compile_fail
//! use egglog_experimental::typed::{builtins::I64, prelude::*};
//! let _ = ruleset(|_: I64| rule((), ()));
//! ```
//!
//! ```
//! use egglog_experimental::typed::{builtins::{F64, I64}, prelude::*};
//!
//! #[sort]
//! pub struct Term;
//! #[declarations]
//! impl Term {
//!     pub fn Num(value: I64) -> Self;
//!     pub fn Pair(left: Term, right: Term) -> Self;
//! }
//!
//! let integer = I64::from(7_i64);
//! let _: I64 = &integer + I64::from(&11_i64);
//! let float = F64::from(1.5_f64);
//! let _: F64 = &float + F64::from(&2.5_f64);
//! let left = Term::Num(7_i64);
//! let right = Term::Num(&integer);
//! let _: Term = Term::Pair(&left, right);
//! ```
//!
//! String owns UTF-8 data, Bool preserves false, and Unit converts to `()`.
//! `join` takes one iterable. Scalar methods accept host values or borrowed
//! wrappers of the exact sort; operators accept owned and borrowed wrappers.
//! Host decoding inspects literals and returns an error for symbolic calls.
//!
//! ```
//! use egglog_experimental::typed::{builtins::{Bool, I64, String as EString, Unit, join}, prelude::*};
//! let text = EString::from("a\0b\n☃");
//! let _: EString = &text + &text;
//! let _: EString = join([&text, &text]);
//! let _: EString = join(std::iter::empty::<&str>());
//! let _: EString = text.replace("b", I64::from(7).to_string());
//! let flag = Bool::from(false);
//! let _: Bool = (!&flag | Bool::from(true)).implies(&flag);
//! assert!(!bool::try_from(&flag)?);
//! let _: () = (&Unit::from(())).try_into()?;
//! # Ok::<(), TypedError>(())
//! ```
//!
//! Big-number methods remain symbolic. Shifts take `I64`, rational projections
//! return `BigInt`, and ordering predicates return `Unit`, not host `bool`.
//!
//! ```
//! use egglog_experimental::typed::builtins::{BigInt, BigRat, I64, Unit};
//! let integer = BigInt::from_string("123456789012345678901");
//! let ratio = BigRat::new(&integer, BigInt::new(2));
//! let _: BigInt = &integer << I64::from(3);
//! let _: BigInt = &integer >> &I64::from(3);
//! let _: BigRat = -&ratio;
//! let _: BigInt = ratio.clone().numer();
//! let _: Unit = ratio.clone().lt(&ratio);
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::BigInt;
//! let _ = BigInt::new(1) << BigInt::new(2);
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{BigInt, F64};
//! let _ = BigInt::new(1) >> F64::from(2.0);
//! ```
//!
//! ```compile_fail,E0308
//! use egglog_experimental::typed::builtins::{BigInt, BigRat};
//! let _: BigRat = BigRat::new(BigInt::new(1), BigInt::new(2)).numer();
//! ```
//!
//! ```compile_fail,E0061
//! use egglog_experimental::typed::builtins::{BigInt, BigRat};
//! let _ = BigRat::new(BigInt::new(1), BigInt::new(2)).denom(BigInt::new(3));
//! ```
//!
//! ```compile_fail,E0308
//! use egglog_experimental::typed::builtins::{BigInt, BigRat};
//! let ratio = BigRat::new(BigInt::new(1), BigInt::new(2));
//! let _: bool = ratio.clone().lt(&ratio);
//! ```
//!
//! The scalar family, argument shape and result remain checked by Rust:
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{Bool, join};
//! let _ = join([Bool::from(false)]);
//! ```
//!
//! ```compile_fail,E0061
//! use egglog_experimental::typed::builtins::join;
//! let _ = join(["a"], ["b"]);
//! ```
//!
//! ```compile_fail,E0061
//! use egglog_experimental::typed::builtins::String;
//! let _ = String::from("text").replace("old");
//! ```
//!
//! ```compile_fail,E0061
//! use egglog_experimental::typed::builtins::String;
//! let _ = String::from("text").replace("old", "new", "extra");
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{Bool, String};
//! let _ = String::from("text").replace("old", Bool::from(false));
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{Bool, String};
//! let _ = Bool::from(true) | String::from("false");
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::Bool;
//! let _ = Bool::from(1_i64);
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::Unit;
//! let _ = Unit::from(false);
//! ```
//!
//! ```compile_fail,E0308
//! use egglog_experimental::typed::builtins::{Bool, I64};
//! let _: Bool = I64::from(7).to_string();
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::{builtins::{Bool, String}, prelude::*};
//! #[sort]
//! pub struct Term;
//! #[declarations]
//! impl Term { pub fn Text(value: String) -> Self; }
//! let _ = Term::Text(Bool::from(false));
//! ```
//!
//! Vector element and result types remain precise through generic functions,
//! borrowed elements, empty iterators, and nested vectors:
//!
//! ```
//! use egglog_experimental::typed::{builtins::{I64, Vec as EVec}, EgglogValue};
//!
//! fn singleton<T: EgglogValue>(value: impl Into<T>) -> EVec<T> {
//!     EVec::<T>::of([value])
//! }
//! fn first<T: EgglogValue>(values: &EVec<T>) -> T {
//!     values.get(0_i64)
//! }
//!
//! let integer = I64::from(7_i64);
//! let values = EVec::<I64>::of([7_i64, 11_i64]);
//! let _: EVec<I64> = EVec::<I64>::of([&integer, &integer]);
//! let _: EVec<I64> = singleton::<I64>(&integer);
//! let _: I64 = first(&values);
//! let _: EVec<EVec<I64>> = singleton::<EVec<I64>>(&values);
//! let _: EVec<I64> = EVec::<I64>::empty();
//! let _: EVec<I64> = EVec::<I64>::of(std::iter::empty::<I64>());
//! let range: EVec<I64> = I64::from(5_i64).range();
//! let _: I64 = range.get(0_i64);
//! ```
//!
//! Pair components retain their independent types, including through tuples
//! and generic functions. `fields()` inspects direct children without evaluating
//! them; `first()` and `second()` author native projection calls.
//!
//! ```
//! use egglog_experimental::typed::{builtins::{F64, I64, Pair}, EgglogValue};
//! fn pair<L: EgglogValue, R: EgglogValue>(left: impl Into<L>, right: impl Into<R>) -> Pair<L, R> {
//!     (left, right).into()
//! }
//! let left = I64::from(7_i64);
//! let right = F64::from(1.5_f64);
//! let values = Pair::<I64, F64>::new(&left, &right);
//! let _: Pair<I64, F64> = pair(&left, &right);
//! let _: Pair<I64, F64> = (7_i64, 1.5_f64).into();
//! let _: Pair<I64, F64> = Pair::from(&values);
//! let _: I64 = values.first();
//! let _: F64 = values.second();
//! let _: (I64, F64) = values.fields()?;
//! let _: (I64, F64) = (&values).try_into()?;
//! let _: (I64, F64) = values.try_into()?;
//! # Ok::<(), egglog_experimental::typed::TypedError>(())
//! ```
//!
//! Sets use ordinary borrowed methods and typed iterator inputs. `contains`
//! and `not_contains` produce symbolic Unit predicates, and `length` produces
//! I64. Decoding an extracted Set returns typed children in the encoded order,
//! whose enumeration is unspecified; it does not implement native `get` order.
//! Decoding never evaluates an authored call. Structural Eq/Hash preserve the
//! supplied syntax and slots, including repeated inputs before native evaluation.
//! No host Ord bound or host set conversion is required.
//!
//! ```
//! use egglog_experimental::typed::{
//!     builtins::{I64, Set, Unit}, EgglogValue, TypedError,
//! };
//! fn singleton<T: EgglogValue>(x: impl Into<T>) -> Set<T> { Set::<T>::of([x]) }
//! fn first<T: EgglogValue>(s: &Set<T>) -> T { s.get(0_i64) }
//! fn inspect<T: EgglogValue>(s: &Set<T>) -> Result<Vec<T>, TypedError> {
//!     Vec::<T>::try_from(s)
//! }
//! let x = I64::from(7_i64);
//! let s: Set<I64> = Set::of([&x, &x]);
//! let _: Set<I64> = singleton::<I64>(&x);
//! let _: Set<I64> = Set::of([x.clone()].iter());
//! let _: Set<I64> = Set::of((0_i64..3).map(I64::from));
//! let _: Set<I64> = Set::empty();
//! let _: Set<I64> = Set::of(std::iter::empty::<I64>());
//! let _: Set<Set<I64>> = Set::of([&s]);
//! let _: I64 = first(&s);
//! let _: I64 = s.length();
//! let _: Unit = s.contains(&x);
//! let _: Unit = s.not_contains(&x);
//! let _: Set<I64> = s.union(&s).diff(&s).intersect(&s).insert(&x).remove(&x);
//! assert!(inspect(&s).is_err());
//! ```
//!
//! Set input, output and fixed arity errors are rejected by the Rust compiler:
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64, Set};
//! let _ = Set::<I64>::of([F64::from(1.5)]);
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64, Set};
//! let _ = Set::<I64>::empty().get(F64::from(0.0));
//! ```
//!
//! ```compile_fail,E0308
//! use egglog_experimental::typed::builtins::{F64, I64, Set};
//! let _: F64 = Set::<I64>::empty().get(0_i64);
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64, Set};
//! let _ = Set::<I64>::empty().contains(F64::from(1.5));
//! ```
//!
//! ```compile_fail,E0308
//! use egglog_experimental::typed::builtins::{Bool, I64, Set};
//! let _: Bool = Set::<I64>::empty().contains(1_i64);
//! ```
//!
//! ```compile_fail,E0308
//! use egglog_experimental::typed::builtins::{I64, Set, Unit};
//! let _: Unit = Set::<I64>::empty().length();
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64, Set};
//! let _ = Set::<I64>::empty().union(Set::<F64>::empty());
//! ```
//!
//! ```compile_fail,E0061
//! use egglog_experimental::typed::builtins::{I64, Set};
//! let _ = Set::<I64>::empty(1_i64);
//! ```
//!
//! ```compile_fail,E0061
//! use egglog_experimental::typed::builtins::{I64, Set};
//! let _ = Set::<I64>::of();
//! ```
//!
//! ```compile_fail,E0061
//! use egglog_experimental::typed::builtins::{I64, Set};
//! let _ = Set::<I64>::of([1_i64], [2_i64]);
//! ```
//!
//! ```compile_fail,E0061
//! use egglog_experimental::typed::builtins::{I64, Set};
//! let _ = Set::<I64>::empty().get();
//! ```
//!
//! ```compile_fail,E0061
//! use egglog_experimental::typed::builtins::{I64, Set};
//! let _ = Set::<I64>::empty().length(1_i64);
//! ```
//!
//! Map's `from_pairs` takes one symbolic `Vec<Pair<K, V>>`. `of` packs a host
//! tuple iterator, preserving order and duplicate keys until native evaluation.
//! `entries()` inspects direct construction or extracted data; it does not
//! evaluate computed vectors or insert chains. Empty inputs need a type context.
//!
//! ```
//! use egglog_experimental::typed::{builtins::{F64, I64, Map, Pair, Vec as EVec}, EgglogValue};
//! fn map<K: EgglogValue, V: EgglogValue>(pairs: impl Into<EVec<Pair<K, V>>>) -> Map<K, V> {
//!     Map::from_pairs(pairs)
//! }
//! let pairs = EVec::<Pair<I64, F64>>::of([Pair::new(7_i64, 1.5_f64)]);
//! let values: Map<I64, F64> = map(&pairs);
//! let _: Map<I64, F64> = Map::from_pairs(pairs);
//! let _: Map<I64, F64> = Map::of(std::iter::empty::<(I64, F64)>());
//! let _: Map<I64, F64> = Map::from_pairs(EVec::<Pair<I64, F64>>::empty());
//! let _: Map<I64, F64> = vec![(7_i64, 1.5_f64)].into();
//! let _: F64 = values.get(&I64::from(7));
//! let _: Map<I64, F64> = values.insert(7_i64, &F64::from(2.5));
//! let _: Vec<(I64, F64)> = values.entries()?;
//! let _: Vec<(I64, F64)> = (&values).try_into()?;
//! let _: Vec<(I64, F64)> = values.try_into()?;
//! # Ok::<(), egglog_experimental::typed::TypedError>(())
//! ```
//!
//! Map rejects wrong key/value sorts, nested input sorts, tuple widths, arity,
//! and lookup result types during compilation:
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64, Map};
//! let _ = Map::<I64, F64>::empty().get(F64::from(1.0));
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64, Map};
//! let _ = Map::<I64, F64>::empty().insert(1_i64, I64::from(2));
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64, Map};
//! let _ = Map::<I64, F64>::of([(1.0_f64, 2.0_f64)]);
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64, Map};
//! let _: Map<I64, F64> = vec![(1_i64, "not a float")].into();
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64, Map, Pair, Vec as EVec};
//! let _ = Map::<I64, F64>::from_pairs(EVec::<Pair<F64, I64>>::empty());
//! ```
//!
//! ```compile_fail,E0271
//! use egglog_experimental::typed::builtins::{F64, I64, Map};
//! let _ = Map::<I64, F64>::of([(1_i64,)]);
//! ```
//!
//! ```compile_fail,E0271
//! use egglog_experimental::typed::builtins::{F64, I64, Map};
//! let _ = Map::<I64, F64>::of([(1_i64, 2.0_f64, 3_i64)]);
//! ```
//!
//! ```compile_fail,E0061
//! use egglog_experimental::typed::builtins::{F64, I64, Map};
//! let _ = Map::<I64, F64>::from_pairs();
//! ```
//!
//! ```compile_fail,E0061
//! use egglog_experimental::typed::builtins::{F64, I64, Map, Pair, Vec as EVec};
//! let pairs = EVec::<Pair<I64, F64>>::empty();
//! let _ = Map::<I64, F64>::from_pairs(&pairs, &pairs);
//! ```
//!
//! ```compile_fail,E0308
//! use egglog_experimental::typed::builtins::{F64, I64, Map};
//! let _: I64 = Map::<I64, F64>::empty().get(1_i64);
//! ```
//!
//! Wrong component sorts or unsupported host conversions fail during compilation:
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64, Pair};
//! let _ = Pair::<I64, F64>::new(F64::from(1.0_f64), 2.0_f64);
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64, Pair};
//! let _ = Pair::<I64, F64>::new(1_i64, I64::from(2_i64));
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64, Pair};
//! let _: Pair<I64, F64> = (1_i64, "not a float").into();
//! ```
//!
//! Construction requires two arguments, and tuple conversion requires a pair:
//!
//! ```compile_fail,E0061
//! use egglog_experimental::typed::builtins::{F64, I64, Pair};
//! let _ = Pair::<I64, F64>::new(1_i64);
//! ```
//!
//! ```compile_fail,E0061
//! use egglog_experimental::typed::builtins::{F64, I64, Pair};
//! let _ = Pair::<I64, F64>::new(1_i64, 2.0_f64, 3_i64);
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64, Pair};
//! let _: Pair<I64, F64> = (1_i64,).into();
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64, Pair};
//! let _: Pair<I64, F64> = (1_i64, 2.0_f64, 3_i64).into();
//! ```
//!
//! Projection results retain the corresponding component sort:
//!
//! ```compile_fail,E0308
//! use egglog_experimental::typed::builtins::{F64, I64, Pair};
//! let _: F64 = Pair::<I64, F64>::new(1_i64, 2.0_f64).first();
//! ```
//!
//! Integer and floating-point sorts cannot be mixed in arithmetic:
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64};
//! let _ = I64::from(1_i64) + F64::from(2.0_f64);
//! ```
//!
//! Literal conversion does not implicitly cast between host numeric types:
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::I64;
//! let _ = I64::from(1.5_f64);
//! ```
//!
//! Closed scalar methods retain their input sorts, result sorts and arities:
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64};
//! let _ = I64::from(1).bool_lt(F64::from(2.0));
//! ```
//!
//! ```compile_fail,E0308
//! use egglog_experimental::typed::builtins::{I64, Unit};
//! let _: Unit = I64::from(1).bool_lt(2);
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::F64;
//! let _ = F64::from_i64(1.0_f64);
//! ```
//!
//! ```compile_fail,E0061
//! use egglog_experimental::typed::builtins::F64;
//! let _ = F64::from_i64();
//! ```
//!
//! ```compile_fail,E0061
//! use egglog_experimental::typed::builtins::Rational;
//! let _ = Rational::new(1, 2).numer(1);
//! ```
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::count_matches;
//! let _ = count_matches("aba", 1_i64);
//! ```
//!
//! A vector's element sort constrains every iterator item:
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64, Vec as EVec};
//! let _ = EVec::<I64>::of([F64::from(1.5_f64)]);
//! ```
//!
//! Lookup requires an integer index and returns the vector's element type:
//!
//! ```compile_fail,E0277
//! use egglog_experimental::typed::builtins::{F64, I64, Vec as EVec};
//! let _ = EVec::<I64>::empty().get(F64::from(0.0_f64));
//! ```
//!
//! ```compile_fail,E0308
//! use egglog_experimental::typed::builtins::{F64, I64, Vec as EVec};
//! let _: F64 = EVec::<I64>::empty().get(0_i64);
//! ```
//!
//! `of` takes one iterable, rather than a Rust variadic argument list:
//!
//! ```compile_fail,E0061
//! use egglog_experimental::typed::builtins::{I64, Vec as EVec};
//! let _ = EVec::<I64>::of([1_i64], [2_i64]);
//! ```
//!
//! ```compile_fail,E0308
//! use egglog_experimental::typed::builtins::{F64, I64, Vec as EVec};
//! let _: EVec<F64> = I64::from(5_i64).range();
//! ```
//!
//! ```compile_fail,E0061
//! use egglog_experimental::typed::builtins::I64;
//! let _ = I64::from(5_i64).range(1_i64);
//! ```
//!
//! ```compile_fail,E0599
//! use egglog_experimental::typed::builtins::F64;
//! let _ = F64::from(5.0_f64).range();
//! ```
//!
//! The declared `Num(I64)` constructor also enforces its input sort and arity:
//!
//! ```compile_fail,E0277
//! # use egglog_experimental::typed::{builtins::{F64, I64}, prelude::*};
//! # #[sort]
//! # pub struct Term;
//! # #[declarations]
//! # impl Term { pub fn Num(value: I64) -> Self; }
//! let _ = Term::Num(F64::from(1.5_f64));
//! ```
//!
//! ```compile_fail,E0061
//! # use egglog_experimental::typed::{builtins::I64, prelude::*};
//! # #[sort]
//! # pub struct Term;
//! # #[declarations]
//! # impl Term { pub fn Num(value: I64) -> Self; }
//! let _ = Term::Num();
//! ```
//!
//! Callable declarations have no argument-count cap. Selectors and generated
//! named argument records support up to 64 inputs, with every position retaining
//! its declared sort. For example, the fifth input of a loop constructor cannot
//! be replaced with its dimension input:
//!
//! ```compile_fail,E0277
//! # use egglog_experimental::typed::{builtins::I64, prelude::*};
//! # #[sort] pub struct Ir;
//! # #[sort] pub struct DimExpr;
//! # #[sort] pub struct DType;
//! # #[declarations]
//! # impl Ir {
//! #     pub fn LoopStart(inp: Ir, loop_id: I64, slot_idx: I64, iters: DimExpr, dtype: DType) -> Self;
//! # }
//! let inp = var::<Ir>("input");
//! let iters = var::<DimExpr>("iters");
//! let _ = Ir::LoopStart(inp, 17, 23, &iters, &iters);
//! ```
//!
//! ```compile_fail,E0061
//! # use egglog_experimental::typed::{builtins::I64, prelude::*};
//! # #[sort] pub struct Ir;
//! # #[sort] pub struct DimExpr;
//! # #[sort] pub struct DType;
//! # #[declarations]
//! # impl Ir {
//! #     pub fn LoopStart(inp: Ir, loop_id: I64, slot_idx: I64, iters: DimExpr, dtype: DType) -> Self;
//! # }
//! let _ = Ir::LoopStart(var::<Ir>("input"), 17, 23, var::<DimExpr>("iters"));
//! ```
//!
//! ```compile_fail,E0061
//! # use egglog_experimental::typed::{builtins::I64, prelude::*};
//! # #[sort] pub struct Ir;
//! # #[sort] pub struct DimExpr;
//! # #[sort] pub struct DType;
//! # #[declarations]
//! # impl Ir {
//! #     pub fn LoopStart(inp: Ir, loop_id: I64, slot_idx: I64, iters: DimExpr, dtype: DType) -> Self;
//! # }
//! let _ = Ir::LoopStart(
//!     var::<Ir>("input"), 17, 23, var::<DimExpr>("iters"), var::<DType>("dtype"), 31,
//! );
//! ```
use crate::proto as pb;
pub mod builtins;
mod close;
mod decl;
mod expr;
mod rule;
mod schedule;
mod selector;
mod session;
mod snapshot;
mod storage;

/// Small execution results and opaque backend-specific diagnostic documents.
pub use crate::proto::{Diagnostic, RunResult};
pub use builtins::ne;
pub use decl::SortRef;
pub use egglog_experimental_typed_macros::{
    constructor, declarations, function, relation, ruleset, sort,
};
pub use expr::{EgglogValue, EqualitySort, let_, var};
pub use rule::{
    Action, Fact, Rule, Ruleset, delete, eq, rewrite, rule, ruleset, set, subsume, union,
};
pub use schedule::{Schedule, sequence};
pub use selector::get_args;
pub use session::EGraph;
pub use snapshot::{ClassRef, ProducerRef, Snapshot, TableRowRef, ValueRef};

/// Authoring, decoding or structured engine failure.
#[derive(Debug)]
pub enum TypedError {
    /// Invalid or currently unsupported authored program.
    Invalid(String),
    /// A result does not have the requested concrete representation.
    Decode(String),
    /// The byte engine returned its structured failure unchanged.
    Engine(Box<pb::Error>),
    /// An ordered retained root could not be observed or reconstructed.
    UnresolvedRoot {
        /// Position in the caller's ordered root list, when known.
        index: Option<usize>,
        /// The failed observation or reconstruction requirement.
        reason: String,
    },
}
impl std::fmt::Display for TypedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Invalid(s) | Self::Decode(s) => f.write_str(s),
            Self::Engine(e) => write!(f, "engine error {}: {}", e.code, e.message),
            Self::UnresolvedRoot { index, reason } => {
                write!(f, "unresolved root {index:?}: {reason}")
            }
        }
    }
}
impl std::error::Error for TypedError {}

/// Common authoring types, declaration macros and operations.
pub mod prelude {
    pub use super::{
        Action, Diagnostic, EGraph, EgglogValue, EqualitySort, Fact, Rule, Ruleset, RunResult,
        Schedule, Snapshot, TypedError, constructor, declarations, delete, eq, function, get_args,
        let_, ne, relation, rewrite, rule, ruleset, sequence, set, sort, subsume, union, var,
    };
}

#[doc(hidden)]
pub mod __private {
    pub use super::{
        decl::Callable,
        expr::{Expr, ValueInput, fresh_scope, variable},
        rule::named_ruleset,
    };
}

#[cfg(test)]
mod tests;
