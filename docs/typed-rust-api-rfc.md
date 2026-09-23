# RFC: Direct typed Rust values for Egglog

Status: implemented; under review

Updated: 2026-09-23

Home: `egglog-experimental`; first consumer: Luminal's CPU ReferenceRuntime path

This is the maintained design for the implementation in this repository.
The [runnable examples](typed-example-coverage.md) and source-included Rust tutorial
teach the API. This document owns the architecture and design rationale.

The callable catalog is consolidated below rather than maintained as a second
API specification.

## Direction

Build typed Rust authoring values in `egglog_experimental::typed`. Lower them
to existing `egglog::ast::Command` values in the shared, versioned
`egglog::program::Program` representation. `EGraph::run_shared_program` validates
that structure and uses core's existing macro expansion, desugaring,
typechecking, global lowering, rule compiler, and executor. Execution does not
parse generated Egglog source. This is a serializable command-tree boundary;
a resolved typed IR and direct linker remain future work.

The public design keeps named sorts, ordinary functions/methods/operators,
reusable query variables, immutable rulesets/schedules, typed inspection, and
execution methods with exact results. Ordinary calls need no callable descriptors;
`Definition::callable` selects a declaration only for explicit installation.
Explicitly named argument records are opt-in for high-arity calls. Ordinary Rust
constructs and combines these values at runtime; declaration macros produce
ordinary Rust functions.
A shared `Arc` expression graph already is a DAG.
Private flattening makes it easier to traverse and lower, without imposing
structural interning or an exactly-once evaluation model.

Compiler-generated bindings are permitted and often necessary: query
variables on the LHS, local lets in a rule head, and persistent globals for
eligible top-level construction. They are private lowering machinery.
Explicit `let_(name, initializer) -> S` remains the public capture operation.
Reusing any other symbolic expression evaluates it again when the enclosing
operation requires it.

The first acceptance result is a working Luminal PR migrating
`Graph::build_search_space::<ReferenceRuntime>` through search, shared LLIR
reconstruction, and execution. It must handle the complete core catalog
installed by that path, runtime-generated rules, and every output. Shared program
serialization now provides a common core boundary for language frontends; it
does not reconstruct Rust wrappers or their declaration-source identities.
Complete GPU authoring migration and joint DAG-cost optimization remain separate
work. Observation uses one rootless `freeze()` snapshot
with exact scalar/container values and cyclic e-class traversal. Typed and native
producers use the same native snapshot builder, not a serialization bridge.

## Public example

This example compiles and executes against the verified conversion implementation.
Fixed theories are module-level Rust values; runtime-dependent generators use
the same builders.

```rust,ignore
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Math;

#[declarations]
impl Math {
    #[constructor(from(i32, i64))]
    pub fn num(value: egg::I64) -> Math;

    #[constructor(from(&str, std::string::String))]
    pub fn var(name: egg::String) -> Math;

    #[function(no_merge)]
    pub fn weight(&self, axis: egg::I64) -> egg::I64;

    pub fn interesting(&self);
}

#[declarations]
impl std::ops::Add<&Math> for &Math {
    type Output = Math;
    fn add(self, rhs: &Math) -> Math;
}

#[declarations]
impl std::ops::Mul<&Math> for &Math {
    type Output = Math;
    fn mul(self, rhs: &Math) -> Math;
}

#[ruleset]
pub fn rewrites(a: &Math, b: &Math, x: &egg::I64, y: &egg::I64) -> Vec<Rule> {
    vec![
        rewrite(a + b, b + a),
        rewrite(Math::num(x) + Math::num(y), Math::num(x + y)),
    ]
}

fn example() -> Result<(), Box<dyn std::error::Error>> {
    let shared = Math::num(2) * "x";
    let output0 = let_("output/0", &shared + 6);
    let output1 = let_("output/1", Math::num(6) + &shared);
    let outputs = [&output0, &output1];

    let mut egraph = EGraph::default();
    egraph.register((
        outputs.as_slice(),
        output0.interesting(),
        set(output0.weight(2), 7),
    ))?;
    let report: RunReport = egraph.run(rewrites.saturate())?;
    assert!(egraph.check(eq(&output0, &output1))?);

    // A query variable is symbolic, not a captured destination value.
    assert!(egraph.check(var::<Math>("term").interesting())?);

    let best: Math = egraph.extract(&output0)?;
    let forest: Vec<Math> = egraph.extract_many(&outputs)?;

    // Inspection returns an ordinary typed tuple, without a companion record.
    let _operands = get_args(&best, |a: &Math, b: &Math| a + b)?;

    let frozen = egraph.freeze()?;
    let root: Math = frozen.lookup(&output0)?;
    for node in frozen.nodes(&root)? {
        if !frozen.is_subsumed(&node)? {
            // Choose a node before inspecting an e-class's alternatives.
            let _children = get_args(&node, |a: &Math, b: &Math| a + b)?;
        }
    }

    for row in frozen.table(|value: &Math, axis: &egg::I64| value.weight(axis))? {
        let (_value, _axis): (Math, egg::I64) = row.args;
        let weight: i64 = (&row.output).try_into()?;
        assert_eq!(weight, 7);
    }
    let _ = (report, forest, root);
    Ok(())
}
```

`shared` preserves authoring topology. The lowerer may introduce private
bindings at valid evaluation positions; it does not remember its evaluated
result across method calls. The two explicit captures do remember results.
`register` returns `()`, and callers retain their ordered outputs.

## Callable roles at a glance

| Role | Selected surface | Important boundary |
| --- | --- | --- |
| Declare a free constructor, function, or relation | `#[constructor] fn make(x: Num) -> Num;` and corresponding function/relation attributes | Same spelling across kinds; options reflect semantic differences. |
| Declare associated functions or receiver methods | Bodyless methods in `#[declarations] impl Num { ... }` | Equality-sort output means constructor; no output means relation. Table policies remain explicit. |
| Declare a standard operator | Bodyless operator method in `#[declarations] impl Trait ...` | One authoritative declaration generates owned/borrowed forms. |
| Build symbolic calls | `make(&x)`, `Num::constant(2)`, `x.weight(1)`, `&x + &y` | Free/inherent inputs accept exact owned, borrowed, or convertible literal values. |
| Lift a value into a domain expression | `&x + 1`, `&x + "y"`, or `Num::from(2)` | `#[constructor(from(...))]` generates concrete `From` implementations; substantive conversions remain ordinary Rust. |
| Write a function row | `set(x.weight(1), 10)` | Output sort statically checked; target kind checked at submission. Its outer call is not read. |
| Delete/subsume a row | `delete(x.weight(1))`, `subsume(interesting(&x))` | Infallible construction; submission validates supported table kinds. |
| Inspect call arguments | `get_args(&expr, \|a: &Num, b: &Num\| a + b)?` | Fallible optional tuple of exact symbolic sorts; no companion record. |
| Inspect a frozen table | `frozen.table(\|x: &Num, axis: &egg::I64\| x.weight(axis))?` | Typed rows and metadata; no linking, evaluation, or string lookup. |
| Look up a captured root | `let observed: Num = frozen.lookup(&capture)?;` | Capture identity checked; same sort, snapshot-owned reference, no producer selection. |
| Inspect a frozen class | `for node in frozen.nodes(&observed)? { ... }` | Each same-sort node selects a constructor; inspect with the same callback API. |
| Decode a scalar | `let value: i64 = (&observed_i64).try_into()?;` | Explicit host conversion, not silent detachment. |
| Reuse construction in a generator | Ordinary functions or closures producing expressions/rules | Keep callbacks for parameterized generation, not wrappers around values. |
| Inspect heterogeneous graph data | Explicit low-level frozen views with diagnostic names and `SortRef` metadata | Native/Luminal integration outside the normal typed prelude. |

Live table lookup/size/CSV methods are separate follow-ups. Listing a Python
operation does not introduce an unimplemented Rust method.

## Authoring contract

### Named sorts and symmetric declarations

Every Egglog sort has a named wrapper, including scalars and containers:
`Unit`, `String`, `Bool`, `I64`, `F64`, `BigInt`, `BigRat`, `Rational`,
`Vec<T>`, `Set<T>`, `Map<K, V>`, `MultiSet<T>`, and `Pair<L, R>`.
These are catalog names; implementation of every primitive over them is not a
prerequisite for the first Luminal PR. Implement the operations that the
selected catalog uses, and report unsupported operations explicitly.

A `builtins` module analogous to Python's `builtins.py` owns their named
families, applied type arguments, primitive declarations, and conversions.
There is no anonymous builtin-sort escape hatch. Standard `From` supplies
unambiguous host-to-symbolic conversions; `TryFrom` decodes supported portable
literals/containers or exact stored frozen payloads and otherwise returns
`DecodeError`. Preserve authored literal bits; runtime normalization remains
core's behavior.

A sort such as `Ir` is also its expression type. Literals, calls, query
variables, captures, extracted terms, and frozen observations all have that same
type. Frozen observations retain private snapshot identity rather than becoming
portable syntax; live submission rejects them recursively.
Construction accepts owned values or borrows of them, using `From<&S> for S`
to retain the existing Arc node. The resulting expression is always owned:
borrowing an input does not introduce a lifetime on `Ir` or a second expression
family. Use `&expr` when an ordinary owned Rust binding will be reused; no
explicit `.clone()` or `.into()` is needed in ordinary calls.

```rust,ignore
#[sort]
pub struct Ir;

#[constructor]
pub fn chain(current: Ir, source: Ir) -> Ir;

#[relation]
pub fn path(current: Ir, source: Ir);

#[relation]
pub fn edge(current: Ir, next: Ir);

#[declarations]
impl Ir {
    #[function(no_merge)]
    pub fn dtype(&self) -> egg::String;
}

let next = chain(&current, &source);
let dtype = next.dtype();
let fields = get_args(&next, |a: &Ir, b: &Ir| chain(a, b))?;
```

All three callable kinds use bodyless function declarations. A free declaration
generates a free function, including when its result sort belongs to another
crate. `#[declarations]` on a concrete inherent or trait implementation treats a
bodyless method with an equality-sort output as a constructor and one without
a return annotation as a relation. Attributes are needed only for meaningful
options or explicit kinds, such as a table's `#[function(no_merge)]` policy.
Methods with bodies remain ordinary Rust, not symbolic definitions.
`self` or `&self` makes an instance method; a declaration without a receiver
makes an associated function. Names retain their authored spelling. No
capitalization convention chooses between callable and metadata roles.

Free/inherent non-receiver parameters accept `impl Into<DeclaredSort>` inputs,
converted left-to-right. Authored trait signatures are checked against their
required parameter and return types; recognized binary operators additionally
accept convertible RHS inputs as described below. Constructors require an owned
equality-sort result; functions require their exact symbolic result. Trait
relations must actually return
`Relation`; the no-return stub generates that return type for Rust to check. Generic
impls/methods, mutable or typed receivers, and incompatible host signatures are
diagnosed rather than translated into another calling convention. Existing
generic builtin implementations remain ordinary Rust.

Generated declaration tokens, resolvers, and metadata stay private.
`Definition::callable(selector)` is an optional installation description; normal
calls have no `.call` or `.project` indirection. `get_args`
supports tuple inspection, and `args = Name` opts into a named record derived
from the same declaration. A match-like macro remains deferred. Rust parameter
names serve IDE hints, documentation and opted-in record fields;
resolved calls store arguments in declaration order, not a named-argument map.
Two definitions sharing a nominal name may use different argument labels, but
must agree on kind, ordered input/output sorts, merge behavior, cost, and
extraction options. Explicit `#[function(no_merge)]` remains unchanged.
Simple merge policies use inline typed closures, for example
`merge = |old: egg::I64, new: egg::I64| old.max(new)`. An existing callable can
be passed directly as the merge builder; neither form needs a forwarding helper.
Repeated declaration options are compile errors at the duplicate occurrence,
uniformly for sorts and callable declarations; names and costs do not
silently take the last supplied value. Merge-policy exclusivity is unchanged.
Scalar and container symbolic methods borrow their receiver. `eq`, `ne`,
`union`, and rewrites use the first symbolic operand's exact
sort to constrain the second; accepting borrows must not require extra sort
annotations or permit cross-sort operations.

### Standard conversions, not another authoring language

An opt-in `From<Source> for Sort` selects an existing constructor or a meaningful
context-independent embedding. `Math::var("x") + 1` and `x + "y"` need no explicit
conversion at the call site when the corresponding integer/name conversions
exist. The same conversions apply to ordinary function/method arguments and the
already-typed RHS of `rewrite`, `eq`, `ne`, `union`, and `set`.

For unary free or associated constructors, `#[constructor(from)]` generates
`From<Input>` and `From<&Input>` for the result sort. A list such as
`#[constructor(from(i32, i64))]` adds exactly those concrete sources. Each
implementation invokes that constructor once using its existing input conversion.
The annotation changes neither callable identity nor evaluation semantics.
It is explicit opt-in: two string constructors such as `var` and `constant`
cannot both own the same conversion. Rust coherence rejects overlapping routes;
receiver, multiargument and self-conversions are not inferred. Keep meaningful
adaptations, such as Unicode list construction or host-enum matching, in Rust.

Use concrete source implementations, including supported host values and owned
or borrowed symbolic values. Integer wrappers accept i32/i64/I64; float wrappers
accept f64/F64 without implicit lossy integer conversion. Rational lifting uses
exact integer-to-BigInt and integer/BigInt-to-BigRat construction with denominator
one. Name conversions accept host strings or symbolic String values where one
application-name constructor is intentionally selected. Rust does not search
conversion chains: composed routes are explicit implementations, not a runtime
registry or a blanket `From<T: Into<_>>` scalar family.

Conversions construct syntax, not values read from an EGraph. They retain
observed children and query identities, never decode frozen fields or select
nullary alternatives from symbolic booleans. Strings construct application
names, never Egglog query variables. Ambiguous constructors, parsing, narrowing,
and context-dependent transformations stay explicit.

The reverse boundary uses concrete `TryFrom` implementations, not a parallel
`.value()` or `.eval()` conversion spelling. A unary constructor can opt into
both directions with `#[constructor(from(i64), try_from(i64))]`. Bare
`try_from` unwraps the declared input sort from an owned or borrowed result;
listed targets additionally use their existing `TryFrom<Input>` implementations.
It requires the exact annotated call. A different constructor, query variable,
capture or unselected frozen class fails without evaluation. A symbolic field
can be unwrapped without being a native literal. Targets must be owned; errors
from their conversion are formatted into `TypedError::Decode`, while exact
declaration errors retain their existing category. Each annotation claims its
input sort and listed targets; Rust coherence rejects overlapping conversions.
Container routes retain immediate symbolic children, not recursive native
materialization. Meaningful domain conversions remain ordinary Rust trait impls.

Bodies inside `#[declarations]` already execute as Rust; no
Python-style `preserve=True` annotation is necessary. Pure inspection reads a
concrete literal or selected constructor and may return a native value. It
neither runs rules nor chooses an e-class alternative. Domain evaluation is a
different operation: explicitly run the appropriate schedule, extract, and then
convert. Python's builtin `.value` and array API `.eval()` demonstrate these two
roles; the latter performs domain evaluation, not merely conversion.

Luminal uses `From<HostDType>` to author dtype constructors and `TryFrom` to read
concrete authored or explicitly selected frozen dtype constructors. Its native
`Expression` remains meaningful execution/code-generation data: decoding
dimensions requires finite-producer selection and context, while evaluating a
dimension requires runtime variable assignments. A shared name or an `eval`
method must not hide those distinct policies. Frozen equality classes require
selection; stored primitive payloads can be read directly. Neither conversion
imports observed expressions into a live EGraph.

Keep a symbolic anchor in constant-only arithmetic: `Math::num(1) + 2` authors
an addition, while `1 + 2` performs Rust arithmetic. Field-binding patterns and
callable selectors retain explicit constructors. Do not reorder operands or
change grouping for convenience. Reverse operators are deferred, so the public
example intentionally keeps `Math::num(6)` on the left of its second output.

### Operators and declared display syntax

An annotated standard operator implementation declares one Egglog operation.
Binary declarations generate two Rust
implementations, for owned and borrowed LHS, accepting `Rhs: Into<DeclaredRhs>`.
They cover the existing four owned/borrowed combinations and opted-in conversions
without changing the fixed Egglog signature. Unary declarations retain both
receiver forms. Recognize fully qualified `std::ops`/`core::ops` `Add`, `Sub`, `Mul`,
`Div`, `Rem`, `BitAnd`, `BitOr`, `BitXor`, `Shl`, `Shr`, `Neg`, and `Not`.
Normalize shared references around concrete operand sorts; preserve the owned
symbolic `Output`. Do not infer this behavior from a user trait merely named
`Add`. Other compatible trait methods generate exactly their declared impl.
The RHS conversion runs once before constructing the call. All forms share one
declaration token and metadata/merge initializer. Private generated signature
checking preserves rejection of malformed authored operator impls. Rust's
coherence rules reject overlapping additional implementations; a convertible-RHS
family reserves that operator's RHS implementation space. No reverse-operator
adapters or inferred converter registry are generated.

Use only traits whose result contracts fit: [`Index`][rust-index] returns a
reference, not a newly constructed expression; Rust comparison operators return
host Boolean values, not Egglog facts. Keep `.select(...)` and `eq(...)` for
those operations. Passing an owned expression moves its shared handle; borrowing
allows reuse without making the expression `Copy` or introducing an arena.

Printing retains the declared free/static/method/operator form: `chain(a, b)`,
`Math::var("x")`, `x.weight(2)`, or `a + b`, with correct parentheses. This is
canonical declaration syntax, not preservation of whether a caller wrote UFCS
instead of a method call. Presentation metadata and source spans do not change
semantic declaration identity. Native-only declarations retain nominal-call
formatting. Frozen references print as references without choosing a producer
or expanding cycles. Diagnostic formatting is not executable serialization.

### Callable kinds and mutation targets

| Kind | Call result | Distinct policy/capability |
| --- | --- | --- |
| Constructor | Its equality sort | Cost, extractability, constructor observation |
| Relation | A proposition/row occurrence | Querying, insertion, deletion, subsumption |
| Table function | Its result sort | Explicit `no_merge` or `merge = builder`, lookup and setting |
| Catalog primitive | Its catalog result | Audited expression or action operation; not a table |

A relation becomes a fact in a query and an insertion in action position; it
does not become a public `Unit` expression. `set`, `union`, deletion,
subsumption, `panic(message)`, and admitted stateful primitives produce `Action`.
`panic` constructs the native failure action; it neither panics during Rust
authoring nor means that another command is expected to fail. There is no `fail`
synonym.
An action cannot become a child of an expression. Pure catalog calls produce
expressions; table lookups also produce symbolic expressions but retain their
state-dependent behavior. Host callbacks and arbitrary native primitive
registration are outside the initial catalog.

Mutation takes an ordinary call expression: `set(x.weight(2), 7)`,
`delete(x.weight(2))`, or `subsume(interesting(&x))`. Construction remains
infallible. Submission checks that the target is a direct supported table call;
`set` requires a function and preserves compile-time output-sort checking.
Lower the target's arguments without evaluating its outer call as a read.
An absent row must not cause a set operation to fail merely while identifying
its key. Deletion/subsumption keep the supported native row kinds and semantics.

`#[sort]` plus ordinary impl declarations is the only application-sort frontend;
there is no enum schema or implicit sibling-constructor catalog. Definitions link
when reached, in first-use order. Declaring a sort does not install all methods
on it. A frozen snapshot includes installed empty tables, not every unused Rust
declaration. As in native extraction, equal-cost representative choices can depend
on declaration order; no enum-order tie guarantee is retained.
Consumer-specific preferences belong at the consumer boundary. Luminal preserves
its pre-migration expression cost and first-minimum/first-producer algorithms,
not the incidental ordering of tied producers. Different snapshots and selected
representatives are acceptable when both are valid under the same assumptions.
This does not authorize new heuristics or treating non-equivalent alternatives
as interchangeable; correctness-sensitive choices require a separate report.
This transition does not introduce integer-before-float preferences.
Heterogeneous consumers inspect diagnostic names and `SortRef` metadata, without
public callable-identity objects or backend table/value IDs. Exact callable
identity remains internal to declaration linking and typed selector validation.
`EgglogValue::call_name()` returns an authored root call's name, or `None` for
variables, literals, captures and frozen observations. `Relation::call_name()`
returns its authored relation name. Use `get_args` for exact typed inspection;
names alone do not establish declaration compatibility.
`SortRef::container_shape()` projects the existing applied sort into an optional
canonical family and ordered argument sorts. A native alias named `MyMap` can
therefore expose `("Map", [key_sort, value_sort])` without interpreting its name
or exposing mutable identity fields.

Names default to the declaration's qualified Rust item path; reexports do not
rename it. Free declarations use their module and function name; inherent methods
include their owner, and trait methods include their trait.
An explicit name is used verbatim, including its UTF-8 spelling, in the native
sort or callable declaration. Omitted names use the existing qualified Rust
default verbatim too. Only internal temporaries, capture anchors and rule/group
occurrence names are generated. Public names may resemble those internal names;
the generator reserves occupied names rather than restricting a public prefix.
Sorts, callables and installed rule/group names share the native declaration
namespace. Incompatible names and callable names reserved for native primitives
or the `unstable-fresh!` macro are rejected before execution; compatible typed
aliases retain one declaration.
Use these defaults in examples rather than preserving old descriptor names or
capitalization. An explicit name allows intentional nominal identity across
producers, such as Luminal's existing native/GPU declarations. It is not required
for ordinary Rust authoring. Declarations with the same nominal name must have
compatible definitions, including ordered exact sorts and merge policy, but not
Rust field labels. Declaration source locations and private resolver identities
are not semantic names.

### Call inspection and opt-in named arguments

Local converters match selected expressions directly, without storing declaration
identities or building a decoder registry.

`get_args(&node, selector) -> Result<Option<ArgsTuple>, TypedError>`
returns owned, exact-sort expression fields. A selector such as
`|a: &Ir, b: &Ir| chain(a, b)` is called once with distinct fresh symbolic inputs.
Its result must be one direct call over every input exactly once, in order.
Constants, omitted/repeated/reordered inputs, captures, and nested argument
computations are invalid selectors, not partial query patterns. The callback
runs ordinary Rust authoring code; no selected operation is evaluated in Egglog.

Validate the selector first, including exact signature and semantic definition
compatibility. A malformed selector is an error. A valid selector whose head
does not match the inspected root returns `None`; literals, variables, captures,
and unselected frozen classes have no matching call root. A selected frozen
constructor node exposes its exact row arguments. Function outputs do not
acquire producer identity merely because they were read from a table.

Sealed, documentation-hidden adapters support borrowed callbacks with 0–32
parameters and typed tuple decoding. This is not a new limit on ordinary
function declarations. Direct concrete function references work when their
Rust signatures satisfy the same adapter. Generic `impl Into<S>` method
references can fail higher-ranked lifetime inference; typed closures are the
documented baseline, without function-address identity or a second overload API.

Ordinary named or callback variables remain the default in queries. For occasional
large patterns, a named argument record can supply fresh variables for the fields
the rule does not constrain. Cloning preserves variable identity; creating fresh
fields again does not.

For high-arity declarations, opt into one explicitly named argument record:

```rust,ignore
#[constructor(args = MatmulArgs)]
pub fn matmul(left: Ir, right: Ir, transpose_left: egg::Bool) -> Ir;

// Ordinary calls remain unchanged; no record is required at a call site.
let product = matmul(&left, &right, false);
if let Some(args) = MatmulArgs::get_args(&product)? {
    use_operand(&args.left);
}

// Named construction is available when field names clarify the call.
let product: Ir = MatmulArgs {
    left,
    right,
    transpose_left: false.into(),
}.into();

// Partial patterns need no callback parameter for each unconstrained field.
let args = MatmulArgs {
    transpose_left: false.into(),
    ..MatmulArgs::fresh()
};
let pattern = Ir::from(args.clone());
// The fields are ordinary variables: bind the pattern before using them on a RHS.
let demand = rule(pattern, needed(&args.left));
```

The declaration is the single source of field names and exact owned symbolic
types. `args = Name` works on constructors, functions and relations; generated
records are sibling Rust items, not automatically capitalized callable names.
Free/inherent records inherit the declaration's visibility; trait-impl records
are private to the enclosing module. Receiver methods include a `receiver`
field. `Record::get_args` performs the same
exact checks as tuple inspection and returns `Result<Option<Record>, TypedError>`:
a different call is `None`, incompatible same-name declarations are errors.
Selected frozen children retain provenance. Relation records inspect authored
relation calls, not value expressions or runtime table rows. `From<Record>`
reconstructs the same callable; it does not evaluate or decode host values.
`Record::fresh()` returns one independent fresh variable per field using the
same private identity mechanism as callback variables. Separate invocations are
independent; cloning the record or its expression preserves those identities.
Ordinary struct update, such as `MatmulArgs { transpose_left: true.into(), ..args }`,
preserves the other fields. On a rule RHS, those variables must already be bound
by its query. A second `fresh()` call is not a copy of a matched record. Exact
evaluation still rejects variables. Concrete record fields require `.into()` for
host literals and borrowed symbolic inputs, unlike convertible call parameters.
Struct update only works within the same record type.
The opt-in record uses the existing 32-argument selector limit; declarations
without records retain their ordinary arity support. There is no `Default`,
placeholder syntax, named-argument runtime map or second expression representation.

### Reusable variables and native rule behavior

`Fact`, `Action`, `Rule`, `Ruleset`, and `Schedule` remain separate:
they represent queries, mutations, stored behavior, collections, and execution
control. `rule(lhs, rhs) -> Rule`, `rewrite(lhs, rhs) -> Rule`, and
`ruleset(input) -> Ruleset` construct ordinary values without validating or
executing an Egglog program. Invalid programs fail when submitted. Native
typechecking still runs; the wrapper does not duplicate it during authoring.

`var::<S>(name) -> S` creates a reusable typed query variable. Exact UTF-8 names
are identities, without normalization. Repeated names denote one binder within
each query; conflicting exact sorts in that query, including its rule RHS, fail
during lowering. Each rule, `check`, or schedule `until` independently binds its
variables. Reusing a name in a different query does not share a binding or rule
cursor. A symbolic variable is not a top-level `let_` capture or an application
constructor such as `Math::var`.

A `ruleset` callback alternatively receives references to fresh typed symbolic
handles, for example `|x: &Math|`. This is the sole callback convention, not an
overload alongside owned parameters. Callback parameter names have no semantic
identity. A private owning token plus slot distinguishes fresh variables from
named variables and from other callback invocations. There is no
active-callback scope stack or lifetime policy for owned variable values. Tokens
remain owned by retained handles, preventing address-reuse aliases. The lowerer
assigns private backend names to both kinds; user names cannot collide with
generated names. Ruleset callbacks and `#[ruleset]` declarations support up to
128 borrowed parameters. This is the library's generated-adapter capacity, not a
Rust function limit. Tuple inputs and inspection selectors retain their separate
32-element limits.

```rust,ignore
let steps = ruleset(|current: &Ir, source: &Ir| {
    let next = chain(current, source);
    rule(
        (path(current, source),),
        (
            edge(current, &next),
            union(source, next),
        ),
    )
});
```

The callback borrows builder-owned variables only while authoring its rules.
Rust prevents these references from escaping. Explicitly cloning a variable
retains its owned syntax for use after the callback returns, including on another
thread. Every consuming query establishes its own bindings. Rules own their DAGs
and do not borrow the callback.

An ordinary Rust binding constructs shared syntax. There is no public
rule-local binding action; the compiler may emit `Action::Let`. An unused
expression can appear in action position to evaluate and discard its result;
`Into<Action>` makes that explicit for a homogeneous action vector.
Put pure shared expression bindings before the rule list when that removes
nested blocks, and reuse identical expressions across rules. Keep loop-dependent
generation and observable host work in their original scopes. Moving a Rust
binding does not move or remove an expression's ordered evaluation action.

`rule(lhs, rhs) -> Rule` is the only general rule constructor; neither
a per-rule callback nor a second scope helper is needed. An expression itself is
a query fact when only its existence matters; do not introduce an unused result
variable with `eq`:

```rust,ignore
let current = var::<Ir>("current");
let source = var::<Ir>("source");
let mark = rule(
    chain(&current, &source),
    path(&current, &source),
);
```

The same owned/borrowed expression inputs work in `check`, `.when`, and schedule
`.until`, including mixed tuples and homogeneous collections. Constructor and
function facts match existing rows without inserting missing rows; primitive
facts require successful native evaluation. This is not Boolean truthiness:
`check(egg::Bool::from(false))` succeeds; use `eq(flag, true)` when truth is the
condition. A failing query primitive remains a nonmatch. Keep `eq` when its result
variable participates in another fact/action or when asserting actual equality.

Inputs may be individual facts/actions, heterogeneous tuples, or homogeneous
collections. Facts, actions, and homogeneous arrays/vectors/slices can also be
borrowed when reused. Fixed query/action inputs prefer tuples; dynamic generators
retain vectors. Callbacks return a
rule, tuple, or collection directly, without `Ok`, `?`, or an authoring-only
`expect`. Genuinely fallible preparation remains ordinary Rust outside the
ruleset callback; there is no result-normalization layer or `try_ruleset` form.

Optional conditions use the same `Rule` value, not a second builder type:

```rust,ignore
let folding = ruleset(|n: &egg::I64, m: &egg::I64| {
    rewrite(
        Math::num(n) * Math::num(m),
        Math::num(0),
    )
    .when(eq(n, 0))
    .label("multiply by zero")
});
```

`Rule::when(facts) -> Self` appends conjunctive query facts, including facts that
bind variables used on the RHS. Repeated calls append in order; the implicit
rewrite match comes first. `.when(())` leaves the occurrence unchanged. There is
no mandatory empty condition argument. `birewrite(lhs, rhs) -> [Rule; 2]` is
shorthand for two ordinary rewrites, in forward then reverse order, not another
builder or rule representation. Use each returned rule's `.when` and options
independently, or map over the pair when both directions share them.

There is no public `hole` or special query-only variable category. An expression
matched in the query may be reused in its actions: its fields are ordinary
query-bound variables. Independently constructing another expression does not
bind its variables. At submission, the existing lowering
traversal rejects RHS-only variables, captures inside rules, and merge variables
outside a merge. Named and fresh query variables cannot be evaluated as top-level
actions or extraction roots. Schedules may use installed captures in a native
`until` check.

Rule options map to existing core options: seminaive or naive evaluation,
decomposition, and subsumed-row visibility. The default remains native
seminaive. At the selected pin, ordinary seminaive rules disallow non-global
table-function reads in RHS actions; naive rules allow the appropriate
read/full contexts. The wrapper preserves these restrictions and errors.
Unsafe-seminaive remains outside the initial safe authoring surface.

In a permitted mode, an RHS lookup stays on the RHS. For example, a naive rule
that matches `Pending(x)` and sets a result using `Lookup(x)` must still fail
at execution when that row is missing. Adding `Lookup(x)` to the LHS would
turn that failure into a nonmatching rule and is not a valid migration.
The wrapper also preserves action order, native buffering/rebuild behavior,
and seminaive cursors; it introduces no independent rule-step memory model.

### Immutable groups and schedules

`Ruleset` is an immutable collection of rule occurrences with an optional
diagnostic label. It can be built from rules, collections/tuples, or a callback
returning rules. Existing rules and groups may be borrowed for composition;
the new group retains their occurrences rather than reconstructing them.
Fixed theories use `#[ruleset]` on a function-shaped declaration. The attribute
exports a module-level `LazyLock<Ruleset>` with exactly the authored name and
visibility, constructed without an EGraph and importable as an ordinary value.
Typed borrowed parameters introduce fresh symbolic variables; the ordinary Rust
body returns rules or groups through the same input adapters as `ruleset(...)`.
The diagnostic name defaults to `module_path!()::function_name`, just like
callable declarations. An optional `name = "..."` overrides it without changing
execution identity. Reexports retain the defining module's name. No implicit
capitalization or extra public name is generated.
Declare a fixed theory's variables once as borrowed parameters and return
`Vec<Rule>` directly. Reuse a same-sort parameter across rules when its name fits
the role: each query binds it independently. Distinct variables within one rule
must stay distinct; renaming cannot introduce an equality constraint. Do not
repeat `let x = &var::<S>("x")` in each rule or split a coherent theory merely to
work around an adapter limit. Keep local bindings for useful shared expressions
and genuinely generated variables. Return `Ruleset` when the body combines
existing groups: it preserves their rule occurrences rather than
rebuilding them just to force a uniform return type.
Parameterized theory generators remain functions; only genuinely fallible
preparation requires `Result<Ruleset, TypedError>`. Internal vectors are ordinary
generation machinery. Fixed theories need no authoring-only `expect`. A callback
grouping multiple rules supplies convenient fresh variables, not shared query
bindings or eager validation.

Each rule construction creates a fresh, privately shared rule object; cloning
preserves its occurrence identity. Installation keys own that object rather
than storing an unprotected address or a global numeric ID. Diagnostic labels
are separate from identity. Semantic option changes and nonempty `.when` additions
use copy-on-write so retained or installed occurrences stay unchanged; no-op
changes preserve the occurrence.
Duplicate clones in a group keep their first occurrence, while separately
constructed equal-looking rules remain distinct. The initial backend mapping
installs each occurrence once in a private singleton ruleset and represents
groups with core's existing combined rulesets. Flatten/deduplicate membership
by occurrence before installation. This gives one native rule/cursor per
occurrence when groups overlap, at the cost of extra group metadata.

Every ruleset is usable directly as a one-run schedule. `sequence(...)`,
`repeat(n)`, `saturate()`, and `until(...)` translate
to native schedules with native stopping behavior. Combined groups execute
together; sequences introduce separate runs. Labels are diagnostic; changing
one does not reset a rule cursor. No mutable named child group changes an
already-built Rust schedule. `EGraph::run` accepts ordinary `Into<Schedule>`
inputs: owned or borrowed schedules and rulesets, including borrowed lazy
declarations. Use `egraph.run(&rewrites)?` for one run and
`egraph.run(rewrites.saturate())?` for saturation. Sequences may mix rulesets and
composed schedules. Immutable schedule nodes are shared through `Arc`; borrowing
or composing a schedule does not recursively copy its tree or create new rule
occurrences. There is no separate `Ruleset::run()` conversion method.

### Fixed values, not a second const language

The `#[ruleset]` attribute emits the existing `LazyLock<Ruleset>` initialization
and fresh-variable callback. It changes the declared item from a function to a
value; its parameters are not runtime arguments. It introduces no expression
syntax, runtime registry, or separate ruleset representation. Definitions
initialize on first use, not during compilation. Actual `const` rule
construction is deferred: the current expression graph owns `Arc` nodes and
runtime collections, and ordinary callback invocation is not const evaluation.
Removing global numeric IDs does not make those allocations or calls const.

A future const design must account for ownership and storage across both static
and runtime construction without adding a second public expression family.
For now, neither borrowed-lifetime expressions nor a rule/expression macro DSL
is introduced. Callable declaration macros produce ordinary functions and trait
impls; the ruleset attribute only removes fixed-theory initialization boilerplate.

### Explicit top-level captures

```rust,ignore
pub fn let_<I: ValueInput>(
    name: impl Into<Arc<str>>,
    initializer: I,
) -> I::Owned;
```

`let_` returns the same sort expression type as its initializer: an `Ir`
initializer produces an `Ir` expression representing the named binding, not
a separate public binding-handle type. `let_(name, &initializer)` also returns an
owned `Ir`. The documentation-hidden `ValueInput` adapter identifies the owned
sort of a value or reference; users neither implement it nor annotate calls with
it. The caller retains the capture expression for
later operations, including `frozen.lookup(&output)` or passing outputs
directly to Luminal's `SearchSpace::from_frozen` together with the owned snapshot.

The portable value records a capture declaration. Constructing it does not
evaluate the initializer or attach it to an EGraph. At its first ordered use,
the destination installs a private backend global for its initializer. Only
successful installation publishes the capture. Later uses read that global
without reevaluating the initializer.

Within an active scope, identical name, exact sort, and structural initializer
coalesce; incompatible reuse is a wrapper error. These comparisons ignore Arc
allocation and origins. Capture initializer evaluation follows the same native
commands and failure rules as ordinary evaluation. A failed installation may
leave backend metadata or earlier effects; it is not an automatically retryable
capture. Recovery follows the destination policy below.

Popping a scope removes captures installed there from the active ledger.
The portable declaration can subsequently install again, under a fresh backend
name. Captures installed before the push remain active. No public `S::global`
or `bind` spelling is added.

## Representation and identities

### An Arc graph for authoring, a flat forest for lowering

Each sort wrapper owns a cheap expression handle backed by immutable
`Arc<Node>`. A call holds its nominal callable reference and ordered child
handles. Combining independent producers creates a new root pointing to both;
it copies neither producer graph nor a declaration environment.

The same wrapper may hold a private frozen leaf retaining shared ownership of
one flat snapshot. A stored value and a selected constructor row are distinct
targets. Snapshot edges remain indices, never owning expression edges back into
the snapshot. Owned observations can outlive the public snapshot facade; one
retained scalar may consequently retain its complete snapshot.

Submission uses an iterative worklist to collect reachable nodes and
declarations. The private lowering representation contains:

- dense `NodeId` values and ordered child IDs;
- exact applied sort/callable references and literal payloads;
- variables identified by exact name or a fresh owning token and slot;
- ordered roots, including duplicates, with their action/query positions;
- source occurrences/origins in a separate table.

Initial flattening preserves allocation sharing. Structural interning is not
required in v1. Origins do not participate in equality, and flattening is not a
second public command or serialization API.

| Identity | Meaning |
| --- | --- |
| Allocation identity | The same authoring Arc; useful for worklists and preserving sharing. |
| Structural expression equality | Equal typed payloads, nominal callees, named/fresh variable identities, captures, and ordered children. Separate allocations may compare equal. |
| Nominal declaration identity | The same qualified declaration name and applied type arguments; incompatible definitions under that identity conflict. |
| Rule occurrence identity | One authored rule instance; clone/reinstallation retains it. |
| Frozen observation identity | Snapshot ownership identity, value-versus-node target kind, and local index. A class and a selected alternative differ, as do separate freezes. |
| Runtime e-class equality | Equality in a particular core EGraph state, tested through Egglog rather than Rust `Eq`. |

Structural `Eq/Hash` does not promise common evaluation. Hashes cache a
fingerprint assembled from payloads and already-cached child fingerprints.
Equality uses an explicit worklist of node pairs, a visited-pair set, and exact
comparison after hash fast paths; hash collisions never establish equality.
It need not be linear in the sum of graph sizes for every differently shared
pair of DAGs. Runtime comparisons use symbolic facts/catalog calls: a Rust
branch on `old == new` examines symbolic structure during authoring.
Frozen leaves compare their snapshot identity, not decoded payload equality.
To compare the numeric contents of an observed `I64` and a Rust integer, decode
the stored value explicitly. No Rust equality operation asks the live graph.

### References retain definitions without ownership cycles

V1 schemas are static Rust declarations, even when runtime code chooses which
functions and rules to use. Each generated function records a nominal reference
with a private static **definition-source token** and lazy resolver. Calling it
authors syntax without resolving the complete definition. Operator ownership
forms share the same logical reference, rather than redeclaring the callable.

A definition contains signatures, policy, referenced declarations, and, where
needed, a flat merge body. Its initializer records references without following
other resolvers. This rule also applies to signature construction, hashing,
formatting, and flattening performed during initialization. The submission
worklist finishes one initializer before following its dependencies. Resolved
definitions live for the process lifetime; they never strongly own another
definition through a mutually recursive Arc graph.

Collect every distinct definition source before coalescing nominal identities.
Otherwise two equal-looking definitions of `A` could both reference nominal
`B` while hiding conflicting definitions of `B`. Source tokens control
collection only and are excluded from semantic equality. Do not use function
pointer addresses as unique source tokens.

Generic builtin families have static family definitions plus explicit applied
sort arguments. A single `OnceLock` inside a generic Rust function is not
per-specialization storage and must not cache the first type for all types.

Recursive equality sorts work by declaring the sorts first, then container
sort dependencies and callable signatures. Constructing `Tree(Tree, Tree)`
does not recursively initialize its definition. In contrast, cyclic
merge-function installation dependencies, including a self-read by a merge,
are rejected: the pinned runtime resolves a merge's callees before installing
the new function.

The shared core program records the lowered nominal declarations and commands,
without serializing Rust resolver pointers, allocation identities, or `TypeId`.
Its versioned JSON format and Rust-generated schema are language independent.
A runtime factory for typed Rust declaration wrappers is not provided.

## DAG-to-AST lowering

The selected core `Expr` owns a tree. A DAG with
`x[i + 1] = Pair(x[i], x[i])` has linear unique nodes and exponential
expanded size. Iterative traversal alone does not prevent that expansion.

Before building ASTs, count every child edge, including both copies in
`Pair(x, x)`, and every ordered root occurrence. Visit each node's outgoing
edges once but increment counts before traversal deduplication. Compute
postorder, inline depth, and saturated expanded-size estimates with explicit
stacks. Root ordering and duplicates survive every phase.

Binding decisions are contextual:

| Context | Binding representation | Initial reuse boundary |
| --- | --- | --- |
| Rule LHS / `check` / `until` | Fresh variables and `Fact::Eq` atoms | One closed query scope |
| Rule RHS | Private `Action::Let` entries in the native action vector | One authored action, only eligible pure/construction subgraphs |
| Top-level setup/capture construction | Private typed zero-argument global tables and sets | One contiguous eligible construction region |
| Merge expression | Bounded tree expansion | No invented local binding facility |

### Queries

Assign a fresh query variable to each non-leaf DAG node and emit an equality
between that variable and a shallow call using child variables. Preserve the
original fact occurrences, now referring to these variables. A shared node
gets one query definition within that binder scope; distinct scopes never
share generated names or bindings.

This is ordinary query elaboration, followed by native typechecking and
planning. It must not insert constructors or execute a top-level let. A failed
`check` must not materialize its queried shared terms. Origin information
links generated variables and facts back to the corresponding source nodes.
RHS-only expressions never enter this pass.

### Rule actions

Lower each authored action left-to-right. At first use of an eligible
pure/construction node, emit a private local binding before its consumer:

```text
(let %t0 (Pair x x))
(let %t1 (Wrap %t0))
(set (Result x) %t1)
```

These are entries in that rule's existing `Actions(Vec<Action>)`. Binding
nodes even on an unshared deep chain can bound AST nesting. Dependencies stay
child-before-parent and arguments retain their native order.

Local bindings and their consumers stay in the same native typechecking unit,
so the consumers can constrain overloaded calls. A discarded polymorphic
result with no native type constraint is a narrower case: report an unsupported
type context or native ambiguity instead of inventing a state-writing sink.

Classify eligibility transitively. Do not memoize table reads, state-reading
primitives, or nodes depending on them merely because the Arc is shared.
Preserve each required read occurrence and its position, using distinct local
bindings per occurrence if needed. Bound the expanded occurrence count before
emission. Clear the reuse map between authored actions. The same Rust variable
used in later actions is still symbolic syntax, not a local capture promise.

No action is deduplicated. An expression explicitly put in action position
remains an evaluation even when its result is unused. The AST path retains
native matching and failure behavior; there is no wrapper-level exactly-once
per firing or per snapshot guarantee.

### Top-level commands and generated globals

The selected AST has singular `Command::Action`, not
`Command::Actions`. Do not depend on the latter from another branch or
simulate it by running a temporary rule.

An eligible construction region contains only literals, established captures,
constructors, and a small audited allowlist of total, state-independent
primitive operations. Eligibility checks the **entire** subtree. Consecutive
setup roots/capture initializers in such a region can share temporaries; an
explicit mutation, state-reading expression, or otherwise ineligible operation
ends the region.

Materialize shared non-leaf nodes and depth cuts with fresh globals, then lower
roots in their original order. Depth cuts apply to unshared chains too. In
explanatory let notation, a small doubling graph becomes:

```text
(let $typed0 (Leaf))
(let $typed1 (Pair $typed0 $typed0))
(let $typed2 (Pair $typed1 $typed1))
(let $output0 (Wrap $typed2))
(let $output1 (Other $typed2))
```

The actual initial lowering uses typed global slots: emit `Command::Function`
with schema `() -> S`, `merge: None`, `let_binding: true`,
`unextractable: true`, `hidden: false`, and `term_constructor: None`, followed
by `Command::Action(Action::Set(...))` that initializes the slot. Read it through
its zero-argument call. This is the same persistent-table shape used by native
global lowering, with the known output sort present before initializer
typechecking. A bare top-level `Action::Let` has no expected result type;
factoring `vec-empty` out of its consumer could otherwise make it ambiguous
when several vector sorts are installed. Use typed slots for explicit captures
and extraction roots too. Publish a capture only after the initializing set
succeeds, not merely after the table declaration.

An expression root submitted for top-level materialization gets a typed slot
even when it is single-use and needs no depth cut. Otherwise a standalone
overloaded expression could still lose its Rust-known result sort. This slot
is private and fresh; registration still returns `()` and retains no reusable
expression-to-result mapping.

Generated text is not parsed, and all these AST commands still pass through
the normal frontend. Names come from the destination's existing fresh-name
generator. The ordinary-expression reuse map expires at the region boundary
and is never a cross-call evaluation cache.

If a top-level action contains a table read, stateful primitive, or an
unaudited/fallible primitive, keep its ordered expression inside the original
singular action command, using bounded tree expansion. Do not move even a
read-free child into an earlier command opportunistically. An oversized or
over-deep expression in this fragment returns `LoweringLimit` before that
submission begins. An explicit capture of such an expression uses one native
initializing set into its typed slot at the original ordered position, with
the same expansion limits; its expression is not split across extra actions.

Core lowers ordinary top-level lets into a persistent zero-argument table and a
write; the typed-slot form declares this representation explicitly. Therefore
compiler globals cost declarations, table rows, frontend
processing, and command/rebuild boundaries. They are not ephemeral SSA slots.
They persist until their scope is popped or the EGraph is dropped; clearing
their rows does not uninstall their definitions. V1 retains them for that
lifetime, measures their count, and filters them from public observation.

Factoring eligible constructor setup must preserve successful public results
against its expanded reference. It does not promise the same execution count,
reports, or partial-failure prefix as one hypothetical enormous inline
command. The authoritative operational behavior is the emitted native command
sequence; no read is silently moved across a user write to obtain sharing.

### Merges

The pinned function AST has `merge: Option<Expr>`, with `old` and
`new` bound during merge execution. It has neither a local-let block nor
an `on_merge` field. Lower a merge by bounded tree expansion in its original
child order. Check both expanded node count and depth before allocating it.

Do not replace merge sharing with globals, rule-local variables, synthesized
table functions, or helper primitives. Those would introduce different binding
or runtime behavior. A large shared merge may consequently be unsupported even
when an equally large setup DAG is supported.

A merge builder is invoked during declaration construction with symbolic
`old`/`new`; runtime uses the emitted native expression. Preserve native
duplicate-output handling, table-read behavior, errors, and merge evaluation.
`no_merge` maps to the existing omitted-merge policy. Do not impose a new
lattice implementation, conflict ordering, or memo contract. Merge callees
must be installed first; reject an unrepresentable dependency cycle before
core can encounter a missing runtime table. The pinned merge checker also
does not use the declared output sort as an expected expression type. A bare
overloaded result such as `vec-empty` may therefore remain ambiguous; reject
that unsupported type context rather than claiming the signature disambiguates
it or rewriting it through another table. `on_merge` and arbitrary host
callbacks remain deferred.

### Depth, destruction, and budgets

Authoring hash/equality, collection, formatting, and destruction need separate
stack-safe algorithms. Use bounded DAG notation for diagnostic formatting.
Drain uniquely owned Arc children through an explicit release worklist;
ordinary derived `Drop` on recursive Arc fields is insufficient. Exercise
both shared and last-owner release, including concurrent clones.

Lowering limits count author nodes/edges, emitted commands/AST occurrences,
and AST/schedule/merge nesting. Size calculations saturate above the limit,
including duplicate edges, so rejection itself stays bounded. Binding cuts
keep supported query/RHS/setup ASTs shallow. Oversized fragments that cannot
be factored are rejected before submission.

There is no guarantee that unchanged core handles every 100,000-node input
stack-safely or in linear time. Its query canonicalizer repeatedly substitutes
variables, and downstream lowering, cloning, display, and drop contain
recursive paths. Test a 100,000-node **authoring** chain separately, then
measure accepted downstream cases under explicit bounds. The initial bound
values must be set by those tests, documented, and applied before AST creation;
iterative closing alone is not evidence of end-to-end safety.

## Destination state, methods, and failure

### Native execution with scope-aware bookkeeping

The typed `EGraph` privately owns the existing core EGraph. All declaration,
rule, action, and schedule execution uses shared programs containing constructed
AST commands through `run_shared_program`; observation and result decoding use core's existing
public read/extraction APIs. There is no typed direct linker or replacement
executor. The wrapper does not offer mutable raw access; a consuming
`into_raw` ends typed bookkeeping.

Use the pinned `extension_state_or_default` facility for a private clonable
`InstalledState`: nominal definitions under their exact names, confirmed
captures, installed rule/group occurrences, generated global inventory, scope
state, and health. Native push/pop snapshots this state with the EGraph.
Maps cloned into a snapshot must not share mutable cache contents.

Submission has these steps:

1. Flatten inputs left-to-right, collect reachable definition sources, and
   perform the wrapper's sort/capability, binder, conflict, frozen-reference,
   and size checks. Existing traversal follows captures and merge dependencies,
   so frozen values cannot be hidden under another authored expression.
2. Check pending and installed native names and prepare dependency order. Declare equality sorts first,
   then dependent applied sorts and callables; install rules/groups as needed.
3. Validate the shared program and commit the planned name generator after all
   wrapper checks, then submit emitted commands in order through
   `run_shared_program`, one command per confirmed-prefix boundary.
   Publish each installation entry only after its command succeeds.
4. Decode that method's expected result; discard temporary evaluation maps.

Core still typechecks all commands and may find errors that the wrapper
cannot predict. One input command may expand/desugar into several operations,
and checking declarations can itself mutate metadata. This pipeline provides
useful early checks, not a promise that every validation error precedes
mutation.

Internal names come from a planner-owned clone of core's symbol generator,
which reserves public and occupied names and tracks generated strings across
all hints. Invalid wrapper submissions leave even the live name generator unchanged.
After validation, commit the reserved names immediately before native execution;
native failure retains that reservation and the confirmed execution prefix.
The committed counter is not rolled back by pop. Restore the active name map,
but never reuse a popped generated name or a cached destination value.

### Sequential visibility and recovery

Top-level commands execute in order, including several commands emitted by
one method. A later command can observe earlier writes. A portable lookup
reused after a write performs a lookup at the new evaluation position; a
generated global from a prior region must not satisfy that lookup.

A failing command may retain metadata, buffered work, or a completed internal
prefix. Previously successful commands remain. No automatic transaction,
rollback, rebuild repair, or persistent read snapshot is promised.

The conservative first recovery policy is explicit:

- Wrapper preflight errors leave destination execution unstarted and healthy.
- The known native failed-check result becomes `Ok(false)` for `check`;
  it is a query outcome, not a string-matched execution error.
- Other failures after entering core, or a mismatch while decoding an
  effectful command's output, mark the typed destination `NeedsRestore`.
  Keep confirmed-prefix information for diagnostics, but refuse further typed
  execution or observation of a supposedly coherent typed state.
- `pop()` may restore an explicitly pushed healthy scope, including its
  installation ledger. If no healthy scope exists, use a fresh destination or
  consume it for raw diagnosis. A failed recovery remains unusable.
- Do not clear the cache and retry the same declaration: failed typechecking
  may already have changed core's metadata.

Public `Clone` of the typed destination is deferred. Push/pop, immutable
portable values, and owned frozen snapshots cover the initial consumer.
Proof/term-encoding configuration and user command-macro registration are also
outside this first facade; the normal core frontend machinery still runs.

### Exact method results

The prelude exposes methods and domain values, not `Command`,
`CommandOutput`, raw `Value`, `ArcSort`, destination `TermId`, or
first-class operation objects.

`Ruleset::to_ast()` is a diagnostic exception: it returns existing native AST
commands with verbatim nominal declaration names, without executing or natively
typechecking them. Their formatted text
is not a lossless source serialization contract.

`ProgramBuilder` supplies the supported offline export route. It preserves the
same dependency order, captures, rule occurrences, and scope rules as successful
live submissions, and finishes as the core `Program`, not a second wire format.

| Initial method | Success value | Meaning |
| --- | --- | --- |
| `EGraph::new(options)` | `EGraph` directly | Infallible destination construction |
| `EGraph::default()` | `EGraph` directly | Construction with default options |
| `install(definitions)` | `()` | Install sorts, selected callables, rules, or rulesets and their dependencies without evaluating expressions or running rules |
| `register(items)` | `()` | Ordered immediate materialization/actions |
| `run(schedule)` / `run(&schedule)` | `RunReport` | Install reachable immutable rules and execute an owned or borrowed native schedule |
| `stats()` | `RunReport` | Native report data, with diagnostic rule/group labels |
| `check(facts)` | `bool` | Native query success/nonmatch; other errors remain errors |
| `extract(&root)` | `S` | Core's best tree representative of that exact sort |
| `extract_with_cost(&root)` | `(S, DefaultCost)` | The same representative and native default cost |
| `extract_many(&roots)` | `Vec<S>` | Best tree for each ordered owned or borrowed root, including duplicates |
| `freeze()` | `FrozenEGraph` | Owned snapshot of supported installed data, with e-class traversal and no selected roots |
| `push()`, `pop()` | `()` | Native scope operation with typed installation state |
| `record(operation)` | `(R, CommandRecord)` | Run a Rust callback returning `R` and retain the native commands it submitted, including failures and scope changes |

All fallible methods return `Result<Success, TypedError>`. Both `stats` and
`freeze` take `&self`. `stats` clones the native cumulative report directly,
without emitting a print command or consuming a lowering command budget; an
unhealthy destination still returns `NeedsRestore`. Methods that install or
evaluate take `&mut self`. `freeze` uses `EGraphOptions::freeze_limits`; frozen
traversal and expression lookup borrow only the snapshot.
The error records the source origin, failing emitted command, confirmed prefix,
and underlying core error where available; it is not a receipt/root ledger.

### Explicit installation, export, and recording

`egraph.install((Num::sort_ref(), Definition::callable(|x: &Num| cost(x))?, &rules))?`
installs only the selected definitions and their reachable dependencies. The
selector runs ordinary Rust to build one direct symbolic call; it does not
evaluate Egglog arguments. It must use each fresh argument exactly once in
declaration order. Primitive operations are not installable declarations.
Installing a sort does not install its unrelated constructors. Installing a
ruleset does not execute a schedule, create dummy rows, or require `repeat(0)`.
Repeated compatible installation retains existing rule occurrences and cursors.
`register` continues to accept only expressions, relation rows, and actions.

For offline export, use `ProgramBuilder::default()` or `new(limits)`. Its
`install`, `register`, `run`, and `check` methods select the intended meaning of
objects: definitions install, expressions/actions materialize, schedules run,
and facts assert a query. `push` and `pop` restore planned installations and
captures while retaining fresh counters. Each lowering failure leaves the
builder unchanged. `finish()` validates and returns `egglog::program::Program`.
The builder assumes earlier commands succeed; its `check` is an assertion that
stops runtime execution when false, unlike the live method's boolean observation.
Native typechecking and execution can still reject an exported program.

The standalone `typed_program_export` example prints the complete JSON program
for folding `2 + 3` and checking equality with `5`:

```sh
cargo run --no-default-features --features typed --example typed_program_export > program.json
```

The shared program provides `to_json`/`from_json`, a Rust-generated schema, and
`parse` for Egglog source. `to_egglog()` is diagnostic source formatting;
`to_replayable_egglog()` checks that parsing preserves fields and literal bits
apart from spans, and returns an error otherwise. Qualified operator names,
unrepresentable identifiers, special float payloads, and internal metadata may
require JSON. The checked printer's parser policy remains part of its contract;
diagnostic text is not automatically a portable executable file.

Execute imported programs in the core graph with `run_shared_program`. The
typed wrapper deliberately has no arbitrary-program import method: native
declarations alone cannot reconstruct macro definition sources, authored capture
initializers, or rule occurrence identities used by typed installation tracking.
This boundary does not serialize snapshots, host extensions, or external files.

`let (result, record) = graph.record(|graph| { /* typed operations */ })?` returns
the callback's value even when that value is an error. The record comes from
core's command recorder and retains each attempted command and its outcome;
popping a scope does not erase history. A false live `check` has a failed native
`Check` entry even though its typed result is `Ok(false)`. A preflight rejection
submits no commands. A failing command may have internal partial effects, and
the unexecuted suffix is not recorded. Nested recordings are rejected; Rust
unwinding stops recording before resuming the panic.

The recorded commands include actual `Push`/`Pop` and the materialization prefix
of extraction. Native `extract_best` and result decoding, `freeze`, `stats`, and
`num_tuples` are direct observations with no command entries. Recording does not
invent an `Extract` command for them. A recording started on an existing graph
is a fragment requiring prior state. `record.program()` returns attempted
commands, including failures; it is not a successful-state snapshot or a promise
that replay continues after false checks or other failed commands.

Registration and rule RHSs share the same documentation-hidden `IntoActions<M>`
adapters; the mode is inferred and is not part of ordinary call syntax. Both
accept owned/borrowed expressions, relation rows, explicit mutation actions,
homogeneous arrays/slices/vectors, nested tuples through arity 32, and `()`.
Borrowed collections are traversed by reference, including multiply borrowed
leaves, without cloning their containers. Facts, rules, rulesets, and schedules
are not registration inputs; immutable rulesets enter through `run`. Empty
registration is a no-op, and an empty query is true.

Extraction uses the existing default tree cost model; `DefaultCost` is core's
current `u64` alias. Preserve core's cost and tie semantics. There is no empty
options argument pretending to select an algorithm; future supported cost or
algorithm choices must introduce real behavior.
For multi-root extraction, reuse installed explicit captures and evaluate each
other root, in order, into a fresh typed private global through the AST route
above. Ordinary `Command::Action(Expr)` returns no value. After every root has
been evaluated, read all current zero-argument rows in one immutable phase and
pass their ordered `(sort, value)` pairs to core's existing `extract_best`.
Do not obtain them through raw `eval_expr`, which bypasses the stipulated
command path. The shared `TermDag` supports one portable result DAG across the
complete output vector. Single-root extraction may use that same path or
decode native `Command::Extract(span, expr, Int(0))` when its expression retains
sufficient type context. Missing finite representatives return a structured
indexed error, never a raw sentinel.
This is shared **reconstruction**, not joint DAG-cost optimization.

Live table-size/row lookup, CSV input, extraction variants, dynamic costs, and
`keep_best` remain follow-ups with their own exact result types. They must use
ordinary call targets or the shared selector mechanism, not restore descriptor
objects. They are not introduced by the ordinary-call migration. Frozen typed
table inspection is specified below. In particular, do not claim destructive
`keep_best` preserves capture globals before testing that lifecycle.

## Luminal acceptance and observation

### One typed compiler path

The first migration targeted [oflatt/luminal PR #1][luminal-pr] at
`1836da847eaa5274af762472437c609a52d3706e`. The current, user-approved follow-up
extends the direct typed path through CPU, Metal, CUDA, search, and diagnostics.
Integration and verification status belongs in the review guide and Luminal's
migration notes; this section describes the intended contract.

```rust,ignore
fn build_reference_space(graph: &Graph) -> Result<SearchSpace, TypedError> {
    // One visit per HLIR node in stable topological order.
    // Preserve the existing sink ordering as an explicit ordered forest.
    let outputs: Vec<Ir> = capture_graph(graph)?;

    let mut egraph = EGraph::default();
    egraph.register(outputs.as_slice())?;
    optimize(&mut egraph, &Default::default(), false)?;
    let frozen = egraph.freeze()?;

    // Nodes expose exact positional values, including scalar/container fields.
    // Keep the snapshot itself plus observed roots, not a second graph copy.
    SearchSpace::from_frozen(frozen, &outputs)
}
```

The exact migration covers `hlir_to_egglog`, selected operation lowering and
rule producers, the base schema/rules, runtime dtype and loop-unroll rules,
and all three matmul-flattening rule files installed by `SumReduce`.
Its nominal sorts include `Expression`, `EList`, `DType`, `IR`,
`OpKind`, and `IList`. Even rules unused by the first numeric example must
construct and install successfully.

The typed path removes handwritten per-producer source lets and `OutputJoin`;
the lowerer may still generate private lets. Preserve every sink in its
defined order and retain explicit duplicate requested roots. Search and
validation use one choice map for the entire output forest; LLIR conversion
uses one producer memo. Generalize the existing `roots[0]` /
`roots.first()` assumptions in choice validation, mutable-choice discovery,
and `egglog_to_llir`. Calling a single-root reconstructor repeatedly would
lose sharing.

Each host operation implements `HLIROp::to_ir(&[&Ir]) -> Ir`; there is no central
downcast catalog. Backend constructors return the shared `OpKind` sort, and
native typed `Rule`, `Action`, `Ruleset`, and `Schedule` values replace runtime
schemas, source fragments, and parser hooks. `Runtime::rules()` returns a complete
phase-to-ruleset map and ordered initialization actions. Callers compose these
values to choose producing rules; constructor exclusions and decoder maps are
unnecessary. Selected expressions pass through an ordered list of local
`get_args`-based converters, backend first and core fallbacks afterward. A
nonmatch does no preparation; the first success or error stops dispatch.
No default runtime objects are used for registration, and no per-op
registration trait is needed. Existing runtime structs and defaults remain where
they are part of Luminal's execution/introspection API. Preparation functions
inspect fields with `get_args` without changing preparation timing, output sizes
or the accepted metadata domain. Rule ownership and hardware gates remain explicit;
they cannot be inferred from the constructors a rule produces. Backend code
generation remains ordinary Luminal code; only Egglog program generation and
string-driven semantic decoding disappear.

Fixed backend theories are retained `#[ruleset]` values, composed into a plain
phase-to-ruleset map. Bindings own installation deduplication and incremental
rule state; Luminal does not maintain another installation catalog. Phases
remain execution policy: the same ruleset can participate in a nested fixed
point or a repeated finishing stage. Initialization actions, preparation
dispatch and cleanup eligibility have separate purposes and lifetimes. The
driver preserves its outer updated-report loop, cycle limit, main-cycle tuple
checkpoints, ordered finishing stages and scheduled backend analysis. Existing
report structures wrap the native reports returned by the typed API; removed
parsing stages have no fabricated timings. A main-cycle tuple checkpoint is not
a bound on work inside saturation.

Preserve the historical operation/dependency boundary rather than redesigning
it during migration. FlashInfer's old rules emit a flat gather-index graph and
mask; preparation recovers the first compact input and drops the mask. Restore
that walk over exact frozen values, including its HLIR-first precedence,
ordered operand traversal and no-witness reconstruction failure. This decodes
dependencies for an already-selected operation; it is not a new Rust fusion
pass. Replacing it with all-witness relations changes both selected inputs and
failure-versus-fallback behavior. Ambiguous-input correctness concerns remain a
separate issue, not grounds for a new eligibility policy in this migration.
Preparation may modify the ordered input vector. Common reconstruction follows
the original candidate dependencies and requires every replacement edge to name
an already-materialized producer; it must not silently make an otherwise
unreachable alternative available.

Search retains the owned snapshot and ordered observed `Ir` roots. Eligibility
and choices refer directly to frozen handles; no copied `NodePayload`, textual
node IDs, serialization bridge, or duplicate edge graph is needed. A decoding
context owns dimension/list selection and reconstruction-local
memoization. Typed selectors and explicit scalar codecs reconstruct LLIR. The
pre-migration metadata-compatible operation substitution remains an explicit
Luminal reconstruction policy, not a fallback in exact typed field decoding. Kernel
profiling, conditional cleanup, buffer ownership, and one producer memo across
the forest remain meaningful Luminal responsibilities. Diagnostics retain source
aliases and distinct HLIR-only/backend runs using typed programs, then inspect
frozen values. Rendering and source listings are output-only.

Do not introduce cross-candidate dimension/list/dtype caches in this migration.
Those are selection and native-value caches, not Egglog registration bookkeeping.
The existing unrelated caches and per-reconstruction producer memo remain.
For backend rules affected by `45cffdbb`, preserve the preceding `d9fa09f4`
builder's semantics: `Rule::from_actions` generated source-match premises before
rendering a rule. Restore exactly those premises lost by the intermediate
quasiquote migration. This is not a new implicit behavior of typed `rule`.
Elsewhere `1836da84` remains the behavioral baseline. Further installation
failures require reproduction and a separate report, not speculative premises,
omitted rules or weakened validation.

### Freeze once, look up retained expressions and traverse

Like [Python's `EGraph.freeze()`][python-freeze], `freeze()` takes no roots and
returns an owned immutable snapshot. The snapshot remembers no selected root
list and remains usable after the live EGraph changes, pops a scope, or is
dropped. Rust adds e-class traversal; Python's current high-level
`FrozenEGraph` exposes declarations and rendering, not this traversal API.

```rust,ignore
impl EGraph {
    pub fn freeze(&self) -> Result<FrozenEGraph, TypedError>;
}

impl FrozenEGraph {
    pub fn lookup<S: EgglogValue>(
        &self,
        capture: &S,
    ) -> Result<S, TypedError>;

    pub fn nodes<S: EqualitySort>(
        &self,
        class: &S,
    ) -> Result<impl Iterator<Item = S> + '_, TypedError>;

    pub fn is_subsumed<S: EqualitySort>(&self, node: &S) -> Result<bool, TypedError>;

    // Checked heterogeneous-to-typed boundary for selection algorithms.
    pub fn typed_node<S: EqualitySort>(
        &self,
        node: FrozenENode<'_>,
    ) -> Result<S, TypedError>;

    // The selector determines Args and Output; adapter bounds are hidden.
    pub fn table(&self, /* selector */) -> Result<TableSnapshot<Args, Output>, TypedError>;
}

pub struct TableRow<A, O> {
    pub args: A,
    pub output: O,
    pub subsumed: bool,
}

pub struct TableSnapshot<A, O> {
    pub name: std::sync::Arc<str>,
    pub rows: Vec<TableRow<A, O>>,
}
```

`lookup` returns the same nominal sort wrapper as its capture. It contains a
private reference to a stored value, not a reconstructed expression tree.
`nodes` accepts a class reference from this snapshot and yields that class's
constructor alternatives as the same sort, including subsumed alternatives.
`typed_node::<S>(node)` also wraps a heterogeneous constructor node, after
checking snapshot ownership and the exact output sort. It retains the selected
row and declaration metadata; it does not extract, copy topology, or weaken
subsequent selector checks. Each yielded node selects a row, so
`get_args` can inspect its head and
return typed children. A class alone has no selected producer and returns
`None` from call inspection. `is_subsumed` requires a selected constructor node
from the same snapshot; ordinary expressions, classes, and foreign references
are errors. Function rows do not become constructor alternatives.

Frozen expressions retain the flat snapshot through shared ownership and can
outlive the `FrozenEGraph` facade. Equality and hashing distinguish snapshot
identity, value versus selected-node identity, and the local index; they do not
expand cycles or equate independently frozen snapshots. Holding one observed
scalar may retain the whole snapshot. Live submission recursively rejects
these references, including those nested in containers, rules, merge bodies,
or captures. No operation silently imports or detaches them.

Table inspection uses the same strict selector as ordinary call inspection:

```rust,ignore
for row in frozen.table(|x: &Num, axis: &egg::I64| x.weight(axis))? {
    let (x, axis): (Num, egg::I64) = row.args;
    let weight: i64 = (&row.output).try_into()?;
    // Explicit host decoding; x remains an observed class reference.
}
```

`TableSnapshot` is iterable over its rows and retains the selected table's
diagnostic name. Its type parameters retain the exact input and output sorts.
The snapshot must contain an exactly compatible declaration: an installed
empty table returns no rows, whereas an absent or conflicting declaration is
an error. Constructors, relations, and bodyless functions have tables;
primitives do not. Relation rows expose `egg::Unit` outputs without turning
authoring relations into expression values or exposing synthetic relation
classes. Selection never links a declaration or evaluates its arguments.
Typed selection must fail closed when the snapshot lacks the semantic
definition needed to establish compatibility; matching only a native table's
name and signature is insufficient. Such native tables remain available through
the heterogeneous observation interface. They are not silently promoted to a
verified typed declaration.

The underlying snapshot owns one flat representation of public declarations,
rows, values, and active captures, including installed empty tables and
referenced classes without constructor producers. Each row retains its exact
callable, ordered arguments, output, and subsumption. Scalars retain
native-stored payloads, including floating-point bits; host decoding uses
explicit fallible conversions from the ordinary builtin wrappers. Shallow
container decoding returns observed child wrappers, preserving sequence order,
multiset duplicates, map pairing, and applied sorts rather than selecting
representatives. It is not automatic conversion to a portable expression.

The heterogeneous integration views live outside the normal typed prelude.
Their `FrozenValueView` distinguishes an e-class, an exact `FrozenScalar`, or the
immediate structure of a `Vec`, `Set`, `MultiSet`, `Map`, or `Pair`. Container
values retain their applied sorts; maps expose paired keys/values, multisets
retain duplicates, and sequences retain order. Scalars cover Unit, bool, i64,
f64 bits, String, BigInt, BigRat, and Rational using native-stored payloads.
Strings are not escaped-and-reparsed, and scalar values are never reconstructed
from display labels. Unsupported sorts return errors.

Low-level node `args()` is the positional decoder: each field can be a scalar, container, or
e-class reference. `eclass_children()` is only a derived traversal of equality
edges through fields/containers, retaining order and duplicates; it does not
replace positional values. These borrowed observation views are not a second
authoring-expression family.
`FrozenENode::name()` and `FrozenTable::name()` borrow diagnostic names from the
snapshot. Table input and output sorts remain available, including for empty
tables; these observations do not expose the internal callable-identity object.

These low-level handles borrow the snapshot and retain ownership checks.
`frozen.as_view(&typed_value)` checks the exact sort and snapshot before giving
the heterogeneous copier a borrowed view. There is no unchecked public route
from a dense index or a foreign typed value. Flat storage preserves sharing
and cycles without recursive expansion.
Traversal order is stable within a snapshot, not a cross-run identity promise.
Luminal keeps its visited sets, filtering, empty-class cascade, choice map,
and shared LLIR reconstruction memo outside the immutable snapshot.
Its selection-space conversion may prune alternatives whose required producers
are absent and reject an exhausted root with its caller index. That existing
selection policy does not remove producer-free classes from the frozen snapshot.

`lookup(&expr)` takes the ordinary sort expression returned by `let_`; callers
do not repeat its name as a string. It accepts installed captures of every
supported sort, including primitive and container captures. Freeze copies their
exact names, sorts, initializer identities, and current values in the same
immutable read phase as public rows, without exposing private capture tables.
Lookup validates that identity against the frozen index. Unknown, incompatible,
or uninstalled captures and non-capture expressions return structured errors.
Lookup never evaluates an expression, reads the live graph, installs a capture,
inserts a constructor, invokes a primitive, or extracts a representative.

Luminal's `SearchSpace::from_frozen` takes an owned `FrozenEGraph` and retained
`&[Ir]` output captures. It checks each capture in caller order, attaches the
output index to errors, and stores the observed class values with duplicates
intact. Snapshot cloning shares immutable storage; different root lists need
not copy it. The snapshot itself remembers no selected roots.

The former `SerializedEGraph`, copied payloads/edges, and string IDs disappear.
Search keeps only admissible alternatives and selected frozen handles. Its
local converters inspect selected constructors with `get_args` and decode
fields without display parsing. Structural validation checks choices and
reachability; reconstruction rejects unsupported selected operations. One
reconstruction memo covers all ordered
roots, preserving shared producers. Cycles remain in frozen data; selected
input-list cycles and non-finite metadata report errors. There is no serializer
import/export, compatibility alias, scalar-string decoder, or fallback.

The primary builder reads resolved native table metadata and native
scalar/container accessors. Typed installation metadata retains exact
declaration definitions and capture identities; public declaration names are
the same in the typed and native views. Other native declarations contribute
their registered names and exact signatures. Both
produce the same diagnostic names, `SortRef` metadata, and frozen values. Core carries
explicit relation-origin metadata through normal declaration, clone, and
push/pop; a table's name or physical output sort is not evidence of its kind.
Proof-generated physical declarations remain outside this observation contract.
Standalone visualization can freeze the typed graph for exact observations,
then consume the wrapper with `into_raw()` and use native serialization for
JSON or DOT display output. The `serde` and `graphviz` features forward the
corresponding native capabilities. This display path adds no frozen-graph
exporter, importer, or semantic serialization bridge.
Native visualization retains declared constructor costs, including explicit
zero; the frozen typed API does not copy visualization-only cost metadata.

Native producers already have native root values. An integration API outside
the typed prelude resolves those values through the builder's private canonical
index and lets the integration callback inspect the borrowed snapshot. It neither
stores selected roots in the snapshot nor invents captures or another public
root-wrapper family. Native and typed paths do not have separate payload kinds.

Allocate local identities before following their references and traverse
iteratively, preserving cycles, sharing, and producer-free classes without
expanding them into trees. `EGraphOptions::freeze_limits: FreezeLimits` supplies
node/edge budgets without changing the parameterless method. Enforce them
during construction; an exceeded budget returns an error, never a truncated
snapshot or textual substitute. Flat ownership also permits stack-safe drop.
“Lossless” covers native-stored public data and captures, not engine checkpointing,
replay, or a persistence format. Unrelated native rendering facilities need not
be redesigned.

## Guidance and alternatives

### Design aims

This is the canonical guidance inferred from the user's reviews, not a claim
that unreviewed implementation choices are approved. It applies to macros,
public APIs, private lowering, snapshots, consumers and documentation alike.
The goal is less information for an author or reader to manage, not merely
shorter identifiers or moving boilerplate into another layer.

1. **Let the theory dominate the page.** A Rust port should aim for similar or
   fewer lines than its `.egg` source. Preserve source order, comments, guards,
   scopes and meaningful execution stages. Remove scaffolding, not explanations;
   keep API regression assertions in tests. Do not force one-line code or introduce
   an expression DSL to meet a line-count target. Put each test expression beside
   its expected result, rather than making readers align two distant arrays.
2. **Use Rust's existing language and tools.** Prefer methods, positional calls,
   operators, borrows, `From`/`Into` and IDE parameter hints. Macros should remove
   mechanical repetition while producing ordinary Rust items. One concept gets
   one useful public representation, not parallel enum/impl frontends or
   separately maintained payload schemas. Use snake_case functions and methods,
   including constructors. Use operator traits when their Rust contract fits;
   a familiar spelling is not a reason to fake a borrowed result or host Boolean.
3. **Supply each piece of information once, where it belongs.** Infer declaration
   kinds from signatures and names from namespaces. Parameters represent actual
   variation: a helper that always uses the same theory should own that choice
   instead of making every caller repeat it. Names add meaning within their
   namespace: `Math::universe`, not `Math::math_u`. Preserve explicit identities
   when they connect independent native producers; do not rename them blindly.
   Local capture names need only distinguish bindings in their destination:
   `let_("output", expr)` needs no module prefix in a standalone example.
   Declare meaningful fixed-theory variables once in the ruleset signature, not
   separately in every rule. Use opt-in named records with `..Args::fresh()` when
   otherwise irrelevant fields dominate the signature; reuse matched records to
   retain unchanged fields. Keep ordinary calls when they are shorter. Reuse names
   across independent rules where their meaning and sort agree, without merging
   distinct variables within any one rule or dropping a shared-field constraint.
   Omit only unconstrained fields: literals and structured subpatterns remain
   explicit even when a replacement preserves them unchanged.
4. **Make semantics explicit; make plumbing disappear.** Costs, merge policies,
   ambiguous conversions and execution stages deserve explicit choices. Repeated
   clone calls, trivial conversion impls and empty options do not. Callbacks earn
   their place through binding or genuine generation, not by wrapping an existing
   value. Symbolic construction records syntax; submission checks programs and
   remains fallible. Do not hide meaningful failures to remove `?`. A conversion
   earns its annotation by simplifying actual calls or providing needed interop;
   replacing an explicit constructor with an equally verbose `From` call is not
   a gain. Prefer useful literal operands such as `&bdd & true` or a literal
   rewrite RHS. Where the target sort is already known, use the literal directly:
   `ne(epilogue, "RELU")`, not `ne(epilogue, egg::String::from("RELU"))`.
   The same applies to existing numeric, Boolean and unit conversions. Keep an
   explicit constructor when it establishes the symbolic domain, binds a pattern
   field, or is needed for exact type inference; never turn symbolic arithmetic
   into host arithmetic merely to shorten it.
5. **Require an abstraction to own something real.** Keep an invariant, substantive
   transformation, error boundary or reused algorithm—not a wrapper that only
   forwards a call or returns a field. Prefer direct composition and exact typed
   data across boundaries to parallel IRs, executable strings or serialization
   round trips. Remove boilerplate at the boundary that creates it, using standard
   Rust conversions rather than making each caller add an adapter. A snapshot
   ownership check or ordered-forest reconstruction earns
   its place; a renamed copy of the same payload does not.
6. **Share immutable definitions; mutate destinations explicitly.** Fixed theories
   are reusable values; parameterized theories are functions. Borrow inputs and
   retain owned DAG nodes internally. Name real sharing and meaningful stages;
   inline single-use aliases that only move an expression away from its use.
   Prefer shared expression bindings before a flat rule list to a nested block
   per rule. Do not replace indentation with distant piles of one-use names.
   Fresh binders, distinct rule occurrences and native incremental state matter;
   incidental allocation counters and table order should not define authoring
   contracts. Sharing syntax is not caching its evaluated result: capture stays
   explicit. Put fixed groups at module scope with `#[ruleset]`, using the same
   simple rule-list style in introductory examples. Import shared Rust modules
   normally; reserve source inclusion for rendering runnable code in rustdoc.
7. **Be uniform where meanings agree, not where they differ.** Named primitive
   sorts include both scalars and containers. Callable forms should share defaults
   and capabilities where possible. Do not force relations into value roles,
   implicitly import frozen observations, conflate host arithmetic with symbolic
   construction, or select ambiguous constructors automatically. Exact values,
   cycles, sharing, provenance and action order survive a shorter surface.
8. **Question every layer, and decide with evidence.** Existing or previously
   unreviewed code is provisional. Check real call sites and source semantics,
   then remove an unnecessary distinction end to end rather than retaining a
   compatibility layer by habit. Test factual claims; ask the user about value
   tradeoffs. Neither smaller code nor fewer parsing stages proves a speedup.
   Passing semantic tests does not establish good authoring ergonomics: inspect
   the formatted rule bodies and repeated scaffolding against their source.
9. **Keep a migration traceable in the diff.** Replace removed `.egg` files at
   their existing paths with `.rs` counterparts when practical, and keep inline
   theories near their original owner. Preserve unrelated formulas, CLI options,
   comments and control flow. Prefer a source-local translation over moving it
   into a generic catalog. Private relations belong beside the theory that uses
   them, with inferred names. Shared declarations still have one canonical owner;
   explain their relocation instead of duplicating them. Separate intentional
   behavior changes and runtime redesigns from the typed authoring migration.
   Preserve algorithms and intentional priorities, not incidental snapshot IDs,
   table order or tied representatives. Accept a different choice only when
   both are valid under the same assumptions; report any correctness dependence
   on an arbitrary choice rather than selecting around it.

### Review questions

- Can the name, type, enclosing object or existing state supply this information?
- Do callers ever vary this parameter, policy, wrapper or callback?
- Does this layer enforce an invariant or merely translate the same thing again?
- Can a source-theory reader follow this without learning an extra vocabulary?
- Which sharing, error, ordering, identity or observation behavior must stay exact?
- Does the shorter version remove complexity, or just hide it somewhere else?
- Does this conversion shorten its real callers, and can each migrated rule or
  calculation be located beside its original source?

### Current alternatives

| Alternative | Decision for this implementation |
| --- | --- |
| Named records or a match-like macro | Opt-in `args = Name` records derive fields from the declaration for high-arity inspection/construction. A match DSL remains deferred; runtime dimension evaluation and CUDA resource ownership remain separate. |
| Symbolic indexing and comparison operators | Keep `.select` and explicit facts: Rust's `Index` returns a reference, while comparisons return host Boolean values. These contracts do not construct owned expressions or symbolic facts. |
| Enum schemas alongside impl declarations | Removed; one impl-based frontend and reached-declaration registration. |
| Function-address identity or nightly callable objects | Not needed; calls retain exact private declaration metadata on stable Rust. |
| Separate frozen expression types or implicit import of observed values | Rejected; same nominal wrappers with checked snapshot references, never silently evaluated or detached. |
| Actual const expression/ruleset construction or a new rule DSL | Deferred; `#[ruleset]` removes lazy initialization boilerplate while keeping ordinary Rust bodies and owned expressions. |
| Converter registry, automatic upcasts for every unary constructor, or reverse operators | Opt in per constructor to concrete standard conversions; nontrivial adapters stay Rust and reverse generation remains deferred. |
| Direct resolved/core linker and custom DAG executor | Deferred; existing AST and `run_program` are the agreed route. |
| Universal structural CSE or one snapshot per public method | Removed; neither follows from the AST path or native command sequencing. |
| Ban private lets/globals | Removed; contextual bindings preserve eligible DAGs in tree ASTs. |
| Port Python's copied declaration maps/global interner | Rejected for Rust authoring; collect definitions at submission and keep interning optional. |
| Put all declarations in mutually owning Arc objects | Rejected; static references/resolvers retain definitions without cycles. |
| Serializer-backed frozen decoding | Removed; exact scalar/container values and cyclic class references are the shared observation boundary. |
| Snapshot replay/persistence or joint DAG extraction | Deferred; neither is implied by lossless observation or shared reconstruction. |
| Move RHS reads into queries | Rejected because it can change errors into nonmatches and alter native rule semantics. |
| Recover by clearing caches after core failure | Rejected because partial metadata mutation survives. Use explicit scope restoration or a fresh owner. |

Python's nominal references, definition maps, and contextual let generation
are evidence for these choices. Its current per-call map copying, global weak
interner, and persistent constructor-expression cache are not copied.
[SealIR's tape and typed views][sealir-ase] provide precedent for flat storage,
but its expression equality is tape identity plus handle; it does not imply
structural CSE for independently authored graphs.

## Source basis and readiness

The [Cargo manifest](../Cargo.toml) pins the supporting core revision.
The [example coverage index](typed-example-coverage.md) records the admitted
source corpus, exclusions, and reproducible validation commands.

Declaration macros already have a separate
[`egglog-experimental-typed-macros` proc-macro crate](../typed-macros/Cargo.toml),
reexported by the typed runtime. The implementation is in
[declarations and macros](../typed-macros/src/lib.rs),
[expression storage](../src/typed/expr.rs), [lowering](../src/typed/lower.rs),
[execution](../src/typed/session.rs), and [frozen observation](../src/typed/freeze.rs).
Luminal's `src/typed_reference/schema.rs` and `src/typed_reference/lower.rs`
are the concrete consumer. The pinned core includes supporting metadata and
read-only observation changes, not a new typed frontend.

The pinned core and Luminal links used throughout this document identify the
historical source evidence for the design, not current dependency revisions.
Python precedent is in
[declarations](https://github.com/egraphs-good/egglog-python/blob/433542b4e7e5a4263566b166d849856a7e20aa5e/python/egglog/declarations.py),
[runtime](https://github.com/egraphs-good/egglog-python/blob/433542b4e7e5a4263566b166d849856a7e20aa5e/python/egglog/runtime.py),
[lowering](https://github.com/egraphs-good/egglog-python/blob/433542b4e7e5a4263566b166d849856a7e20aa5e/python/egglog/egraph_state.py), and
[rootless freeze][python-freeze]. These are precedents, not a dependency on
Python's authoring implementation.

[core-commands]: https://github.com/egraphs-good/egglog/blob/e264c37a3332453eb0b6486c82c8766dd1af17df/src/ast/mod.rs
[rust-index]: https://doc.rust-lang.org/core/ops/trait.Index.html
[core-runtime]: https://github.com/egraphs-good/egglog/blob/e264c37a3332453eb0b6486c82c8766dd1af17df/src/lib.rs
[core-types]: https://github.com/egraphs-good/egglog/blob/e264c37a3332453eb0b6486c82c8766dd1af17df/src/typechecking.rs
[core-globals]: https://github.com/egraphs-good/egglog/blob/e264c37a3332453eb0b6486c82c8766dd1af17df/src/ast/remove_globals.rs
[core-lowering]: https://github.com/egraphs-good/egglog/blob/e264c37a3332453eb0b6486c82c8766dd1af17df/src/core.rs
[core-extract]: https://github.com/egraphs-good/egglog/blob/e264c37a3332453eb0b6486c82c8766dd1af17df/src/extract.rs
[core-serialize]: https://github.com/egraphs-good/egglog/blob/e264c37a3332453eb0b6486c82c8766dd1af17df/src/serialize.rs
[python-freeze]: https://github.com/egraphs-good/egglog-python/blob/433542b4e7e5a4263566b166d849856a7e20aa5e/python/egglog/egraph.py
[sealir-ase]: https://github.com/saulshanabrook/sealir/blob/0fd2913c1e06f180ad5b2a3fec240985d0742664/sealir/ase.py
[luminal-pr]: https://github.com/oflatt/luminal/pull/1
[luminal-graph]: https://github.com/oflatt/luminal/blob/1836da847eaa5274af762472437c609a52d3706e/src/graph.rs
[luminal-egglog]: https://github.com/oflatt/luminal/blob/1836da847eaa5274af762472437c609a52d3706e/src/egglog_utils/mod.rs
[luminal-hlir]: https://github.com/oflatt/luminal/blob/1836da847eaa5274af762472437c609a52d3706e/src/hlir.rs
[luminal-tests]: https://github.com/oflatt/luminal/blob/1836da847eaa5274af762472437c609a52d3706e/src/tests/mod.rs
