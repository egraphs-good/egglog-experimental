# egglog-experimental

This repo implements several experimental extensions to the core [`egglog`](https://github.com/egraphs-good/egglog).
Currently, this can be thought of as a standard library to `egglog`.

You can use the egglog [Zulip](https://egraphs.zulipchat.com/#narrow/stream/375765-egglog) to ask questions and suggest improvements to this repo.

## Trying it out

The easiest way to try out `egglog-experimental` is to use the [web demo](https://egraphs-good.github.io/egglog-demo), which builds on top of latest egglog-experimental.

To install egglog-experimental binary locally, you need to install `cargo` and run

```
git clone git@github.com:egraphs-good/egglog-experimental.git
cargo install --path=egglog-experimental
```

To use it in a Rust project, you can add it as a dependency in a `Cargo.toml` file.

```
egglog-experimental = "3.0"
```

## Documentation

Check out the crate documentation (built locally) for the current list of implemented extensions, API details, and demo links.
Releases are coordinated with compatible releases of egglog.

## Typed Rust authoring

The [RFC](docs/typed-rust-api-rfc.md) is the maintained design and implementation guide.
Its [design aims](docs/typed-rust-api-rfc.md#design-aims) are the review criteria
for the API, implementation and consumers—not just example style.

Enable the `typed` Cargo feature for typed declarations, expressions, rules, and
EGraph methods. Start with the [runnable basics lesson](examples/typed_tutorial_basics.rs),
then browse the [example index](docs/typed-example-coverage.md). The six lessons
also appear in the crate's `typed::tutorial` rustdoc.

Declarations produce ordinary Rust functions. `#[declarations] impl Num` can
declare constructors such as `Num::var("x")` and receiver methods such as
`x.upper()`. Annotated standard operator implementations author the same calls
through expressions such as `&x + &y` or `&x + 2`; one borrowed implementation
supplies owned and borrowed LHS forms with an `Into<Num>` RHS. Inside
`#[declarations]`, bodyless methods returning an equality sort are constructors;
omitting the return type declares a relation. Methods with bodies remain ordinary
Rust. Table functions keep explicit `#[function(merge = ...)]` or
`#[function(no_merge)]` policies. Free declarations use callable attributes.
There is no separate enum declaration syntax.
Names default to the qualified Rust declaration path; ordinary examples need no
`name = ...` annotation. Use an explicit name only to share an intentional
identity with another producer, such as an existing native Egglog declaration.

Rules and immutable rulesets are ordinary, infallible Rust values. For example,
using the declarations from [the math example](examples/typed_math.rs):

```rust
let algebra = ruleset(|a: &Math, b: &Math| {
    (
        rewrite(a + b, b + a),
        rewrite(a / a, 1.0).when(a.is_not_zero()),
    )
});
let x = var::<Math>("x");
let add_zero = rewrite(&x + 0.0, &x);
let theory = ruleset((algebra, add_zero));
```

Callbacks provide fresh borrowed variables; `var` provides reusable explicit
names whose exact UTF-8 identity is local to each query. Both author the same
owned expression graphs. `rule(lhs, rhs)` accepts query facts and ordered actions;
`rewrite(lhs, rhs).when(facts)` adds optional query conditions. No callback `Ok`,
authoring `?`, or special rewrite-builder type is needed. Construction records
definitions; lowering checks query bindings when they are submitted to an EGraph.
Native commands may still fail after earlier actions have taken effect, so
operational methods retain their errors and documented recovery behavior.
Defining a theory does not install or run it. A ruleset is already a one-run
schedule: submit it with `egraph.run(&theory)?`, or saturate it with
`egraph.run(theory.saturate())?`. Keep a reusable schedule in a local and pass
`&schedule` on repeated submissions; sharing preserves its rule occurrences and
incremental cursors.

To install definitions without running rules or creating rows, use
`egraph.install((Math::sort_ref(), Definition::callable(selector)?, &theory))?`.
The selector identifies an ordinary declared callable using fresh borrowed
arguments. `register` continues to mean immediate materialization/actions.

`ProgramBuilder` provides the same installation and lowering operations offline
and produces the shared `egglog::program::Program` for JSON interchange. Its
`to_egglog()` output is diagnostic; `to_replayable_egglog()` checks whether the
text preserves command fields and literal bits. `egraph.record(|graph| ...)?`
returns the callback result and core's attempted-command record, including
failures and scope changes. Direct observations and native extraction results
are not command entries. See the [export and recording contract](docs/typed-rust-api-rfc.md#explicit-installation-export-and-recording).

Export the standalone addition/folding example without running Egglog:

```sh
cargo run --no-default-features --features typed --example typed_program_export > program.json
```

The JSON includes declarations, a captured `2 + 3` expression, the folding
schedule, and an assertion that the result equals `5`. Core or another frontend
can deserialize this same `Program` and submit it through `run_shared_program`.

Fixed theories use a declaration attribute instead of handwritten lazy wrappers:

```rust,ignore
#[ruleset]
pub fn identities(x: &Math) -> Vec<Rule> {
    vec![rewrite(x + 0.0, x), rewrite(x * 1.0, x)]
}
```

`identities` is a lazy ruleset value, not a callable function. Its parameters
introduce symbolic variables once on first access; its body is ordinary Rust.
Its diagnostic name defaults to the defining module and `identities`; use
`#[ruleset(name = "...")]` only for an intentional override. Reexports preserve
that name and the same rule occurrences.
Runtime-dependent generators remain ordinary functions.

Use distinct named variables or borrowed callback parameters for a query pattern:

```rust
let expression = var::<Math>("expression");
let derivative = expression.diff(&x);
let mark_derivatives = rule(&derivative, derivative.universe());
```

Matched expressions and their variables can be reused on the RHS, but each rule
must bind those variables in its query. Calls accept borrowed values and supported
literal conversions directly. Table actions retain their target call:
`set(x.upper(), bound)`, `delete(relation(x))`, or `subsume(&x + &y)`.

Unary constructors can generate ordinary concrete `From` implementations:

```rust,ignore
#[sort]
pub struct Num;

#[declarations]
impl Num {
    #[constructor(from(i32, i64))]
    pub fn constant(value: egg::I64) -> Self;
    #[constructor(from(&str, std::string::String))]
    pub fn var(name: egg::String) -> Self;
    pub fn sin(&self) -> Self;
    pub fn interesting(&self);
}
```

`from` opts in for the declared input and its borrow; listed types add concrete
routes through that input's existing `Into` conversions. Nontrivial conversions
remain ordinary Rust implementations. The examples map numbers to constant
constructors and unambiguous names to name
constructors; `Num::from("x")` is an application node, not the query variable
`var::<Num>("x")`. Keep a symbolic left operand, as in `Num::from(2) * (&x * 3)`:
conversion does not supply reverse operators or change expression grouping.
Explicit constructors remain useful for field-binding patterns and selectors.
These infallible conversions author syntax; fallible `TryFrom` observation or
explicit numeric conversion operations have separate meanings.

For inspection, `get_args(&expr, |a: &Math, b: &Math| a + b)?` returns
`Some((left, right))` when the root has that callable, or `None` for another
root. The selector must return one direct call using every fresh input once,
in order. `freeze()` returns an owned snapshot; `lookup` returns the same sort
wrapper, `nodes(&class)?` selects constructor alternatives, and `table(selector)?`
returns typed argument/output rows. Decode observed scalars explicitly with
`TryFrom`. Observed values retain their snapshot and cannot enter live execution.

Expression facts ask whether a constructor/function row exists or a primitive
evaluates successfully; they work directly in rules, `when`, `until`, and `check`.
Use `eq` for real equality constraints and shared result binders, not disposable
existence variables. A boolean expression fact accepts either boolean value:
write `eq(boolean, true)` to require truth. Unlike `register(expression)`,
queries do not materialize missing constructor or function rows.
