// Core web-demo/rw-analysis.egg: mutually dependent constant propagation and
// program rewriting on the complete fifteen-location loop example.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;
#[sort]
pub struct Val;

#[declarations]
impl Val {
    #[constructor(from(i64, i32))]
    pub fn int(value: egg::I64) -> Val;
    // Top denotes an arbitrary value, not a distinguished runtime constant.
    pub fn top() -> Val;
    pub fn truth() -> Val;
    pub fn falsity() -> Val;
}
#[sort]
pub struct Var;

#[declarations]
impl Var {
    #[constructor(from(&str, std::string::String))]
    pub fn named(name: egg::String) -> Var;
}
#[sort]
pub struct Loc;

#[declarations]
impl Loc {
    #[constructor(from(i64, i32))]
    pub fn at(index: egg::I64) -> Loc;
}
#[sort]
pub struct Expr;

#[declarations]
impl Expr {
    pub fn add(left: Var, right: Var) -> Expr;
    pub fn equal(left: Var, right: Var) -> Expr;
    pub fn var(variable: Var) -> Expr;
    #[constructor(from(i64, i32, egg::I64, &egg::I64))]
    pub fn constant(value: Val) -> Expr;
}
#[sort]
pub struct Stmt;

#[declarations]
impl Stmt {
    pub fn assign(variable: Var, value: Expr) -> Stmt;
    pub fn if_(condition: Var, yes: Loc, no: Loc) -> Stmt;
    pub fn goto(target: Loc) -> Stmt;
    pub fn call(function: Var) -> Stmt;
    pub fn end() -> Stmt;
}
#[constructor]
pub fn merge_val(left: Val, right: Val) -> Val;
#[constructor]
pub fn add_val(left: Val, right: Val) -> Val;
#[constructor]
pub fn eq_val(left: Val, right: Val) -> Val;
#[constructor]
pub fn program(location: Loc) -> Stmt;
#[relation]
pub fn bool_val(value: Val);
#[relation]
pub fn rewritten(location: Loc, statement: Stmt);
#[function(merge = merge_val)]
pub fn constants(location: Loc, variable: Var) -> Val;

impl From<bool> for Val {
    fn from(value: bool) -> Self {
        if value {
            Self::truth()
        } else {
            Self::falsity()
        }
    }
}

#[ruleset]
fn theory(
    value: &Val,
    integer: &egg::I64,
    other_integer: &egg::I64,
    li: &egg::I64,
    x: &Var,
    k: &Val,
    name: &egg::String,
    y: &egg::String,
    e: &Expr,
    l: &Loc,
    f: &Var,
    b: &Var,
    l1: &Loc,
    l2: &Loc,
    a: &Var,
    va: &Val,
    vb: &Val,
) -> Vec<Rule> {
    let top = Val::top();
    let truth = Val::truth();
    let falsity = Val::falsity();
    let left_int = Val::int(integer);
    let right_int = Val::int(other_integer);
    vec![
        rewrite(merge_val(&top, value), &top),
        rewrite(merge_val(value, &top), &top),
        rewrite(merge_val(&truth, &falsity), &top),
        rewrite(merge_val(&truth, &left_int), &top),
        rewrite(merge_val(&falsity, &truth), &top),
        rewrite(merge_val(&falsity, &left_int), &top),
        rewrite(merge_val(&left_int, &right_int), &top).when(ne(integer, other_integer)),
        rewrite(merge_val(value, value), value),
        rewrite(add_val(&top, value), &top),
        rewrite(add_val(value, &top), &top),
        rewrite(add_val(&truth, value), &top),
        rewrite(add_val(&falsity, value), &top),
        rewrite(add_val(value, &truth), &top),
        rewrite(add_val(value, &falsity), &top),
        rewrite(
            add_val(&left_int, right_int),
            Val::int(integer + other_integer),
        ),
        rewrite(eq_val(&top, value), &top),
        rewrite(eq_val(value, &top), top),
        rewrite(eq_val(&truth, &falsity), &falsity),
        rewrite(eq_val(&truth, &left_int), &falsity),
        rewrite(eq_val(&falsity, &truth), &falsity),
        rewrite(eq_val(&falsity, &left_int), &falsity),
        rewrite(eq_val(&left_int, &truth), &falsity),
        rewrite(eq_val(left_int, &falsity), falsity),
        rewrite(eq_val(value, value), truth),
        // Transfer constants through assignments and branches.
        rule(
            rewritten(Loc::at(li), Stmt::assign(x, Expr::constant(k))),
            set(constants(Loc::at(li + 1), x), k),
        ),
        rule(
            (
                rewritten(l, Stmt::assign(x, Expr::add(a, b))),
                eq(va, constants(l, a)),
                eq(vb, constants(l, b)),
                eq(l, Loc::at(li)),
            ),
            set(constants(Loc::at(li + 1), x), add_val(va, vb)),
        ),
        rule(
            (
                rewritten(l, Stmt::assign(x, Expr::equal(a, b))),
                eq(va, constants(l, a)),
                eq(vb, constants(l, b)),
                eq(l, Loc::at(li)),
            ),
            set(constants(Loc::at(li + 1), x), eq_val(va, vb)),
        ),
        rule(
            (
                rewritten(Loc::at(li), Stmt::assign(Var::named(name), e)),
                eq(value, constants(Loc::at(li), Var::named(y))),
                ne(name, y),
            ),
            set(constants(Loc::at(li + 1), Var::named(y)), value),
        ),
        // Transformation: demand, constant replacement, then fallback.
        rule(
            (
                eq(program(l), Stmt::assign(x, Expr::add(a, b))),
                eq(va, constants(l, a)),
                eq(vb, constants(l, b)),
            ),
            add_val(va, vb),
        ),
        rule(
            (
                eq(program(l), Stmt::assign(x, Expr::equal(a, b))),
                eq(va, constants(l, a)),
                eq(vb, constants(l, b)),
            ),
            eq_val(va, vb),
        ),
        rule(
            (
                eq(program(l), Stmt::assign(x, Expr::add(a, b))),
                eq(Val::int(integer), add_val(constants(l, a), constants(l, b))),
            ),
            rewritten(l, Stmt::assign(x, Expr::constant(Val::int(integer)))),
        ),
        rule(
            (
                eq(program(l), Stmt::assign(x, Expr::add(a, b))),
                eq(Val::top(), add_val(constants(l, a), constants(l, b))),
            ),
            rewritten(l, Stmt::assign(x, Expr::add(a, b))),
        ),
        rule(
            (
                eq(program(l), Stmt::assign(x, Expr::equal(a, b))),
                eq(value, eq_val(constants(l, a), constants(l, b))),
                bool_val(value),
            ),
            rewritten(l, Stmt::assign(x, value)),
        ),
        rule(
            (
                eq(program(l), Stmt::assign(x, Expr::equal(a, b))),
                eq(Val::top(), eq_val(constants(l, a), constants(l, b))),
            ),
            rewritten(l, Stmt::assign(x, Expr::equal(a, b))),
        ),
        rule(
            eq(program(l), Stmt::assign(x, Expr::constant(value))),
            rewritten(l, Stmt::assign(x, value)),
        ),
        rule(
            (
                rewritten(l, Stmt::call(f)),
                eq(value, constants(l, x)),
                eq(l, Loc::at(li)),
            ),
            set(constants(Loc::at(li + 1), x), value),
        ),
        rule(eq(program(l), Stmt::call(f)), rewritten(l, Stmt::call(f))),
        rule(
            (
                rewritten(l, Stmt::if_(b, l1, l2)),
                eq(value, constants(l, x)),
            ),
            (set(constants(l1, x), value), set(constants(l2, x), value)),
        ),
        rule(
            (
                eq(program(l), Stmt::if_(b, l1, l2)),
                eq(Val::truth(), constants(l, b)),
            ),
            rewritten(l, Stmt::goto(l1)),
        ),
        rule(
            (
                eq(program(l), Stmt::if_(b, l1, l2)),
                eq(Val::falsity(), constants(l, b)),
            ),
            rewritten(l, Stmt::goto(l2)),
        ),
        rule(
            (
                eq(program(l), Stmt::if_(b, l1, l2)),
                eq(Val::top(), constants(l, b)),
            ),
            rewritten(l, Stmt::if_(b, l1, l2)),
        ),
        rule(
            (rewritten(l1, Stmt::goto(l2)), eq(value, constants(l1, x))),
            set(constants(l2, x), value),
        ),
        rule(
            eq(program(l1), Stmt::goto(l2)),
            rewritten(l1, Stmt::goto(l2)),
        ),
    ]
}

pub fn main() -> Result<(), TypedError> {
    let [b, ten, one, zero, x, cond, y] =
        ["b", "ten", "one", "zero", "x", "cond", "y"].map(Var::named);
    let statements = [
        // x = 10; while (b) { if (x == 10) DoSomething();
        //                     else { DoSomethingElse(); x = x + 1; } } y = x;
        Stmt::assign(&b, Val::top()),
        Stmt::assign(&ten, 10),
        Stmt::assign(&one, 1),
        Stmt::assign(&zero, 0),
        Stmt::assign(&x, 10),
        Stmt::if_(b, 6, 13),
        Stmt::assign(&cond, Expr::equal(&x, ten)),
        Stmt::if_(cond, 8, 10),
        Stmt::call("DoSomething"),
        Stmt::goto(12),
        Stmt::call("DoSomethingElse"),
        Stmt::assign(&x, Expr::add(&x, one)),
        Stmt::goto(5),
        Stmt::assign(&y, Expr::add(x, zero)),
        Stmt::end(),
    ];
    let mut egraph = EGraph::default();
    egraph.register((bool_val(true), bool_val(false)))?;
    for (i, stmt) in statements.into_iter().enumerate() {
        egraph.register(union(program(i as i64), stmt))?;
    }
    egraph.run(theory.repeat(20))?;
    assert!(egraph.check(eq(constants(14, y), 10))?);
    Ok(())
}
