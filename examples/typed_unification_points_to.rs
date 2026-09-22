// Core web-demo/unification-points-to.egg, including the full swap/f program
// database (and its original statement-name typos), not a reduced alias graph.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;
#[sort]
pub struct Func;

#[declarations]
impl Func {
    #[constructor(from(&str, std::string::String))]
    pub fn named(name: egg::String) -> Func;
}
#[sort]
pub struct Stmt;

#[declarations]
impl Stmt {
    #[constructor(from(&str, std::string::String))]
    pub fn named(name: egg::String) -> Stmt;
}
#[sort]
pub struct Expr;

#[declarations]
impl Expr {
    #[constructor(from(&str, std::string::String))]
    pub fn named(name: egg::String) -> Expr;
}
#[sort]
pub struct Field;

#[declarations]
impl Field {
    #[constructor(from(&str, std::string::String))]
    pub fn named(name: egg::String) -> Field;
}
#[sort]
pub struct Type;

#[declarations]
impl Type {
    #[constructor(from(&str, std::string::String))]
    pub fn named(name: egg::String) -> Type;
}
#[sort]
pub struct Alloc;

#[declarations]
impl Alloc {
    pub fn wrap(inner: Alloc) -> Alloc;
    pub fn variable(expr: Expr) -> Alloc;
}
#[relation(args = FunctionArgs)]
pub fn function(f: Func, argument: Expr, input: Type, output: Type);
#[relation]
pub fn func_stmt(f: Func, statement: Stmt);
#[relation]
pub fn assign(statement: Stmt, ty: Type, variable: Expr, value: Expr);
#[relation]
pub fn field_assign(statement: Stmt, base: Expr, field: Field, value: Expr);
#[relation]
pub fn store(statement: Stmt, pointer: Expr, value: Expr);
#[relation]
pub fn expr_statement(statement: Stmt, expr: Expr);
#[relation]
pub fn return_value(statement: Stmt, expr: Expr);
#[relation]
pub fn equal(result: Expr, left: Expr, right: Expr);
#[relation]
pub fn call(result: Expr, function: Func, argument: Expr);
#[relation]
pub fn add(result: Expr, left: Expr, right: Expr);
#[relation]
pub fn get_field(result: Expr, base: Expr, field: Field);
#[relation]
pub fn struct_field(result: Expr, field: Field, value: Expr);
#[relation]
pub fn address(result: Expr, base: Expr, field: Field);
#[relation]
pub fn load(result: Expr, pointer: Expr);
#[relation]
pub fn malloc(result: Expr, ty: Type);
#[constructor]
pub fn expr_points_to(expr: Expr) -> Alloc;
#[constructor]
pub fn ptr_points_to(allocation: Alloc) -> Alloc;

#[ruleset]
fn theory(
    s: &Stmt,
    t1: &Type,
    t2: &Type,
    v: &Expr,
    c: &Expr,
    t: &Type,
    e: &Expr,
    a: &Alloc,
    u: &Expr,
    b: &Alloc,
    ef: &Expr,
    f: &Field,
    l: &Expr,
    x: &Expr,
    callee: &Func,
) -> Vec<Rule> {
    let function = FunctionArgs::fresh();
    vec![
        // A variable initialized by malloc points to its own allocation.
        rule(
            (assign(s, t1, v, c), malloc(c, t2)),
            union(expr_points_to(v), Alloc::variable(v)),
        ),
        // Assignment propagates the value's allocation to the destination.
        rule(
            (assign(s, t, v, e), eq(expr_points_to(e), a)),
            union(expr_points_to(v), a),
        ),
        // If v -> a and u -> b, storing *v = u makes a point to b.
        rule(
            (
                store(s, v, u),
                eq(expr_points_to(v), a),
                eq(expr_points_to(u), b),
            ),
            union(ptr_points_to(a), b),
        ),
        // This analysis is field-insensitive: e and e.f share points-to information.
        rule(
            (get_field(ef, e, f), eq(expr_points_to(ef), a)),
            union(expr_points_to(e), a),
        ),
        rule(
            (eq(expr_points_to(e), a), get_field(ef, e, f)),
            union(expr_points_to(ef), a),
        ),
        // Address-of relates the base allocation, its pointee, and the field address.
        rule(
            (
                eq(expr_points_to(u), a),
                eq(ptr_points_to(a), b),
                address(e, u, f),
            ),
            union(expr_points_to(e), b),
        ),
        rule(
            (
                eq(expr_points_to(u), a),
                address(e, u, f),
                eq(expr_points_to(e), b),
            ),
            union(ptr_points_to(a), b),
        ),
        // An aggregate shares the allocations of its stored components.
        rule(
            (struct_field(l, f, x), eq(expr_points_to(x), b)),
            union(expr_points_to(l), b),
        ),
        // Calls propagate actual-argument allocations to the formal parameter.
        rule(
            (
                Relation::from(function.clone()),
                call(e, &function.f, v),
                eq(expr_points_to(v), a),
            ),
            union(expr_points_to(&function.argument), a),
        ),
        // A function's returned allocation flows to its call result.
        rule(
            (
                call(e, callee, v),
                func_stmt(callee, s),
                return_value(s, u),
                eq(expr_points_to(u), a),
            ),
            union(expr_points_to(e), a),
        ),
        // Loading follows the pointer through its allocation to its pointee.
        rule(
            (
                load(e, u),
                eq(expr_points_to(u), a),
                eq(ptr_points_to(a), b),
            ),
            union(expr_points_to(e), b),
        ),
    ]
}

pub fn main() -> Result<(), TypedError> {
    let mut egraph = EGraph::default();
    for (f, arg, input, output) in [
        ("swap", "r", "void", "{int *x; int *y;}*"),
        ("f", "i", "int", "int"),
    ] {
        egraph.register(function(f, arg, input, output))?;
    }
    for (f, statements) in [
        (
            "swap",
            vec![
                "int **xp = &(r->x)",
                "int **yp = &(r->y)",
                "int *z = *xp",
                "int *w = *yp",
                "*xp = a",
                "*yp = b",
            ],
        ),
        (
            "f",
            vec![
                "struct s *sp = malloc(sizeof(struct s))",
                "int *u = malloc(sizeof(int))",
                "int *v = malloc(sizeof(int))",
                "*u = i",
                "*v = i",
                "*sp = (struct s){u, v}",
                "swap(sp)",
                "int **zpp = &(sp->x)",
                "int *zp = *zpp",
                "return *zp",
            ],
        ),
    ] {
        for s in statements {
            egraph.register(func_stmt(f, s))?;
        }
    }
    for (s, t, v, e) in [
        ("int **xp = &(r->x)", "int **", "xp", "&(r->x)"),
        ("int **yp = &(r->x)", "int **", "yp", "&(r->y)"),
        ("int *a = *xp", "int *", "a", "*xp"),
        ("int *b = *yp", "int *", "b", "*yp"),
        (
            "struct s *sp = malloc(sizeof(struct s))",
            "struct s*",
            "sp",
            "malloc(sizeof(struct s))",
        ),
        (
            "int *u = malloc(sizeof(int))",
            "int *",
            "u",
            "malloc(sizeof(int))",
        ),
        (
            "int *v = malloc(sizeof(int))",
            "int *",
            "v",
            "malloc(sizeof(int))",
        ),
        ("int **zpp = &(sp->x)", "int **", "zpp", "&(sp->x)"),
        ("int *zp = *zpp", "int *", "zp", "*zpp"),
    ] {
        egraph.register(assign(s, t, v, e))?;
    }
    for (s, v, u) in [
        ("*xp = a", "xp", "a"),
        ("*yp = b", "yp", "b"),
        ("*u = i", "u", "i"),
        ("*v = i", "v", "i"),
        ("*sp = (struct s){u, v}", "sp", "(struct s){u, v}"),
    ] {
        egraph.register(store(s, v, u))?;
    }
    for (e, u, f) in [
        ("&(r->x)", "r", "x"),
        ("&(r->y)", "r", "y"),
        ("&(sp->x)", "sp", "x"),
    ] {
        egraph.register(address(e, u, f))?;
    }
    for (e, u) in [("*xp", "xp"), ("*yp", "yp"), ("*zpp", "zpp"), ("*zp", "zp")] {
        egraph.register(load(e, u))?;
    }
    for (e, t) in [
        ("malloc(sizeof(struct s))", "struct s"),
        ("malloc(sizeof(int))", "int"),
    ] {
        egraph.register(malloc(e, t))?;
    }
    for (f, v) in [("x", "u"), ("y", "v")] {
        egraph.register(struct_field("(struct s){u, v}", f, v))?;
    }
    egraph.register((
        expr_statement("swap(sp)", "swap(sp)"),
        return_value("return *zp", "*zp"),
        call("swap(sp)", "swap", "sp"),
    ))?;
    egraph.run(theory.repeat(40))?;
    let [u, v, sp] = ["u", "v", "sp"].map(|name| Alloc::variable(name));
    assert!(egraph.check((eq(&v, &u), ne(v, &sp)))?);
    // Variant enumeration is outside v1; retain both extraction roots.
    egraph.extract(&u)?;
    egraph.extract(&sp)?;
    Ok(())
}
