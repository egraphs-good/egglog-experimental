// Core web-demo/array.egg: the four SMT-array examples, including disequality.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Math;

#[declarations]
impl Math {
    #[constructor(from(i64, i32))]
    pub fn num(value: egg::I64) -> Math;
    #[constructor(from(&str, std::string::String))]
    pub fn var(name: egg::String) -> Math;
}
#[sort]
pub struct Array;

#[declarations]
impl Array {
    pub fn constant(value: egg::I64) -> Array;
    #[constructor(from(&str, std::string::String))]
    pub fn a_var(name: egg::String) -> Array;
    pub fn select(&self, index: Math) -> Math;
    pub fn store(&self, index: Math, value: Math) -> Array;
}
#[relation]
pub fn neq(left: Math, right: Math);

#[declarations]
impl std::ops::Add<&Math> for &Math {
    type Output = Math;
    fn add(self, rhs: &Math) -> Math;
}

#[ruleset]
fn theory(
    x: &Math,
    y: &Math,
    z: &Math,
    e: &Math,
    i: &egg::I64,
    a: &egg::I64,
    b: &egg::I64,
    n1: &Math,
    n2: &Math,
    mem: &Array,
    i1: &Math,
    i2: &Math,
    e1: &Math,
    mem1: &Array,
    e2: &Math,
) -> Vec<Rule> {
    vec![
        rule(neq(x, y), neq(y, x)),
        rule(
            neq(x, x),
            panic("query (neq x x) found something equal to itself"),
        ),
        // Injectivity carries disequality through addition.
        rule((neq(x, y), x + z), neq(x + z, y + z)),
        rule((eq(x + Math::num(i), e), ne(i, 0)), neq(e, x)),
        rule(
            (eq(Math::num(a), n1), eq(Math::num(b), n2), ne(a, b)),
            neq(n1, n2),
        ),
        // A read sees the latest write at its own index.
        rewrite(mem.store(i1, e).select(i1), e),
        // Reads pass through writes only when the indices are known distinct.
        rule(
            (eq(mem.store(i1, e).select(i2), e1), neq(i1, i2)),
            union(mem.select(i2), e1),
        ),
        // A later write at the same index replaces the earlier value.
        rewrite(mem.store(i1, e1).store(i1, e2), mem.store(i1, e2)),
        // Writes at distinct indices commute.
        rule(
            (eq(mem.store(i2, e2).store(i1, e1), mem1), neq(i1, i2)),
            union(mem.store(i1, e1).store(i2, e2), mem1),
        ),
        rewrite(x + y, y + x),
        rewrite((x + y) + z, x + (y + z)),
        rewrite(Math::num(a) + Math::num(b), a + b),
        rewrite(x + 0, x),
    ]
}

pub fn main() -> Result<(), TypedError> {
    let mut egraph = EGraph::default();
    egraph.push()?;
    let [r1, r2, r3] = ["r1", "r2", "r3"].map(Math::var);
    let mem = Array::a_var("mem1");
    let index17 = &r1 + 17;
    let test1 = let_("test1", mem.store(&r1, 42).select(&r1));
    let test2 = let_("test2", mem.store(&r1, 42).select(&index17));
    let test3 = let_(
        "test3",
        mem.store(&r1 + &r2, 1)
            .store(&r2 + &r1, 2)
            .select(&r1 + &r3),
    );
    let test4 = let_(
        "test4",
        Math::num(1) + ((Math::num(1) + (Math::num(1) + &r1)) + -3),
    );
    egraph.register((
        neq(&r1, &r2),
        neq(&r2, &r3),
        neq(&r1, &r3),
        &test1,
        &test2,
        &test3,
        &test4,
    ))?;
    egraph.run(theory.repeat(5))?;
    assert!(egraph.check((
        eq(test1, 42),
        neq(&r1, r2),
        neq(&r1, &index17),
        eq(test2, mem.select(index17)),
        eq(test3, mem.select(&r1 + r3)),
        eq(test4, r1)
    ))?);
    egraph.pop()?;
    Ok(())
}
