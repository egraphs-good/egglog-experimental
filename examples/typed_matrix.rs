// Core/Python matrix examples plus the getting-started notebook's dimension,
// identity-product and demand stages. Inputs are explicitly registered before
// running, as required by the typed submission boundary.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;
#[sort]
pub struct Dim;

#[declarations]
impl Dim {
    #[constructor(from(&str, std::string::String))]
    pub fn named(name: egg::String) -> Dim;
    #[constructor(from(i64, i32))]
    pub fn lit(value: egg::I64) -> Dim;
}
#[sort]
pub struct Matrix;

#[declarations]
impl Matrix {
    pub fn kron(left: Matrix, right: Matrix) -> Matrix;
    #[constructor(from(&str, std::string::String))]
    pub fn named(name: egg::String) -> Matrix;
    pub fn id(size: Dim) -> Matrix;
}
#[constructor]
pub fn rows(matrix: Matrix) -> Dim;
#[constructor]
pub fn cols(matrix: Matrix) -> Dim;

#[declarations]
impl std::ops::Mul<&Dim> for &Dim {
    type Output = Dim;
    fn mul(self, rhs: &Dim) -> Dim;
}

#[declarations]
impl std::ops::Mul<&Matrix> for &Matrix {
    type Output = Matrix;
    fn mul(self, rhs: &Matrix) -> Matrix;
}

#[ruleset]
fn dims(a: &Dim, b: &Dim, c: &Dim, i: &egg::I64, j: &egg::I64) -> Vec<Rule> {
    vec![
        rewrite(a * (b * c), (a * b) * c),
        rewrite((a * b) * c, a * (b * c)),
        rewrite(Dim::lit(i) * Dim::lit(j), i * j),
        rewrite(a * b, b * a),
    ]
}

#[ruleset]
fn sizes(a: &Matrix, b: &Matrix, n: &Dim) -> Vec<Rule> {
    vec![
        rewrite(rows(Matrix::kron(a, b)), rows(a) * rows(b)),
        rewrite(cols(Matrix::kron(a, b)), cols(a) * cols(b)),
        rewrite(rows(a * b), rows(a)),
        rewrite(cols(a * b), cols(b)),
        rewrite(rows(Matrix::id(n)), n),
        rewrite(cols(Matrix::id(n)), n),
    ]
}

#[ruleset]
fn algebra(a: &Matrix, b: &Matrix, c: &Matrix, d: &Matrix, n: &Dim) -> Vec<Rule> {
    vec![
        rewrite(Matrix::id(n) * a, a),
        rewrite(a * Matrix::id(n), a),
        rewrite(a * (b * c), (a * b) * c),
        rewrite((a * b) * c, a * (b * c)),
        rewrite(
            Matrix::kron(a, Matrix::kron(b, c)),
            Matrix::kron(Matrix::kron(a, b), c),
        ),
        rewrite(
            Matrix::kron(Matrix::kron(a, b), c),
            Matrix::kron(a, Matrix::kron(b, c)),
        ),
        rewrite(
            Matrix::kron(a * c, b * d),
            Matrix::kron(a, b) * Matrix::kron(c, d),
        ),
        rewrite(
            Matrix::kron(a, b) * Matrix::kron(c, d),
            Matrix::kron(a * c, b * d),
        )
        .when((eq(cols(a), rows(c)), eq(cols(b), rows(d)))),
    ]
}

#[ruleset]
fn demand(a: &Matrix, b: &Matrix) -> Vec<Rule> {
    vec![
        rule(a * b, (cols(a), rows(a), cols(b), rows(b))),
        rule(Matrix::kron(a, b), (cols(a), rows(a), cols(b), rows(b))),
    ]
}

#[ruleset]
fn theory() -> Ruleset {
    ruleset((&dims, &sizes, &algebra, &demand))
}

pub fn main() -> Result<(), TypedError> {
    let mut egraph = EGraph::default();
    let x = Dim::named("x");
    let result = let_("dimension", (&x * 10) * 10);
    egraph.register(&result)?;
    egraph.run(dims.repeat(10))?;
    egraph.extract(&result)?;
    assert!(egraph.check(eq(result, &x * 100))?);
    let y = Dim::named("y");
    let identity_product = Matrix::id(&x) * Matrix::id(&y);
    let captured_rows = let_("identity_rows", rows(&identity_product));
    let captured_cols = let_("identity_cols", cols(identity_product));
    egraph.register((&captured_rows, &captured_cols))?;
    egraph.run(sizes.repeat(10))?;
    egraph.extract(&captured_rows)?;
    egraph.extract(&captured_cols)?;
    assert!(egraph.check((eq(captured_rows, x), eq(captured_cols, y)))?);
    egraph.push()?;
    let a = Matrix::named("X");
    let b = Matrix::named("Y");
    egraph.register(&a * &b)?;
    assert!(!egraph.check(rows(&a))?);
    egraph.run(&demand)?;
    assert!(egraph.check((rows(&a), cols(a), rows(&b), cols(b)))?);
    egraph.pop()?;
    let [n, m, p] = ["n", "m", "p"].map(Dim::named);
    let [a, b, c] = ["A", "B", "C"].map(Matrix::named);
    for (matrix, dim) in [(&a, &n), (&b, &m), (&c, &p)] {
        egraph.register((union(rows(matrix), dim), union(cols(matrix), dim)))?;
    }
    let ex1 = let_(
        "ex1",
        Matrix::kron(Matrix::id(&n), &b) * Matrix::kron(&a, Matrix::id(&m)),
    );
    let captured_rows = let_("rows", rows(&ex1));
    let captured_cols = let_("cols", cols(&ex1));
    egraph.register((&ex1, &captured_rows, &captured_cols))?;
    egraph.run(theory.repeat(20))?;
    assert!(egraph.check((
        eq(rows(&b), &m),
        eq(rows(Matrix::kron(Matrix::id(&n), &b)), n * &m),
        eq(&ex1, Matrix::kron(&a, b))
    ))?);
    egraph.extract(&ex1)?;
    let ex2 = let_(
        "ex2",
        Matrix::kron(Matrix::id(p), &c) * Matrix::kron(&a, Matrix::id(m)),
    );
    egraph.register(&ex2)?;
    egraph.run(theory.repeat(10))?;
    assert!(!egraph.check(eq(&ex2, Matrix::kron(a, c)))?);
    egraph.run(theory.repeat(10))?;
    egraph.extract(&ex2)?;
    Ok(())
}
