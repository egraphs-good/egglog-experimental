// Python examples/ndarrays.py: symbolic shape/index analysis and generated
// strings. This program does not execute NumPy or call Python from a rule.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Value;

#[declarations]
impl Value {
    #[constructor(from(i64, i32))]
    pub fn number(value: egg::I64) -> Value;
}
#[sort]
pub struct Values;

#[declarations]
impl Values {
    #[constructor(from)]
    pub fn vector(values: egg::Vec<Value>) -> Values;
}
#[constructor]
pub fn value_at(values: Values, index: Value) -> Value;
#[constructor]
pub fn length(values: Values) -> Value;
#[constructor]
pub fn concat(left: Values, right: Values) -> Values;
#[sort]
pub struct NDArray;
#[constructor]
pub fn at(array: NDArray, index: Values) -> Value;
#[constructor]
pub fn shape(array: NDArray) -> Values;
#[constructor]
pub fn arange(length: Value) -> NDArray;
#[constructor]
pub fn py_value(source: egg::String) -> Value;
#[constructor]
pub fn py_values(source: egg::String) -> Values;
#[constructor]
pub fn py_nd_array(source: egg::String) -> NDArray;
#[constructor]
pub fn cross(left: NDArray, right: NDArray) -> NDArray;

fn assert_simplifies<S: EqualitySort>(
    egraph: &mut EGraph,
    rules: &Ruleset,
    left: S,
    right: S,
) -> Result<(), TypedError> {
    egraph.register(&left)?;
    egraph.run(rules.repeat(30))?;
    egraph.extract(&left)?;
    assert!(egraph.check(eq(&left, right))?);
    Ok(())
}

#[declarations]
impl std::ops::Add<&Value> for &Value {
    type Output = Value;
    fn add(self, rhs: &Value) -> Value;
}

#[declarations]
impl std::ops::Mul<&Value> for &Value {
    type Output = Value;
    fn mul(self, rhs: &Value) -> Value;
}

#[ruleset]
fn value_rules(
    i: &egg::I64,
    j: &egg::I64,
    values: &egg::Vec<Value>,
    left: &egg::Vec<Value>,
    right: &egg::Vec<Value>,
    n: &Value,
    index: &Values,
) -> Vec<Rule> {
    vec![
        rewrite(Value::number(i) * Value::number(j), Value::number(i * j)),
        rewrite(Value::number(i) + Value::number(j), Value::number(i + j)),
        rewrite(
            value_at(Values::vector(values), Value::number(i)),
            values.get(i),
        ),
        rewrite(length(Values::vector(values)), Value::number(values.len())),
        rewrite(
            concat(Values::vector(left), Values::vector(right)),
            Values::vector(left.append(right)),
        ),
        rewrite(shape(arange(n)), Values::vector(egg::Vec::of([n]))),
        rewrite(at(arange(n), index), value_at(index, 0)),
    ]
}

#[ruleset]
fn python_values(l: &egg::String, r: &egg::String) -> Vec<Rule> {
    vec![
        rewrite(py_value(l) + py_value(r), py_value(l + " + " + r)),
        rewrite(py_value(l) * py_value(r), py_value(l + " * " + r)),
        rewrite(
            value_at(py_values(l), py_value(r)),
            py_value(l + "[" + r + "]"),
        ),
        rewrite(
            length(py_values(l)),
            py_value(egg::String::from("len(") + l + ")"),
        ),
        rewrite(concat(py_values(l), py_values(r)), py_values(l + " + " + r)),
        rewrite(
            at(py_nd_array(l), py_values(r)),
            py_value(l + "[" + r + "]"),
        ),
        rewrite(shape(py_nd_array(l)), py_values(l + ".shape")),
        rewrite(
            arange(py_value(l)),
            py_nd_array(egg::String::from("np.arange(") + l + ")"),
        ),
    ]
}

#[ruleset]
fn cross_shapes(l: &NDArray, r: &NDArray, index: &Values) -> Vec<Rule> {
    vec![
        rewrite(shape(cross(l, r)), concat(shape(l), shape(r))),
        rewrite(at(cross(l, r), index), at(l, index) * at(r, index)),
    ]
}

#[ruleset]
fn python_cross(l: &egg::String, r: &egg::String) -> Vec<Rule> {
    vec![rewrite(
        cross(py_nd_array(l), py_nd_array(r)),
        py_nd_array(egg::String::from("np.multiply.outer(") + l + ", " + r + ")"),
    )]
}

#[ruleset]
fn python_stage() -> Ruleset {
    ruleset((&value_rules, &python_values))
}

#[ruleset]
fn cross_stage() -> Ruleset {
    ruleset((&python_stage, &cross_shapes))
}

#[ruleset]
fn python_cross_stage() -> Ruleset {
    ruleset((&cross_stage, &python_cross))
}

pub fn main() -> Result<(), TypedError> {
    let mut egraph = EGraph::default();
    let range = arange(10);
    assert_simplifies(
        &mut egraph,
        &value_rules,
        shape(&range),
        Values::vector([10]),
    )?;
    for i in [0, 1] {
        assert_simplifies(
            &mut egraph,
            &value_rules,
            at(&range, Values::vector([i])),
            Value::number(i),
        )?;
    }

    assert_simplifies(
        &mut egraph,
        &python_stage,
        shape(py_nd_array("x")),
        py_values("x.shape"),
    )?;
    assert_simplifies(
        &mut egraph,
        &python_stage,
        at(arange(py_value("x")), py_values("y")),
        py_value("np.arange(x)[y]"),
    )?;

    assert_simplifies(
        &mut egraph,
        &cross_stage,
        shape(cross(range, arange(11))),
        Values::vector([10, 11]),
    )?;
    let product = cross(py_nd_array("x"), py_nd_array("y"));
    assert_simplifies(
        &mut egraph,
        &cross_stage,
        shape(&product),
        py_values("x.shape + y.shape"),
    )?;
    assert_simplifies(
        &mut egraph,
        &cross_stage,
        at(&product, py_values("idx")),
        py_value("x[idx] * y[idx]"),
    )?;
    assert_simplifies(
        &mut egraph,
        &python_cross_stage,
        at(product, py_values("idx")),
        py_value("np.multiply.outer(x, y)[idx]"),
    )?;
    Ok(())
}
