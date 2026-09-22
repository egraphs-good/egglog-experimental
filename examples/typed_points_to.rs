// Core web-demo/points-to.egg: class-based inclusion points-to analysis.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Class;

#[declarations]
impl Class {
    #[constructor(from(&str, std::string::String))]
    pub fn named(name: egg::String) -> Class;
}
#[sort]
pub struct Field;

#[declarations]
impl Field {
    #[constructor(from(&str, std::string::String))]
    pub fn named(name: egg::String) -> Field;
}
#[sort]
pub struct Stmt;

#[declarations]
impl Stmt {
    pub fn new(variable: egg::String, class: Class) -> Stmt;
    pub fn assign(destination: egg::String, source: egg::String) -> Stmt;
    pub fn store(destination: egg::String, field: Field, source: egg::String) -> Stmt;
    pub fn load(destination: egg::String, source: egg::String, field: Field) -> Stmt;
}
#[relation]
pub fn var_points_to(variable: egg::String, class: Class);
#[relation]
pub fn heap_points_to(source: Class, field: Field, target: Class);

#[ruleset]
fn rules(
    variable: &egg::String,
    class: &Class,
    destination: &egg::String,
    source: &egg::String,
    field: &Field,
    c1: &Class,
    c2: &Class,
) -> Vec<Rule> {
    vec![
        // Allocation gives a variable its class; assignment copies that information.
        rule(Stmt::new(variable, class), var_points_to(variable, class)),
        rule(
            (
                Stmt::assign(destination, source),
                var_points_to(source, class),
            ),
            var_points_to(destination, class),
        ),
        // Loading v2.f follows v2's class, then that class's field edge.
        rule(
            (
                Stmt::load(destination, source, field),
                var_points_to(source, c1),
                heap_points_to(c1, field, c2),
            ),
            var_points_to(destination, c2),
        ),
        // Storing v1.f = v2 adds a field edge between their possible classes.
        rule(
            (
                Stmt::store(destination, field, source),
                var_points_to(destination, c1),
                var_points_to(source, c2),
            ),
            heap_points_to(c1, field, c2),
        ),
    ]
}

pub fn main() -> Result<(), TypedError> {
    // The source's "From Datalog to Flix" example aliases o3 = o2, stores o1 in
    // o2.f, then loads o3.f. The load must see through that alias.
    let a = Class::named("A");
    let b = Class::named("B");
    let field = Field::named("f");
    let mut egraph = EGraph::default();
    egraph.register((
        Stmt::new("o1", "A"),
        Stmt::new("o2", "B"),
        Stmt::assign("o3", "o2"),
        Stmt::store("o2", "f", "o1"),
        Stmt::load("r", "o3", &field),
    ))?;
    egraph.run(rules.repeat(3))?;
    assert!(egraph.check((
        var_points_to("o1", &a),
        var_points_to("o2", &b),
        var_points_to("o3", &b),
        heap_points_to(b, field, &a),
        var_points_to("r", a),
    ))?);
    Ok(())
}
