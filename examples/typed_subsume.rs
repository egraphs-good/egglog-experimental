// Core web-demo/subsume.egg: subsumed constructors remain checkable, not usable
// as new rewrite matches or extraction candidates.
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
#[relation]
pub fn saved_root(value: Math);

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
fn replace_three(x: &Math) -> Vec<Rule> {
    // Model a target where multiplying by three is expensive: force extraction
    // to use additions even though the original product remains equal to them.
    let lhs = Math::num(3) * x;
    vec![rule(
        &lhs,
        (union(&lhs, x + (x + x)), subsume(Math::num(3) * x)),
    )]
}

#[ruleset]
fn commute_saved(root: &Math, y: &Math) -> Vec<Rule> {
    vec![rewrite(root * y, y * root).when(saved_root(root))]
}

#[ruleset]
fn rules() -> Ruleset {
    ruleset((&replace_three, &commute_saved))
}

pub fn main() -> Result<(), TypedError> {
    let variable = Math::var("x");
    let original = Math::num(2) * (Math::num(3) * &variable);
    let output = let_("output", &original);
    let expected = Math::num(2) * (&variable + (&variable + &variable));
    let mut egraph = EGraph::default();
    // A saved relation binds the source's global $x in later rules. Inlining
    // its initializer would incorrectly try to match the now-subsumed Mul.
    egraph.register((&output, saved_root(&output)))?;
    egraph.run(replace_three.repeat(10))?;
    assert!(egraph.check(eq(&output, &expected))?);
    assert_eq!(egraph.extract(&output)?, expected);
    assert!(egraph.check(eq(&output, original))?);
    egraph.run(rules.repeat(10))?;
    assert_eq!(egraph.extract(&output)?, expected);
    Ok(())
}
