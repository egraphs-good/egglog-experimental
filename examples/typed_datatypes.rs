// Core web-demo/datatypes.egg: mutually dependent equality and vector sorts.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Math;

#[declarations]
impl Math {
    pub fn sum(values: egg::Vec<Math>) -> Math;
    pub fn boolean(value: Boolean) -> Math;
}
#[sort]
pub struct Boolean;

#[declarations]
impl Boolean {
    pub fn truth() -> Boolean;
    pub fn falsity() -> Boolean;
}

impl From<bool> for Boolean {
    fn from(value: bool) -> Self {
        if value {
            Self::truth()
        } else {
            Self::falsity()
        }
    }
}

impl From<bool> for Math {
    fn from(value: bool) -> Self {
        Self::boolean(Boolean::from(value))
    }
}

#[declarations]
impl std::ops::Add<&Math> for &Math {
    type Output = Math;
    fn add(self, rhs: &Math) -> Math;
}

pub fn main() -> Result<(), TypedError> {
    let expr = let_(
        "expr",
        Math::sum(egg::Vec::<Math>::of([true, false])) + true,
    );
    let mut egraph = EGraph::default();
    egraph.register(&expr)?;
    Ok(())
}
