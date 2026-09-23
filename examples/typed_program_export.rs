//! Export a typed Rust theory as the shared program JSON consumed by core and Python.
//! Run with `cargo run --no-default-features --features typed --example typed_program_export`.

use egglog_experimental::typed::{builtins::I64, prelude::*};

#[sort(name = "ProgramMath")]
struct Math;

#[declarations]
impl Math {
    #[constructor(name = "program_num")]
    fn num(value: I64) -> Self;
    #[constructor(name = "program_add")]
    fn add(left: Self, right: Self) -> Self;
}

#[ruleset]
fn fold(left: &I64, right: &I64) -> Rule {
    rewrite(
        Math::add(Math::num(left), Math::num(right)),
        Math::num(left + right),
    )
}

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let root = let_("sum", Math::add(Math::num(2), Math::num(3)));
    let mut program = ProgramBuilder::default();
    program.install((Math::sort_ref(), &fold))?;
    program.register(&root)?;
    program.run(fold.saturate())?;
    program.check(eq(&root, Math::num(5)))?;
    // No Egglog expression has executed. Consumers execute the same definitions,
    // materialization, schedule, and final assertion from this versioned format.
    println!("{}", program.finish()?.to_json()?);
    Ok(())
}
