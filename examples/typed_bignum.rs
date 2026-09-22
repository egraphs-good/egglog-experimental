// Core bignum.egg and Python bignum.py: normalization and exact arithmetic.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[function(no_merge)]
pub fn big_nums(numerator: egg::BigInt, denominator: egg::BigInt) -> egg::BigRat;

pub fn main() -> Result<(), TypedError> {
    let x = egg::BigInt::from(-1234);
    let y = egg::BigInt::from_string("2");
    let z = egg::BigRat::new(&x, &y);
    let mut egraph = EGraph::default();
    assert!(egraph.check(eq(z.numer().to_string(), "-617"))?);
    let numerator = egraph.extract(&z.numer().to_string())?;
    assert_eq!(numerator, egg::String::from("-617"));
    egraph.register(set(big_nums(x, y), z))?;
    let a = var::<egg::BigInt>("a");
    let b = var::<egg::BigInt>("b");
    let c = var::<egg::BigRat>("c");
    assert!(egraph.check((
        eq(big_nums(&a, &b), &c),
        eq(c.numer(), a >> 1),
        eq(c.denom(), b >> 1),
    ))?);
    Ok(())
}
