#![cfg(feature = "typed")]
#![allow(non_snake_case)] // These valid authored spellings are the regression.

use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Atom;
#[declarations]
impl Atom {
    pub fn Leaf() -> Self;
}

#[sort]
pub struct Captured;
#[declarations]
impl Captured {
    #[constructor(args = CaptureArgs)]
    pub fn Capture(
        definition: Atom,
        DEFINITION: Atom,
        __egglog_definition: Atom,
        __EGGLOG_DEFINITION: Atom,
    ) -> Self;
    #[constructor(args = RawArgs)]
    pub fn Wrap(r#__EGGLOG_DEFINITION: Atom) -> Self;
    #[constructor(args = RawSuffixArgs)]
    pub fn RawSuffix(__EGGLOG_DEFINITION: Atom, r#__EGGLOG_DEFINITION_1: Atom) -> Self;
}

#[sort]
pub struct Wrapped;
// A free callable named `value` also detects capture by conversion locals.
#[constructor(from, try_from, args = ValueArgs)]
pub fn value(definition: Atom) -> Wrapped;

#[test]
fn generated_bindings_do_not_capture_authored_names() -> Result<(), TypedError> {
    let atom = Atom::Leaf();
    let captured = Captured::Capture(&atom, &atom, &atom, &atom);
    let args = CaptureArgs::get_args(&captured)?.unwrap();
    assert_eq!(args.definition, atom);
    assert_eq!(args.DEFINITION, atom);
    assert_eq!(args.__egglog_definition, atom);
    assert_eq!(args.__EGGLOG_DEFINITION, atom);
    let raw = Captured::Wrap(&atom);
    assert_eq!(
        RawArgs::get_args(&raw)?.unwrap().r#__EGGLOG_DEFINITION,
        atom
    );
    let suffix = Captured::RawSuffix(&atom, &atom);
    let args = RawSuffixArgs::get_args(&suffix)?.unwrap();
    assert_eq!(args.__EGGLOG_DEFINITION, atom);
    assert_eq!(args.r#__EGGLOG_DEFINITION_1, atom);
    let wrapped: Wrapped = atom.clone().into();
    assert_eq!(Atom::try_from(&wrapped)?, atom);
    assert_eq!(ValueArgs::get_args(&wrapped)?.unwrap().definition, atom);
    Ok(())
}
