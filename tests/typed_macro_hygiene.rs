#![cfg(feature = "typed")]
#![allow(non_snake_case)] // These valid authored spellings are the regression.

use egglog_experimental::typed::builtins::I64;
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
    #[function(no_merge, args = FunctionArgs)]
    pub fn Read(
        definition: Atom,
        DEFINITION: Atom,
        __egglog_definition: Atom,
        __EGGLOG_DEFINITION: Atom,
    ) -> Atom;
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
    let read = Captured::Read(&atom, &atom, &atom, &atom);
    let fields = FunctionArgs::get_args(&read)?.unwrap();
    assert_eq!(fields.definition, atom);
    assert_eq!(fields.DEFINITION, atom);
    assert_eq!(fields.__egglog_definition, atom);
    assert_eq!(fields.__EGGLOG_DEFINITION, atom);
    assert_eq!(Atom::from(fields), read);
    Ok(())
}

#[relation]
fn input_pair(left: I64, right: I64);
#[relation]
fn output_pair(left: I64, right: I64);

#[ruleset]
fn parameter_names(r#type: &I64, __egglog_scope: &I64) -> Rule {
    rule(
        input_pair(r#type, __egglog_scope),
        output_pair(r#type, __egglog_scope),
    )
}

#[test]
fn ruleset_parameters_keep_authored_names_and_macro_hygiene() -> Result<(), TypedError> {
    let mut graph = EGraph::with_recording(true)?;
    graph.register(input_pair(11, 17))?;
    graph.run(&parameter_names)?;
    assert!(graph.check(output_pair(11, 17))?);
    let names: std::collections::HashSet<_> = graph
        .history()?
        .nodes
        .into_iter()
        .filter_map(|node| match node.kind {
            Some(egglog_experimental::proto::node::Kind::Var(name)) => Some(name),
            _ => None,
        })
        .collect();
    assert_eq!(names, ["type".into(), "__egglog_scope".into()].into());
    Ok(())
}
