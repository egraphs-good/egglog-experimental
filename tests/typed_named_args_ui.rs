#![cfg(feature = "typed")]

#[test]
fn named_records_reject_invalid_declarations_and_fields() {
    trybuild::TestCases::new().compile_fail("tests/typed_named_args_ui/*.rs");
}
