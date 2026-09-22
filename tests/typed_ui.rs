#![cfg(feature = "typed")]

#[test]
fn authoring_rejects_invalid_types() {
    let tests = trybuild::TestCases::new();
    tests.compile_fail("tests/typed_ui/*.rs");
}
