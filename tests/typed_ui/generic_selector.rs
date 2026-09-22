use egglog_experimental::typed::{builtins::I64, prelude::*};
#[sort]
pub struct Num;
#[constructor]
fn make(value: I64) -> Num;
fn main() {
    // An impl-Into function item fixes one reference lifetime. Use a typed
    // closure when a selector needs a fresh reference for every probe lifetime.
    let _: Result<Option<(I64,)>, TypedError> = get_args(&make(1), make);
}
