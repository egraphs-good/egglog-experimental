use egglog_experimental::typed::{builtins::I64, prelude::*};
#[sort]
pub struct Num;
#[declarations]
impl Num {
    fn primitive_output(value: I64) -> I64;
}
#[declarations]
impl Num {
    #[function]
    fn missing_policy(value: I64) -> Num;
}
#[declarations]
impl Num {
    fn borrowed_output(value: I64) -> &Num;
}
#[declarations]
impl Num {
    async fn asynchronous(value: I64) -> Num;
}
#[declarations]
impl Num {
    const fn constant(value: I64) -> Num;
}
#[declarations]
impl Num {
    unsafe fn unsafe_stub(value: I64) -> Num;
}
#[declarations]
impl Num {
    fn generic<T>(value: T) -> Num;
}
#[declarations]
impl Num {
    #[constructor]
    fn annotated_body(value: I64) -> Num { unreachable!() }
}
fn main() {}
