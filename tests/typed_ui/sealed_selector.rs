use egglog_experimental::typed::{
    __private::Expr, SelectCall, SelectedArgs, TypedError, builtins::I64,
};

struct UncheckedArguments;
impl SelectedArgs for UncheckedArguments {
    fn decode(_: &[Expr]) -> Result<Self, TypedError> {
        Ok(Self)
    }
}

struct UncheckedSelector;
impl SelectCall<()> for UncheckedSelector {
    type Root = I64;
}

fn main() {}
