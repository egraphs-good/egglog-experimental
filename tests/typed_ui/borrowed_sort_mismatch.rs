use egglog_experimental::typed::{
    builtins::{I64, String},
    prelude::*,
};

fn main() {
    let number = I64::from(1);
    let text = String::from("one");
    let _ = eq(&number, &text);
}
