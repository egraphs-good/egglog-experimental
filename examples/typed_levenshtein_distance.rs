// Core web-demo/levenshtein-distance.egg: recursive edit distance over terms.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Expr;

#[declarations]
impl Expr {
    #[constructor(from(i64, i32))]
    pub fn num(value: egg::I64) -> Expr;
    pub fn min(first: Expr, second: Expr, third: Expr) -> Expr;
}
#[sort]
pub struct Text;

#[declarations]
impl Text {
    pub fn empty() -> Text;
    pub fn cons(head: egg::String, rest: Text) -> Text;
}
#[constructor]
pub fn length(text: Text) -> Expr;
#[constructor]
pub fn edit_distance(left: Text, right: Text) -> Expr;
#[function(no_merge)]
pub fn unwrap(value: Expr) -> egg::I64;

impl From<&str> for Text {
    fn from(value: &str) -> Self {
        value
            .chars()
            .rev()
            .fold(Self::empty(), |rest, c| Self::cons(c.to_string(), rest))
    }
}

impl From<std::string::String> for Text {
    fn from(value: std::string::String) -> Self {
        Self::from(value.as_str())
    }
}

#[declarations]
impl std::ops::Add<&Expr> for &Expr {
    type Output = Expr;
    fn add(self, rhs: &Expr) -> Expr;
}

#[ruleset]
fn rules(
    a: &egg::I64,
    b: &egg::I64,
    c: &egg::I64,
    head: &egg::String,
    rest: &Text,
    s: &Text,
    left: &Text,
    right: &Text,
    a_name: &egg::String,
    b_name: &egg::String,
    n: &egg::I64,
) -> Vec<Rule> {
    let left_text = Text::cons(a_name, left);
    let right_text = Text::cons(b_name, right);
    let number = Expr::num(n);
    vec![
        rewrite(Expr::num(a) + Expr::num(b), a + b),
        rewrite(
            Expr::min(Expr::num(a), Expr::num(b), Expr::num(c)),
            a.min(b).min(c),
        ),
        rewrite(length(Text::empty()), 0),
        rewrite(length(Text::cons(head, rest)), Expr::num(1) + length(rest)),
        rewrite(edit_distance(Text::empty(), s), length(s)),
        rewrite(edit_distance(s, Text::empty()), length(s)),
        rewrite(
            edit_distance(Text::cons(head, left), Text::cons(head, right)),
            edit_distance(left, right),
        ),
        rewrite(
            edit_distance(&left_text, &right_text),
            Expr::num(1)
                + Expr::min(
                    edit_distance(left, right),
                    edit_distance(left_text, right),
                    edit_distance(left, right_text),
                ),
        )
        .when(ne(a_name, b_name)),
        rule(&number, set(unwrap(&number), n)),
    ]
}

pub fn main() -> Result<(), TypedError> {
    let cases = [
        ("horse", "ros", 3),
        ("intention", "execution", 5),
        ("horse", "", 5),
    ];
    let outputs: std::vec::Vec<_> = cases
        .iter()
        .enumerate()
        .map(|(i, (a, b, _))| let_(format!("edit-distance::{i}"), edit_distance(*a, *b)))
        .collect();
    let mut egraph = EGraph::default();
    egraph.register(outputs.as_slice())?;
    egraph.run(rules.repeat(100))?;
    for (output, (_, _, expected)) in outputs.into_iter().zip(cases) {
        assert_eq!(egraph.extract(&unwrap(&output))?, egg::I64::from(expected));
        assert!(egraph.check(eq(output, expected))?);
    }
    Ok(())
}
