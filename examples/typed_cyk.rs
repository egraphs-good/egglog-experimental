// All three grammars/inputs from core web-demo/cyk.egg. The approved v1
// boundary replaces the two variant displays with single-best extraction.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;
#[sort]
pub struct Terminal;

#[declarations]
impl Terminal {
    pub fn term(name: egg::String) -> Terminal;
}
#[sort]
pub struct Nonterminal;

#[declarations]
impl Nonterminal {
    #[constructor(from(&str, std::string::String))]
    pub fn non_term(name: egg::String) -> Nonterminal;
}
#[sort]
pub struct Tree;

#[declarations]
impl Tree {
    pub fn branch(name: egg::String, left: Tree, right: Tree) -> Tree;
    pub fn leaf(name: egg::String, text: egg::String) -> Tree;
}
#[function(no_merge)]
pub fn get_string(position: egg::I64) -> egg::String;
#[relation]
pub fn prod(head: Nonterminal, left: Nonterminal, right: Nonterminal);
#[relation]
pub fn end(head: Nonterminal, text: egg::String);
#[relation]
pub fn parses(length: egg::I64, start: egg::I64, head: Nonterminal);
#[constructor(cost = 1000)]
pub fn build(length: egg::I64, start: egg::I64, head: Nonterminal) -> Tree;

#[ruleset]
fn grammar(
    a: &egg::String,
    text: &egg::String,
    pos: &egg::I64,
    b: &egg::String,
    c: &egg::String,
    p1: &egg::I64,
    p2: &egg::I64,
    start: &egg::I64,
    f1: &Tree,
    f2: &Tree,
) -> Vec<Rule> {
    let head = Nonterminal::non_term(a);
    let left = Nonterminal::non_term(b);
    let right = Nonterminal::non_term(c);
    vec![
        rule(
            (end(&head, text), eq(text, get_string(pos))),
            (
                parses(1, pos, &head),
                union(build(1, pos, &head), Tree::leaf(a, text)),
            ),
        ),
        rule(
            (
                prod(&head, &left, &right),
                parses(p1, start, &left),
                parses(p2, start + p1, &right),
            ),
            parses(p1 + p2, start, &head),
        ),
        rule(
            (
                prod(&head, &left, &right),
                eq(f1, build(p1, start, left)),
                eq(f2, build(p2, start + p1, right)),
            ),
            union(build(p1 + p2, start, head), Tree::branch(a, f1, f2)),
        ),
    ]
}

pub fn main() -> Result<(), TypedError> {
    let mut egraph = EGraph::default();
    egraph.push()?;
    for (i, word) in ["she", "eats", "a", "fish", "with", "a", "fork"]
        .into_iter()
        .enumerate()
    {
        egraph.register(set(get_string((i + 1) as i64), word))?;
    }
    for (a, b, c) in [
        ("S", "NP", "VP"),
        ("VP", "VP", "PP"),
        ("VP", "V", "NP"),
        ("PP", "P", "NP"),
        ("NP", "DET", "N"),
    ] {
        egraph.register(prod(a, b, c))?;
    }
    for (a, s) in [
        ("VP", "eats"),
        ("NP", "she"),
        ("V", "eats"),
        ("P", "with"),
        ("N", "fish"),
        ("N", "fork"),
        ("DET", "a"),
    ] {
        egraph.register(end(a, s))?;
    }
    egraph.run(grammar.repeat(100))?;
    assert!(egraph.check(parses(7, 1, "S"))?);
    for name in ["VP", ""] {
        assert!(!egraph.check(parses(7, 1, name))?);
    }
    let test1 = let_("test1", build(7, 1, "S"));
    egraph.register(&test1)?;
    egraph.extract(&test1)?;
    egraph.pop()?;
    egraph.push()?;
    for (a, b, c) in [
        ("S", "A", "B"),
        ("S", "B", "C"),
        ("A", "B", "A"),
        ("B", "C", "C"),
        ("C", "A", "B"),
    ] {
        egraph.register(prod(a, b, c))?;
    }
    for (a, s) in [("A", "a"), ("B", "b"), ("C", "a")] {
        egraph.register(end(a, s))?;
    }
    for (case, words) in [["a", "b", "a", "a", "b"], ["a", "a", "a", "a", "a"]]
        .into_iter()
        .enumerate()
    {
        egraph.push()?;
        for (i, word) in words.into_iter().enumerate() {
            egraph.register(set(get_string((i + 1) as i64), word))?;
        }
        egraph.run(grammar.repeat(100))?;
        assert!(egraph.check(parses(5, 1, "S"))?);
        assert!(!egraph.check(parses(5, 1, "B"))?);
        if case == 1 {
            assert!(egraph.check(parses(5, 1, "A"))?);
            for name in ["", "unrelated"] {
                assert!(!egraph.check(parses(5, 1, name))?);
            }
        }
        let result = let_(format!("test{}", case + 2), build(5, 1, "S"));
        egraph.register(&result)?;
        egraph.extract(&result)?;
        egraph.pop()?;
    }
    egraph.pop()?;
    Ok(())
}
