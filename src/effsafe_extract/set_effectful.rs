//! `(set-effectful Sort e)`: mark the e-class of `e` as effectful.
//!
//! `Sort` must be an existing eq sort, and `e` must have that sort. Marks may
//! appear at top level or in rule heads. The per-sort relation is declared on
//! first use; no separate declaration is needed.

use egglog::ast::{Action, Command, Expr, ParseError};
use egglog::util::SymbolGen;
use egglog::{CommandMacro, Error, TypeInfo};

/// The macro's name in programs.
pub const SET_EFFECTFUL: &str = "set-effectful";

const RELATION_PREFIX: &str = "effsafe_effectful_";

/// The generated relation holding the effectful e-classes of `sort`.
pub fn effectful_relation(sort: &str) -> String {
    format!("{RELATION_PREFIX}{sort}")
}

/// The sort whose effectful e-classes `relation` holds, if it is one of ours.
pub fn effectful_relation_sort(relation: &str) -> Option<&str> {
    relation.strip_prefix(RELATION_PREFIX)
}

/// Rewrite `set-effectful` actions and declare their per-sort relations.
pub struct SetEffectful;

impl CommandMacro for SetEffectful {
    fn transform(
        &self,
        mut command: Command,
        _symbol_gen: &mut SymbolGen,
        type_info: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        let mut declarations = Vec::new();
        match &mut command {
            Command::Rule { rule } => {
                for action in &mut rule.head.0 {
                    rewrite_action(action, type_info, &mut declarations)?;
                }
            }
            Command::Action(action) => rewrite_action(action, type_info, &mut declarations)?,
            _ => {}
        }
        declarations.push(command);
        Ok(declarations)
    }
}

fn rewrite_action(
    action: &mut Action,
    type_info: &TypeInfo,
    declarations: &mut Vec<Command>,
) -> Result<(), Error> {
    let Action::Expr(_, Expr::Call(span, name, args)) = action else {
        return Ok(());
    };
    if name != SET_EFFECTFUL {
        return Ok(());
    }
    let [Expr::Var(sort_span, sort), expr] = args.as_slice() else {
        return Err(Error::ParseError(ParseError(
            span.clone(),
            "usage: (set-effectful <Sort> <expr>) where <Sort> is an eq sort".to_string(),
        )));
    };
    match type_info.get_sort_by_name(sort) {
        Some(s) if s.is_eq_sort() => {}
        Some(_) => {
            return Err(Error::ParseError(ParseError(
                sort_span.clone(),
                format!("set-effectful: {sort} is not an eq sort"),
            )));
        }
        None => {
            return Err(Error::ParseError(ParseError(
                sort_span.clone(),
                format!("set-effectful: unknown sort {sort}"),
            )));
        }
    }

    let relation = effectful_relation(sort);
    if type_info.get_func_type(&relation).is_none()
        && !declarations
            .iter()
            .any(|command| matches!(command, Command::Relation { name, .. } if name == &relation))
    {
        declarations.push(Command::Relation {
            span: span.clone(),
            name: relation.clone(),
            inputs: vec![sort.clone()],
        });
    }
    let expr = expr.clone();
    *name = relation;
    *args = vec![expr];
    Ok(())
}
