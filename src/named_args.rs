//! Named arguments for constructors, functions, relations, and datatypes.
//!
//! This module lets declarations name their fields:
//!
//! ```text
//! (constructor MyCar (:color Color :numwheel i64) Vehicle)
//! (function foo (:a i64 :b i64) i64 :no-merge)
//! (relation edge (:from Node :to Node))
//! (datatype Vehicle (MyCar :color Color :numwheel i64))
//! ```
//!
//! Once a name is declared with named fields, call sites may pass arguments by
//! name in any order, mix leading positional arguments with trailing named
//! ones, and use a trailing `...` to bind every unspecified field to a fresh
//! variable:
//!
//! ```text
//! (rule ((MyCar :color c ...))        ((Use c)))   ; :numwheel bound to a fresh var
//! (rule ((MyCar c ...))               ((Use c)))   ; c is :color, :numwheel fresh
//! (rule ((MyCar :numwheel w :color c)) ((Use c)))  ; any order
//! ```
//!
//! # Implementation strategy
//!
//! Everything happens in one [`CommandMacro`]. `:name` and `...` already parse
//! as ordinary variables, and a declaration's `:name Sort` pairs already parse
//! as a longer sort list, so no parse-time macro is needed: a declaration
//! command arrives with its field names still in the sort list, and a named
//! call arrives as an ordinary [`Expr::Call`] whose arguments include
//! `Expr::Var(":color")` and `Expr::Var("...")`.
//!
//! Running as a command macro rather than at parse time is what makes scoping
//! correct. egglog parses a whole program before running any of it, so a
//! parse-time macro sees declarations in *source* order; command macros run in
//! *execution* order, after every preceding command has taken effect. That is
//! what lets a call see declarations from a file that an earlier `(include ...)`
//! pulled in, and what lets `(push)`/`(pop)` and redeclaration work: field names
//! are recorded per `(name, arity)`, and each call site resolves against the
//! arity the e-graph currently has for that name.
//!
//! The recorded names outlive a `(pop)`, since the registry is not itself
//! scoped, but they can never be *applied* out of scope: a stale entry is only
//! reachable through an arity that the live type information still reports.

use egglog::ast::{
    Action, Command, Expr, GenericActions as Actions, ParseError, Span, Subdatatypes, Variant,
};
use egglog::util::{FreshGen, SymbolGen};
use egglog::{CommandMacro, EGraph, Error, TypeInfo};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

/// Add named-argument support to an e-graph.
///
/// Each call installs a registry of its own, so separate e-graphs never share
/// field names.
pub fn register_named_args(egraph: &mut EGraph) {
    egraph
        .command_macros_mut()
        .register(Arc::new(NamedArgs::default()));
}

/// Field names of every declaration seen so far.
#[derive(Default)]
struct Declarations {
    /// Field names per `(name, arity)`. A positional declaration records
    /// `None`, so redeclaring a name at the same arity stops the old field
    /// names from being applied.
    by_arity: HashMap<(String, usize), Option<Vec<String>>>,
    /// The arity of the most recent declaration of each name. Only used when
    /// the type information does not know the name, which is the case in
    /// desugaring mode, where declarations are not run.
    latest_arity: HashMap<String, usize>,
}

/// The command macro implementing named arguments.
#[derive(Default)]
struct NamedArgs {
    declarations: Mutex<Declarations>,
}

impl CommandMacro for NamedArgs {
    fn transform(
        &self,
        command: Command,
        symbol_gen: &mut SymbolGen,
        type_info: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        let command = self.declare(command)?;
        Ok(vec![self.expand_calls(command, symbol_gen, type_info)?])
    }
}

impl NamedArgs {
    /// Record the field names of a declaration and strip them from its sort
    /// list, leaving an ordinary positional declaration.
    fn declare(&self, command: Command) -> Result<Command, Error> {
        Ok(match command {
            Command::Constructor {
                span,
                name,
                mut schema,
                cost,
                unextractable,
                hidden,
                let_binding,
                term_constructor,
            } => {
                let (names, input) = split_fields(&schema.input, &span)?;
                self.record(&name, names, input.len());
                schema.input = input;
                Command::Constructor {
                    span,
                    name,
                    schema,
                    cost,
                    unextractable,
                    hidden,
                    let_binding,
                    term_constructor,
                }
            }
            Command::Function {
                span,
                name,
                mut schema,
                merge,
                hidden,
                let_binding,
                term_constructor,
                unextractable,
            } => {
                let (names, input) = split_fields(&schema.input, &span)?;
                self.record(&name, names, input.len());
                schema.input = input;
                Command::Function {
                    span,
                    name,
                    schema,
                    merge,
                    hidden,
                    let_binding,
                    term_constructor,
                    unextractable,
                }
            }
            Command::Relation { span, name, inputs } => {
                let (names, inputs) = split_fields(&inputs, &span)?;
                self.record(&name, names, inputs.len());
                Command::Relation { span, name, inputs }
            }
            Command::Datatype {
                span,
                name,
                variants,
            } => Command::Datatype {
                span,
                name,
                variants: self.declare_variants(variants)?,
            },
            Command::Datatypes { span, datatypes } => {
                let mut declared = Vec::with_capacity(datatypes.len());
                for (sub_span, name, subdatatypes) in datatypes {
                    let subdatatypes = match subdatatypes {
                        Subdatatypes::Variants(variants) => {
                            Subdatatypes::Variants(self.declare_variants(variants)?)
                        }
                        new_sort => new_sort,
                    };
                    declared.push((sub_span, name, subdatatypes));
                }
                Command::Datatypes {
                    span,
                    datatypes: declared,
                }
            }
            other => other,
        })
    }

    fn declare_variants(&self, variants: Vec<Variant>) -> Result<Vec<Variant>, Error> {
        variants
            .into_iter()
            .map(|mut variant| {
                let (names, types) = split_fields(&variant.types, &variant.span)?;
                self.record(&variant.name, names, types.len());
                variant.types = types;
                Ok(variant)
            })
            .collect()
    }

    fn record(&self, name: &str, names: Option<Vec<String>>, arity: usize) {
        let mut declarations = self.declarations.lock().unwrap();
        declarations
            .by_arity
            .insert((name.to_string(), arity), names);
        declarations.latest_arity.insert(name.to_string(), arity);
    }

    /// Rewrite every named call in `command` into a positional one.
    fn expand_calls(
        &self,
        command: Command,
        symbol_gen: &mut SymbolGen,
        type_info: &TypeInfo,
    ) -> Result<Command, Error> {
        // `set`, `delete`, and `subsume` keep the table name beside its
        // arguments instead of as a call, so `visit_exprs` never offers them as
        // one. Rebuild them into a call, expand that, and take it apart again.
        let command = self.expand_table_actions(command, symbol_gen, type_info)?;

        let mut failure = None;
        let expanded = command.visit_exprs(&mut |expr| match self
            .expand_call(&expr, symbol_gen, type_info)
        {
            Ok(Some(expanded)) => expanded,
            Ok(None) => expr,
            Err(error) => {
                failure.get_or_insert(error);
                expr
            }
        });
        match failure {
            Some(error) => Err(Error::ParseError(error)),
            None => Ok(expanded),
        }
    }

    fn expand_table_actions(
        &self,
        command: Command,
        symbol_gen: &mut SymbolGen,
        type_info: &TypeInfo,
    ) -> Result<Command, Error> {
        Ok(match command {
            Command::Action(action) => {
                Command::Action(self.expand_table_action(action, symbol_gen, type_info)?)
            }
            Command::Rule { mut rule } => {
                rule.head = Actions(
                    rule.head
                        .0
                        .into_iter()
                        .map(|action| self.expand_table_action(action, symbol_gen, type_info))
                        .collect::<Result<_, _>>()?,
                );
                Command::Rule { rule }
            }
            Command::Fail(span, command) => Command::Fail(
                span,
                Box::new(self.expand_table_actions(*command, symbol_gen, type_info)?),
            ),
            other => other,
        })
    }

    fn expand_table_action(
        &self,
        action: Action,
        symbol_gen: &mut SymbolGen,
        type_info: &TypeInfo,
    ) -> Result<Action, Error> {
        Ok(match action {
            Action::Set(span, table, args, value) => {
                let args = self.expand_table_args(&span, &table, args, symbol_gen, type_info)?;
                Action::Set(span, table, args, value)
            }
            Action::Change(span, change, table, args) => {
                let args = self.expand_table_args(&span, &table, args, symbol_gen, type_info)?;
                Action::Change(span, change, table, args)
            }
            other => other,
        })
    }

    fn expand_table_args(
        &self,
        span: &Span,
        table: &str,
        args: Vec<Expr>,
        symbol_gen: &mut SymbolGen,
        type_info: &TypeInfo,
    ) -> Result<Vec<Expr>, Error> {
        let call = Expr::Call(span.clone(), table.to_string(), args);
        match self.expand_call(&call, symbol_gen, type_info) {
            Ok(Some(Expr::Call(_, _, expanded))) => Ok(expanded),
            Ok(_) => match call {
                Expr::Call(_, _, args) => Ok(args),
                _ => unreachable!("built as a call just above"),
            },
            Err(error) => Err(Error::ParseError(error)),
        }
    }

    /// Rewrite one call, or return `None` to leave it alone.
    fn expand_call(
        &self,
        expr: &Expr,
        symbol_gen: &mut SymbolGen,
        type_info: &TypeInfo,
    ) -> Result<Option<Expr>, ParseError> {
        let Expr::Call(span, name, args) = expr else {
            return Ok(None);
        };

        // Resolve against the arity the e-graph currently has for this name, so
        // a declaration that has been popped or replaced cannot be applied.
        let declarations = self.declarations.lock().unwrap();
        let arity = type_info
            .get_func_type(name)
            .map(|func| func.input.len())
            .or_else(|| declarations.latest_arity.get(name).copied());
        let Some(arity) = arity else {
            // Nothing is declared under this name; let type checking report it.
            return Ok(None);
        };
        let field_names = match declarations.by_arity.get(&(name.clone(), arity)) {
            Some(Some(field_names)) => field_names.clone(),
            Some(None) | None => {
                drop(declarations);
                // Declared without field names. Marker syntax cannot work here,
                // and reporting that beats leaving `:color` to fail later as an
                // unbound symbol.
                return match args.iter().find_map(marker) {
                    Some(found) => error(
                        span.clone(),
                        &format!(
                            "`{name}` was not declared with named fields, so `{found}` cannot be used here"
                        ),
                    ),
                    None => Ok(None),
                };
            }
        };
        drop(declarations);

        if !args.iter().any(|arg| marker(arg).is_some()) && args.len() == arity {
            // An ordinary positional call, which needs no rewriting.
            return Ok(None);
        }

        let mut slots: Vec<Option<Expr>> = vec![None; arity];
        let mut has_ellipsis = false;
        let mut seen_named = false;
        let mut next_positional = 0;

        let mut i = 0;
        while i < args.len() {
            if has_ellipsis {
                return error(args[i].span(), "`...` must be the last argument");
            }
            match marker(&args[i]) {
                Some("...") => {
                    has_ellipsis = true;
                    i += 1;
                }
                Some(key) => {
                    seen_named = true;
                    let key = &key[1..];
                    let position = field_names.iter().position(|field| field == key);
                    let Some(position) = position else {
                        return error(
                            args[i].span(),
                            &format!("`{name}` has no argument named `{key}`"),
                        );
                    };
                    if slots[position].is_some() {
                        return error(
                            args[i].span(),
                            &format!("argument `{key}` of `{name}` specified more than once"),
                        );
                    }
                    i += 1;
                    let Some(value) = args.get(i) else {
                        return error(args[i - 1].span(), &format!("`:{key}` requires a value"));
                    };
                    if let Some(found) = marker(value) {
                        return error(
                            value.span(),
                            &format!("expected a value for `:{key}` but found `{found}`"),
                        );
                    }
                    slots[position] = Some(value.clone());
                    i += 1;
                }
                None => {
                    if seen_named {
                        return error(
                            args[i].span(),
                            "positional arguments must come before named arguments",
                        );
                    }
                    if next_positional >= arity {
                        return error(
                            args[i].span(),
                            &format!("`{name}` takes {arity} argument(s) but was given more"),
                        );
                    }
                    slots[next_positional] = Some(args[i].clone());
                    next_positional += 1;
                    i += 1;
                }
            }
        }

        let mut expanded = Vec::with_capacity(arity);
        let mut missing = Vec::new();
        for (index, slot) in slots.into_iter().enumerate() {
            match slot {
                Some(arg) => expanded.push(arg),
                // A fixed hint keeps these names unique among themselves; a
                // field-name hint could collide with another field's name.
                None if has_ellipsis => {
                    expanded.push(Expr::Var(span.clone(), symbol_gen.fresh("_")))
                }
                None => missing.push(field_names[index].clone()),
            }
        }

        if !missing.is_empty() {
            return error(
                span.clone(),
                &format!(
                    "`{name}` is missing argument(s): {} (add `...` to bind the rest to fresh variables)",
                    missing.join(", ")
                ),
            );
        }

        Ok(Some(Expr::Call(span.clone(), name.clone(), expanded)))
    }
}

/// The `...` ellipsis and `:name` keywords parse as variables, but can never be
/// a plain argument value.
fn marker(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::Var(_, name) if name == "..." || name.starts_with(':') => Some(name),
        _ => None,
    }
}

/// Split a declaration's sort list into field names and sorts. Returns
/// `Some(names)` when the declaration is named (`(:a T :b U)`), or `None` when
/// it is positional (`(T U)`). A declaration must name either all fields or
/// none, which is what makes the two forms distinguishable.
fn split_fields(
    items: &[String],
    span: &Span,
) -> Result<(Option<Vec<String>>, Vec<String>), Error> {
    let bad = |message: String| Err(Error::ParseError(ParseError(span.clone(), message)));
    if !items.first().is_some_and(|item| item.starts_with(':')) {
        for item in items {
            if item.starts_with(':') {
                return bad(format!(
                    "unexpected named argument `{item}`; name either all fields or none"
                ));
            }
        }
        return Ok((None, items.to_vec()));
    }

    let mut names = Vec::new();
    let mut sorts = Vec::new();
    let mut i = 0;
    while i < items.len() {
        let key = &items[i];
        if !key.starts_with(':') {
            return bad(format!(
                "expected `:name` but found `{key}`; name either all fields or none"
            ));
        }
        let name = key[1..].to_string();
        i += 1;
        let Some(sort) = items.get(i) else {
            return bad(format!("argument `{name}` is missing its sort"));
        };
        if sort.starts_with(':') {
            return bad(format!("expected a sort for `{name}` but found `{sort}`"));
        }
        if names.contains(&name) {
            return bad(format!("duplicate argument name `{name}`"));
        }
        names.push(name);
        sorts.push(sort.clone());
        i += 1;
    }
    Ok((Some(names), sorts))
}

fn error<T>(span: Span, message: &str) -> Result<T, ParseError> {
    Err(ParseError(span, message.to_string()))
}
