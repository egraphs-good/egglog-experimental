use egglog::{
    CommandMacro, Error, TypeInfo,
    ast::ResolvedFact,
    ast::{Actions, Command, Expr, ParseError, Rule, Schema},
    util::{FreshGen, IndexSet, SymbolGen},
};
use egglog_ast::generic_ast::{GenericFact, Literal};

/// Implementation of the unstable-fresh! macro for egglog-experimental
pub struct FreshMacro;

impl FreshMacro {
    pub fn new() -> Self {
        Self
    }
}

type Symbol = String;

impl CommandMacro for FreshMacro {
    fn transform(
        &self,
        command: Command,
        symbol_gen: &mut SymbolGen,
        type_info: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        match command {
            Command::Rule { rule } => {
                // Collect fresh sorts - if none found, return the rule unchanged
                let fresh_sorts = collect_fresh_sorts(rule.head.clone())?;
                if fresh_sorts.is_empty() {
                    Ok(vec![Command::Rule { rule }])
                } else {
                    // unstable-fresh! requires TypeInfo for correct type inference
                    desugar_fresh_rule(rule, fresh_sorts, symbol_gen, type_info)
                }
            }
            _ => Ok(vec![command]),
        }
    }
}

// Main desugaring function using proper typechecking
fn desugar_fresh_rule(
    rule: Rule,
    fresh_sorts: Vec<Symbol>,
    symbol_gen: &mut SymbolGen,
    type_info: &TypeInfo,
) -> Result<Vec<Command>, Error> {
    let rule_span = rule.span.clone();

    // Typecheck the query to get resolved facts with type information
    let resolved_facts = type_info.typecheck_facts(symbol_gen, &rule.body)?;

    // Collect all unique variables from the resolved facts with their types
    let query_vars = collect_query_vars(&resolved_facts);

    // Generate unique constructor name
    let constructor_name = symbol_gen.fresh("GeneratedFreshTable").to_string();

    // Build schema for the constructor - use actual types from resolved facts
    let mut schema = Vec::new();

    // Add a column for each query variable with its actual type
    for (_, sort) in &query_vars {
        schema.push(sort.to_string());
    }

    // Add i64 for unique index
    schema.push("i64".to_string());

    // Output sort is the unstable-fresh! sort
    let output_sort = fresh_sorts[0].clone();

    // Create constructor function declaration
    let constructor_command = Command::Constructor {
        span: rule_span.clone(),
        name: constructor_name.clone(),
        schema: Schema {
            input: schema,
            output: output_sort,
        },
        cost: None,
        unextractable: true,
    };

    // Get just the variable names for rewriting
    let query_var_names: Vec<String> = query_vars.iter().map(|(name, _)| name.clone()).collect();

    // Rewrite rule actions to use constructor using visit_exprs
    let mut fresh_index = 0i64;
    let new_actions = rule.head.visit_exprs(&mut |expr| {
        if let Expr::Call(span, head, _args) = &expr {
            if head.as_str() == "unstable-fresh!" {
                let mut new_args: Vec<Expr> = query_var_names
                    .iter()
                    .map(|name| Expr::Var(span.clone(), name.clone()))
                    .collect();
                new_args.push(Expr::Lit(span.clone(), Literal::Int(fresh_index)));
                fresh_index += 1;
                return Expr::Call(span.clone(), constructor_name.clone(), new_args);
            }
        }
        expr
    });

    let new_rule = Rule {
        head: new_actions,
        ..rule
    };

    // Return both the constructor and the rule
    Ok(vec![constructor_command, Command::Rule { rule: new_rule }])
}

// Collect all unique variables from resolved facts with their types
fn collect_query_vars(resolved_facts: &[ResolvedFact]) -> IndexSet<(Symbol, Symbol)> {
    let mut vars = IndexSet::default();

    for fact in resolved_facts {
        match fact {
            GenericFact::Eq(_ann, e1, e2) => {
                collect_vars_from_resolved_expr(e1, &mut vars);
                collect_vars_from_resolved_expr(e2, &mut vars);
            }
            GenericFact::Fact(e) => {
                collect_vars_from_resolved_expr(e, &mut vars);
            }
        }
    }

    vars
}

// Collect variables from a resolved expression using visit_vars
fn collect_vars_from_resolved_expr(
    expr: &egglog::ast::ResolvedExpr,
    vars: &mut IndexSet<(Symbol, Symbol)>,
) {
    expr.visit_vars(&mut |_span, resolved_var| {
        let name = resolved_var.name.to_string();
        let sort = resolved_var.sort.name().to_string();
        vars.insert((name, sort));
    });
}

fn collect_fresh_sorts(actions: Actions) -> Result<Vec<Symbol>, Error> {
    let mut sorts = Vec::new();
    let mut error: Option<Error> = None;

    // Use visit_exprs to traverse all expressions in the actions
    let _ = actions.visit_exprs(&mut |expr| {
        if error.is_some() {
            return expr; // Skip processing if we already have an error
        }

        if let Expr::Call(span, head, args) = &expr {
            if head.as_str() == "unstable-fresh!" {
                if args.len() != 1 {
                    error = Some(Error::ParseError(ParseError(
                        span.clone(),
                        format!(
                            "unstable-fresh! expects exactly 1 argument (the sort name), got {}",
                            args.len()
                        ),
                    )));
                } else if let Expr::Var(_span, sort_name) = &args[0] {
                    sorts.push(sort_name.clone());
                } else {
                    error = Some(Error::ParseError(ParseError(
                        span.clone(),
                        "unstable-fresh! argument must be a sort name".to_string(),
                    )));
                }
            }
        }
        expr
    });

    match error {
        Some(e) => Err(e),
        None => Ok(sorts),
    }
}
