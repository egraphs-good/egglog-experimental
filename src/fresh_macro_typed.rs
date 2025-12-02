use egglog::{
    ast::{Action, Actions, Command, Expr, Rule, Schema},
    util::{FreshGen, SymbolGen},
    CommandMacro, Error, TypeInfo,
};
use egglog_ast::generic_ast::Literal;
use std::collections::HashSet;

// Helper function to collect fresh sorts from actions
fn collect_fresh_sorts(actions: &[Action]) -> Vec<String> {
    let mut sorts = Vec::new();
    for action in actions {
        collect_fresh_sorts_from_action(action, &mut sorts);
    }
    sorts
}

fn collect_fresh_sorts_from_action(action: &Action, sorts: &mut Vec<String>) {
    match action {
        Action::Let(_, expr) => collect_fresh_sorts_from_expr(expr, sorts),
        Action::Set(_, _, expr) => collect_fresh_sorts_from_expr(expr, sorts),
        Action::Delete(_, expr) => collect_fresh_sorts_from_expr(expr, sorts),
        Action::Union(_, e1, e2) => {
            collect_fresh_sorts_from_expr(e1, sorts);
            collect_fresh_sorts_from_expr(e2, sorts);
        }
        Action::Extract(_, e1, e2) => {
            collect_fresh_sorts_from_expr(e1, sorts);
            collect_fresh_sorts_from_expr(e2, sorts);
        }
        Action::Panic(_) => {}
        Action::Expr(expr) => collect_fresh_sorts_from_expr(expr, sorts),
    }
}

fn collect_fresh_sorts_from_expr(expr: &Expr, sorts: &mut Vec<String>) {
    match expr {
        Expr::Call(_, head, args) => {
            if head == "fresh!" && args.len() == 1 {
                if let Expr::Var(_, sort) = &args[0] {
                    sorts.push(sort.clone());
                }
            }
            for arg in args {
                collect_fresh_sorts_from_expr(arg, sorts);
            }
        }
        _ => {}
    }
}

// Convert resolved expression to surface expression
fn resolved_to_surface(expr: &egglog::ResolvedExpr) -> Expr {
    expr.to_surface()
}

// Collect query columns from resolved facts
fn collect_query_columns(
    resolved_facts: &[egglog::ResolvedFact],
) -> Vec<(Expr, String)> {
    let mut columns = Vec::new();
    let mut seen = HashSet::new();
    
    for fact in resolved_facts {
        collect_columns_from_fact(fact, &mut columns, &mut seen);
    }
    
    columns
}

fn collect_columns_from_fact(
    fact: &egglog::ResolvedFact,
    columns: &mut Vec<(Expr, String)>,
    seen: &mut HashSet<String>,
) {
    match fact {
        egglog::ResolvedFact::Eq(_, e1, e2) => {
            collect_columns_from_expr(e1, columns, seen);
            collect_columns_from_expr(e2, columns, seen);
        }
        egglog::ResolvedFact::Fact(expr) => {
            collect_columns_from_expr(expr, columns, seen);
        }
    }
}

fn collect_columns_from_expr(
    expr: &egglog::ResolvedExpr,
    columns: &mut Vec<(Expr, String)>,
    seen: &mut HashSet<String>,
) {
    // Convert to surface expression for uniqueness checking
    let surface = resolved_to_surface(expr);
    let surface_str = surface.to_string();
    
    if !seen.contains(&surface_str) {
        seen.insert(surface_str);
        let sort_name = expr.output_type().name().to_string();
        columns.push((surface, sort_name));
    }
    
    // Recursively collect from subexpressions
    match expr {
        egglog::ResolvedExpr::Call(_, _, _, args) => {
            for arg in args {
                collect_columns_from_expr(arg, columns, seen);
            }
        }
        _ => {}
    }
}

// Rewrite fresh! calls in actions
fn rewrite_fresh_action(
    action: &Action,
    constructor_name: &str,
    column_exprs: &[Expr],
    fresh_index: &mut i64,
) -> Action {
    match action {
        Action::Let(span, expr) => {
            Action::Let(span.clone(), rewrite_fresh_expr(expr, constructor_name, column_exprs, fresh_index))
        }
        Action::Set(span, head, expr) => {
            Action::Set(
                span.clone(),
                head.clone(),
                rewrite_fresh_expr(expr, constructor_name, column_exprs, fresh_index),
            )
        }
        Action::Delete(span, expr) => {
            Action::Delete(
                span.clone(),
                rewrite_fresh_expr(expr, constructor_name, column_exprs, fresh_index),
            )
        }
        Action::Union(span, e1, e2) => Action::Union(
            span.clone(),
            rewrite_fresh_expr(e1, constructor_name, column_exprs, fresh_index),
            rewrite_fresh_expr(e2, constructor_name, column_exprs, fresh_index),
        ),
        Action::Extract(span, e1, e2) => Action::Extract(
            span.clone(),
            rewrite_fresh_expr(e1, constructor_name, column_exprs, fresh_index),
            rewrite_fresh_expr(e2, constructor_name, column_exprs, fresh_index),
        ),
        Action::Panic(s) => Action::Panic(s.clone()),
        Action::Expr(expr) => {
            Action::Expr(rewrite_fresh_expr(expr, constructor_name, column_exprs, fresh_index))
        }
    }
}

fn rewrite_fresh_expr(
    expr: &Expr,
    constructor_name: &str,
    column_exprs: &[Expr],
    fresh_index: &mut i64,
) -> Expr {
    match expr {
        Expr::Call(span, head, args) => {
            if head == "fresh!" && args.len() == 1 {
                // Replace fresh! with constructor call
                let mut constructor_args = column_exprs.to_vec();
                constructor_args.push(Expr::Lit(span.clone(), Literal::Int(*fresh_index)));
                *fresh_index += 1;
                Expr::Call(span.clone(), constructor_name.to_string(), constructor_args)
            } else {
                // Recursively rewrite arguments
                let new_args = args
                    .iter()
                    .map(|arg| rewrite_fresh_expr(arg, constructor_name, column_exprs, fresh_index))
                    .collect();
                Expr::Call(span.clone(), head.clone(), new_args)
            }
        }
        Expr::Var(span, v) => Expr::Var(span.clone(), v.clone()),
        Expr::Lit(span, l) => Expr::Lit(span.clone(), l.clone()),
    }
}

// Main desugaring function with proper typechecking
pub fn desugar_fresh_rule(
    rule: Rule,
    symbol_gen: &mut SymbolGen,
    type_info: &TypeInfo,
) -> Result<Vec<Command>, Error> {
    // Collect fresh! sorts from actions
    let fresh_sorts = collect_fresh_sorts(&rule.head.0);
    if fresh_sorts.is_empty() {
        return Ok(vec![Command::Rule { rule }]);
    }

    let rule_span = rule.span.clone();
    // Generate unique constructor name
    let constructor_name = symbol_gen.fresh("GeneratedFreshTable").to_string();

    // Typecheck the query to get correct types for all subexpressions
    let resolved_facts = type_info
        .typecheck_facts(symbol_gen, &rule.body)
        .map_err(Error::TypeError)?;

    // Collect column information with proper types
    let column_info = collect_query_columns(&resolved_facts);
    let column_exprs: Vec<Expr> = column_info.iter().map(|(expr, _)| expr.clone()).collect();
    let mut constructor_inputs: Vec<String> = column_info
        .iter()
        .map(|(_, sort)| sort.clone())
        .collect();
    constructor_inputs.push("i64".to_string());

    // Output sort is the fresh! sort
    let output_sort = fresh_sorts[0].clone();

    // Create constructor function declaration
    let constructor_command = Command::Constructor {
        span: rule_span.clone(),
        name: constructor_name.clone(),
        schema: Schema {
            input: constructor_inputs,
            output: output_sort,
        },
        cost: None,
        unextractable: true,
    };

    // Rewrite rule actions to use constructor
    let mut fresh_index = 0i64;
    let new_actions_vec: Vec<Action> = rule
        .head
        .0
        .iter()
        .map(|action| {
            rewrite_fresh_action(
                action,
                &constructor_name,
                &column_exprs,
                &mut fresh_index,
            )
        })
        .collect();
    let new_actions = Actions(new_actions_vec);

    let new_rule = Rule {
        span: rule.span,
        name: rule.name,
        ruleset: rule.ruleset,
        body: rule.body,
        head: new_actions,
    };

    Ok(vec![constructor_command, Command::Rule { rule: new_rule }])
}
