use egglog::{
    CommandMacro, Error, ResolvedCall, TypeInfo,
    ast::{Action, Actions, Command, Expr, Rule, Schema},
    ast::{ResolvedExpr, ResolvedFact},
    util::{FreshGen, IndexSet, SymbolGen},
};
use egglog_ast::generic_ast::{GenericExpr, GenericFact, Literal};

/// Implementation of the fresh! macro for egglog-experimental
pub struct FreshMacro;

impl FreshMacro {
    pub fn new() -> Self {
        Self
    }
}

type Symbol = String;

impl CommandMacro for FreshMacro {
    fn matches(&self, command: &Command) -> bool {
        if let Command::Rule { rule } = command {
            rule.head.0.iter().any(contains_fresh_action)
        } else {
            false
        }
    }

    fn transform(
        &self,
        command: Command,
        symbol_gen: &mut SymbolGen,
        type_info: Option<&TypeInfo>,
    ) -> Result<Vec<Command>, Error> {
        match command {
            Command::Rule { rule } => {
                // Fresh! requires TypeInfo for correct type inference
                if let Some(type_info) = type_info {
                    desugar_fresh_rule(rule, symbol_gen, type_info)
                } else {
                    Err(Error::ParseError(egglog::ast::ParseError(
                        rule.span.clone(),
                        "fresh! macro requires TypeInfo to be available".to_string(),
                    )))
                }
            }
            _ => Ok(vec![command]),
        }
    }
}

// Main desugaring function using proper typechecking
fn desugar_fresh_rule(
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

    // Typecheck the query to get resolved facts with type information
    let resolved_facts = type_info.typecheck_facts(symbol_gen, &rule.body)?;

    // Collect all unique columns from the resolved facts with their types
    let query_columns = collect_query_columns(&resolved_facts);

    // Generate unique constructor name
    let constructor_name = symbol_gen.fresh("GeneratedFreshTable").to_string();

    // Build schema for the constructor - use actual types from resolved facts
    let mut schema = Vec::new();

    // Add a column for each query subexpression with its actual type
    for (_, sort) in &query_columns {
        schema.push(sort.to_string());
    }

    // Add i64 for unique index
    schema.push("i64".to_string());

    // Output sort is the fresh! sort
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

    // Convert columns back to surface Exprs for rewriting
    let query_exprs: Vec<Expr> = query_columns.iter().map(|(e, _)| e.clone()).collect();

    // Rewrite rule actions to use constructor
    let mut fresh_index = 0i64;
    let new_actions_vec: Vec<Action> = rule
        .head
        .0
        .iter()
        .map(|action| {
            rewrite_fresh_action(
                action.clone(),
                &constructor_name,
                &query_exprs,
                &mut fresh_index,
            )
        })
        .collect();

    let new_actions = Actions::new(new_actions_vec);

    let new_rule = Rule {
        head: new_actions,
        ..rule
    };

    // Return both the constructor and the rule
    Ok(vec![constructor_command, Command::Rule { rule: new_rule }])
}

// Collect all unique subexpressions from resolved facts with their types
fn collect_query_columns(resolved_facts: &Vec<ResolvedFact>) -> IndexSet<(Expr, Symbol)> {
    let mut columns = IndexSet::default();

    for fact in resolved_facts {
        match fact {
            GenericFact::Eq(_ann, e1, e2) => {
                collect_resolved_columns(e1, &mut columns);
                collect_resolved_columns(e2, &mut columns);
            }
            GenericFact::Fact(e) => {
                collect_resolved_columns(e, &mut columns);
            }
        }
    }

    columns
}

// Recursively collect columns from resolved expressions
fn collect_resolved_columns(expr: &ResolvedExpr, columns: &mut IndexSet<(Expr, Symbol)>) {
    // Get the output type of this expression from the call
    let sort = match expr {
        GenericExpr::Call(_, call, _) => call.output().name().to_string(),
        GenericExpr::Var(_, v) => v.sort.name().to_string(),
        GenericExpr::Lit(_, lit) => {
            // Infer type from literal
            match lit {
                Literal::Int(_) => "i64".to_string(),
                Literal::Float(_) => "f64".to_string(),
                Literal::Bool(_) => "bool".to_string(),
                Literal::String(_) => "String".to_string(),
                Literal::Unit => "Unit".to_string(),
            }
        }
    };

    // Convert resolved expr to surface expr
    let surface_expr = resolved_to_surface(expr);

    // Add to columns if not already present
    columns.insert((surface_expr, sort));

    // Recurse into subexpressions
    if let GenericExpr::Call(_, _, args) = expr {
        for arg in args {
            collect_resolved_columns(arg, columns);
        }
    }
}

// Convert ResolvedExpr to surface Expr
fn resolved_to_surface(expr: &ResolvedExpr) -> Expr {
    match expr {
        GenericExpr::Var(ann, v) => Expr::Var(ann.clone(), v.name.to_string()),
        GenericExpr::Lit(ann, l) => Expr::Lit(ann.clone(), l.clone()),
        GenericExpr::Call(ann, call, args) => {
            let head = match call {
                ResolvedCall::Func(func) => func.name.to_string(),
                ResolvedCall::Primitive(_prim) => "primitive".to_string(),
            };
            let surface_args = args.iter().map(resolved_to_surface).collect();
            Expr::Call(ann.clone(), head, surface_args)
        }
    }
}

fn contains_fresh_action(action: &Action) -> bool {
    match action {
        Action::Let(_, _, expr) => contains_fresh_expr(expr),
        Action::Set(_, _, _, expr) => contains_fresh_expr(expr),
        Action::Union(_, e1, e2) => contains_fresh_expr(e1) || contains_fresh_expr(e2),
        Action::Expr(_, expr) => contains_fresh_expr(expr),
        _ => false,
    }
}

fn contains_fresh_expr(expr: &Expr) -> bool {
    match expr {
        Expr::Call(_span, head, _args) if head.as_str() == "unstable-fresh!" => true,
        Expr::Call(_, _, args) => args.iter().any(contains_fresh_expr),
        _ => false,
    }
}

fn collect_fresh_sorts(actions: &[Action]) -> Vec<Symbol> {
    let mut sorts = Vec::new();
    for action in actions {
        collect_fresh_from_action(action, &mut sorts);
    }
    sorts
}

fn collect_fresh_from_action(action: &Action, sorts: &mut Vec<Symbol>) {
    match action {
        Action::Let(_, _, expr) => collect_fresh_from_expr(expr, sorts),
        Action::Set(_, _, _, expr) => collect_fresh_from_expr(expr, sorts),
        Action::Union(_, e1, e2) => {
            collect_fresh_from_expr(e1, sorts);
            collect_fresh_from_expr(e2, sorts);
        }
        Action::Expr(_, expr) => collect_fresh_from_expr(expr, sorts),
        _ => {}
    }
}

fn collect_fresh_from_expr(expr: &Expr, sorts: &mut Vec<Symbol>) {
    match expr {
        Expr::Call(_span, head, args) if head.as_str() == "unstable-fresh!" => {
            if args.len() == 1 {
                if let Expr::Var(_span, sort_name) = &args[0] {
                    sorts.push(sort_name.clone());
                }
            }
        }
        Expr::Call(_, _, args) => {
            for arg in args {
                collect_fresh_from_expr(arg, sorts);
            }
        }
        _ => {}
    }
}

fn rewrite_fresh_action(
    action: Action,
    constructor_name: &Symbol,
    query_exprs: &[Expr],
    fresh_index: &mut i64,
) -> Action {
    match action {
        Action::Let(span, var, expr) => Action::Let(
            span,
            var,
            rewrite_fresh_expr(expr, constructor_name, query_exprs, fresh_index),
        ),
        Action::Set(span, name, args, expr) => Action::Set(
            span,
            name,
            args,
            rewrite_fresh_expr(expr, constructor_name, query_exprs, fresh_index),
        ),
        Action::Union(span, e1, e2) => Action::Union(
            span,
            rewrite_fresh_expr(e1, constructor_name, query_exprs, fresh_index),
            rewrite_fresh_expr(e2, constructor_name, query_exprs, fresh_index),
        ),
        Action::Expr(span, expr) => Action::Expr(
            span,
            rewrite_fresh_expr(expr, constructor_name, query_exprs, fresh_index),
        ),
        other => other,
    }
}

fn rewrite_fresh_expr(
    expr: Expr,
    constructor_name: &Symbol,
    query_exprs: &[Expr],
    fresh_index: &mut i64,
) -> Expr {
    match expr {
        Expr::Call(span, head, _args) if head.as_str() == "unstable-fresh!" => {
            let mut new_args = query_exprs.to_vec();
            new_args.push(Expr::Lit(span.clone(), Literal::Int(*fresh_index)));
            *fresh_index += 1;
            Expr::Call(span, constructor_name.clone(), new_args)
        }
        Expr::Call(span, head, args) => {
            let new_args = args
                .into_iter()
                .map(|arg| rewrite_fresh_expr(arg, constructor_name, query_exprs, fresh_index))
                .collect();
            Expr::Call(span, head, new_args)
        }
        _ => expr,
    }
}
