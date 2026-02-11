use egglog::{
    CommandMacro, Error, TypeInfo,
    ast::ResolvedFact,
    ast::{Action, Actions, Command, Expr, Rule, Schema},
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
            Command::Rule { rule } if rule.head.0.iter().any(contains_fresh_action) => {
                // unstable-fresh! requires TypeInfo for correct type inference
                desugar_fresh_rule(rule, symbol_gen, type_info)
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
    // Collect unstable-fresh! sorts from actions
    let fresh_sorts = collect_fresh_sorts(&rule.head.0);
    if fresh_sorts.is_empty() {
        return Ok(vec![Command::Rule { rule }]);
    }

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
                &query_var_names,
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
    query_var_names: &[String],
    fresh_index: &mut i64,
) -> Action {
    match action {
        Action::Let(span, var, expr) => Action::Let(
            span,
            var,
            rewrite_fresh_expr(expr, constructor_name, query_var_names, fresh_index),
        ),
        Action::Set(span, name, args, expr) => Action::Set(
            span,
            name,
            args,
            rewrite_fresh_expr(expr, constructor_name, query_var_names, fresh_index),
        ),
        Action::Union(span, e1, e2) => Action::Union(
            span,
            rewrite_fresh_expr(e1, constructor_name, query_var_names, fresh_index),
            rewrite_fresh_expr(e2, constructor_name, query_var_names, fresh_index),
        ),
        Action::Expr(span, expr) => Action::Expr(
            span,
            rewrite_fresh_expr(expr, constructor_name, query_var_names, fresh_index),
        ),
        other => other,
    }
}

fn rewrite_fresh_expr(
    expr: Expr,
    constructor_name: &Symbol,
    query_var_names: &[String],
    fresh_index: &mut i64,
) -> Expr {
    match expr {
        Expr::Call(span, head, _args) if head.as_str() == "unstable-fresh!" => {
            let mut new_args: Vec<Expr> = query_var_names
                .iter()
                .map(|name| Expr::Var(span.clone(), name.clone()))
                .collect();
            new_args.push(Expr::Lit(span.clone(), Literal::Int(*fresh_index)));
            *fresh_index += 1;
            Expr::Call(span, constructor_name.clone(), new_args)
        }
        Expr::Call(span, head, args) => {
            let new_args = args
                .into_iter()
                .map(|arg| rewrite_fresh_expr(arg, constructor_name, query_var_names, fresh_index))
                .collect();
            Expr::Call(span, head, new_args)
        }
        _ => expr,
    }
}
