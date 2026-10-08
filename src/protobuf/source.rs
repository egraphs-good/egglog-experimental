//! Sequential, typechecking-only source producer for the initial protobuf slice.
//!
//! Submit each yielded program through the byte adapter before requesting the
//! next one, and stop on a transport or decoded execution error. Parsing is eager
//! (like native source execution); resolution is sequential so a later type error
//! does not erase an executed prefix. Native syntax is never executed here.
//! Rulesets are fixed after their first run. Relations, uncatalogued primitives, local lets,
//! proof modes, dynamic costs and general schedules remain unsupported.

use super::*;
use ast::{GenericAction as ResolvedAction, GenericNCommand as N, ResolvedExpr, ResolvedFact};
use egglog::ResolvedCall;
use std::collections::VecDeque;

/// A source stream whose authored declarations, expressions and rules become
/// protobuf records. The native graph holds only the producer's type environment.
pub struct Source {
    graph: EGraph,
    commands: VecDeque<Command>,
    program: pb::Program,
    rulesets: HashMap<String, usize>,
    installed: HashSet<String>,
    local_prefix: String,
}

impl Source {
    /// Parses source without executing it. Each iterator item is one ordered
    /// submission phase; callers must stop after a failed decoded response.
    pub fn new(filename: Option<String>, source: &str) -> Result<Self, TransportError> {
        let mut graph = crate::new_experimental_egraph();
        let commands: VecDeque<_> = graph
            .parse_program(filename, source)
            .map_err(|error| TransportError(error.to_string()))?
            .into();
        // Rules are revalidated when their fixed theory is published. A local
        // source name may legally become a function name in the meantime. Pick
        // a namespace disjoint from parsed declarations and variable bindings,
        // not from a raw-source substring test (strings are not identifiers).
        let mut local_prefix = "__proto_source_local_".to_string();
        for command in &commands {
            let mut avoid = |name: String| {
                while name.starts_with(&local_prefix) {
                    local_prefix.push('_');
                }
                name
            };
            command
                .clone()
                .map_string_symbols(&mut avoid)
                .map_symbols(&mut |head| head, &mut avoid);
        }
        Ok(Self {
            graph,
            commands,
            program: pb::Program {
                ir_version: 1,
                rulesets: vec![pb::Ruleset {
                    name: Some(String::new()),
                    kind: Some(pb::ruleset::Kind::Rules(pb::RuleList::default())),
                    ..Default::default()
                }],
                ..Default::default()
            },
            rulesets: HashMap::from([(String::new(), 0)]),
            installed: HashSet::new(),
            local_prefix,
        })
    }

    fn compile(&mut self, command: Command) -> Result<pb::Program, String> {
        let macros = self.graph.command_macros().clone();
        let types = self.graph.type_info().clone();
        let expanded = macros
            .apply(command, &mut self.graph.parser.symbol_gen, &types)
            .map_err(|error| error.to_string())?;
        if expanded.len() != 1 {
            return Err(
                "multi-command source macros require separate ordered submission phases".into(),
            );
        }
        let mut publish = vec![];
        for command in expanded {
            // Keep provenance until export: desugaring alone cannot distinguish
            // a relation's generated constructor or an authored rewrite.
            let rewrite = match &command {
                Command::Rewrite(_, _, subsume) => Some(*subsume),
                Command::Relation { .. } => {
                    return Err("source relations require relation-identity lowering".into());
                }
                Command::Include(..) => {
                    return Err("source includes require ordered producer expansion".into());
                }
                Command::BiRewrite(..) => {
                    return Err("source bidirectional rewrites are not supported yet".into());
                }
                _ => None,
            };
            let command = match command {
                // The experimental parser deliberately shadows core extract.
                // With no cost-mutating commands in this slice its default tree
                // model agrees with static constructor costs. Do not execute the
                // UserDefined command to discover/resolve its arguments.
                Command::UserDefined(span, name, args) if name == "extract" => {
                    let (expr, variants) = match args.as_slice() {
                        [expr] => (expr.clone(), Expr::Lit(span.clone(), Literal::Int(0))),
                        [expr, variants] => (expr.clone(), variants.clone()),
                        _ => {
                            return Err(
                                "source extract supports only a root and literal variant count"
                                    .into(),
                            );
                        }
                    };
                    Command::Extract(span, expr, variants)
                }
                Command::UserDefined(_, name, _) => {
                    return Err(format!(
                        "source extension {name} requires structured declaration/command preparation"
                    ));
                }
                command => command,
            };
            let resolved = self
                .graph
                .resolve_command_preserving_globals(command)
                .map_err(|error| error.to_string())?;
            if rewrite.is_some() && resolved.len() != 1 {
                return Err("native rewrite desugaring changed: expected one resolved rule".into());
            }
            for command in resolved {
                match command {
                    N::Sort {
                        name,
                        presort_and_args: Some(_),
                        uf: None,
                        proof_func: None,
                        container_rebuild: None,
                        proof_constructors: None,
                        unionable: true,
                        ..
                    } => {
                        self.sort(&name)?;
                    }
                    N::Sort {
                        span,
                        name,
                        presort_and_args: None,
                        uf: None,
                        proof_func: None,
                        container_rebuild: None,
                        proof_constructors: None,
                        unionable: true,
                    } => {
                        let span = self.span(&span)?;
                        self.program.declarations.push(pb::Declaration {
                            kind: Some(pb::declaration::Kind::EqSort(pb::EqSort {
                                name,
                                ..Default::default()
                            })),
                            span,
                            ..Default::default()
                        });
                    }
                    N::Function(function) => {
                        if function.internal_hidden
                            || function.internal_let
                            || function.term_constructor.is_some()
                        {
                            return Err(
                                "internal function annotations require separate source lowering"
                                    .into(),
                            );
                        }
                        let inputs = function
                            .schema
                            .input
                            .iter()
                            .map(|name| {
                                Ok(pb::Arg {
                                    sort: self.sort(name)?,
                                    name: String::new(),
                                })
                            })
                            .collect::<Result<_, String>>()?;
                        let output = self.sort(&function.schema.output)?;
                        let kind = match function.subtype {
                            ast::FunctionSubtype::Constructor => {
                                let cost = function.cost.map(|cost| {
                                    let cost = i64::try_from(cost).map_err(|_| "constructor cost exceeds this adapter's i64 domain")?;
                                    self.expr(&ResolvedExpr::Lit(function.span.clone(), Literal::Int(cost)), false, 0)
                                }).transpose()?;
                                pb::declaration::Kind::Constructor(pb::Constructor {
                                    name: function.name,
                                    inputs,
                                    output,
                                    cost,
                                    unextractable: function.unextractable,
                                })
                            }
                            ast::FunctionSubtype::Custom => {
                                if !function.unextractable {
                                    return Err("extractable functions are not supported by this source slice".into());
                                }
                                let merge = function
                                    .merge
                                    .as_ref()
                                    .map(|expr| self.expr(expr, false, 0))
                                    .transpose()?;
                                pb::declaration::Kind::Function(pb::Function {
                                    name: function.name,
                                    inputs,
                                    output,
                                    merge,
                                })
                            }
                        };
                        let span = self.span(&function.span)?;
                        self.program.declarations.push(pb::Declaration {
                            kind: Some(kind),
                            span,
                            ..Default::default()
                        });
                    }
                    N::AddRuleset(span, name) => {
                        if self.rulesets.contains_key(&name) {
                            return Err(format!("ruleset {name} is already declared"));
                        }
                        let span = self.span(&span)?;
                        self.rulesets
                            .insert(name.clone(), self.program.rulesets.len());
                        self.program.rulesets.push(pb::Ruleset {
                            name: Some(name),
                            span,
                            kind: Some(pb::ruleset::Kind::Rules(pb::RuleList::default())),
                            ..Default::default()
                        });
                    }
                    N::NormRule { rule } => self.rule(rule, rewrite)?,
                    N::CoreAction(ResolvedAction::Let(span, var, expr)) => {
                        let output = self.sort(var.sort.name())?;
                        let value = self.expr(&expr, false, 0)?;
                        let span = self.span(&span)?;
                        self.program.declarations.push(pb::Declaration {
                            kind: Some(pb::declaration::Kind::Function(pb::Function {
                                name: var.name.clone(),
                                output,
                                ..Default::default()
                            })),
                            span,
                            ..Default::default()
                        });
                        self.program.commands.push(pb::Command {
                            kind: Some(pb::command::Kind::Action(pb::Action {
                                kind: Some(pb::action::Kind::Set(pb::Set {
                                    target: Some(pb::Call {
                                        func: var.name,
                                        args: vec![],
                                    }),
                                    value: Some(value),
                                })),
                                span,
                            })),
                            span,
                        });
                    }
                    N::CoreAction(action) => {
                        let action = self.action(&action, false)?;
                        self.program.commands.push(pb::Command {
                            span: action.span,
                            kind: Some(pb::command::Kind::Action(action)),
                        });
                    }
                    N::Check(span, facts) => {
                        let facts = self.facts(&facts)?;
                        let span = self.span(&span)?;
                        self.program.commands.push(pb::Command {
                            span,
                            kind: Some(pb::command::Kind::Check(pb::Check { facts })),
                        });
                    }
                    N::Extract(span, expr, variants) => {
                        let ResolvedExpr::Lit(_, Literal::Int(count)) = variants else {
                            return Err("source extraction requires a literal variant count".into());
                        };
                        let count = u32::try_from(count)
                            .map_err(|_| "source extraction variant count out of range")?
                            .max(1);
                        let root = self.expr(&expr, false, 0)?;
                        let span = self.span(&span)?;
                        self.program.commands.push(pb::Command {
                            span,
                            kind: Some(pb::command::Kind::Extract(pb::Extract {
                                roots: vec![root],
                                variants: count,
                                extractor: pb::Extractor::Tree.into(),
                                ..Default::default()
                            })),
                        });
                    }
                    N::RunSchedule(mut schedule) => {
                        loop {
                            schedule = match schedule {
                                ast::GenericSchedule::Repeat(_, 1, child) => *child,
                                ast::GenericSchedule::Sequence(_, mut children)
                                    if children.len() == 1 =>
                                {
                                    children.remove(0)
                                }
                                other => {
                                    schedule = other;
                                    break;
                                }
                            };
                        }
                        let ast::GenericSchedule::Run(span, config) = schedule else {
                            return Err(
                                "source schedules currently require one ruleset step".into()
                            );
                        };
                        if config.until.is_some() {
                            return Err("source run-until is not supported yet".into());
                        }
                        let index = *self
                            .rulesets
                            .get(&config.ruleset)
                            .ok_or_else(|| format!("unknown ruleset {}", config.ruleset))?;
                        if self.installed.insert(config.ruleset.clone()) {
                            publish.push(index);
                        }
                        let span = self.span(&span)?;
                        self.program.commands.push(pb::Command {
                            span,
                            kind: Some(pb::command::Kind::Run(pb::Run {
                                ruleset: Some(pb::RulesetRef {
                                    kind: Some(pb::ruleset_ref::Kind::Name(config.ruleset)),
                                }),
                                ..Default::default()
                            })),
                        });
                    }
                    _ => return Err("source command is outside the initial producer slice".into()),
                }
            }
        }
        Ok(pb::Program {
            ir_version: 1,
            sorts: self.program.sorts.clone(),
            nodes: self.program.nodes.clone(),
            files: self.program.files.clone(),
            declarations: std::mem::take(&mut self.program.declarations),
            commands: std::mem::take(&mut self.program.commands),
            // Unused rules are still validated at their source position. Only
            // binding/publication waits until the first run of the theory.
            rules: self.program.rules.clone(),
            rulesets: publish
                .into_iter()
                .map(|index| self.program.rulesets[index].clone())
                .collect(),
        })
    }

    fn rule(
        &mut self,
        rule: ast::GenericRule<ResolvedCall, ast::ResolvedVar>,
        rewrite: Option<bool>,
    ) -> Result<(), String> {
        if self.installed.contains(&rule.ruleset) {
            return Err(format!(
                "cannot add a rule to {} after its first run; occurrence-preserving versions are not implemented",
                rule.ruleset
            ));
        }
        let ruleset = *self
            .rulesets
            .get(&rule.ruleset)
            .ok_or_else(|| format!("unknown ruleset {}", rule.ruleset))?;
        let Some(pb::ruleset::Kind::Rules(list)) = &self.program.rulesets[ruleset].kind else {
            unreachable!()
        };
        if list
            .rules
            .iter()
            .any(|index| self.program.rules[*index as usize].name.as_ref() == Some(&rule.name))
        {
            return Err(egglog::Error::RuleAlreadyExists(rule.name, rule.span).to_string());
        }
        if rule.eval_mode != ast::RuleEvalMode::Seminaive || rule.no_decomp || rule.include_subsumed
        {
            return Err("source rule options are not supported yet".into());
        }
        // Native source-position shadowing checks have already run. Rename only
        // resolved locals, consistently across query/head; global refs remain
        // explicit capture calls. ResolvedVar equality ignores is_global_ref,
        // so it must not be used as the key for this derived lowering map.
        let mut locals = HashMap::new();
        let rule = rule.map_symbols(&mut |call| call, &mut |mut var| {
            if !var.is_global_ref {
                let next = locals.len();
                var.name = locals
                    .entry(var.name)
                    .or_insert_with(|| {
                        format!("{}{}_{next}", self.local_prefix, self.program.rules.len())
                    })
                    .clone();
            }
            var
        });
        let kind = if let Some(subsume) = rewrite {
            let (
                Some(ResolvedFact::Eq(_, ResolvedExpr::Var(_, binder), lhs)),
                Some(ResolvedAction::Union(_, ResolvedExpr::Var(_, target), rhs)),
            ) = (rule.body.first(), rule.head.0.first())
            else {
                return Err("native rewrite desugaring changed: missing match/union".into());
            };
            if binder.name != target.name
                || binder.is_global_ref
                || target.is_global_ref
                || rule.head.0.len() != 1 + usize::from(subsume)
            {
                return Err("native rewrite desugaring changed: mismatched witness/actions".into());
            }
            if subsume {
                let (
                    ResolvedExpr::Call(_, function, args),
                    ResolvedAction::Change(_, ast::Change::Subsume, changed, changed_args),
                ) = (lhs, &rule.head.0[1])
                else {
                    return Err("native rewrite desugaring changed: invalid subsumption".into());
                };
                if function != changed || args != changed_args {
                    return Err("native rewrite desugaring changed: subsumption target".into());
                }
            }
            pb::rule_decl::Kind::Rewrite(pb::Rewrite {
                lhs: self.expr(lhs, false, 0)?,
                rhs: self.expr(rhs, true, 0)?,
                conditions: self.facts(&rule.body[1..])?,
                subsume,
            })
        } else {
            pb::rule_decl::Kind::Rule(pb::Rule {
                query: self.facts(&rule.body)?,
                head: rule
                    .head
                    .0
                    .iter()
                    .map(|action| self.action(action, true))
                    .collect::<Result<_, _>>()?,
            })
        };
        let span = self.span(&rule.span)?;
        let index = u32::try_from(self.program.rules.len()).map_err(|_| "too many source rules")?;
        self.program.rules.push(pb::RuleDecl {
            kind: Some(kind),
            name: Some(rule.name),
            eval_mode: pb::RuleEvalMode::Seminaive.into(),
            span,
            ..Default::default()
        });
        let Some(pb::ruleset::Kind::Rules(list)) = &mut self.program.rulesets[ruleset].kind else {
            unreachable!()
        };
        list.rules.push(index);
        Ok(())
    }

    fn facts(&mut self, facts: &[ResolvedFact]) -> Result<Vec<u32>, String> {
        facts
            .iter()
            .map(|fact| match fact {
                ResolvedFact::Fact(expr) => self.expr(expr, false, 0),
                ResolvedFact::Eq(span, lhs, rhs) => {
                    let lhs = self.expr(lhs, false, 0)?;
                    let rhs = self.expr(rhs, false, 0)?;
                    let span = self.span(span)?;
                    let index = u32::try_from(self.program.nodes.len())
                        .map_err(|_| "too many source nodes")?;
                    self.program.nodes.push(pb::Node {
                        sort_id: self.program.nodes[lhs as usize].sort_id,
                        kind: Some(pb::node::Kind::Union(pb::Union {
                            members: vec![lhs, rhs],
                        })),
                        span,
                    });
                    Ok(index)
                }
            })
            .collect()
    }

    fn action(
        &mut self,
        action: &ResolvedAction<ResolvedCall, ast::ResolvedVar>,
        rule_head: bool,
    ) -> Result<pb::Action, String> {
        let (span, kind) = match action {
            ResolvedAction::Expr(span, expr) => (span, pb::action::Kind::Term(self.expr(expr, rule_head, 0)?)),
            ResolvedAction::Set(span, function, args, value) => (span, pb::action::Kind::Set(pb::Set {
                target: Some(self.call(function, args, rule_head, 0)?), value: Some(self.expr(value, rule_head, 0)?),
            })),
            ResolvedAction::Change(span, change, function, args) => {
                let call = self.call(function, args, rule_head, 0)?;
                (span, match change { ast::Change::Delete => pb::action::Kind::Delete(call), ast::Change::Subsume => pb::action::Kind::Subsume(call) })
            }
            ResolvedAction::Panic(span, message) if !rule_head => (span, pb::action::Kind::Panic(message.clone())),
            _ => return Err("source local bindings, general action unions and rule panics are not supported yet".into()),
        };
        Ok(pb::Action {
            kind: Some(kind),
            span: self.span(span)?,
        })
    }

    fn call(
        &mut self,
        function: &ResolvedCall,
        args: &[ResolvedExpr],
        rule_head: bool,
        depth: usize,
    ) -> Result<pb::Call, String> {
        let name = match function {
            ResolvedCall::Func(function) => function.name.clone(),
            ResolvedCall::Primitive(primitive) => {
                let key = primitive.export_builtin(&mut self.program)?;
                self.graph
                    .type_info()
                    .export_builtin_definition(&key, &mut self.program)?;
                key
            }
        };
        Ok(pb::Call {
            func: name,
            args: args
                .iter()
                .map(|expr| self.expr(expr, rule_head, depth + 1))
                .collect::<Result<_, _>>()?,
        })
    }

    fn expr(&mut self, expr: &ResolvedExpr, rule_head: bool, depth: usize) -> Result<u32, String> {
        if depth > 256 {
            return Err("source expression depth exceeds 256".into());
        }
        let (sort, kind) = match expr {
            ResolvedExpr::Lit(_, literal) => {
                let (sort, value) = match literal {
                    Literal::Int(value) => ("i64", pb::primitive_value::Value::I64(*value)),
                    Literal::Float(value) => (
                        "f64",
                        pb::primitive_value::Value::F64Bits(value.0.to_bits()),
                    ),
                    Literal::String(value) => {
                        ("String", pb::primitive_value::Value::String(value.clone()))
                    }
                    Literal::Bool(value) => ("bool", pb::primitive_value::Value::Bool(*value)),
                    Literal::Unit => ("Unit", pb::primitive_value::Value::Unit(pb::Unit {})),
                };
                (
                    sort,
                    pb::node::Kind::PrimitiveValue(pb::PrimitiveValue { value: Some(value) }),
                )
            }
            ResolvedExpr::Var(_, var) => {
                if var.is_global_ref && rule_head {
                    return Err(
                        "source globals in rule heads require retained query bindings".into(),
                    );
                }
                (
                    var.sort.name(),
                    if var.is_global_ref {
                        pb::node::Kind::Call(pb::Call {
                            func: var.name.clone(),
                            args: vec![],
                        })
                    } else {
                        pb::node::Kind::Var(var.name.clone())
                    },
                )
            }
            ResolvedExpr::Call(_, function, args) => (
                function.output().name(),
                pb::node::Kind::Call(self.call(function, args, rule_head, depth)?),
            ),
        };
        let sort_id = self.sort(sort)?;
        let span = self.span(&expr.span())?;
        let index = u32::try_from(self.program.nodes.len()).map_err(|_| "too many source nodes")?;
        self.program.nodes.push(pb::Node {
            sort_id,
            kind: Some(kind),
            span,
        });
        Ok(index)
    }

    fn sort(&mut self, name: &str) -> Result<u32, String> {
        let native = self
            .graph
            .get_sort_by_name(name)
            .ok_or_else(|| format!("unknown sort {name}"))?;
        self.graph.export_sort(native, &mut self.program.sorts)
    }

    fn span(&mut self, span: &ast::Span) -> Result<Option<pb::Span>, String> {
        let ast::Span::Egglog(span) = span else {
            return Ok(None);
        };
        let file = pb::SourceFile {
            name: span.file.name.clone().unwrap_or_default(),
            contents: Some(span.file.contents.clone()),
        };
        let index = self
            .program
            .files
            .iter()
            .position(|existing| existing == &file)
            .unwrap_or_else(|| {
                self.program.files.push(file);
                self.program.files.len() - 1
            });
        Ok(Some(pb::Span {
            file: u32::try_from(index).map_err(|_| "too many source files")?,
            start: u32::try_from(span.i).map_err(|_| "source span exceeds u32")?,
            end: u32::try_from(span.j).map_err(|_| "source span exceeds u32")?,
        }))
    }
}

impl Iterator for Source {
    type Item = Result<pb::Program, TransportError>;

    fn next(&mut self) -> Option<Self::Item> {
        let command = self.commands.pop_front()?;
        let result = self.compile(command).map_err(TransportError);
        if result.is_err() {
            self.commands.clear();
        }
        Some(result)
    }
}

/// Renders the initial producer's decoded protobuf slice as native source.
/// This does not execute or retain the source, and rejects unsupported forms.
/// Submit successive rendered phases to the same native graph in source order.
pub fn render(program: &pb::Program) -> Result<String, TransportError> {
    if program.sorts.iter().any(|sort| matches!(&sort.kind, Some(pb::sort::Kind::Family(family)) if !family.args.is_empty())) {
        return Err(TransportError("container phases require the stateful source Renderer".into()));
    }
    let mut definitions = crate::new_experimental_egraph()
        .type_info()
        .builtin_catalog()
        .map_err(TransportError)?
        .definitions;
    egglog::builtin::definitions::reconcile_declarations(program, &mut definitions)
        .map_err(TransportError)?;
    validate_private_names(program).map_err(TransportError)?;
    let mut lowered = program.clone();
    project_names(&mut lowered, &definitions);
    render_prepared(&lowered, vec![])
}

/// Stateful, typechecking-only renderer. Tracks structural sort declarations
/// across phases; callers submit each result in order and stop on an error.
pub struct Renderer {
    session: Session,
}

impl Default for Renderer {
    fn default() -> Self {
        Self {
            session: Session {
                graph: crate::new_experimental_egraph(),
                definitions: pb::Program::default(),
                names: NativeNames::default(),
                request: 0,
                rulesets: HashMap::new(),
                origins: HashMap::new(),
            },
        }
    }
}

impl Renderer {
    /// Validates and renders one phase, retaining only type/definition state.
    pub fn render(&mut self, program: &pb::Program) -> Result<String, TransportError> {
        let mut lowered = program.clone();
        let (session, materialized) = self
            .session
            .prepare(&mut lowered)
            .map_err(|e| TransportError(e.0.message))?;
        let source = render_prepared(&lowered, materialized)?;
        self.session = session;
        Ok(source)
    }
}

fn render_prepared(
    program: &pb::Program,
    materialized: Vec<Command>,
) -> Result<String, TransportError> {
    let result = (|| -> Result<Vec<Command>, String> {
        if program.ir_version != 1 {
            return Err("unsupported source IR version".into());
        }
        let mut native = crate::new_experimental_egraph();
        validate_host_declarations(program, &mut native)?;
        // Native AST Display assumes symbols are source atoms; protobuf names
        // need not be. Validate every interpolated identifier before formatting,
        // using the native parser rather than maintaining another token grammar.
        let mut names = vec![];
        for sort in &program.sorts {
            match &sort.kind {
                Some(pb::sort::Kind::Eq(name)) => names.push(name.as_str()),
                Some(pb::sort::Kind::Family(family)) => names.push(family.name.as_str()),
                Some(pb::sort::Kind::Var(_)) => (),
                _ => return Err("unsupported source sort".into()),
            }
        }
        for node in &program.nodes {
            match &node.kind {
                Some(pb::node::Kind::Var(name)) => names.push(name.as_str()),
                Some(pb::node::Kind::Call(call)) => names.push(call.func.as_str()),
                _ => (),
            }
        }
        for declaration in &program.declarations {
            match &declaration.kind {
                Some(pb::declaration::Kind::EqSort(sort)) => names.push(sort.name.as_str()),
                Some(pb::declaration::Kind::Constructor(constructor)) => names.push(constructor.name.as_str()),
                Some(pb::declaration::Kind::Function(function)) => names.push(function.name.as_str()),
                _ => (),
            }
        }
        for ruleset in &program.rulesets {
            if let Some(name) = &ruleset.name && !name.is_empty() { names.push(name.as_str()); }
        }
        for command in &program.commands {
            if let Some(pb::command::Kind::Run(run)) = &command.kind
                && let Some(pb::ruleset_ref::Kind::Name(name)) = run.ruleset.as_ref().and_then(|reference| reference.kind.as_ref())
                && !name.is_empty()
            { names.push(name.as_str()); }
        }
        for action in program.commands.iter().filter_map(|command| match &command.kind {
            Some(pb::command::Kind::Action(action)) => Some(action), _ => None,
        }).chain(program.rules.iter().flat_map(|rule| match &rule.kind {
            Some(pb::rule_decl::Kind::Rule(rule)) => rule.head.as_slice(), _ => &[],
        })) {
            match &action.kind {
                Some(pb::action::Kind::Set(set)) => {
                    if let Some(call) = &set.target { names.push(call.func.as_str()); }
                }
                Some(pb::action::Kind::Delete(call) | pb::action::Kind::Subsume(call)) => names.push(call.func.as_str()),
                _ => (),
            }
        }
        let mut parser = native.parser;
        for name in names {
            if !matches!(parser.get_expr_from_string(None, name), Ok(Expr::Var(_, parsed)) if parsed == name) {
                return Err(format!("identifier {name:?} cannot be rendered as one native source atom"));
            }
        }
        let mut commands = vec![];
        for declaration in &program.declarations {
            if let Some(pb::declaration::Kind::EqSort(sort)) = &declaration.kind {
                commands.push(Command::Sort {
                    span: native_span(program, declaration.span.as_ref())?, name: sort.name.clone(), presort_and_args: None,
                    uf: None, proof_func: None, container_rebuild: None, proof_constructors: None, unionable: true,
                });
            }
        }
        commands.extend(materialized);
        for declaration in &program.declarations {
            let span = native_span(program, declaration.span.as_ref())?;
            commands.push(
                match declaration
                    .kind
                    .as_ref()
                    .ok_or("missing declaration kind")?
                {
                    pb::declaration::Kind::EqSort(_) => continue,
                    pb::declaration::Kind::Constructor(constructor) => Command::Constructor {
                        span,
                        name: constructor.name.clone(),
                        schema: signature(program, &constructor.inputs, constructor.output)?,
                        cost: constructor
                            .cost
                            .map(|index| -> Result<u64, String> {
                                match expression(program, index, &mut HashSet::new())? {
                                    Expr::Lit(_, Literal::Int(cost)) => u64::try_from(cost)
                                        .map_err(|_| "negative constructor cost".into()),
                                    _ => Err("source constructor cost must be an inert i64".into()),
                                }
                            })
                            .transpose()?,
                        unextractable: constructor.unextractable,
                        hidden: false,
                        let_binding: false,
                        term_constructor: None,
                    },
                    pb::declaration::Kind::Function(function) => Command::Function {
                        span,
                        name: function.name.clone(),
                        schema: signature(program, &function.inputs, function.output)?,
                        merge: function
                            .merge
                            .map(|index| expression(program, index, &mut HashSet::new()))
                            .transpose()?,
                        hidden: false,
                        let_binding: false,
                        term_constructor: None,
                        unextractable: true,
                    },
                    pb::declaration::Kind::HostPrimitive(_) | pb::declaration::Kind::HostSortFamily(_) => continue,
                    _ => return Err("unsupported source declaration".into()),
                },
            );
        }
        for ruleset in &program.rulesets {
            let name = ruleset.name.as_ref().ok_or("anonymous source ruleset")?;
            if !name.is_empty() {
                commands.push(Command::AddRuleset(
                    native_span(program, ruleset.span.as_ref())?,
                    name.clone(),
                ));
            }
            let Some(pb::ruleset::Kind::Rules(rules)) = &ruleset.kind else {
                return Err("unsupported source ruleset composition".into());
            };
            for index in &rules.rules {
                let rule = program
                    .rules
                    .get(*index as usize)
                    .ok_or("source rule index out of bounds")?;
                commands.push(lower_rule(
                    program,
                    rule,
                    name,
                    rule.name.as_deref().unwrap_or(""),
                )?);
            }
        }
        for command in &program.commands {
            let span = native_span(program, command.span.as_ref())?;
            match command.kind.as_ref().ok_or("missing command kind")? {
                pb::command::Kind::Action(action) => commands.extend(
                    lower_action(program, action)?
                        .into_iter()
                        .map(Command::Action),
                ),
                pb::command::Kind::Check(check) => {
                    commands.push(Command::Check(span, facts(program, &check.facts)?))
                }
                pb::command::Kind::PrintFunction(print) => {
                    commands.push(Command::PrintFunction(
                        span, print.table.clone(),
                        if print.max_rows == 0 { None } else { Some(usize::try_from(print.max_rows).map_err(|_| "table row limit exceeds native usize")?) },
                        None, ast::PrintFunctionMode::Default,
                    ));
                }
                pb::command::Kind::Extract(extract)
                    if extract.extractor == i32::from(pb::Extractor::Tree)
                        && extract.cost_model.is_empty()
                        && extract.variants > 0 =>
                {
                    for root in &extract.roots {
                        commands.push(Command::Extract(
                            span.clone(),
                            expression(program, *root, &mut HashSet::new())?,
                            Expr::Lit(
                                span.clone(),
                                Literal::Int(if extract.variants == 1 {
                                    0
                                } else {
                                    i64::from(extract.variants)
                                }),
                            ),
                        ));
                    }
                }
                pb::command::Kind::Run(run) if run.scheduler.is_empty() => {
                    let name = match run
                        .ruleset
                        .as_ref()
                        .and_then(|reference| reference.kind.as_ref())
                        .ok_or("missing ruleset reference")?
                    {
                        pb::ruleset_ref::Kind::Name(name) => name,
                        pb::ruleset_ref::Kind::Index(index) => program
                            .rulesets
                            .get(*index as usize)
                            .and_then(|ruleset| ruleset.name.as_ref())
                            .ok_or("invalid source ruleset reference")?,
                    };
                    commands.push(Command::RunSchedule(ast::Schedule::Run(
                        span,
                        ast::RunConfig {
                            ruleset: name.clone(),
                            until: None,
                        },
                    )));
                }
                _ => return Err("unsupported source command".into()),
            }
        }
        // Atom validity is insufficient in action position: a function named
        // `panic` would print as a Panic action, and `include` becomes a command
        // only at top level. Check the actual parse context, with the current
        // experimental command registry, before returning executable text.
        for command in &commands {
            let (actions, in_rule) = match command {
                Command::Action(action) => (std::slice::from_ref(action), false),
                Command::Rule { rule } => (rule.head.0.as_slice(), true),
                _ => continue,
            };
            for action in actions {
                let Action::Expr(_, expected) = action else { continue };
                let text = if in_rule {
                    format!("(rule () ({action}))")
                } else {
                    action.to_string()
                };
                let parsed = parser.get_program_from_string(None, &text).map_err(|error| error.to_string())?;
                let actual = match parsed.as_slice() {
                    [Command::Action(Action::Expr(_, expr))] if !in_rule => Some(expr),
                    [Command::Rule { rule }] if in_rule => match rule.head.0.as_slice() {
                        [Action::Expr(_, expr)] => Some(expr),
                        _ => None,
                    },
                    _ => None,
                };
                if actual.is_none_or(|expr| expr.to_string() != expected.to_string()) {
                    return Err(format!("expression action {action} changes meaning when parsed as source"));
                }
            }
        }
        Ok(commands)
    })()
    .map_err(TransportError)?;
    Ok(result
        .into_iter()
        .map(|command| format!("{command}\n"))
        .collect())
}
