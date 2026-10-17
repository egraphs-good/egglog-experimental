//! Sequential, typechecking-only source producer for the initial protobuf slice.
//!
//! Submit each yielded program through the byte adapter before requesting the
//! next one, and stop on a transport or decoded execution error. Parsing is eager
//! (like native source execution); resolution is sequential so a later type error
//! does not erase an executed prefix. Native syntax is never executed here.
//! Scope-aware callers use [`Source::next_submission`] and the existing clone /
//! return requests; the Program iterator deliberately rejects scope operations.
//! Rulesets and their dependencies are fixed after first selection. Uncatalogued primitives, effectful local lets,
//! dynamic costs and general schedules remain unsupported. The explicit Core
//! frontend also admits Run-only sequence/repeat/saturate controls. Proof requests keep
//! their authored identity; execution mode belongs to the receiving engine.

use super::*;
use ast::{GenericAction as ResolvedAction, GenericNCommand as N, ResolvedExpr, ResolvedFact};
use egglog::ResolvedCall;
use std::collections::VecDeque;
use std::path::{Path, PathBuf};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Dialect {
    Experimental,
    Core,
}

#[derive(Clone, Copy)]
enum RewriteKind {
    Directional(bool),
    Bidirectional,
}

/// An ordered source phase. Push saves the active handle and continues in a
/// clone; Pop returns to saved handles, one level at a time. Stop consuming after
/// any failed request, including a Pop with too few saved handles.
pub enum Submission {
    /// Install definitions and execute commands through RunProgram.
    Program(pb::Program),
    /// Save the active handle and continue in a clone this many times.
    Push(usize),
    /// Return to saved handles in order, retaining completed returns on error.
    Pop {
        /// Number of saved scopes to restore.
        count: usize,
        /// Authored location for reporting an exhausted scope stack.
        span: ast::Span,
    },
}

struct SourceScope {
    graph: EGraph,
    program: pb::Program,
    rulesets: HashMap<String, usize>,
    installed: HashSet<String>,
    relations: HashSet<String>,
    local_prefix: String,
}

/// A source stream whose authored declarations, expressions and rules become
/// protobuf records. The native graph holds only the producer's type environment.
pub struct Source {
    dialect: Dialect,
    graph: EGraph,
    commands: VecDeque<(Command, usize)>,
    include_base: PathBuf,
    scopes: Vec<SourceScope>,
    program: pb::Program,
    rulesets: HashMap<String, usize>,
    installed: HashSet<String>,
    relations: HashSet<String>,
    local_prefix: String,
}

// Project the resolved body before unstable-fn target preparation replaces
// source target literals with backend-only bindings. The clone is read-only
// compiler provenance; no runtime ID is installed into another graph.
pub(crate) fn primitive_definition(
    graph: &EGraph,
    name: &str,
    inputs: &[ArcSort],
    output: &ArcSort,
    body: &ResolvedExpr,
) -> Result<pb::Program, String> {
    let mut source = Source {
        dialect: Dialect::Experimental,
        graph: graph.clone(),
        commands: VecDeque::new(),
        include_base: PathBuf::new(),
        scopes: Vec::new(),
        program: pb::Program {
            ir_version: 1,
            ..Default::default()
        },
        rulesets: HashMap::new(),
        installed: HashSet::new(),
        relations: HashSet::new(),
        local_prefix: String::new(),
    };
    let inputs = inputs
        .iter()
        .enumerate()
        .map(|(index, sort)| {
            Ok(pb::Arg {
                name: format!("_{index}"),
                sort: source.sort(sort.name())?,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let output = source.sort(output.name())?;
    let body = source.expr(body, None, 0)?;
    source.program.declarations.push(pb::Declaration {
        kind: Some(pb::declaration::Kind::Primitive(pb::Primitive {
            name: name.into(),
            inputs,
            output,
            body: Some(body),
        })),
        ..Default::default()
    });
    Ok(source.program)
}

impl Source {
    /// Parses source without executing it. Each iterator item is one ordered
    /// submission phase; callers must stop after a failed decoded response.
    pub fn new(filename: Option<String>, source: &str) -> Result<Self, TransportError> {
        Self::with_dialect(filename, source, Dialect::Experimental)
    }

    /// Parses Core source, including Run-only controls without custom schedulers.
    /// This is an explicit frontend choice, not a wire execution setting.
    pub fn new_core(filename: Option<String>, source: &str) -> Result<Self, TransportError> {
        Self::with_dialect(filename, source, Dialect::Core)
    }

    fn with_dialect(
        filename: Option<String>,
        source: &str,
        dialect: Dialect,
    ) -> Result<Self, TransportError> {
        let mut graph = match dialect {
            Dialect::Experimental => crate::new_experimental_egraph(),
            Dialect::Core => EGraph::default(),
        };
        let commands: VecDeque<_> = graph
            .parse_program(filename, source)
            .map_err(|error| TransportError(error.to_string()))?
            .into_iter()
            .map(|command| (command, 0))
            .collect();
        // Rules are revalidated when their fixed theory is published. A local
        // source name may legally become a function name in the meantime. Pick
        // a namespace disjoint from parsed declarations and variable bindings,
        // not from a raw-source substring test (strings are not identifiers).
        let mut local_prefix = "__proto_source_local_".to_string();
        for (command, _) in &commands {
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
            dialect,
            graph,
            commands,
            include_base: PathBuf::new(),
            scopes: Vec::new(),
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
            relations: HashSet::new(),
            local_prefix,
        })
    }

    /// Resolve authored include paths against an explicit directory rather than
    /// the process working directory. Nested includes use this same base, as in
    /// native execution; source filenames remain the authored include paths.
    pub fn with_include_base(mut self, base: impl AsRef<Path>) -> Result<Self, TransportError> {
        let base = base
            .as_ref()
            .canonicalize()
            .map_err(|error| TransportError(format!("include base: {error}")))?;
        if !base.is_dir() {
            return Err(TransportError("include base must be a directory".into()));
        }
        self.include_base = base;
        Ok(self)
    }

    /// Lower the next ordered phase, including scope requests. Unlike the flat
    /// Program iterator this preserves operations that cannot fit in Program.
    /// Included files are parsed when reached, retaining earlier executed phases
    /// if opening or parsing an include fails.
    pub fn next_submission(&mut self) -> Option<Result<Submission, TransportError>> {
        self.advance(true)
    }

    fn advance(&mut self, scopes: bool) -> Option<Result<Submission, TransportError>> {
        let result = loop {
            let (command, depth) = self.commands.pop_front()?;
            match command {
                Command::Include(span, file) => {
                    if depth >= 256 {
                        break Err("source include nesting exceeds 256".into());
                    }
                    let path = self.include_base.join(&file);
                    let contents = match std::fs::read_to_string(path) {
                        Ok(contents) => contents,
                        Err(error) => {
                            break Err(egglog::Error::IoError(file.into(), error, span).to_string());
                        }
                    };
                    let commands = match self.graph.parse_program(Some(file), &contents) {
                        Ok(commands) => commands,
                        Err(error) => break Err(error.to_string()),
                    };
                    for command in &commands {
                        let mut avoid = |name: String| {
                            while name.starts_with(&self.local_prefix) {
                                self.local_prefix.push('_');
                            }
                            name
                        };
                        command
                            .clone()
                            .map_string_symbols(&mut avoid)
                            .map_symbols(&mut |head| head, &mut avoid);
                    }
                    for command in commands.into_iter().rev() {
                        self.commands.push_front((command, depth + 1));
                    }
                }
                Command::Push(count) if scopes => {
                    for _ in 0..count {
                        // The remaining input queue is deliberately not scoped.
                        self.scopes.push(SourceScope {
                            graph: self.graph.clone(),
                            program: self.program.clone(),
                            rulesets: self.rulesets.clone(),
                            installed: self.installed.clone(),
                            relations: self.relations.clone(),
                            local_prefix: self.local_prefix.clone(),
                        });
                    }
                    break Ok(Submission::Push(count));
                }
                Command::Pop(span, count) if scopes => {
                    for _ in 0..count {
                        let Some(saved) = self.scopes.pop() else {
                            // Yield the authored request so the caller performs
                            // native partial returns before reporting underflow.
                            self.commands.clear();
                            break;
                        };
                        self.graph.restore_from(saved.graph);
                        self.program = saved.program;
                        self.rulesets = saved.rulesets;
                        self.installed = saved.installed;
                        self.relations = saved.relations;
                        self.local_prefix = saved.local_prefix;
                    }
                    break Ok(Submission::Pop { count, span });
                }
                Command::Push(_) | Command::Pop(..) => {
                    break Err(
                        "source scopes require next_submission and clone/return requests".into(),
                    );
                }
                command => break self.compile(command).map(Submission::Program),
            }
        };
        if result.is_err() {
            self.commands.clear();
        }
        Some(result.map_err(TransportError))
    }

    fn compile(&mut self, command: Command) -> Result<pb::Program, String> {
        let explicit_sort_alias = match &command {
            Command::Sort {
                name,
                presort_and_args: Some(_),
                ..
            } => Some(name.clone()),
            _ => None,
        };
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
        for mut command in expanded {
            let mut fail_spans = vec![];
            while let Command::Fail(span, child) = command {
                fail_spans.push(span);
                command = *child;
            }
            if !fail_spans.is_empty()
                && (!matches!(
                    &command,
                    Command::Check(..)
                        | Command::Prove(..)
                        | Command::ProveExists(..)
                        | Command::Action(..)
                        | Command::RunSchedule(..)
                        | Command::PrintOverallStatistics(_, None)
                ) || matches!(&command, Command::Action(Action::Let(..))))
            {
                return Err("source Fail requires a supported native command; declarations and observations are not implemented".into());
            }
            let first_command = self.program.commands.len();
            // Keep provenance until export: desugaring alone cannot distinguish
            // a relation's generated constructor or an authored rewrite.
            let rewrite = match &command {
                Command::Rewrite(_, _, subsume) => Some(RewriteKind::Directional(*subsume)),
                Command::BiRewrite(..) => Some(RewriteKind::Bidirectional),
                Command::Relation { span, name, inputs } => {
                    // Resolve the authored declaration in the producer's type
                    // environment, but do not export its desugared private row
                    // sort/constructor. The wire relation has only inputs.
                    self.graph
                        .resolve_command_preserving_globals(command.clone())
                        .map_err(|error| error.to_string())?;
                    let inputs = inputs
                        .iter()
                        .map(|name| {
                            Ok(pb::Arg {
                                sort: self.sort(name)?,
                                name: String::new(),
                            })
                        })
                        .collect::<Result<_, String>>()?;
                    let span = self.span(span)?;
                    self.relations.insert(name.clone());
                    self.program.declarations.push(pb::Declaration {
                        kind: Some(pb::declaration::Kind::Relation(pb::Relation {
                            name: name.clone(),
                            inputs,
                        })),
                        span,
                        ..Default::default()
                    });
                    continue;
                }
                _ => None,
            };
            // Normal desugaring expands Prove into a hidden helper program.
            // Resolve just its query here, then publish the authored command.
            let prove = matches!(command, Command::Prove(..));
            let command = match command {
                Command::Prove(span, facts) => Command::Check(span, facts),
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
                Command::UserDefined(_, name, args) if name == "primitive" => {
                    let definition =
                        crate::primitive::RegisterPrimitive::register(&mut self.graph, &args)
                            .map_err(|error| error.to_string())??;
                    crate::builtin::definitions::reconcile_declarations(
                        &definition,
                        &mut self.program,
                    )?;
                    continue;
                }
                Command::UserDefined(_, name, _) => {
                    return Err(format!(
                        "source extension {name} requires structured declaration/command preparation"
                    ));
                }
                command => command,
            };
            let mut resolved = if let Command::Sort {
                span,
                name,
                presort_and_args: Some(_),
                uf: None,
                proof_func: None,
                container_rebuild: None,
                proof_constructors: None,
                unionable: true,
            } = &command
            {
                // Ask the actual provider to resolve the application on a disposable
                // type graph, then reuse an existing structural instance if present.
                let mut graph = self.graph.clone();
                let resolved = graph
                    .resolve_command_preserving_globals(command.clone())
                    .map_err(|error| error.to_string())?;
                let native = graph
                    .get_sort_by_name(name)
                    .ok_or("missing resolved source sort")?
                    .clone();
                let mut sorts = self.program.sorts.clone();
                let index = graph.export_sort(&native, &mut sorts)?;
                let mut existing = self
                    .graph
                    .type_info()
                    .get_arcsorts_by(|sort| !sort.is_eq_sort());
                existing.sort_by(|a, b| a.name().cmp(b.name()));
                let canonical = existing.into_iter().find(|sort| {
                    self.graph.export_sort(sort, &mut sorts.clone()).ok() == Some(index)
                });
                if let Some(canonical) = canonical {
                    self.graph
                        .bind_source_sort_alias(name, canonical.name(), span.clone())?;
                } else {
                    self.graph = graph;
                }
                if explicit_sort_alias.as_ref() == Some(name) {
                    let alias = pb::EgglogTypeBinding {
                        symbol: name.clone(),
                    };
                    if !sorts[index as usize].egglog_aliases.contains(&alias) {
                        sorts[index as usize].egglog_aliases.push(alias);
                    }
                    if sorts[index as usize].span.is_none() {
                        sorts[index as usize].span = self.span(span)?;
                    }
                }
                self.program.sorts = sorts;
                resolved
            } else {
                self.graph
                    .resolve_command_preserving_globals(command)
                    .map_err(|error| error.to_string())?
            };
            if matches!(rewrite, Some(RewriteKind::Bidirectional)) {
                // Resolve/typecheck both native binders before retaining the
                // authored forward body as one canonical bidirectional rule.
                let [N::NormRule { rule: forward }, N::NormRule { rule: reverse }] =
                    resolved.as_mut_slice()
                else {
                    return Err(
                        "native birewrite desugaring changed: expected two resolved rules".into(),
                    );
                };
                let name = forward
                    .name
                    .strip_suffix("=>")
                    .ok_or("native birewrite desugaring changed: missing forward suffix")?;
                if reverse.name != format!("{name}<=") || forward.ruleset != reverse.ruleset {
                    return Err("native birewrite desugaring changed: reverse identity".into());
                }
                forward.name = name.into();
                resolved.truncate(1);
            } else if rewrite.is_some() && resolved.len() != 1 {
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
                                    self.expr(&ResolvedExpr::Lit(function.span.clone(), Literal::Int(cost)), None, 0)
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
                                    .map(|expr| self.expr(expr, None, 0))
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
                    command @ (N::AddRuleset(..) | N::UnstableCombinedRuleset(..)) => {
                        let (span, name, kind) = match command {
                            N::AddRuleset(span, name) => (
                                span,
                                name,
                                pb::ruleset::Kind::Rules(pb::RuleList::default()),
                            ),
                            N::UnstableCombinedRuleset(span, name, children) => (
                                span,
                                name,
                                pb::ruleset::Kind::Combined(pb::CombinedRuleset {
                                    // Native declarations retain names, including
                                    // children declared before the first Run.
                                    rulesets: children
                                        .into_iter()
                                        .map(|name| pb::RulesetRef {
                                            kind: Some(pb::ruleset_ref::Kind::Name(name)),
                                        })
                                        .collect(),
                                }),
                            ),
                            _ => unreachable!(),
                        };
                        if self.rulesets.contains_key(&name) {
                            return Err(format!("ruleset {name} is already declared"));
                        }
                        let span = self.span(&span)?;
                        self.rulesets
                            .insert(name.clone(), self.program.rulesets.len());
                        self.program.rulesets.push(pb::Ruleset {
                            name: Some(name),
                            span,
                            kind: Some(kind),
                            ..Default::default()
                        });
                    }
                    N::NormRule { rule } => self.rule(rule, rewrite)?,
                    N::CoreAction(ResolvedAction::Let(span, var, expr)) => {
                        let value = self.expr(&expr, None, 0)?;
                        let output = self.program.nodes[value as usize].sort_id;
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
                        let action = self.action(&action, None)?;
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
                            kind: Some(if prove {
                                pb::command::Kind::Prove(pb::Prove { facts })
                            } else {
                                pb::command::Kind::Check(pb::Check { facts })
                            }),
                        });
                    }
                    N::PrintOverallStatistics(span, None) => {
                        let span = self.span(&span)?;
                        self.program.commands.push(pb::Command {
                            span,
                            kind: Some(pb::command::Kind::Stats(pb::Unit {})),
                        });
                    }
                    N::PrintFunction(span, table, limit, file, mode) => {
                        if file.is_some() || mode != ast::PrintFunctionMode::Default {
                            return Err(
                                "source table printing requires default mode without a file".into(),
                            );
                        }
                        let max_rows = limit
                            .map(u64::try_from)
                            .transpose()
                            .map_err(|_| "table row limit exceeds wire u64")?;
                        let span = self.span(&span)?;
                        self.program.commands.push(pb::Command {
                            span,
                            kind: Some(pb::command::Kind::PrintFunction(pb::PrintFunction {
                                table,
                                max_rows,
                            })),
                        });
                    }
                    N::ProveExists(span, call) => {
                        let ResolvedCall::Func(function) = call else {
                            return Err("source prove-exists requires a constructor".into());
                        };
                        let span = self.span(&span)?;
                        self.program.commands.push(pb::Command {
                            span,
                            kind: Some(pb::command::Kind::ProveExists(pb::ProveExists {
                                constructor: function.name.clone(),
                            })),
                        });
                    }
                    N::Extract(span, expr, variants) => {
                        let ResolvedExpr::Lit(_, Literal::Int(count)) = variants else {
                            return Err("source extraction requires a literal variant count".into());
                        };
                        let count = u32::try_from(count)
                            .map_err(|_| "source extraction variant count out of range")?
                            .max(1);
                        let root = self.expr(&expr, None, 0)?;
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
                        if self.dialect == Dialect::Core {
                            // Core's command parser inserts one outer Sequence
                            // for run-schedule; a legacy (run r 1) is Repeat1(Run).
                            // Explicit seq and repeat inside that envelope stay.
                            schedule = match schedule {
                                ast::GenericSchedule::Sequence(_, mut children)
                                    if children.len() == 1 =>
                                {
                                    children.remove(0)
                                }
                                ast::GenericSchedule::Repeat(span, 1, child) => match *child {
                                    run @ ast::GenericSchedule::Run(..) => run,
                                    other => ast::GenericSchedule::Repeat(span, 1, Box::new(other)),
                                },
                                other => other,
                            };
                            let command = self.schedule(schedule, &mut publish)?;
                            self.program.commands.push(command);
                            continue;
                        }
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
                        self.publish_ruleset(&config.ruleset, &mut publish)?;
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
            if !fail_spans.is_empty() {
                if self.program.commands.len() != first_command + 1 {
                    return Err("source Fail requires exactly one authored command".into());
                }
                let mut command = self.program.commands.pop().unwrap();
                for span in fail_spans.into_iter().rev() {
                    command = pb::Command {
                        span: self.span(&span)?,
                        kind: Some(pb::command::Kind::Fail(Box::new(command))),
                    };
                }
                self.program.commands.push(command);
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

    // Publish/freeze the newly selected named closure without compacting the
    // command-bearing arenas or duplicating shared rule occurrences. Names may
    // resolve forward at this point; all emitted edges remain named references.
    fn publish_ruleset(&mut self, name: &str, publish: &mut Vec<usize>) -> Result<(), String> {
        let root = *self
            .rulesets
            .get(name)
            .ok_or_else(|| format!("unknown ruleset {name}"))?;
        let mut pending = vec![(root, false)];
        let mut active = HashSet::new();
        let mut completed = HashSet::new();
        let mut order = vec![];
        while let Some((index, leaving)) = pending.pop() {
            let ruleset = &self.program.rulesets[index];
            let name = ruleset.name.as_ref().expect("source rulesets are named");
            if self.installed.contains(name) || completed.contains(&index) {
                continue;
            }
            if leaving {
                active.remove(&index);
                completed.insert(index);
                order.push(index);
                continue;
            }
            if !active.insert(index) {
                return Err(format!("cyclic source ruleset {name}"));
            }
            pending.push((index, true));
            if let Some(pb::ruleset::Kind::Combined(combined)) = &ruleset.kind {
                for child in combined.rulesets.iter().rev() {
                    let Some(pb::ruleset_ref::Kind::Name(name)) = &child.kind else {
                        unreachable!("source ruleset dependencies are named")
                    };
                    let child = *self
                        .rulesets
                        .get(name)
                        .ok_or_else(|| format!("unknown ruleset {name}"))?;
                    pending.push((child, false));
                }
            }
        }
        for index in order {
            self.installed
                .insert(self.program.rulesets[index].name.clone().unwrap());
            publish.push(index);
        }
        Ok(())
    }

    fn schedule(
        &mut self,
        schedule: ast::GenericSchedule<ResolvedCall, ast::ResolvedVar>,
        publish: &mut Vec<usize>,
    ) -> Result<pb::Command, String> {
        use ast::GenericSchedule as S;
        let (span, kind) = match schedule {
            S::Run(span, config) => {
                if config.until.is_some() {
                    return Err("source run-until is not supported yet".into());
                }
                self.publish_ruleset(&config.ruleset, publish)?;
                (
                    span,
                    pb::command::Kind::Run(pb::Run {
                        ruleset: Some(pb::RulesetRef {
                            kind: Some(pb::ruleset_ref::Kind::Name(config.ruleset)),
                        }),
                        ..Default::default()
                    }),
                )
            }
            S::Sequence(span, children) => {
                let body = children
                    .into_iter()
                    .map(|child| self.schedule(child, publish))
                    .collect::<Result<_, _>>()?;
                (
                    span,
                    pb::command::Kind::Repeat(pb::Repeat {
                        times: Some(1),
                        body,
                        ..Default::default()
                    }),
                )
            }
            S::Repeat(..) | S::Saturate(..) => {
                let (span, count, child) = match schedule {
                    S::Repeat(span, count, child) => (span, Some(count), child),
                    S::Saturate(span, child) => (span, None, child),
                    _ => unreachable!(),
                };
                // The parser gives each loop a body-list Sequence. Remove that
                // one container, not an explicitly authored seq among its children.
                let children = match *child {
                    S::Sequence(_, children) => children,
                    child => vec![child],
                };
                let body = children
                    .into_iter()
                    .map(|child| self.schedule(child, publish))
                    .collect::<Result<_, _>>()?;
                let kind = if count == Some(0) {
                    pb::command::Kind::Repeat(pb::Repeat {
                        times: Some(0),
                        body,
                        ..Default::default()
                    })
                } else {
                    pb::command::Kind::Saturate(pb::Saturate {
                        max_iterations: count
                            .map(|n| u64::try_from(n).map_err(|_| "source loop bound exceeds u64"))
                            .transpose()?,
                        body,
                        ..Default::default()
                    })
                };
                (span, kind)
            }
        };
        Ok(pb::Command {
            span: self.span(&span)?,
            kind: Some(kind),
        })
    }

    fn rule(
        &mut self,
        rule: ast::GenericRule<ResolvedCall, ast::ResolvedVar>,
        rewrite: Option<RewriteKind>,
    ) -> Result<(), String> {
        let ruleset = *self
            .rulesets
            .get(&rule.ruleset)
            .ok_or_else(|| format!("unknown ruleset {}", rule.ruleset))?;
        let Some(pb::ruleset::Kind::Rules(list)) = &self.program.rulesets[ruleset].kind else {
            return Err(egglog::Error::CombinedRulesetError(rule.ruleset, rule.span).to_string());
        };
        if self.installed.contains(&rule.ruleset) {
            return Err(format!(
                "cannot add a rule to {} after its first run; occurrence-preserving versions are not implemented",
                rule.ruleset
            ));
        }
        let names = if matches!(rewrite, Some(RewriteKind::Bidirectional)) {
            vec![format!("{}=>", rule.name), format!("{}<=", rule.name)]
        } else {
            vec![rule.name.clone()]
        };
        if let Some(duplicate) = list.rules.iter().find_map(|index| {
            let previous = &self.program.rules[*index as usize];
            let previous_name = previous.name.as_ref()?;
            names
                .iter()
                .find(|name| {
                    if matches!(previous.kind, Some(pb::rule_decl::Kind::Birewrite(_))) {
                        **name == format!("{previous_name}=>")
                            || **name == format!("{previous_name}<=")
                    } else {
                        *name == previous_name
                    }
                })
                .cloned()
        }) {
            return Err(egglog::Error::RuleAlreadyExists(duplicate, rule.span).to_string());
        }
        if rule.eval_mode != ast::RuleEvalMode::Seminaive || rule.no_decomp || rule.include_subsumed
        {
            return Err("source rule options are not supported yet".into());
        }
        // Native source-position shadowing checks have already run. Rename only
        // resolved locals, consistently across query/head; globals are captured
        // separately below. ResolvedVar equality ignores is_global_ref,
        // so it must not be used as the key for this derived lowering map.
        let mut locals = HashMap::new();
        let mut rule = rule.map_symbols(&mut |call| call, &mut |mut var| {
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
        // Match Core's remove_globals pass: globals used by actions are query
        // bindings, retained before any head writes. A bidirectional rewrite
        // also uses its authored LHS as the reverse head.
        let mut globals = HashMap::new();
        let mut captures = Vec::new();
        let mut capture = |expr: ResolvedExpr| {
            if let ResolvedExpr::Var(span, var) = &expr
                && var.is_global_ref
                && !globals.contains_key(&var.name)
            {
                let local = ResolvedExpr::Var(
                    span.clone(),
                    ast::ResolvedVar {
                        name: format!(
                            "{}{}_{}",
                            self.local_prefix,
                            self.program.rules.len(),
                            locals.len() + globals.len()
                        ),
                        sort: var.sort.clone(),
                        is_global_ref: false,
                    },
                );
                globals.insert(var.name.clone(), local.clone());
                captures.push(ResolvedFact::Eq(span.clone(), expr.clone(), local));
            }
            expr
        };
        rule.head.clone().visit_exprs(&mut capture);
        if matches!(rewrite, Some(RewriteKind::Bidirectional))
            && let Some(fact) = rule.body.first()
        {
            fact.clone().visit_exprs(&mut capture);
        }
        let mut replace = |expr: ResolvedExpr| match &expr {
            ResolvedExpr::Var(_, var) if var.is_global_ref => {
                globals.get(&var.name).cloned().unwrap_or(expr)
            }
            _ => expr,
        };
        rule.head = rule.head.visit_exprs(&mut replace);
        // Canonical rewrites reuse the LHS for a subsume action and for the
        // reverse direction. Keep those occurrences aligned with the head.
        if rewrite.is_some() {
            rule.body = rule
                .body
                .into_iter()
                .map(|fact| fact.visit_exprs(&mut replace))
                .collect();
        }
        rule.body.extend(captures);
        let mut aliases = HashMap::new();
        let kind = if let Some(rewrite) = rewrite {
            let subsume = matches!(rewrite, RewriteKind::Directional(true));
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
            let lhs = self.expr(lhs, None, 0)?;
            let rhs = self.expr(rhs, Some(&aliases), 0)?;
            let conditions = self.facts(&rule.body[1..])?;
            match rewrite {
                RewriteKind::Directional(subsume) => pb::rule_decl::Kind::Rewrite(pb::Rewrite {
                    lhs,
                    rhs,
                    conditions,
                    subsume,
                }),
                RewriteKind::Bidirectional => pb::rule_decl::Kind::Birewrite(pb::BiRewrite {
                    lhs,
                    rhs,
                    conditions,
                }),
            }
        } else {
            let query = self.facts(&rule.body)?;
            let mut head = Vec::with_capacity(rule.head.0.len());
            // Ordinary Call sharing does not retain its result. Recreating a
            // constructor is only safe while later actions cannot remove its
            // row; this also applies under an otherwise pure primitive call.
            let mut recreate_constructors = vec![true; rule.head.0.len()];
            let mut destructive = false;
            for (index, action) in rule.head.0.iter().enumerate().rev() {
                recreate_constructors[index] = !destructive;
                destructive |= matches!(action, ResolvedAction::Change(..));
                action.clone().visit_exprs(&mut |expr| {
                    if let ResolvedExpr::Call(_, ResolvedCall::Primitive(primitive), _) = &expr
                        && !primitive
                            .prim_with_id
                            .is_valid_in_context(egglog::Context::Pure)
                    {
                        destructive = true;
                    }
                    expr
                });
            }
            for (index, action) in rule.head.0.iter().enumerate() {
                if let ResolvedAction::Let(span, var, expr) = action {
                    let node = self.expr(expr, Some(&aliases), 0)?;
                    if !pure_local_alias(expr, recreate_constructors[index]) {
                        return Err("source local aliases with reads, stateful calls or constructors before destructive actions require retained-value lowering".into());
                    }
                    aliases.insert(var.name.clone(), node);
                    // Calls still evaluate at the authored position, including
                    // unused constructors and fallible pure primitives. A
                    // literal or retained variable needs no evaluation action.
                    if matches!(expr, ResolvedExpr::Call(..)) {
                        head.push(pb::Action {
                            kind: Some(pb::action::Kind::Term(node)),
                            span: self.span(span)?,
                        });
                    }
                } else {
                    head.push(self.action(action, Some(&aliases))?);
                }
            }
            pb::rule_decl::Kind::Rule(pb::Rule { query, head })
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
                ResolvedFact::Fact(expr) => self.expr(expr, None, 0),
                ResolvedFact::Eq(span, lhs, rhs) => {
                    let lhs = self.expr(lhs, None, 0)?;
                    let rhs = self.expr(rhs, None, 0)?;
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
        aliases: Option<&HashMap<String, u32>>,
    ) -> Result<pb::Action, String> {
        let (span, kind) = match action {
            ResolvedAction::Expr(span, expr) => {
                (span, pb::action::Kind::Term(self.expr(expr, aliases, 0)?))
            }
            ResolvedAction::Union(span, lhs, rhs) => {
                let lhs = self.expr(lhs, aliases, 0)?;
                let rhs = self.expr(rhs, aliases, 0)?;
                let index =
                    u32::try_from(self.program.nodes.len()).map_err(|_| "too many source nodes")?;
                let node_span = self.span(span)?;
                // Each authored action owns a fresh Union occurrence, even
                // when its member expressions match another action's members.
                self.program.nodes.push(pb::Node {
                    sort_id: self.program.nodes[lhs as usize].sort_id,
                    kind: Some(pb::node::Kind::Union(pb::Union {
                        members: vec![lhs, rhs],
                    })),
                    span: node_span,
                });
                (span, pb::action::Kind::Term(index))
            }
            ResolvedAction::Set(span, function, args, value) => (
                span,
                pb::action::Kind::Set(pb::Set {
                    target: Some(self.call(function, args, aliases, 0, span)?),
                    value: Some(self.expr(value, aliases, 0)?),
                }),
            ),
            ResolvedAction::Change(span, change, function, args) => {
                let call = self.call(function, args, aliases, 0, span)?;
                (
                    span,
                    match change {
                        ast::Change::Delete => pb::action::Kind::Delete(call),
                        ast::Change::Subsume => pb::action::Kind::Subsume(call),
                    },
                )
            }
            ResolvedAction::Panic(span, message) if aliases.is_none() => {
                (span, pb::action::Kind::Panic(message.clone()))
            }
            _ => return Err("source local bindings and rule panics are not supported yet".into()),
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
        aliases: Option<&HashMap<String, u32>>,
        depth: usize,
        span: &ast::Span,
    ) -> Result<pb::Call, String> {
        let mut children = Vec::with_capacity(args.len());
        for expr in args {
            children.push(self.expr(expr, aliases, depth + 1)?);
        }
        match function {
            ResolvedCall::Func(function) => Ok(pb::Call {
                func: function.name.clone(),
                args: children,
            }),
            ResolvedCall::Primitive(primitive) => {
                let span = self.span(span)?;
                primitive.export_builtin_call(&self.graph, &children, span, &mut self.program)
            }
        }
    }

    fn expr(
        &mut self,
        expr: &ResolvedExpr,
        aliases: Option<&HashMap<String, u32>>,
        depth: usize,
    ) -> Result<u32, String> {
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
                if !var.is_global_ref
                    && let Some(node) = aliases.and_then(|aliases| aliases.get(&var.name))
                {
                    return Ok(*node);
                }
                if var.is_global_ref && aliases.is_some() {
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
            ResolvedExpr::Call(span, function, args) => (
                if matches!(function, ResolvedCall::Func(function) if self.relations.contains(&function.name))
                {
                    "Unit"
                } else {
                    function.output().name()
                },
                if let ResolvedCall::Primitive(primitive) = function {
                    let children = args
                        .iter()
                        .map(|expr| self.expr(expr, aliases, depth + 1))
                        .collect::<Result<Vec<_>, _>>()?;
                    let span = self.span(span)?;
                    primitive.export_builtin_node(
                        &self.graph,
                        &children,
                        span,
                        &mut self.program,
                    )?
                } else {
                    pb::node::Kind::Call(self.call(function, args, aliases, depth, span)?)
                },
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

// Pure registration excludes ambient reads/writes, but its arguments may still
// construct equality values. Guard those recursively against later deletion or
// other stateful calls. Query/global capture Vars already retain their values.
fn pure_local_alias(expr: &ResolvedExpr, recreate_constructors: bool) -> bool {
    match expr {
        ResolvedExpr::Lit(..) | ResolvedExpr::Var(..) => true,
        ResolvedExpr::Call(_, call, args) => {
            let pure = match call {
                ResolvedCall::Func(function) => {
                    recreate_constructors && function.subtype == ast::FunctionSubtype::Constructor
                }
                ResolvedCall::Primitive(primitive) => primitive
                    .prim_with_id
                    .is_valid_in_context(egglog::Context::Pure),
            };
            pure && args
                .iter()
                .all(|arg| pure_local_alias(arg, recreate_constructors))
        }
    }
}

impl Iterator for Source {
    type Item = Result<pb::Program, TransportError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.advance(false).map(|result| {
            result.map(|submission| match submission {
                Submission::Program(program) => program,
                Submission::Push(_) | Submission::Pop { .. } => unreachable!(),
            })
        })
    }
}

/// Stateful, typechecking-only renderer. Tracks structural sort declarations
/// across phases; callers submit each result in order and stop on an error.
/// Experimental output can be reparsed by [`Source`] into a fresh engine, with
/// bounded aliases for nominal declarations and prepared ruleset selections.
/// Core retains its flat, named ruleset support boundary. Reuse one renderer for
/// the whole stream: aliases are stable across phases, but do not recover original keys
/// for same-engine resupply. Execution names and structural-sort limits are unchanged.
/// Use [`Self::render_submission`] for Source-managed scopes, and a fresh renderer
/// after externally resetting or popping the text environment.
pub struct Renderer {
    dialect: Dialect,
    session: Session,
    sort_names: HashMap<String, String>,
    scopes: Vec<(Session, HashMap<String, String>)>,
}

impl Default for Renderer {
    fn default() -> Self {
        Self::with_dialect(Dialect::Experimental)
    }
}

impl Renderer {
    /// Render Core text, including the admitted Run-only control trees.
    pub fn core() -> Self {
        Self::with_dialect(Dialect::Core)
    }

    fn with_dialect(dialect: Dialect) -> Self {
        Self {
            dialect,
            sort_names: HashMap::new(),
            scopes: Vec::new(),
            session: Session {
                graph: match dialect {
                    Dialect::Experimental => crate::new_experimental_egraph(),
                    Dialect::Core => EGraph::default(),
                },
                extension: None,
                mode: pb::ExecutionMode::Normal,
                definitions: pb::Program::default(),
                names: NativeNames::default(),
                request: 0,
                clone_parent: None,
                rulesets: Vec::new(),
                rules: Vec::new(),
                sorts: HashSet::new(),
            },
        }
    }
}

impl Renderer {
    /// Render ordered programs and scope controls with matching type snapshots.
    /// The snapshot excludes the scope stack; native pop retains fresh-symbol
    /// state while definitions and source aliases return to the saved scope.
    pub fn render_submission(&mut self, submission: &Submission) -> Result<String, TransportError> {
        match submission {
            Submission::Program(program) => self.render(program),
            Submission::Push(count) => {
                for _ in 0..*count {
                    self.scopes
                        .push((self.session.clone(), self.sort_names.clone()));
                }
                Ok(format!("(push {count})\n"))
            }
            Submission::Pop { count, span } => {
                for _ in 0..*count {
                    let Some((saved, names)) = self.scopes.pop() else {
                        return Err(TransportError(egglog::Error::Pop(span.clone()).to_string()));
                    };
                    let active = std::mem::replace(&mut self.session, saved);
                    let saved_graph = std::mem::replace(&mut self.session.graph, active.graph);
                    self.session.graph.restore_from(saved_graph);
                    self.session.request = active.request;
                    self.sort_names = names;
                }
                Ok(format!("(pop {count})\n"))
            }
        }
    }

    /// Validates and renders one phase, retaining only type/definition state.
    pub fn render(&mut self, program: &pb::Program) -> Result<String, TransportError> {
        // Core preserves literal names, which can collide with prepared private
        // holders. Keep its existing flat support boundary; Experimental aliases
        // nominal declarations and can reuse the adapter's installation plan.
        if self.dialect == Dialect::Core {
            let mut names: HashSet<_> = self
                .session
                .definitions
                .rulesets
                .iter()
                .filter_map(|ruleset| ruleset.name.as_deref())
                .collect();
            let mut rules = HashMap::new();
            for (index, ruleset) in program.rulesets.iter().enumerate() {
                let name = ruleset
                    .name
                    .as_deref()
                    .ok_or_else(|| TransportError("anonymous source ruleset".into()))?;
                if !names.insert(name) {
                    return Err(TransportError(
                        "source ruleset resupply is not supported yet".into(),
                    ));
                }
                let Some(pb::ruleset::Kind::Rules(leaf)) = &ruleset.kind else {
                    return Err(TransportError(
                        "unsupported source ruleset composition".into(),
                    ));
                };
                for rule in &leaf.rules {
                    if rules
                        .insert(*rule, index)
                        .is_some_and(|previous| previous != index)
                    {
                        return Err(TransportError(
                            "sharing a rule between source rulesets is not supported yet".into(),
                        ));
                    }
                }
            }
        }
        let mut lowered = program.clone();
        let prepared = self
            .session
            .prepare(&mut lowered)
            .map_err(|e| TransportError(e.0.message))?;
        let mut authored = if self.dialect == Dialect::Core {
            // Preparation filters compatible resupply from `lowered`, so use
            // the complete canonical definitions, not just this phase's names.
            let names = project_names(&mut pb::Program::default(), &prepared.definitions);
            let sorts: HashSet<_> = names.sorts.values().collect();
            for name in names.sorts.values() {
                if self.session.graph.get_sort_by_name(name).is_some() {
                    return Err(TransportError(format!(
                        "authored sort {name:?} collides with a native Core sort"
                    )));
                }
            }
            for name in names.callables.values() {
                // Core reserves container aliases before any instantiation.
                // Presort family names are not nominal sort declarations.
                if sorts.contains(name)
                    || self.session.graph.get_sort_by_name(name).is_some()
                    || self.session.graph.type_info().is_primitive(name)
                {
                    return Err(TransportError(format!(
                        "authored callable {name:?} collides with a native Core name"
                    )));
                }
            }
            names
        } else {
            // Complete reconciled indices are append-stable across resupply and
            // request-local arena/declaration order. Aliases exist only in text;
            // execution and stored definitions retain their original names.
            let mut names = NativeNames::default();
            for (index, declaration) in prepared.definitions.declarations.iter().enumerate() {
                let (namespace, logical) = match &declaration.kind {
                    Some(pb::declaration::Kind::EqSort(sort)) => ("sort", &sort.name),
                    Some(pb::declaration::Kind::Constructor(function)) => ("call", &function.name),
                    Some(pb::declaration::Kind::Function(function)) => ("call", &function.name),
                    Some(pb::declaration::Kind::Relation(relation)) => ("call", &relation.name),
                    Some(pb::declaration::Kind::Primitive(primitive)) => ("call", &primitive.name),
                    _ => continue,
                };
                // Distinct from projected unknown references and structural
                // aliases. A logical spelling equal to this alias is projected
                // normally and cannot acquire another declaration's identity.
                let alias = format!("__egglog_source_{namespace}_{index}");
                if self.session.graph.get_sort_by_name(&alias).is_some()
                    || self.session.graph.get_function(&alias).is_some()
                    || self.session.graph.type_info().is_primitive(&alias)
                {
                    return Err(TransportError(format!(
                        "source alias {alias:?} collides with a native name"
                    )));
                }
                let target = if namespace == "sort" {
                    &mut names.sorts
                } else {
                    &mut names.callables
                };
                target.insert(native_name(namespace, logical), alias);
            }
            names
        };
        let mut sort_names = self.sort_names.clone();
        let mut definitions = prepared.definitions.clone();
        project_names(&mut definitions, &prepared.definitions);
        let mut occupied: HashMap<String, String> = authored
            .sorts
            .iter()
            .chain(&authored.callables)
            .map(|(native, text)| (text.clone(), native.clone()))
            .collect();
        for sorts in [&definitions.sorts, &lowered.sorts] {
            for (index, sort) in sorts.iter().enumerate() {
                if !matches!(&sort.kind,
                Some(pb::sort::Kind::Family(family)) if !family.args.is_empty())
                    && !matches!(&sort.kind, Some(pb::sort::Kind::Func(_)))
                {
                    continue;
                }
                let Some(native) = structural_sort_name(sorts, index as u32, &mut HashSet::new())
                    .map_err(TransportError)?
                else {
                    continue;
                };
                let text = sort_names
                    .entry(native.clone())
                    .or_insert_with(|| {
                        sort.egglog_aliases
                            .first()
                            .map(|alias| alias.symbol.clone())
                            .unwrap_or_else(|| native.clone())
                    })
                    .clone();
                if occupied
                    .insert(text.clone(), native.clone())
                    .is_some_and(|old| old != native)
                    || text != native
                        && (self.session.graph.get_sort_by_name(&text).is_some()
                            || self.session.graph.get_function(&text).is_some()
                            || self.session.graph.type_info().is_primitive(&text))
                {
                    return Err(TransportError(format!(
                        "source sort alias {text:?} collides with another name"
                    )));
                }
                authored.sorts.insert(native.clone(), text.clone());
                if matches!(&sort.kind, Some(pb::sort::Kind::Func(_))) {
                    let native = egglog::sort::FunctionSort::constructor_alias(&native);
                    let text = egglog::sort::FunctionSort::constructor_alias(&text);
                    if occupied
                        .insert(text.clone(), native.clone())
                        .is_some_and(|old| old != native)
                    {
                        return Err(TransportError(format!(
                            "source function constructor {text:?} collides with another name"
                        )));
                    }
                    authored.callables.insert(native, text);
                }
            }
        }
        // Dependency analysis needs physical callable identity, before
        // PartialCall targets become the literals emitted in source.
        let declaration_order =
            declaration_order(&lowered, &mut self.session.graph).map_err(TransportError)?;
        let mut native = match self.dialect {
            Dialect::Experimental => crate::new_experimental_egraph(),
            Dialect::Core => EGraph::default(),
        };
        let mut text_native = native.clone();
        for declaration in &definitions.declarations {
            if let Some(pb::declaration::Kind::EqSort(sort)) = &declaration.kind {
                let mut command = Command::Sort {
                    span: ast::Span::Panic,
                    name: sort.name.clone(),
                    presort_and_args: None,
                    uf: None,
                    proof_func: None,
                    container_rebuild: None,
                    proof_constructors: None,
                    unionable: true,
                };
                native
                    .resolve_command_before_proofs(command.clone())
                    .map_err(|error| TransportError(error.to_string()))?;
                source_sort_names(&mut command, &authored);
                text_native
                    .resolve_command_before_proofs(command)
                    .map_err(|error| TransportError(error.to_string()))?;
            }
        }
        for (_, mut command) in
            materialize_sorts(&lowered, &mut native, &mut HashSet::new()).map_err(TransportError)?
        {
            source_sort_names(&mut command, &authored);
            text_native
                .resolve_command_before_proofs(command)
                .map_err(|error| TransportError(error.to_string()))?;
        }
        source_builtin_names(&lowered, &mut native, &mut text_native, &mut authored)
            .map_err(TransportError)?;
        // Target literals are callable references only in PartialCall.
        // Remap them before lowering; ordinary String values stay data.
        for node in &mut lowered.nodes {
            if let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::PartialCall(call)),
            })) = &mut node.kind
                && let Some(logical) = authored.callables.get(&call.func)
            {
                call.func = logical.clone();
            }
        }
        let source = render_prepared(
            &lowered,
            &prepared,
            self.dialect,
            &authored,
            &declaration_order,
        )?;
        // The renderer's graph is always NORMAL and receives definitions only:
        // registration compiles rules/merges, but no action or helper runs.
        // Installation can partially register definitions before an error.
        // Adopt neither that state nor its private-name stamp on failed render.
        let mut session = self.session.clone();
        session
            .install(
                prepared,
                &mut pb::RunProgramResponse {
                    profile: Some(pb::ProfileSummary::default()),
                    ..Default::default()
                },
            )
            .map_err(|error| TransportError(error.message))?;
        self.session = session;
        self.sort_names = sort_names;
        Ok(source)
    }
}

// A text type alias changes native specialization keys. Recover the exact core
// definition, then select its text-native instance, including output-only calls.
// Neither step decodes or manufactures private dispatch names.
fn source_builtin_names(
    program: &pb::Program,
    graph: &mut EGraph,
    text_graph: &mut EGraph,
    authored: &mut NativeNames,
) -> Result<(), String> {
    let mut text_program = pb::Program {
        sorts: program.sorts.clone(),
        ..Default::default()
    };
    for sort in &mut text_program.sorts {
        if let Some(pb::sort::Kind::Eq(name)) = &mut sort.kind
            && let Some(text) = authored.sorts.get(name)
        {
            *name = text.clone();
        }
    }
    for node in &program.nodes {
        let (call, function) = match &node.kind {
            Some(pb::node::Kind::Call(call)) => (call, None),
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::PartialCall(call)),
            })) => {
                let Some(pb::sort::Kind::Func(function)) =
                    &program.sorts[node.sort_id as usize].kind
                else {
                    return Err("partial call requires a function sort".into());
                };
                (call, Some(function))
            }
            _ => continue,
        };
        if authored.callables.contains_key(&call.func) {
            continue;
        }
        let mut arguments = call
            .args
            .iter()
            .map(|arg| program.nodes[*arg as usize].sort_id)
            .collect::<Vec<_>>();
        let output = if let Some(function) = function {
            arguments.extend(&function.params);
            function.result
        } else {
            node.sort_id
        };
        let sorts = arguments
            .iter()
            .copied()
            .chain([output])
            .map(|index| {
                let name = sort_name(&program.sorts, index)?;
                graph
                    .get_sort_by_name(&name)
                    .cloned()
                    .ok_or_else(|| format!("unknown source sort {name}"))
            })
            .collect::<Result<Vec<_>, String>>()?;
        let resolved = ResolvedCall::from_resolution(
            &call.func,
            &sorts,
            graph.type_info(),
            egglog::Context::Full,
            &ast::Span::Panic,
        )
        .map_err(|error| error.to_string())?;
        if let ResolvedCall::Primitive(primitive) = resolved {
            let core = primitive.export_builtin(&mut pb::Program::default())?;
            let sorts = sorts
                .iter()
                .map(|sort| {
                    authored
                        .sorts
                        .get(sort.name())
                        .map_or(sort.name(), String::as_str)
                })
                .collect::<Vec<_>>();
            let text = text_graph.resolve_builtin_call(
                &text_program,
                &core,
                &arguments,
                output,
                &sorts,
            )?;
            authored.callables.insert(call.func.clone(), text);
        }
    }
    Ok(())
}

fn source_sort_names(command: &mut Command, authored: &NativeNames) {
    let Command::Sort {
        name,
        presort_and_args,
        ..
    } = command
    else {
        return;
    };
    if let Some(text) = authored.sorts.get(name) {
        *name = text.clone();
    }
    if let Some((_, args)) = presort_and_args {
        for arg in args {
            if let Expr::Call(_, first, rest) = arg {
                if let Some(text) = authored.sorts.get(first) {
                    *first = text.clone();
                }
                for arg in rest {
                    if let Expr::Var(_, name) = arg
                        && let Some(text) = authored.sorts.get(name)
                    {
                        *name = text.clone();
                    }
                }
            }
            if let Expr::Var(_, name) = arg
                && let Some(text) = authored.sorts.get(name)
            {
                *name = text.clone();
            }
        }
    }
}

fn render_prepared(
    program: &pb::Program,
    prepared: &Prepared,
    dialect: Dialect,
    authored: &NativeNames,
    declaration_order: &[usize],
) -> Result<String, TransportError> {
    let result = (|| -> Result<Vec<Command>, String> {
        if program.ir_version != 1 {
            return Err("unsupported source IR version".into());
        }
        validate_union_occurrences(program)?;
        let mut native = match dialect {
            Dialect::Experimental => crate::new_experimental_egraph(),
            Dialect::Core => EGraph::default(),
        };
        validate_host_declarations(program, &mut native)?;
        // Native AST Display assumes symbols are source atoms; protobuf names
        // need not be. Validate every interpolated identifier before formatting,
        // using the native parser rather than maintaining another token grammar.
        let mut names = vec![];
        for sort in &program.sorts {
            match &sort.kind {
                Some(pb::sort::Kind::Eq(name)) => names.push(name.as_str()),
                Some(pb::sort::Kind::Family(family)) => names.push(family.name.as_str()),
                Some(pb::sort::Kind::Var(_) | pb::sort::Kind::Func(_)) => (),
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
                Some(pb::declaration::Kind::Relation(relation)) => names.push(relation.name.as_str()),
                Some(pb::declaration::Kind::Primitive(primitive)) => names.push(primitive.name.as_str()),
                _ => (),
            }
        }
        // These are the exact strings emitted by the typed AST mapping below.
        // Do not reverse-map the untyped list: binders/ruleset names can legally
        // equal a physical callable key without denoting that callable.
        names.extend(authored.sorts.values().map(String::as_str));
        names.extend(authored.callables.values().map(String::as_str));
        if dialect == Dialect::Core {
            for ruleset in &program.rulesets {
                if let Some(name) = &ruleset.name && !name.is_empty() { names.push(name.as_str()); }
            }
        }
        for command in super::command_tree(&program.commands) {
            if dialect == Dialect::Experimental && matches!(&command.kind, Some(pb::command::Kind::Repeat(_) | pb::command::Kind::Saturate(_))) {
                return Err("composite schedule rendering is unsupported: run-schedule has distinct experimental source semantics".into());
            }
            if let Some(pb::command::Kind::ProveExists(prove)) = &command.kind {
                names.push(prove.constructor.as_str());
            }
            if dialect == Dialect::Core
                && let Some(pb::command::Kind::Run(run)) = &command.kind
                && let Some(pb::ruleset_ref::Kind::Name(name)) = run.ruleset.as_ref().and_then(|reference| reference.kind.as_ref())
                && !name.is_empty()
            { names.push(name.as_str()); }
        }
        for action in super::command_tree(&program.commands).filter_map(|command| match &command.kind {
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
        commands.extend(prepared.materialized.iter().cloned());
        for &index in declaration_order {
            let declaration = &program.declarations[index];
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
                    pb::declaration::Kind::Primitive(primitive) => {
                        if dialect == Dialect::Core {
                            return Err("program-defined primitive source requires the Experimental provider".into());
                        }
                        primitive_command(program, primitive, span)?
                    },
                    pb::declaration::Kind::Relation(relation) => Command::Relation {
                        span,
                        name: relation.name.clone(),
                        inputs: relation.inputs.iter().map(|arg| sort_name(&program.sorts, arg.sort)).collect::<Result<_, _>>()?,
                    },
                    pb::declaration::Kind::HostPrimitive(_) | pb::declaration::Kind::HostSortFamily(_) => continue,
                },
            );
        }
        if dialect == Dialect::Experimental {
            // Native handles and canonical rules are aligned by occurrence, not
            // label/body equality. Change presentation only, never Prepared.
            let labels: HashMap<_, _> = prepared.rules.iter().zip(&prepared.definitions.rules)
                .map(|(native, rule)| (native.as_str(), rule.name.as_deref().unwrap_or("")))
                .collect();
            let function_constructors: HashSet<_> = program.sorts.iter().enumerate()
                .filter(|(_, sort)| matches!(sort.kind, Some(pb::sort::Kind::Func(_))))
                // Signature patterns have no native constructor. Only closed
                // function sorts were materialized into the runtime graph.
                .filter_map(|(index, _)| structural_sort_name(&program.sorts, index as u32, &mut HashSet::new()).transpose())
                .map(|name| name
                    .map(|name| egglog::sort::FunctionSort::constructor_alias(&name)))
                .collect::<Result<_, _>>()?;
            for installation in &prepared.installations {
                if !matches!(installation.site, pb::maintenance_site::Target::Ruleset(_)) {
                    continue;
                }
                let Some(mut command) = installation.command.clone() else { continue };
                let name = match &mut command {
                    Command::Rule { rule } => Some(&mut rule.name),
                    Command::Rewrite(_, rewrite, _) | Command::BiRewrite(_, rewrite) => Some(&mut rewrite.name),
                    _ => None,
                };
                if let Some(name) = name {
                    *name = labels.get(name.as_str()).ok_or("missing prepared rule label")?.to_string();
                }
                // PartialCall's first String is a typed callable reference.
                // Other String literals, including identical spellings, are data.
                command = command.visit_exprs(&mut |mut expr| {
                    if let Expr::Call(_, head, args) = &mut expr
                        && function_constructors.contains(head)
                        && let Some(Expr::Lit(_, Literal::String(target))) = args.first_mut()
                        && let Some(alias) = authored.callables.get(target)
                    {
                        *target = alias.clone();
                    }
                    expr
                });
                commands.push(command);
            }
        } else {
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
        }
        for mut command in &program.commands {
            let mut fail_spans = vec![];
            while let Some(pb::command::Kind::Fail(child)) = &command.kind {
                fail_spans.push(native_span(program, command.span.as_ref())?);
                command = child;
            }
            if !(fail_spans.is_empty() || matches!(
                &command.kind,
                Some(pb::command::Kind::Action(_)
                    | pb::command::Kind::Check(_)
                    | pb::command::Kind::Prove(_)
                    | pb::command::Kind::ProveExists(_)
                    | pb::command::Kind::Run(_)
                    | pb::command::Kind::Stats(_))
            ) || dialect == Dialect::Core && matches!(
                &command.kind,
                Some(pb::command::Kind::Repeat(_) | pb::command::Kind::Saturate(_))
            ))
            {
                return Err("Fail requires a supported native command; observation and loop wrappers are not implemented".into());
            }
            let first_command = commands.len();
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
                pb::command::Kind::Stats(_) => {
                    commands.push(Command::PrintOverallStatistics(span, None));
                }
                pb::command::Kind::Prove(prove) => {
                    commands.push(Command::Prove(span, facts(program, &prove.facts)?))
                }
                pb::command::Kind::ProveExists(prove) => {
                    commands.push(Command::ProveExists(span, prove.constructor.clone()))
                }
                pb::command::Kind::PrintFunction(print) => {
                    commands.push(Command::PrintFunction(
                        span, print.table.clone(),
                        print.max_rows.map(usize::try_from).transpose().map_err(|_| "table row limit exceeds native usize")?,
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
                pb::command::Kind::Run(_)
                | pb::command::Kind::Repeat(_)
                | pb::command::Kind::Saturate(_) => {
                    commands.push(Command::RunSchedule(source_schedule(
                        program, command, (dialect == Dialect::Experimental).then_some(&prepared.context),
                    )?));
                }
                _ => return Err("unsupported source command".into()),
            }
            if !fail_spans.is_empty() {
                if commands.len() != first_command + 1 {
                    return Err("Fail requires exactly one native command".into());
                }
                let mut command = commands.pop().unwrap();
                for span in fail_spans.into_iter().rev() {
                    command = Command::Fail(span, Box::new(command));
                }
                commands.push(command);
            }
        }
        for command in &mut commands {
            *command = command.clone().map_symbols(
                &mut |name: String| authored.callables.get(&name).cloned().unwrap_or(name),
                &mut |name| name,
            );
            let mut leaf = command;
            while let Command::Fail(_, child) = leaf {
                leaf = child;
            }
            source_sort_names(leaf, authored);
            match leaf {
                Command::Constructor { name, schema, .. }
                | Command::Function { name, schema, .. } => {
                    if let Some(logical) = authored.callables.get(name) {
                        *name = logical.clone();
                    }
                    for name in schema.input.iter_mut().chain([&mut schema.output]) {
                        if let Some(logical) = authored.sorts.get(name) {
                            *name = logical.clone();
                        }
                    }
                }
                Command::Relation { name, inputs, .. } => {
                    if let Some(logical) = authored.callables.get(name) {
                        *name = logical.clone();
                    }
                    for name in inputs {
                        if let Some(logical) = authored.sorts.get(name) {
                            *name = logical.clone();
                        }
                    }
                }
                Command::UserDefined(_, command, args) if command == "primitive" => {
                    // Generic map_symbols deliberately skips UserDefined.
                    // This generated command has typed declaration/signature
                    // positions; only its body has callable heads and binders.
                    let [Expr::Var(_, name), inputs, Expr::Var(_, output), body] = args.as_mut_slice() else {
                        return Err("malformed generated primitive declaration".into());
                    };
                    if let Some(alias) = authored.callables.get(name) { *name = alias.clone(); }
                    *inputs = inputs.clone().map_symbols(
                        &mut |name: String| authored.sorts.get(&name).cloned().unwrap_or(name),
                        &mut |name: String| authored.sorts.get(&name).cloned().unwrap_or(name),
                    );
                    if let Some(alias) = authored.sorts.get(output) { *output = alias.clone(); }
                    *body = body.clone().map_symbols(
                        &mut |name: String| authored.callables.get(&name).cloned().unwrap_or(name),
                        &mut |name| name,
                    );
                }
                Command::PrintFunction(_, name, ..) => {
                    if let Some(logical) = authored.callables.get(name) {
                        *name = logical.clone();
                    }
                }
                _ => (),
            }
        }
        // Atom validity is insufficient in action position: a function named
        // `panic` would print as a Panic action, and `include` becomes a command
        // only at top level. Check the actual parse context, with the current
        // selected command registry, before returning executable text.
        for mut command in &commands {
            while let Command::Fail(_, child) = command {
                command = child;
            }
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
        .map(|mut command| {
            let mut fail_depth = 0;
            while let Command::Fail(_, child) = command {
                fail_depth += 1;
                command = *child;
            }
            // The experimental parser shadows run-schedule with a callback
            // command, which cannot be proof-instrumented. The admitted flat
            // native Run needs its unshadowed spelling even beneath Fail.
            let leaf = match command {
                Command::RunSchedule(ast::Schedule::Run(_, config)) => {
                    format!("(run {} 1)", config.ruleset)
                }
                Command::RunSchedule(schedule) => {
                    format!("(run-schedule {})", render_schedule(&schedule))
                }
                command => command.to_string(),
            };
            format!(
                "{}{leaf}{}\n",
                "(fail ".repeat(fail_depth),
                ")".repeat(fail_depth)
            )
        })
        .collect())
}

// Preserve the wire distinction between exact Repeat1 (an explicit seq) and
// bounded Saturate1 (a native repeat). The executor's normalization deliberately
// erases that syntactic distinction, so it is not the source inverse.
fn source_schedule(
    program: &pb::Program,
    command: &pb::Command,
    context: Option<&RequestOccurrences>,
) -> Result<ast::Schedule, String> {
    let span = native_span(program, command.span.as_ref())?;
    let (body, bound, sequence) = match command.kind.as_ref().ok_or("missing schedule")? {
        pb::command::Kind::Run(run) if run.scheduler.is_empty() => {
            let reference = run
                .ruleset
                .as_ref()
                .and_then(|r| r.kind.as_ref())
                .ok_or("missing ruleset reference")?;
            let name = match (context, reference) {
                (Some(context), pb::ruleset_ref::Kind::Name(name)) => context
                    .names
                    .get(name)
                    .ok_or("invalid source ruleset reference")?,
                (Some(context), pb::ruleset_ref::Kind::Index(index)) => context
                    .rulesets
                    .get(*index as usize)
                    .ok_or("invalid source ruleset reference")?,
                (None, pb::ruleset_ref::Kind::Name(name)) => name,
                (None, pb::ruleset_ref::Kind::Index(index)) => program
                    .rulesets
                    .get(*index as usize)
                    .and_then(|ruleset| ruleset.name.as_ref())
                    .ok_or("invalid source ruleset reference")?,
            };
            return Ok(ast::Schedule::Run(
                span,
                ast::RunConfig {
                    ruleset: name.clone(),
                    until: None,
                },
            ));
        }
        pb::command::Kind::Repeat(repeat)
            if matches!(repeat.times, Some(0 | 1)) && repeat.until.is_empty() =>
        {
            (&repeat.body, repeat.times, repeat.times == Some(1))
        }
        pb::command::Kind::Saturate(saturate)
            if saturate.until.is_empty() && saturate.max_iterations != Some(0) =>
        {
            (&saturate.body, saturate.max_iterations, false)
        }
        _ => {
            return Err(
                "source schedules require Run, Repeat0/1 or Saturate without until or scheduler"
                    .into(),
            );
        }
    };
    let children = body
        .iter()
        .map(|child| source_schedule(program, child, context))
        .collect::<Result<_, _>>()?;
    let body = ast::Schedule::Sequence(span.clone(), children);
    Ok(if sequence {
        body
    } else if let Some(bound) = bound {
        ast::Schedule::Repeat(
            span,
            usize::try_from(bound).map_err(|_| "source loop bound exceeds usize")?,
            Box::new(body),
        )
    } else {
        ast::Schedule::Saturate(span, Box::new(body))
    })
}

// A repeat/saturate's immediate Sequence is its parser body-list envelope,
// unlike an explicit seq child. Native Display prints both as seq and would
// insert another canonical Repeat1 when Source reimports the text.
fn render_schedule(schedule: &ast::Schedule) -> String {
    let (head, children) = match schedule {
        ast::Schedule::Run(_, config) => return format!("(run {})", config.ruleset),
        ast::Schedule::Sequence(_, children) => ("seq".to_owned(), children.as_slice()),
        ast::Schedule::Repeat(_, _, body) | ast::Schedule::Saturate(_, body) => {
            let head = match schedule {
                ast::Schedule::Repeat(_, bound, _) => format!("repeat {bound}"),
                _ => "saturate".to_owned(),
            };
            let ast::Schedule::Sequence(_, children) = body.as_ref() else {
                unreachable!("source_schedule emits one loop body-list envelope")
            };
            (head, children.as_slice())
        }
    };
    let mut text = format!("({head}");
    for child in children {
        text.push(' ');
        text.push_str(&render_schedule(child));
    }
    text.push(')');
    text
}
