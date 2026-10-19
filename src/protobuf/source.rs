//! Sequential, typechecking-only source producer for the initial protobuf slice.
//!
//! Submit each yielded program through the byte adapter before requesting the
//! next one, and stop on a transport or decoded execution error. Parsing is eager
//! (like native source execution); resolution is sequential so a later type error
//! does not erase an executed prefix. Native syntax is never executed here.
//! Scope-aware callers use [`Source::next_submission`] and the existing clone /
//! return requests; the Program iterator deliberately rejects scope operations.
//! Selected rulesets are immutable snapshots; later source additions publish
//! occurrence-preserving prefix/delta versions. Uncatalogued primitives, effectful local lets,
//! named cost models remain unsupported. Experimental constructor annotations use
//! the native cost macros with their actual provenance. The explicit Core
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

// Cleanup must address the retained key, not reevaluate an equal-looking call
// after deletion. The two source uses naturally have different spans.
fn retained_cost_key<H, V: PartialEq>(
    left: &[ast::GenericExpr<H, V>],
    right: &[ast::GenericExpr<H, V>],
) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| match (left, right) {
                (ast::GenericExpr::Var(_, left), ast::GenericExpr::Var(_, right)) => left == right,
                (ast::GenericExpr::Lit(_, left), ast::GenericExpr::Lit(_, right)) => left == right,
                _ => false,
            })
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

#[derive(Clone)]
struct SourceRuleset {
    kind: pb::ruleset::Kind,
    span: Option<pb::Span>,
    version: Option<usize>,
    published_rules: usize,
}

// Source aliases may have different physical spellings. Retain authored table
// provenance so two native tables cannot silently become compatible resupply of
// one wire declaration. Graph snapshots restore this index with its scope.
#[derive(Clone, Default)]
struct SourceTableNames(HashMap<String, String>);

struct SourceScope {
    graph: EGraph,
    program: pb::Program,
    rulesets: HashMap<String, SourceRuleset>,
    relations: HashSet<String>,
    schedulers: HashSet<String>,
    local_prefix: String,
}

/// A source stream whose authored declarations, expressions and rules become
/// protobuf records. The native graph holds only the producer's type environment.
pub struct Source {
    dialect: Dialect,
    mode: Option<pb::ExecutionMode>,
    started: bool,
    graph: EGraph,
    // Keep the explicit provider alive for this type environment and its scopes.
    // Scope graphs inherit registrations; they never initialize it again.
    _extension: Option<Arc<dyn NativeExtension>>,
    commands: VecDeque<(Command, usize)>,
    include_base: PathBuf,
    scopes: Vec<SourceScope>,
    program: pb::Program,
    rulesets: HashMap<String, SourceRuleset>,
    relations: HashSet<String>,
    // Names only: the producer must never instantiate or run a scheduler.
    schedulers: HashSet<String>,
    local_prefix: String,
    // Native fresh names survive Pop; never reuse a discarded version's name.
    next_ruleset: u64,
    cost_origins: std::sync::Arc<std::sync::Mutex<crate::set_cost::CostOrigins>>,
    pending_error: Option<String>,
}

struct InputSignature {
    table: String,
    inputs: Vec<u32>,
    output: u32,
    custom: bool,
}

// The rows are already completely parsed. Publishing only here prevents a
// malformed later row from leaving any CSV-derived commands behind.
fn append_input_rows(
    program: &mut pb::Program,
    target: InputSignature,
    rows: Vec<Vec<Literal>>,
    span: Option<pb::Span>,
) -> Result<(), String> {
    for row in rows {
        let mut values = Vec::with_capacity(row.len());
        for (literal, sort_id) in row.into_iter().zip(
            target
                .inputs
                .iter()
                .copied()
                .chain(target.custom.then_some(target.output)),
        ) {
            let value = match literal {
                Literal::Int(value) => pb::primitive_value::Value::I64(value),
                Literal::Float(value) => pb::primitive_value::Value::F64Bits(value.0.to_bits()),
                Literal::String(value) => pb::primitive_value::Value::String(value),
                Literal::Bool(value) => pb::primitive_value::Value::Bool(value),
                Literal::Unit => pb::primitive_value::Value::Unit(pb::Unit {}),
            };
            values.push(u32::try_from(program.nodes.len()).map_err(|_| "too many input nodes")?);
            program.nodes.push(pb::Node {
                sort_id,
                span,
                kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(value),
                })),
            });
        }
        let value = target
            .custom
            .then(|| values.pop().expect("parsed output column"));
        let call = pb::Call {
            func: target.table.clone(),
            args: values,
        };
        let kind = if let Some(value) = value {
            pb::action::Kind::Set(pb::Set {
                target: Some(call),
                value: Some(value),
            })
        } else {
            let root = u32::try_from(program.nodes.len()).map_err(|_| "too many input nodes")?;
            program.nodes.push(pb::Node {
                sort_id: target.output,
                span,
                kind: Some(pb::node::Kind::Call(call)),
            });
            pb::action::Kind::Term(root)
        };
        program.commands.push(pb::Command {
            span,
            kind: Some(pb::command::Kind::Action(pb::Action {
                span,
                kind: Some(kind),
            })),
        });
    }
    Ok(())
}

/// Resolve an exact declaration-only descriptor and decode a complete native
/// tab-separated input file into ordinary ordered actions. No live graph or
/// filesystem dependency is retained in the returned, self-contained Program.
pub fn produce_input(
    descriptor: &pb::Program,
    table: &str,
    path: &str,
    fact_directory: Option<&Path>,
    extension: Option<Arc<dyn NativeExtension>>,
) -> Result<pb::Program, TransportError> {
    if !descriptor.commands.is_empty()
        || !descriptor.rulesets.is_empty()
        || !descriptor.rules.is_empty()
    {
        return Err(TransportError(
            "input descriptor must contain declarations only".into(),
        ));
    }
    let mut compiler = if let Some(extension) = extension {
        Renderer::with_extension(extension)?
    } else {
        Renderer::default()
    };
    let mut lowered = descriptor.clone();
    let prepared = compiler
        .session
        .prepare(&mut lowered)
        .map_err(|error| TransportError(error.0.message))?;
    compiler
        .session
        .install(
            prepared,
            &mut pb::RunProgramResponse {
                profile: Some(pb::ProfileSummary::default()),
                ..Default::default()
            },
        )
        .map_err(|error| TransportError(error.message))?;
    let signature = compiler
        .session
        .graph
        .authoring_type_info()
        .get_func_type(&native_name("call", table))
        .cloned()
        .ok_or_else(|| TransportError(format!("unknown input table {table}")))?;
    let declaration = descriptor
        .declarations
        .iter()
        .find_map(|declaration| match &declaration.kind {
            Some(pb::declaration::Kind::Function(function)) if function.name == table => {
                Some(InputSignature {
                    table: table.into(),
                    inputs: function.inputs.iter().map(|arg| arg.sort).collect(),
                    output: function.output,
                    custom: true,
                })
            }
            Some(pb::declaration::Kind::Constructor(constructor)) if constructor.name == table => {
                Some(InputSignature {
                    table: table.into(),
                    inputs: constructor.inputs.iter().map(|arg| arg.sort).collect(),
                    output: constructor.output,
                    custom: false,
                })
            }
            Some(pb::declaration::Kind::Relation(relation)) if relation.name == table => {
                Some(InputSignature {
                    table: table.into(),
                    inputs: relation.inputs.iter().map(|arg| arg.sort).collect(),
                    output: 0,
                    custom: false,
                })
            }
            _ => None,
        })
        .ok_or_else(|| TransportError("input requires a table-backed callable".into()))?;
    let mut program = descriptor.clone();
    let file = u32::try_from(program.files.len())
        .map_err(|_| TransportError("too many input source files".into()))?;
    program.files.push(pb::SourceFile {
        name: path.into(),
        // A displayable empty diagnostic excerpt, not the CSV contents.
        contents: Some(String::new()),
    });
    let span = Some(pb::Span {
        file,
        start: 0,
        end: 0,
    });
    let native_spans = NativeSpans::default();
    let rows = egglog::parse_input_file(
        &signature,
        path,
        fact_directory,
        native_span(&program, span.as_ref(), &native_spans).map_err(TransportError)?,
    )
    .map_err(|error| TransportError(error.to_string()))?;
    let mut declaration = declaration;
    if descriptor.declarations.iter().any(|row| matches!(&row.kind, Some(pb::declaration::Kind::Relation(relation)) if relation.name == table)) {
        let unit = compiler.session.graph.authoring_type_info().get_sort_by_name("Unit").unwrap();
        declaration.output = compiler.session.graph.export_sort(unit, &mut program.sorts).map_err(TransportError)?;
    }
    append_input_rows(&mut program, declaration, rows, span).map_err(TransportError)?;
    Ok(program)
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
        mode: None,
        started: false,
        graph: graph.clone(),
        _extension: None,
        commands: VecDeque::new(),
        include_base: PathBuf::new(),
        scopes: Vec::new(),
        program: pb::Program {
            ir_version: 1,
            ..Default::default()
        },
        rulesets: HashMap::new(),
        relations: HashSet::new(),
        schedulers: HashSet::new(),
        local_prefix: String::new(),
        next_ruleset: 0,
        cost_origins: Default::default(),
        pending_error: None,
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
        Self::with_dialect(filename, source, Dialect::Experimental, None)
    }

    /// Parses Experimental source with explicit native provider definitions.
    /// Registration is inert and precedes parsing; no source/payload executes.
    pub fn with_extension(
        filename: Option<String>,
        source: &str,
        extension: Arc<dyn NativeExtension>,
    ) -> Result<Self, TransportError> {
        Self::with_dialect(filename, source, Dialect::Experimental, Some(extension))
    }

    /// Parses Core source, including Run-only controls without custom schedulers.
    /// This is an explicit frontend choice, not a wire execution setting.
    pub fn new_core(filename: Option<String>, source: &str) -> Result<Self, TransportError> {
        Self::with_dialect(filename, source, Dialect::Core, None)
    }

    fn with_dialect(
        filename: Option<String>,
        source: &str,
        dialect: Dialect,
        extension: Option<Arc<dyn NativeExtension>>,
    ) -> Result<Self, TransportError> {
        let mut graph = match dialect {
            Dialect::Experimental => crate::new_experimental_egraph(),
            Dialect::Core => EGraph::default(),
        };
        if let Some(extension) = &extension {
            extension.initialize(&mut graph).map_err(TransportError)?;
        }
        let cost_origins = if dialect == Dialect::Experimental {
            crate::set_cost::record_cost_origins(&mut graph)
        } else {
            Default::default()
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
            mode: None,
            started: false,
            graph,
            _extension: extension,
            commands,
            include_base: PathBuf::new(),
            scopes: Vec::new(),
            program: pb::Program {
                ir_version: 1,
                ..Default::default()
            },
            rulesets: HashMap::from([(
                String::new(),
                SourceRuleset {
                    kind: pb::ruleset::Kind::Rules(pb::RuleList::default()),
                    span: None,
                    version: None,
                    published_rules: 0,
                },
            )]),
            relations: HashSet::new(),
            schedulers: HashSet::new(),
            local_prefix,
            next_ruleset: 0,
            cost_origins,
            pending_error: None,
        })
    }

    /// Select the immutable receiving mode before producing any submission.
    /// This follows native source admission and global lowering in that mode;
    /// it does not change the meaning of an ordinary wire Function.
    pub fn with_execution_mode(mut self, mode: pb::ExecutionMode) -> Result<Self, TransportError> {
        if self.started || self.mode.is_some() {
            return Err(TransportError(
                "source execution mode is already fixed".into(),
            ));
        }
        self.graph = match mode {
            pb::ExecutionMode::Normal => self.graph,
            pb::ExecutionMode::TermEncoding => self.graph.with_term_encoding_enabled(),
            pb::ExecutionMode::Proofs => self.graph.with_proofs_enabled(),
            // Preserve authored Check commands; the receiving engine owns
            // ProofTesting's conversion into proof requests.
            pb::ExecutionMode::ProofTesting => self.graph.with_proofs_enabled(),
        };
        self.mode = Some(mode);
        Ok(self)
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
        self.started = true;
        if let Some(error) = self.pending_error.take() {
            self.commands.clear();
            return Some(Err(TransportError(error)));
        }
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
                            relations: self.relations.clone(),
                            schedulers: self.schedulers.clone(),
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
                        self.relations = saved.relations;
                        self.schedulers = saved.schedulers;
                        self.local_prefix = saved.local_prefix;
                    }
                    break Ok(Submission::Pop { count, span });
                }
                Command::Push(_) | Command::Pop(..) => {
                    break Err(
                        "source scopes require next_submission and clone/return requests".into(),
                    );
                }
                command => {
                    let cost_start = match &command {
                        Command::Action(Action::Let(_, name, _)) => {
                            self.cost_origins.lock().unwrap().starts.get(name).cloned()
                        }
                        Command::Action(Action::Expr(span, _)) => self
                            .cost_origins
                            .lock()
                            .unwrap()
                            .sets
                            .get(span)
                            .filter(|(_, arity)| *arity == 0)
                            .map(|_| (span.clone(), Vec::new())),
                        _ => None,
                    };
                    if let Some((span, captures)) = cost_start {
                        break self
                            .cost_phase(command, span, captures, None)
                            .map(Submission::Program);
                    }
                    if let Command::Action(Action::Let(_, first, _)) = &command {
                        let mut captures = vec![first.clone()];
                        for (command, _) in &self.commands {
                            let Command::Action(Action::Let(_, name, _)) = command else {
                                break;
                            };
                            captures.push(name.clone());
                        }
                        let next = captures.len() - 1;
                        if let Some((
                            Command::Action(Action::Change(
                                span,
                                ast::Change::Delete,
                                constructor,
                                key,
                            )),
                            _,
                        )) = self.commands.get(next)
                            && let Some((
                                Command::Action(Action::Change(
                                    _,
                                    ast::Change::Delete,
                                    helper,
                                    helper_key,
                                )),
                                _,
                            )) = self.commands.get(next + 1)
                            && self
                                .graph
                                .extension_state::<crate::set_cost::SourceCostRoles>()
                                .and_then(|roles| roles.0.get(helper))
                                == Some(constructor)
                            && retained_cost_key(key, helper_key)
                            && key.len() == captures.len()
                            && key.iter().zip(&captures).all(
                                |(arg, name)| matches!(arg, Expr::Var(_, used) if used == name),
                            )
                        {
                            let constructor = constructor.clone();
                            let span = span.clone();
                            break self
                                .cost_phase(command, span, captures, Some(constructor))
                                .map(Submission::Program);
                        }
                    }
                    // A native dynamic helper is separate storage. Admit a
                    // deletion only with the exact adjacent cleanup emitted by
                    // Renderer; wire Delete performs that same paired cleanup.
                    if let Command::Action(Action::Change(_, ast::Change::Delete, target, args)) =
                        &command
                        && let Some(helper) = self
                            .graph
                            .extension_state::<crate::set_cost::SourceCostRoles>()
                            .and_then(|roles| {
                                roles
                                    .0
                                    .iter()
                                    .find(|(_, constructor)| *constructor == target)
                                    .map(|(helper, _)| helper.clone())
                            })
                    {
                        if !matches!(self.commands.front(), Some((Command::Action(Action::Change(_, ast::Change::Delete, name, key)), _)) if *name == helper && retained_cost_key(key, args))
                        {
                            break Err("dynamic-cost constructor deletion requires its exact adjacent helper cleanup".into());
                        }
                        self.commands.pop_front();
                    }
                    break self.compile(command).map(Submission::Program);
                }
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
        let types = self.graph.authoring_type_info().clone();
        let mut expanded = macros
            .apply(command, &mut self.graph.parser.symbol_gen, &types)
            .map_err(|error| error.to_string())?;
        if expanded.len() == 1 {
            return self.compile_expanded(expanded, explicit_sort_alias);
        }
        // Native fresh expansion declares its keyed constructor, then installs
        // the rewritten rule. Both fit one authored phase. Arbitrary vectors
        // cannot be combined: Program declarations precede runtime commands.
        if !matches!(
            expanded.as_slice(),
            [Command::Constructor { .. }, Command::Rule { .. }]
        ) {
            return Err(
                "multi-command source macros require separate ordered submission phases".into(),
            );
        }
        let rule = expanded.pop().unwrap();
        let mut prefix = self.compile_expanded(expanded, None)?;
        let program = self.program.clone();
        let rulesets = self.rulesets.clone();
        match self.compile_expanded(vec![rule], None) {
            Ok(mut complete) => {
                prefix.declarations.append(&mut complete.declarations);
                complete.declarations = prefix.declarations;
                Ok(complete)
            }
            Err(error) => {
                // Native retains the constructor if its later rule fails. Do
                // not export any nodes or publication state from that child.
                self.program = program;
                self.rulesets = rulesets;
                self.pending_error = Some(error);
                Ok(prefix)
            }
        }
    }

    // Lower already expanded commands without applying user macros again.
    fn compile_expanded(
        &mut self,
        expanded: Vec<Command>,
        explicit_sort_alias: Option<String>,
    ) -> Result<pb::Program, String> {
        let encoded = self
            .mode
            .is_some_and(|mode| mode != pb::ExecutionMode::Normal);
        // These single-command phases need real empty table backends for later
        // literal function captures. Fail also retains a global Let's header.
        // Compile before recording headers; preserving-globals export below
        // still supplies all wire metadata.
        let mut compiler = match expanded.as_slice() {
            [command] => {
                let mut header = command;
                while let Command::Fail(_, child) = header {
                    header = child;
                }
                if matches!(
                    header,
                    Command::Datatype { .. }
                        | Command::Datatypes { .. }
                        | Command::Relation { .. }
                        | Command::Constructor { .. }
                        | Command::Function { .. }
                        | Command::Action(Action::Let(..))
                ) || (encoded && matches!(header, Command::Sort { .. }))
                {
                    let mut graph = self.graph.clone();
                    // Source already expanded this command. Suppress a second
                    // provider transform only in the disposable compiler context.
                    let macros = std::mem::take(graph.command_macros_mut());
                    let mut compiler = graph
                        .validate_program(vec![command.clone()])
                        .map_err(|error| error.to_string())?;
                    *compiler.command_macros_mut() = macros;
                    Some(compiler)
                } else {
                    None
                }
            }
            _ => None,
        };
        let mut publish = vec![];
        for mut command in expanded {
            let mut fail_spans = vec![];
            while let Command::Fail(span, child) = command {
                fail_spans.push(span);
                command = *child;
            }
            if let Command::Input { span, name, file } = &command {
                let parsed = (|| {
                    let signature = self
                        .graph
                        .authoring_type_info()
                        .get_func_type(name)
                        .cloned()
                        .ok_or_else(|| {
                            egglog::Error::TypeError(egglog::TypeError::UnboundFunction(
                                name.clone(),
                                span.clone(),
                            ))
                        })?;
                    let rows = egglog::parse_input_file(
                        &signature,
                        file,
                        self.graph.fact_directory.as_deref(),
                        span.clone(),
                    )?;
                    Ok::<_, egglog::Error>((signature, rows))
                })();
                let (signature, rows) = match parsed {
                    Ok(parsed) => parsed,
                    Err(error) => {
                        let mut result = Err(error);
                        for span in fail_spans.into_iter().rev() {
                            result = if result.is_err() {
                                Ok(())
                            } else {
                                Err(egglog::Error::ExpectFail(span))
                            };
                        }
                        result.map_err(|error| error.to_string())?;
                        continue;
                    }
                };
                let inputs = signature
                    .input
                    .iter()
                    .map(|sort| self.sort(sort.name()))
                    .collect::<Result<Vec<_>, _>>()?;
                let output = self.sort(if self.relations.contains(name) {
                    "Unit"
                } else {
                    signature.output.name()
                })?;
                let first = self.program.commands.len();
                let located = self.span(span)?;
                append_input_rows(
                    &mut self.program,
                    InputSignature {
                        table: name.clone(),
                        inputs,
                        output,
                        custom: signature.subtype == ast::FunctionSubtype::Custom,
                    },
                    rows,
                    located,
                )?;
                if !fail_spans.is_empty() {
                    let body = self.program.commands.drain(first..).collect();
                    let mut command = pb::Command {
                        span: located,
                        kind: Some(pb::command::Kind::Repeat(pb::Repeat {
                            times: Some(1),
                            body,
                            until: vec![],
                        })),
                    };
                    for span in fail_spans.into_iter().rev() {
                        command = pb::Command {
                            span: self.span(&span)?,
                            kind: Some(pb::command::Kind::Fail(Box::new(command))),
                        };
                    }
                    self.program.commands.push(command);
                }
                continue;
            }
            if !fail_spans.is_empty()
                && !matches!(
                    &command,
                    Command::Check(..)
                        | Command::Prove(..)
                        | Command::ProveExists(..)
                        | Command::Action(..)
                        | Command::ActionScope(..)
                        | Command::RunSchedule(..)
                        | Command::PrintOverallStatistics(_, None)
                )
                && !matches!(&command, Command::UserDefined(_, name, _) if name == "run-schedule")
            {
                return Err("source Fail requires a supported native command; declarations and observations are not implemented".into());
            }
            let first_command = self.program.commands.len();
            // Keep provenance until export: desugaring alone cannot distinguish
            // a relation's generated constructor or an authored rewrite.
            let rewrite = match &command {
                Command::Rewrite(_, _, subsume) => Some(RewriteKind::Directional(*subsume)),
                Command::BiRewrite(..) => Some(RewriteKind::Bidirectional),
                Command::Relation {
                    span, name, inputs, ..
                } => {
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
            let mut source_extractor = pb::Extractor::Tree;
            let command = match command {
                Command::Prove(span, facts) => Command::Check(span, facts),
                // The experimental parser deliberately shadows core extract.
                // With no cost-mutating commands in this slice its default tree
                // model agrees with static constructor costs. Do not execute the
                // UserDefined command to discover/resolve its arguments.
                Command::UserDefined(span, name, args) if name == "extract" => {
                    let (args, greedy) = crate::greedy_dag_extract::split_trailing_extractor(&args)
                        .map_err(|error| error.to_string())?;
                    if greedy {
                        source_extractor = pb::Extractor::GreedyDag;
                    }
                    let (expr, variants) = match args {
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
                Command::UserDefined(span, name, args) if name == "multi-extract" => {
                    let parsed = crate::parse_multi_extract_args(&args)
                        .map_err(|error| error.to_string())?;
                    let Expr::Lit(_, Literal::Int(count)) = parsed.variants else {
                        return Err(
                            "source multi-extract requires a positive literal i64 count".into()
                        );
                    };
                    let count = u32::try_from(*count)
                        .ok()
                        .filter(|count| *count > 0)
                        .ok_or("source multi-extract count must be positive and fit wire u32")?;
                    let mut roots = Vec::with_capacity(parsed.roots.len());
                    for root in parsed.roots {
                        let resolved = self
                            .graph
                            .resolve_command_preserving_globals(Command::Action(Action::Expr(
                                root.span(),
                                root.clone(),
                            )))
                            .map_err(|error| error.to_string())?;
                        let [N::CoreAction(ResolvedAction::Expr(_, root))] = resolved.as_slice()
                        else {
                            return Err("source multi-extract root resolution shape changed".into());
                        };
                        roots.push(self.expr(root, None, 0)?);
                    }
                    let span = self.span(&span)?;
                    self.program.commands.push(pb::Command {
                        span,
                        kind: Some(pb::command::Kind::Extract(pb::Extract {
                            roots,
                            variants: count,
                            extractor: if parsed.greedy {
                                pb::Extractor::GreedyDag
                            } else {
                                pb::Extractor::Tree
                            }
                            .into(),
                            ..Default::default()
                        })),
                    });
                    continue;
                }
                Command::UserDefined(span, name, args) if name == "keep-best" => {
                    let (args, greedy) = crate::greedy_dag_extract::split_trailing_extractor(&args)
                        .map_err(|error| error.to_string())?;
                    if args.is_empty() {
                        return Err("source keep-best requires literal table names".into());
                    }
                    let tables = args
                        .iter()
                        .map(|arg| {
                            let Expr::Lit(_, Literal::String(name)) = arg else {
                                return Err(
                                    "source keep-best requires literal table names".to_string()
                                );
                            };
                            self.graph
                                .authoring_type_info()
                                .get_func_type(name)
                                .ok_or_else(|| format!("unknown keep-best table {name}"))?;
                            Ok(name.clone())
                        })
                        .collect::<Result<_, String>>()?;
                    let span = self.span(&span)?;
                    self.program.commands.push(pb::Command {
                        span,
                        kind: Some(pb::command::Kind::KeepBest(pb::KeepBest {
                            tables,
                            extractor: if greedy {
                                pb::Extractor::GreedyDag
                            } else {
                                pb::Extractor::Tree
                            }
                            .into(),
                            ..Default::default()
                        })),
                    });
                    continue;
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
                command @ Command::UserDefined(..) if matches!(&command, Command::UserDefined(_, name, _) if matches!(name.as_str(), "let-scheduler" | "run-schedule")) => {
                    command
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
                    .authoring_type_info()
                    .get_sort_by_name(name)
                    .ok_or("missing resolved source sort")?
                    .clone();
                let mut sorts = self.program.sorts.clone();
                let index = graph.export_sort(&native, &mut sorts)?;
                let mut existing = self
                    .graph
                    .authoring_type_info()
                    .get_arcsorts_by(|sort| !sort.is_eq_sort());
                existing.sort_by(|a, b| a.name().cmp(b.name()));
                let canonical = existing.into_iter().find(|sort| {
                    self.graph.export_sort(sort, &mut sorts.clone()).ok() == Some(index)
                });
                if let Some(canonical) = canonical {
                    self.graph
                        .bind_source_sort_alias(name, canonical.name(), span.clone())?;
                    // An alias registers no new sort in either environment.
                    // Do not restore the disposable, separately compiled header.
                    compiler = None;
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
                        let constructor = self
                            .cost_origins
                            .lock()
                            .unwrap()
                            .declarations
                            .get(&(function.span.clone(), function.name.clone()))
                            .cloned();
                        if let Some(constructor) = constructor {
                            let target = self
                                .graph
                                .authoring_type_info()
                                .get_func_type(&constructor)
                                .ok_or("dynamic-cost constructor was not resolved")?;
                            if target.subtype != ast::FunctionSubtype::Constructor
                                || target
                                    .input
                                    .iter()
                                    .map(|sort| sort.name())
                                    .collect::<Vec<_>>()
                                    != function
                                        .schema
                                        .input
                                        .iter()
                                        .map(String::as_str)
                                        .collect::<Vec<_>>()
                                || function.schema.output != "i64"
                                || !function.internal_hidden
                                || !function.unextractable
                            {
                                return Err("native dynamic-cost declaration shape changed".into());
                            }
                            self.graph
                                .extension_state_or_default::<crate::set_cost::SourceCostRoles>()
                                .0
                                .insert(function.name, constructor);
                            continue;
                        }
                        if function.internal_let || function.term_constructor.is_some() {
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
                        let hidden = function.internal_hidden;
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
                            hidden,
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
                        if self.rulesets.contains_key(&name)
                            || self
                                .program
                                .rulesets
                                .iter()
                                .any(|set| set.name.as_ref() == Some(&name))
                        {
                            return Err(format!("ruleset {name} is already declared"));
                        }
                        let span = self.span(&span)?;
                        self.rulesets.insert(
                            name,
                            SourceRuleset {
                                kind,
                                span,
                                version: None,
                                published_rules: 0,
                            },
                        );
                    }
                    N::NormRule { rule } => self.rule(rule, rewrite)?,
                    N::CoreAction(ResolvedAction::Let(span, var, expr)) => {
                        let value = self.expr(&expr, None, 0)?;
                        let output = self.program.nodes[value as usize].sort_id;
                        let span = self.span(&span)?;
                        if encoded {
                            // Follow native proof_global_remover for an actual Let.
                            // Native compiler validation above admits only Eq globals.
                            self.program.declarations.push(pb::Declaration {
                                kind: Some(pb::declaration::Kind::Constructor(pb::Constructor {
                                    name: var.name.clone(),
                                    output,
                                    unextractable: true,
                                    ..Default::default()
                                })),
                                hidden: true,
                                span,
                                ..Default::default()
                            });
                            let anchor = u32::try_from(self.program.nodes.len())
                                .map_err(|_| "too many source nodes")?;
                            self.program.nodes.push(pb::Node {
                                sort_id: output,
                                kind: Some(pb::node::Kind::Call(pb::Call {
                                    func: var.name,
                                    args: vec![],
                                })),
                                span,
                            });
                            let union = u32::try_from(self.program.nodes.len())
                                .map_err(|_| "too many source nodes")?;
                            self.program.nodes.push(pb::Node {
                                sort_id: output,
                                kind: Some(pb::node::Kind::Union(pb::Union {
                                    members: vec![anchor, value],
                                })),
                                span,
                            });
                            self.program.commands.push(pb::Command {
                                kind: Some(pb::command::Kind::Action(pb::Action {
                                    kind: Some(pb::action::Kind::Term(union)),
                                    span,
                                })),
                                span,
                            });
                            continue;
                        }
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
                    N::ActionScope(span, actions) => {
                        let action = self.action_scope(&actions)?;
                        let span = self.span(&span)?;
                        self.program.commands.push(pb::Command {
                            span,
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
                                extractor: source_extractor.into(),
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
                        let command = self.schedule(schedule, &mut publish)?;
                        self.program.commands.push(command);
                    }
                    N::UserDefined(span, name, args) if name == "let-scheduler" => {
                        let bind = source_scheduler_binding(&span, &args)?;
                        if !self.schedulers.insert(bind.name.clone()) {
                            return Err(format!("scheduler {} already exists", bind.name));
                        }
                        let span = self.span(&span)?;
                        self.program.commands.push(pb::Command {
                            span,
                            kind: Some(pb::command::Kind::BindScheduler(bind)),
                        });
                    }
                    N::UserDefined(span, name, args) if name == "run-schedule" => {
                        let mut locals = HashSet::new();
                        let body = args
                            .iter()
                            .map(|arg| self.extended_schedule(arg, &mut locals, &mut publish, 0))
                            .collect::<Result<Vec<_>, _>>()?;
                        let command = match body.as_slice() {
                            // Only control roots can lose the implicit list.
                            // Bind/observation leaves must remain local and keep
                            // their schedule report and mode admission boundary.
                            [command]
                                if matches!(
                                    command.kind,
                                    Some(
                                        pb::command::Kind::Run(_)
                                            | pb::command::Kind::Repeat(_)
                                            | pb::command::Kind::Saturate(_)
                                    )
                                ) =>
                            {
                                command.clone()
                            }
                            _ => pb::Command {
                                span: self.span(&span)?,
                                kind: Some(pb::command::Kind::Repeat(pb::Repeat {
                                    times: Some(1),
                                    body,
                                    ..Default::default()
                                })),
                            },
                        };
                        self.program.commands.push(command);
                    }
                    N::PrintSize(span, table) => {
                        let span = self.span(&span)?;
                        self.program.commands.push(pb::Command {
                            span,
                            kind: Some(pb::command::Kind::PrintSize(pb::PrintSize {
                                tables: table.into_iter().collect(),
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
        let program = self.phase(publish)?;
        if let Some(mut compiler) = compiler {
            // Export updates only these producer-owned name/role records.
            // Keep them with the compiled context, never with a live Engine.
            *compiler.extension_state_or_default::<SourceTableNames>() = self
                .graph
                .extension_state::<SourceTableNames>()
                .cloned()
                .unwrap_or_default();
            if let Some(roles) = self
                .graph
                .extension_state::<crate::set_cost::SourceCostRoles>()
            {
                *compiler.extension_state_or_default::<crate::set_cost::SourceCostRoles>() =
                    roles.clone();
            }
            self.graph = compiler;
        }
        Ok(program)
    }

    // One phase owns exactly its completed command prefix and new definitions;
    // immutable rule cursors remain publication-local, including failed macros.
    fn phase(&mut self, publish: Vec<usize>) -> Result<pb::Program, String> {
        let mut tables = self
            .graph
            .extension_state::<SourceTableNames>()
            .cloned()
            .unwrap_or_default();
        for declaration in &self.program.declarations {
            let physical = match &declaration.kind {
                Some(pb::declaration::Kind::Constructor(table)) => &table.name,
                Some(pb::declaration::Kind::Function(table)) => &table.name,
                Some(pb::declaration::Kind::Relation(table)) => &table.name,
                _ => continue,
            };
            let logical = self
                .graph
                .authoring_type_info()
                .get_func_type(physical)
                .and_then(|table| match &table.table_name {
                    Some(ast::TableName::Public(name)) => Some(name.clone()),
                    _ => None,
                })
                .unwrap_or_else(|| physical.clone());
            if tables
                .0
                .insert(logical.clone(), physical.clone())
                .is_some_and(|previous| previous != *physical)
            {
                return Err(format!(
                    "distinct source tables share logical name {logical:?}"
                ));
            }
        }
        let local_rulesets: HashMap<usize, u32> = publish
            .iter()
            .enumerate()
            .map(|(local, global)| {
                Ok((
                    *global,
                    u32::try_from(local).map_err(|_| "too many source rulesets")?,
                ))
            })
            .collect::<Result<_, String>>()?;
        let rulesets = publish
            .into_iter()
            .map(|index| {
                let mut ruleset = self.program.rulesets[index].clone();
                if let Some(pb::ruleset::Kind::Combined(combined)) = &mut ruleset.kind {
                    for child in &mut combined.rulesets {
                        if let Some(pb::ruleset_ref::Kind::Index(index)) = &mut child.kind {
                            *index = *local_rulesets
                                .get(&(*index as usize))
                                .expect("new anonymous deltas are published with their version");
                        }
                    }
                }
                ruleset
            })
            .collect();
        let mut program = pb::Program {
            ir_version: 1,
            sorts: self.program.sorts.clone(),
            nodes: self.program.nodes.clone(),
            files: self.program.files.clone(),
            declarations: std::mem::take(&mut self.program.declarations),
            commands: std::mem::take(&mut self.program.commands),
            // Unused rules are still validated at their source position. Only
            // binding/publication waits until the first run of the theory.
            rules: self.program.rules.clone(),
            rulesets,
        };
        let types: &egglog::TypeInfo = self.graph.authoring_type_info();
        let logical_name = |name: &mut String| {
            if let Some(function) = types.get_func_type(name)
                && let Some(ast::TableName::Public(logical)) = &function.table_name
            {
                *name = logical.clone();
            }
        };
        map_callable_names(&mut program, logical_name, logical_name);
        *self.graph.extension_state_or_default::<SourceTableNames>() = tables;
        Ok(program)
    }

    fn cost_phase(
        &mut self,
        first: Command,
        span: ast::Span,
        captures: Vec<String>,
        deletion: Option<String>,
    ) -> Result<pb::Program, String> {
        let deleting = deletion.is_some();
        let (constructor, arity) = if let Some(constructor) = deletion {
            (constructor, captures.len())
        } else {
            self.cost_origins
                .lock()
                .unwrap()
                .sets
                .get(&span)
                .cloned()
                .ok_or("missing native set-cost origin")?
        };
        if captures.len() != arity {
            return Err("native set-cost capture count changed".into());
        }
        let mut expansion = vec![first];
        for _ in 0..arity + 1 {
            expansion.push(
                self.commands
                    .pop_front()
                    .ok_or("incomplete native set-cost expansion")?
                    .0,
            );
        }
        let target_args = captures
            .iter()
            .map(|name| Expr::Var(ast::Span::Panic, name.clone()))
            .collect::<Vec<_>>();
        let same_key = |args: &[Expr]| {
            args.iter()
                .map(ToString::to_string)
                .eq(target_args.iter().map(ToString::to_string))
        };
        let target_matches = if deleting {
            matches!(&expansion[arity], Command::Action(Action::Change(_, ast::Change::Delete, name, args)) if name == &constructor && same_key(args))
        } else {
            matches!(&expansion[arity], Command::Action(Action::Expr(target_span, Expr::Call(_, name, args))) if target_span == &span && name == &constructor && same_key(args))
        };
        let helper_matches = if deleting {
            matches!(&expansion[arity + 1], Command::Action(Action::Change(_, ast::Change::Delete, name, args)) if *name == crate::set_cost::get_cost_table_name(&constructor) && same_key(args))
        } else {
            matches!(&expansion[arity + 1], Command::Action(Action::Set(write_span, name, args, _)) if write_span == &span && *name == crate::set_cost::get_cost_table_name(&constructor) && same_key(args))
        };
        if !target_matches || !helper_matches
            || expansion[..arity].iter().zip(&captures).any(|(command, name)| !matches!(command, Command::Action(Action::Let(_, actual, _)) if actual == name))
        { return Err("native top-level set-cost expansion shape changed".into()); }
        let helper = crate::set_cost::get_cost_table_name(&constructor);
        if self
            .graph
            .extension_state::<crate::set_cost::SourceCostRoles>()
            .and_then(|roles| roles.0.get(&helper))
            != Some(&constructor)
        {
            return Err("set-cost requires a declared dynamic-cost constructor".into());
        }
        let mut prefix = Vec::new();
        let mut arguments = Vec::new();
        let mut cost = None;
        for (index, command) in expansion.into_iter().enumerate() {
            let resolved = match self.graph.resolve_command_preserving_globals(command) {
                Ok(resolved) => resolved,
                Err(error) => {
                    // Native executes each expanded command before typechecking
                    // the next. Publish that same completed prefix first; a
                    // failed prefix execution still wins over this later error.
                    if prefix.is_empty() {
                        return Err(error.to_string());
                    }
                    self.program.commands.extend(prefix);
                    self.pending_error = Some(error.to_string());
                    return self.phase(Vec::new());
                }
            };
            let [N::CoreAction(action)] = resolved.as_slice() else {
                return Err("native set-cost resolution shape changed".into());
            };
            let (action_span, term) = match action {
                ResolvedAction::Let(action_span, var, expr)
                    if index < arity && var.name == captures[index] =>
                {
                    let value = self.expr(expr, None, 0)?;
                    arguments.push(value);
                    self.graph
                        .extension_state_or_default::<crate::set_cost::SourceCostRoles>()
                        .1
                        .insert(var.name.clone());
                    (action_span, Some(value))
                }
                ResolvedAction::Expr(
                    action_span,
                    ResolvedExpr::Call(_, ResolvedCall::Func(target), _),
                ) if index == arity && target.name == constructor => {
                    let sort_id = self.sort(target.output.name())?;
                    let term = u32::try_from(self.program.nodes.len())
                        .map_err(|_| "too many source nodes")?;
                    let node_span = self.span(action_span)?;
                    self.program.nodes.push(pb::Node {
                        sort_id,
                        kind: Some(pb::node::Kind::Call(pb::Call {
                            func: constructor.clone(),
                            args: arguments.clone(),
                        })),
                        span: node_span,
                    });
                    // One target evaluation includes the ordered captures. Do
                    // not evaluate them once as prefix terms and again as args.
                    prefix.clear();
                    (action_span, Some(term))
                }
                ResolvedAction::Change(
                    action_span,
                    ast::Change::Delete,
                    ResolvedCall::Func(target),
                    _,
                ) if deleting && index == arity && target.name == constructor => {
                    prefix.clear();
                    prefix.push(pb::Command {
                        span: self.span(action_span)?,
                        kind: Some(pb::command::Kind::Action(pb::Action {
                            span: self.span(action_span)?,
                            kind: Some(pb::action::Kind::Delete(pb::Call {
                                func: constructor.clone(),
                                args: arguments.clone(),
                            })),
                        })),
                    });
                    (action_span, None)
                }
                ResolvedAction::Change(
                    action_span,
                    ast::Change::Delete,
                    ResolvedCall::Func(function),
                    _,
                ) if deleting && index == arity + 1 && function.name == helper => {
                    (action_span, None)
                }
                ResolvedAction::Set(action_span, ResolvedCall::Func(function), _, value)
                    if index == arity + 1 && function.name == helper =>
                {
                    cost = Some(self.expr(value, None, 0)?);
                    (action_span, None)
                }
                _ => return Err("native set-cost resolved action order changed".into()),
            };
            if let Some(term) = term {
                prefix.push(pb::Command {
                    span: self.span(action_span)?,
                    kind: Some(pb::command::Kind::Action(pb::Action {
                        span: self.span(action_span)?,
                        kind: Some(pb::action::Kind::Term(term)),
                    })),
                });
            }
        }
        let span = self.span(&span)?;
        self.program.commands.push(pb::Command {
            span,
            kind: Some(pb::command::Kind::Action(pb::Action {
                span,
                kind: Some(if deleting {
                    pb::action::Kind::Delete(pb::Call {
                        func: constructor,
                        args: arguments,
                    })
                } else {
                    pb::action::Kind::SetCost(pb::SetCost {
                        target: Some(pb::Call {
                            func: constructor,
                            args: arguments,
                        }),
                        cost,
                    })
                }),
            })),
        });
        self.phase(Vec::new())
    }

    // Resolve the current authored closure into immutable wire versions. A new
    // leaf suffix references its old named prefix, never reinstalls old rules.
    fn publish_ruleset(&mut self, name: &str, publish: &mut Vec<usize>) -> Result<usize, String> {
        let mut pending = vec![(name.to_owned(), false)];
        let mut active = HashSet::new();
        let mut completed: HashMap<String, usize> = HashMap::new();
        while let Some((logical, leaving)) = pending.pop() {
            if completed.contains_key(&logical) {
                continue;
            }
            let ruleset = self
                .rulesets
                .get(&logical)
                .ok_or_else(|| format!("unknown ruleset {logical}"))?
                .clone();
            if !leaving {
                if !active.insert(logical.clone()) {
                    return Err(format!("cyclic source ruleset {logical}"));
                }
                pending.push((logical.clone(), true));
                if let pb::ruleset::Kind::Combined(combined) = ruleset.kind {
                    for child in combined.rulesets.into_iter().rev() {
                        let Some(pb::ruleset_ref::Kind::Name(name)) = child.kind else {
                            unreachable!("authored dependencies retain logical names")
                        };
                        pending.push((name, false));
                    }
                }
                continue;
            }
            active.remove(&logical);
            let mut published_rules = ruleset.published_rules;
            let kind = match ruleset.kind {
                pb::ruleset::Kind::Rules(list) => {
                    if let Some(version) = ruleset.version
                        && ruleset.published_rules == list.rules.len()
                    {
                        completed.insert(logical, version);
                        continue;
                    }
                    published_rules = list.rules.len();
                    if let Some(previous) = ruleset.version {
                        let delta = u32::try_from(self.program.rulesets.len())
                            .map_err(|_| "too many source rulesets")?;
                        self.program.rulesets.push(pb::Ruleset {
                            kind: Some(pb::ruleset::Kind::Rules(pb::RuleList {
                                rules: list.rules[ruleset.published_rules..].to_vec(),
                            })),
                            span: ruleset.span,
                            ..Default::default()
                        });
                        publish.push(delta as usize);
                        pb::ruleset::Kind::Combined(pb::CombinedRuleset {
                            rulesets: vec![
                                pb::RulesetRef {
                                    kind: Some(pb::ruleset_ref::Kind::Name(
                                        self.program.rulesets[previous].name.clone().unwrap(),
                                    )),
                                },
                                pb::RulesetRef {
                                    kind: Some(pb::ruleset_ref::Kind::Index(delta)),
                                },
                            ],
                        })
                    } else {
                        pb::ruleset::Kind::Rules(list)
                    }
                }
                pb::ruleset::Kind::Combined(combined) => {
                    pb::ruleset::Kind::Combined(pb::CombinedRuleset {
                        rulesets: combined
                            .rulesets
                            .into_iter()
                            .map(|child| {
                                let Some(pb::ruleset_ref::Kind::Name(name)) = child.kind else {
                                    unreachable!()
                                };
                                let version = completed[&name];
                                pb::RulesetRef {
                                    kind: Some(pb::ruleset_ref::Kind::Name(
                                        self.program.rulesets[version].name.clone().unwrap(),
                                    )),
                                }
                            })
                            .collect(),
                    })
                }
            };
            if let Some(version) = ruleset.version
                && self.program.rulesets[version].kind.as_ref() == Some(&kind)
            {
                completed.insert(logical, version);
                continue;
            }
            let physical = if ruleset.version.is_none() {
                logical.clone()
            } else {
                loop {
                    let candidate = format!("{}ruleset_{}", self.local_prefix, self.next_ruleset);
                    self.next_ruleset = self
                        .next_ruleset
                        .checked_add(1)
                        .ok_or("source ruleset version identity space exhausted")?;
                    if !self.rulesets.contains_key(&candidate)
                        && !self
                            .program
                            .rulesets
                            .iter()
                            .any(|set| set.name.as_ref() == Some(&candidate))
                    {
                        break candidate;
                    }
                }
            };
            let version = self.program.rulesets.len();
            self.program.rulesets.push(pb::Ruleset {
                name: Some(physical),
                kind: Some(kind),
                span: ruleset.span,
                ..Default::default()
            });
            let authored = self.rulesets.get_mut(&logical).unwrap();
            authored.version = Some(version);
            authored.published_rules = published_rules;
            completed.insert(logical, version);
            publish.push(version);
        }
        Ok(completed[name])
    }

    fn schedule(
        &mut self,
        schedule: ast::GenericSchedule<ResolvedCall, ast::ResolvedVar>,
        publish: &mut Vec<usize>,
    ) -> Result<pb::Command, String> {
        use ast::GenericSchedule as S;
        let (span, kind) = match schedule {
            S::Run(span, config) => {
                let version = self.publish_ruleset(&config.ruleset, publish)?;
                let kind = pb::command::Kind::Run(pb::Run {
                    ruleset: Some(pb::RulesetRef {
                        kind: Some(pb::ruleset_ref::Kind::Name(
                            self.program.rulesets[version].name.clone().unwrap(),
                        )),
                    }),
                    ..Default::default()
                });
                if let Some(until) = config.until {
                    // An explicitly empty native conjunction is true; wire's
                    // empty list instead means there is no precondition.
                    let until = if until.is_empty() {
                        vec![self.expr(&ResolvedExpr::Lit(span.clone(), Literal::Unit), None, 0)?]
                    } else {
                        self.facts(&until)?
                    };
                    (
                        span.clone(),
                        pb::command::Kind::Repeat(pb::Repeat {
                            times: Some(1),
                            until,
                            body: vec![pb::Command {
                                span: self.span(&span)?,
                                kind: Some(kind),
                            }],
                        }),
                    )
                } else {
                    (span, kind)
                }
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

    // Project the actual experimental extension syntax, without invoking its
    // callback. Each body is validated even when an enclosing count is zero.
    fn extended_schedule(
        &mut self,
        expr: &Expr,
        locals: &mut HashSet<String>,
        publish: &mut Vec<usize>,
        depth: usize,
    ) -> Result<pb::Command, String> {
        if depth > 256 {
            return Err("source schedule nesting exceeds 256".into());
        }
        let span = expr.span();
        if let Some(header) = scheduling::loop_header(expr).map_err(|error| error.to_string())? {
            let until = if let Some(until) = header.until {
                if until.is_empty() {
                    vec![self.expr(&ResolvedExpr::Lit(span.clone(), Literal::Unit), None, 0)?]
                } else {
                    let resolved = self
                        .graph
                        .resolve_command_preserving_globals(Command::Check(span.clone(), until))
                        .map_err(|error| error.to_string())?;
                    let [N::Check(_, facts)] = resolved.as_slice() else {
                        return Err("source until resolution changed its native query".into());
                    };
                    self.facts(facts)?
                }
            } else {
                vec![]
            };
            let mut nested = locals.clone();
            let body = header
                .body
                .iter()
                .map(|child| self.extended_schedule(child, &mut nested, publish, depth + 1))
                .collect::<Result<Vec<_>, _>>()?;
            return Ok(pb::Command {
                span: self.span(&span)?,
                kind: Some(if header.exact {
                    pb::command::Kind::Repeat(pb::Repeat {
                        times: header.bound,
                        until,
                        body,
                    })
                } else {
                    pb::command::Kind::Saturate(pb::Saturate {
                        max_iterations: header.bound,
                        until,
                        body,
                    })
                }),
            });
        }
        let (ruleset, scheduler, until) = match expr {
            Expr::Call(_, head, args) if head == "fail" => {
                let [child] = args.as_slice() else {
                    return Err("source fail requires one schedule step".into());
                };
                let child = self.extended_schedule(child, locals, publish, depth + 1)?;
                return Ok(pb::Command {
                    span: self.span(&span)?,
                    kind: Some(pb::command::Kind::Fail(Box::new(child))),
                });
            }
            Expr::Call(_, head, args)
                if matches!(
                    head.as_str(),
                    "eval" | "set" | "delete" | "subsume" | "union" | "panic"
                ) =>
            {
                let action = match (head.as_str(), args.as_slice()) {
                    ("eval", [expr]) => Action::Expr(span.clone(), expr.clone()),
                    ("set", [Expr::Call(_, name, args), value]) => {
                        Action::Set(span.clone(), name.clone(), args.clone(), value.clone())
                    }
                    ("delete" | "subsume", [Expr::Call(_, name, args)]) => Action::Change(
                        span.clone(),
                        if head == "delete" {
                            ast::Change::Delete
                        } else {
                            ast::Change::Subsume
                        },
                        name.clone(),
                        args.clone(),
                    ),
                    ("union", [left, right]) => {
                        Action::Union(span.clone(), left.clone(), right.clone())
                    }
                    ("panic", [Expr::Lit(_, Literal::String(message))]) => {
                        Action::Panic(span.clone(), message.clone())
                    }
                    _ => return Err("source action schedule step has invalid arguments".into()),
                };
                let resolved = self
                    .graph
                    .resolve_command_preserving_globals(Command::Action(action))
                    .map_err(|error| error.to_string())?;
                let [N::CoreAction(action)] = resolved.as_slice() else {
                    return Err("source action schedule step requires one ordinary action".into());
                };
                let action = self.action(action, None)?;
                return Ok(pb::Command {
                    span: self.span(&span)?,
                    kind: Some(pb::command::Kind::Action(action)),
                });
            }
            Expr::Var(_, ruleset) => (ruleset.as_str(), "", None),
            Expr::Call(_, head, args) if matches!(head.as_str(), "run" | "run-with") => {
                let (scheduler, args) = if head == "run-with" {
                    let [Expr::Var(_, name), rest @ ..] = args.as_slice() else {
                        return Err("source run-with requires a scheduler name".into());
                    };
                    if !locals.contains(name) && !self.schedulers.contains(name) {
                        return Err(format!("unknown scheduler {name}"));
                    }
                    (name.as_str(), rest)
                } else {
                    ("", args.as_slice())
                };
                let (ruleset, rest) = match args {
                    [Expr::Var(_, name), rest @ ..] if name != ":until" => (name.as_str(), rest),
                    _ => ("", args),
                };
                let until = match rest {
                    [] => None,
                    [Expr::Var(_, option), condition] if option == ":until" => Some(condition),
                    _ => {
                        return Err(
                            "source run requires a ruleset and optional :until expression".into(),
                        );
                    }
                };
                (ruleset, scheduler, until)
            }
            Expr::Call(_, head, args) if head == "let-scheduler" => {
                let bind = source_scheduler_binding(&span, args)?;
                if self.schedulers.contains(&bind.name) {
                    return Err(
                        "source local scheduler shadowing a permanent binding is unsupported"
                            .into(),
                    );
                }
                if !locals.insert(bind.name.clone()) {
                    return Err(format!("scheduler {} already exists", bind.name));
                }
                return Ok(pb::Command {
                    span: self.span(&span)?,
                    kind: Some(pb::command::Kind::BindScheduler(bind)),
                });
            }
            Expr::Call(_, head, args) if matches!(head.as_str(), "seq" | "repeat" | "saturate") => {
                let (times, args) = if head == "repeat" {
                    let [Expr::Lit(_, Literal::Int(count)), rest @ ..] = args.as_slice() else {
                        return Err("source repeat requires an integer count".into());
                    };
                    (Some((*count).max(0) as u64), rest)
                } else {
                    (None, args.as_slice())
                };
                let mut nested = locals.clone();
                let body = args
                    .iter()
                    .map(|child| self.extended_schedule(child, &mut nested, publish, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?;
                let kind = if head == "saturate" {
                    pb::command::Kind::Saturate(pb::Saturate {
                        body,
                        ..Default::default()
                    })
                } else {
                    pb::command::Kind::Repeat(pb::Repeat {
                        body,
                        times: times.or(Some(1)),
                        ..Default::default()
                    })
                };
                return Ok(pb::Command {
                    span: self.span(&span)?,
                    kind: Some(kind),
                });
            }
            Expr::Call(_, head, args) if head == "print-size" => {
                let tables = match args.as_slice() {
                    [] => vec![],
                    [Expr::Var(_, table)] => vec![table.clone()],
                    _ => return Err("source print-size requires at most one table".into()),
                };
                return Ok(pb::Command {
                    span: self.span(&span)?,
                    kind: Some(pb::command::Kind::PrintSize(pb::PrintSize { tables })),
                });
            }
            _ => return Err("source schedule body has no supported native projection".into()),
        };
        let version = self.publish_ruleset(ruleset, publish)?;
        let run = pb::Command {
            span: self.span(&span)?,
            kind: Some(pb::command::Kind::Run(pb::Run {
                ruleset: Some(pb::RulesetRef {
                    kind: Some(pb::ruleset_ref::Kind::Name(
                        self.program.rulesets[version].name.clone().unwrap(),
                    )),
                }),
                scheduler: scheduler.into(),
            })),
        };
        if let Some(condition) = until {
            // Match the extension's Fact::Fact construction exactly; Core's
            // parser has a different equality-fact syntax.
            let resolved = self
                .graph
                .resolve_command_preserving_globals(Command::Check(
                    condition.span(),
                    vec![Fact::Fact(condition.clone())],
                ))
                .map_err(|error| error.to_string())?;
            let [N::Check(_, facts)] = resolved.as_slice() else {
                return Err("source until resolution changed its native query".into());
            };
            let until = self.facts(facts)?;
            Ok(pb::Command {
                span: self.span(&span)?,
                kind: Some(pb::command::Kind::Repeat(pb::Repeat {
                    times: Some(1),
                    until,
                    body: vec![run],
                })),
            })
        } else {
            Ok(run)
        }
    }

    fn rule(
        &mut self,
        rule: ast::GenericRule<ResolvedCall, ast::ResolvedVar>,
        rewrite: Option<RewriteKind>,
    ) -> Result<(), String> {
        let ruleset = self
            .rulesets
            .get(&rule.ruleset)
            .ok_or_else(|| format!("unknown ruleset {}", rule.ruleset))?;
        let pb::ruleset::Kind::Rules(list) = &ruleset.kind else {
            return Err(egglog::Error::CombinedRulesetError(rule.ruleset, rule.span).to_string());
        };
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
                // Subsume keeps the row and its class; subsequent constructor
                // lookup cannot clear its dominant subsumption flag.
                destructive |= matches!(action, ResolvedAction::Change(_, ast::Change::Delete, ..));
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
            let mut index = 0;
            while index < rule.head.0.len() {
                // The native macro creates N captures, one materialization,
                // and one helper write. Recognize the complete typed group
                // before ordinary local-alias admission, never its name alone.
                let mut group = None;
                let captures = rule.head.0[index..]
                    .iter()
                    .take_while(|action| matches!(action, ResolvedAction::Let(..)))
                    .count();
                for (target_index, action) in rule
                    .head
                    .0
                    .iter()
                    .enumerate()
                    .skip(index)
                    .take(captures + 1)
                {
                    let ResolvedAction::Expr(
                        span,
                        ResolvedExpr::Call(_, ResolvedCall::Func(target), key),
                    ) = action
                    else {
                        continue;
                    };
                    let origin = self.cost_origins.lock().unwrap().sets.get(span).cloned();
                    let Some((constructor, arity)) = origin else {
                        continue;
                    };
                    if target_index != index + arity {
                        continue;
                    }
                    if target.name != constructor || key.len() != arity {
                        return Err("native set-cost target shape changed".into());
                    }
                    let Some(
                        write @ ResolvedAction::Set(
                            write_span,
                            ResolvedCall::Func(helper),
                            written_key,
                            cost,
                        ),
                    ) = rule.head.0.get(target_index + 1)
                    else {
                        return Err("native set-cost write shape changed".into());
                    };
                    if write_span != span
                        || written_key != key
                        || self
                            .graph
                            .extension_state::<crate::set_cost::SourceCostRoles>()
                            .and_then(|roles| roles.0.get(&helper.name))
                            != Some(&constructor)
                    {
                        return Err("native set-cost helper role changed".into());
                    }
                    let mut captured = aliases.clone();
                    let mut generated = HashSet::new();
                    for (capture, argument) in rule.head.0[index..target_index].iter().zip(key) {
                        let (ResolvedAction::Let(_, var, value), ResolvedExpr::Var(_, use_var)) =
                            (capture, argument)
                        else {
                            return Err("native set-cost argument capture shape changed".into());
                        };
                        if var != use_var {
                            return Err("native set-cost capture order changed".into());
                        }
                        captured.insert(var.name.clone(), self.expr(value, Some(&aliases), 0)?);
                        generated.insert(var.name.clone());
                    }
                    let mut escaped = false;
                    cost.clone().visit_exprs(&mut |expr| {
                        escaped |= matches!(&expr, ResolvedExpr::Var(_, var) if generated.contains(&var.name));
                        expr
                    });
                    for action in &rule.head.0[target_index + 2..] {
                        action.clone().visit_exprs(&mut |expr| {
                            escaped |= matches!(&expr, ResolvedExpr::Var(_, var) if generated.contains(&var.name));
                            expr
                        });
                    }
                    if escaped {
                        return Err("native set-cost capture escaped its group".into());
                    }
                    group = Some((self.action(write, Some(&captured))?, target_index + 2));
                    break;
                }
                if let Some((action, next)) = group {
                    head.push(action);
                    index = next;
                    continue;
                }
                if captures > 0
                    && let Some(ResolvedAction::Change(
                        _,
                        ast::Change::Delete,
                        ResolvedCall::Func(target),
                        key,
                    )) = rule.head.0.get(index + captures)
                    && let Some(ResolvedAction::Change(
                        _,
                        ast::Change::Delete,
                        ResolvedCall::Func(helper),
                        helper_key,
                    )) = rule.head.0.get(index + captures + 1)
                    && self
                        .graph
                        .extension_state::<crate::set_cost::SourceCostRoles>()
                        .and_then(|roles| roles.0.get(&helper.name))
                        == Some(&target.name)
                    && retained_cost_key(key, helper_key)
                    && key.len() == captures
                {
                    let mut captured = aliases.clone();
                    let mut generated = HashSet::new();
                    for (capture, argument) in rule.head.0[index..index + captures].iter().zip(key)
                    {
                        let (ResolvedAction::Let(_, var, value), ResolvedExpr::Var(_, used)) =
                            (capture, argument)
                        else {
                            return Err("constructor-cost deletion capture shape changed".into());
                        };
                        if var != used {
                            return Err("constructor-cost deletion capture order changed".into());
                        }
                        let mut depends_on_capture = false;
                        value.clone().visit_exprs(&mut |expr| {
                            depends_on_capture |= matches!(&expr, ResolvedExpr::Var(_, var) if generated.contains(&var.name));
                            expr
                        });
                        if depends_on_capture {
                            return Err(
                                "constructor-cost deletion captures must be independent".into()
                            );
                        }
                        captured.insert(var.name.clone(), self.expr(value, Some(&aliases), 0)?);
                        generated.insert(var.name.clone());
                    }
                    let mut escaped = false;
                    for action in &rule.head.0[index + captures + 2..] {
                        action.clone().visit_exprs(&mut |expr| {
                            escaped |= matches!(&expr, ResolvedExpr::Var(_, var) if generated.contains(&var.name));
                            expr
                        });
                    }
                    if escaped {
                        return Err("constructor-cost deletion capture escaped its group".into());
                    }
                    head.push(self.action(&rule.head.0[index + captures], Some(&captured))?);
                    index += captures + 2;
                    continue;
                }
                let action = &rule.head.0[index];
                if let ResolvedAction::Change(
                    _,
                    ast::Change::Delete,
                    ResolvedCall::Func(target),
                    key,
                ) = action
                    && let Some(helper) = self
                        .graph
                        .extension_state::<crate::set_cost::SourceCostRoles>()
                        .and_then(|roles| {
                            roles
                                .0
                                .iter()
                                .find(|(_, constructor)| **constructor == target.name)
                                .map(|(helper, _)| helper.clone())
                        })
                {
                    if !matches!(rule.head.0.get(index + 1), Some(ResolvedAction::Change(_, ast::Change::Delete, ResolvedCall::Func(changed), args)) if changed.name == helper && retained_cost_key(args, key))
                    {
                        return Err("dynamic-cost constructor deletion requires its exact adjacent helper cleanup".into());
                    }
                    head.push(self.action(action, Some(&aliases))?);
                    index += 2;
                    continue;
                }
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
                index += 1;
            }
            pb::rule_decl::Kind::Rule(pb::Rule { query, head })
        };
        let span = self.span(&rule.span)?;
        let index = u32::try_from(self.program.rules.len()).map_err(|_| "too many source rules")?;
        let ruleset_name = rule.ruleset.clone();
        self.program.rules.push(pb::RuleDecl {
            kind: Some(kind),
            name: Some(rule.name),
            eval_mode: match rule.eval_mode {
                ast::RuleEvalMode::Seminaive => pb::RuleEvalMode::Seminaive,
                ast::RuleEvalMode::Naive => pb::RuleEvalMode::Naive,
                ast::RuleEvalMode::UnsafeSeminaive => pb::RuleEvalMode::UnsafeSeminaive,
            }
            .into(),
            no_decomp: rule.no_decomp,
            include_subsumed: rule.include_subsumed,
            span,
            ..Default::default()
        });
        let pb::ruleset::Kind::Rules(list) =
            &mut self.rulesets.get_mut(&ruleset_name).unwrap().kind
        else {
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

    // Constructor aliases are closed. Mixed scopes must be the exact ordered
    // local plan of an admitted DAG; observable alias reuse is not portable.
    fn action_scope(
        &mut self,
        actions: &ast::GenericActions<ResolvedCall, ast::ResolvedVar>,
    ) -> Result<pb::Action, String> {
        let (terminal, prefix) = actions
            .0
            .split_last()
            .ok_or("source action scope is empty")?;
        if !matches!(terminal, ResolvedAction::Expr(..) | ResolvedAction::Set(..)) {
            return Err("source action scope requires a Term or Set terminal".into());
        }
        let mut aliases = HashMap::new();
        let mut dependencies = HashMap::new();
        let mut reached = HashSet::new();
        let mut constructor_only = true;
        let mut evaluations = Vec::new();
        for (position, action) in actions.0.iter().enumerate() {
            let mut pending = match action {
                ResolvedAction::Let(_, _, expr) if position < prefix.len() => vec![expr],
                ResolvedAction::Expr(_, expr) if position == prefix.len() => vec![expr],
                ResolvedAction::Set(_, _, args, value) if position == prefix.len() => {
                    args.iter().chain([value]).collect()
                }
                _ => return Err("source action scope requires local Lets and one terminal".into()),
            };
            let mut used = HashSet::new();
            while let Some(expr) = pending.pop() {
                match expr {
                    ResolvedExpr::Lit(..) => (),
                    ResolvedExpr::Var(_, var) if !var.is_global_ref && aliases.contains_key(&var.name) => {
                        used.insert(var.name.clone());
                    }
                    ResolvedExpr::Call(_, call, args) => {
                        constructor_only &= matches!(call, ResolvedCall::Func(function)
                            if function.subtype == ast::FunctionSubtype::Constructor
                                && !self.relations.contains(&function.name));
                        pending.extend(args);
                    }
                    _ => return Err("source action scope requires closed constructor/scalar locals, without reads, primitives or globals".into()),
                }
            }
            if let ResolvedAction::Let(_, var, expr) = action {
                let node = self.expr(expr, Some(&aliases), 0)?;
                if aliases.insert(var.name.clone(), node).is_some() {
                    return Err("source action scope has a duplicate local".into());
                }
                dependencies.insert(var.name.clone(), used);
                evaluations.push(node);
            } else {
                let mut pending: Vec<_> = used.into_iter().collect();
                while let Some(name) = pending.pop() {
                    if reached.insert(name.clone()) {
                        pending.extend(dependencies[&name].iter().cloned());
                    }
                }
            }
        }
        if reached.len() != prefix.len() {
            return Err("source action scope has an unreachable local evaluation".into());
        }
        let action = self.action(terminal, Some(&aliases))?;
        if !matches!(
            action.kind,
            Some(pb::action::Kind::Term(_) | pb::action::Kind::Set(_))
        ) {
            return Err("source action scope terminal is not a plain Term or Set".into());
        }
        if !constructor_only {
            let native_spans = NativeSpans::default();
            let (depths, expansions) = validate_node_graph(&self.program, &native_spans)?;
            // Source can know only an authored alias for a structural sort.
            // Match execution's canonical sort context without changing it.
            let mut graph = self.graph.clone();
            materialize_sorts(
                &self.program,
                &mut graph,
                &mut HashSet::new(),
                &native_spans,
            )?;
            let constructors = self
                .program
                .nodes
                .iter()
                .filter_map(|node| match &node.kind {
                    Some(pb::node::Kind::Call(call))
                        if self.graph.authoring_type_info().is_constructor(&call.func)
                            && !self.relations.contains(&call.func) =>
                    {
                        Some(call.func.clone())
                    }
                    _ => None,
                })
                .collect();
            // Reuse admission and first-demand lowering, including opaque Call
            // barriers. Inlining locals must reproduce their actual order once.
            let position = self.program.commands.len() as u32;
            self.program.commands.push(pb::Command {
                kind: Some(pb::command::Kind::Action(action.clone())),
                ..Default::default()
            });
            let selected = classify_constructor_dags(
                &self.program,
                &constructors,
                &depths,
                &expansions,
                &graph,
            );
            self.program.commands.pop();
            let selected = selected?;
            let closed = selected
                .get(&vec![position])
                .ok_or("source action scope is not an admitted ordered constructor DAG")?;
            let (_, expected) =
                constructor_dag_actions(&self.program, &action, |_| false, &native_spans, closed)?;
            if expected != evaluations {
                return Err(
                    "source action scope changes first-demand evaluation order or alias reuse"
                        .into(),
                );
            }
        }
        Ok(action)
    }

    fn action(
        &mut self,
        action: &ResolvedAction<ResolvedCall, ast::ResolvedVar>,
        aliases: Option<&HashMap<String, u32>>,
    ) -> Result<pb::Action, String> {
        let cost_origin = if let ResolvedAction::Set(span, ..) = action {
            self.cost_origins.lock().unwrap().sets.get(span).cloned()
        } else {
            None
        };
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
                if let Some((constructor, arity)) = cost_origin {
                    let ResolvedCall::Func(helper) = function else {
                        return Err("native set-cost helper is not a function".into());
                    };
                    if args.len() != arity
                        || self
                            .graph
                            .extension_state::<crate::set_cost::SourceCostRoles>()
                            .and_then(|roles| roles.0.get(&helper.name))
                            != Some(&constructor)
                    {
                        return Err("set-cost requires a declared dynamic-cost constructor".into());
                    }
                    let args = args
                        .iter()
                        .map(|arg| self.expr(arg, aliases, 0))
                        .collect::<Result<_, _>>()?;
                    pb::action::Kind::SetCost(pb::SetCost {
                        target: Some(pb::Call {
                            func: constructor,
                            args,
                        }),
                        cost: Some(self.expr(value, aliases, 0)?),
                    })
                } else {
                    if let ResolvedCall::Func(function) = function
                        && self
                            .graph
                            .extension_state::<crate::set_cost::SourceCostRoles>()
                            .is_some_and(|roles| roles.0.contains_key(&function.name))
                    {
                        return Err(
                            "raw assigned-cost helper writes are not portable source actions"
                                .into(),
                        );
                    }
                    pb::action::Kind::Set(pb::Set {
                        target: Some(self.call(function, args, aliases, 0, span)?),
                        value: Some(self.expr(value, aliases, 0)?),
                    })
                },
            ),
            ResolvedAction::Change(span, change, function, args) => {
                if let ResolvedCall::Func(function) = function
                    && self
                        .graph
                        .extension_state::<crate::set_cost::SourceCostRoles>()
                        .is_some_and(|roles| roles.0.contains_key(&function.name))
                {
                    return Err(
                        "unpaired assigned-cost helper changes are not portable source actions"
                            .into(),
                    );
                }
                let call = self.call(function, args, aliases, 0, span)?;
                (
                    span,
                    match change {
                        ast::Change::Delete => pb::action::Kind::Delete(call),
                        ast::Change::Subsume => pb::action::Kind::Subsume(call),
                    },
                )
            }
            ResolvedAction::Panic(span, message) => {
                (span, pb::action::Kind::Panic(message.clone()))
            }
            _ => return Err("source local binding requires rule-head lowering".into()),
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
                if var.is_global_ref
                    && self
                        .graph
                        .extension_state::<crate::set_cost::SourceCostRoles>()
                        .is_some_and(|roles| roles.1.contains(&var.name))
                {
                    return Err("native set-cost captures cannot escape their action".into());
                }
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
                    let mut call = self.call(function, args, aliases, depth, span)?;
                    if let ResolvedCall::Func(function) = function
                        && let Some(constructor) = self
                            .graph
                            .extension_state::<crate::set_cost::SourceCostRoles>()
                            .and_then(|roles| roles.0.get(&function.name))
                    {
                        call.func = constructor.clone();
                        pb::node::Kind::GetCost(call)
                    } else {
                        pb::node::Kind::Call(call)
                    }
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
            .authoring_type_info()
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

// Parse configuration only. Unlike the native extension's builder, this must
// not allocate a scheduler instance in the producer's type environment.
fn source_scheduler_binding(span: &ast::Span, args: &[Expr]) -> Result<pb::BindScheduler, String> {
    let [Expr::Var(_, name), Expr::Call(config_span, kind, args)] = args else {
        return Err("source let-scheduler requires a name and scheduler configuration".into());
    };
    if kind != "back-off" {
        return Err(format!("source scheduler kind {kind} is unsupported"));
    }
    let tags =
        crate::scheduling::parse_tags(config_span, args).map_err(|error| error.to_string())?;
    let mut options = pb::BackOff::default();
    for (tag, value) in tags {
        let target = match tag.as_str() {
            ":match-limit" => &mut options.match_limit,
            ":ban-length" => &mut options.ban_length,
            ":node-limit" => &mut options.node_limit,
            _ => return Err(format!("unknown back-off scheduler tag {tag} at {span:?}")),
        };
        let Literal::Int(value) = value else {
            return Err(format!("scheduler {tag} must be a non-negative integer"));
        };
        usize::try_from(value)
            .map_err(|_| format!("scheduler {tag} exceeds native non-negative usize"))?;
        *target = Some(
            u64::try_from(value).map_err(|_| format!("scheduler {tag} must be non-negative"))?,
        );
    }
    Ok(pb::BindScheduler {
        name: name.clone(),
        scheduler: Some(pb::Scheduler {
            kind: Some(pb::scheduler::Kind::BackOff(options)),
        }),
    })
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
/// Core keeps literal sort/callable names; rule holders and selectors have
/// private presentation aliases, preserving shared occurrences rather than
/// literal `:ruleset`/default spellings. Reuse one renderer for the whole stream:
/// aliases are stable across phases, but do not recover original keys
/// for same-engine resupply. Execution names and structural-sort limits are unchanged.
/// Use [`Self::render_submission`] for Source-managed scopes, and a fresh renderer
/// after externally resetting or popping the text environment.
#[derive(Clone)]
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
    /// Render Experimental text using explicit inert native provider definitions.
    /// Clones and scope snapshots retain this same provider without reinitializing.
    pub fn with_extension(extension: Arc<dyn NativeExtension>) -> Result<Self, TransportError> {
        let mut renderer = Self::default();
        extension
            .initialize(&mut renderer.session.graph)
            .map_err(TransportError)?;
        renderer.session.extension = Some(extension);
        Ok(renderer)
    }

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
                cost_models: HashMap::new(),
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
        if self.dialect == Dialect::Core && (program.nodes.iter().any(|node| matches!(node.kind, Some(pb::node::Kind::GetCost(_))))
            || super::command_tree(&program.commands).any(|command| matches!(
                &command.kind,
                Some(pb::command::Kind::Action(action)) if matches!(action.kind, Some(pb::action::Kind::SetCost(_)))
            ))
            || program.rules.iter().any(|rule| matches!(
                &rule.kind,
                Some(pb::rule_decl::Kind::Rule(rule)) if rule.head.iter().any(|action| matches!(action.kind, Some(pb::action::Kind::SetCost(_))))
            )))
        {
            return Err(TransportError("assigned-cost source rendering is not supported".into()));
        }
        let mut lowered = program.clone();
        let prepared = self
            .session
            .prepare(&mut lowered)
            .map_err(|e| TransportError(e.0.message))?;
        if self.dialect == Dialect::Experimental {
            let unextractable: HashSet<_> = prepared
                .definitions
                .declarations
                .iter()
                .filter_map(|declaration| match &declaration.kind {
                    Some(pb::declaration::Kind::Constructor(constructor))
                        if constructor.unextractable =>
                    {
                        Some(native_name("call", &constructor.name))
                    }
                    _ => None,
                })
                .collect();
            if lowered.nodes.iter().any(|node| matches!(&node.kind, Some(pb::node::Kind::GetCost(call)) if unextractable.contains(&call.func)))
                || super::command_tree(&lowered.commands).filter_map(|command| match &command.kind {
                    Some(pb::command::Kind::Action(action)) => Some(action), _ => None,
                }).chain(lowered.rules.iter().flat_map(|rule| match &rule.kind {
                    Some(pb::rule_decl::Kind::Rule(rule)) => rule.head.as_slice(), _ => &[],
                })).any(|action| match &action.kind {
                    Some(pb::action::Kind::SetCost(set)) => set.target.as_ref().is_some_and(|call| unextractable.contains(&call.func)),
                    Some(pb::action::Kind::Delete(call)) => unextractable.contains(&call.func),
                    _ => false,
                })
            { return Err(TransportError("source dynamic-cost helpers do not exist for unextractable constructors".into())); }
        }
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
        if let Some(extension) = &self.session.extension {
            extension.initialize(&mut native).map_err(TransportError)?;
        }
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
        for (_, mut command) in materialize_sorts(
            &lowered,
            &mut native,
            &mut HashSet::new(),
            &prepared.context.native_spans,
        )
        .map_err(TransportError)?
        {
            source_sort_names(&mut command, &authored);
            text_native
                .resolve_command_before_proofs(command)
                .map_err(|error| TransportError(error.to_string()))?;
        }
        // Rule heads are reprojected for native cost roles below. Normalize
        // this private canonical copy just like the execution copy, using the
        // initialized provider and nominal context, not raw Custom payloads.
        lower_custom_values(
            &mut definitions,
            &mut native,
            self.session.extension.as_deref(),
        )
        .map_err(TransportError)?;
        lower_container_values(&mut definitions).map_err(TransportError)?;
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
        if self.dialect == Dialect::Core {
            // Native shadowing includes sorts, functions and global lets. Do
            // not silently capture a literal authored name with a private
            // selector from this or an earlier phase. No new identity registry:
            // aliases are derived only from the existing prepared handles.
            let private: HashSet<_> = prepared
                .rulesets
                .iter()
                .filter(|name| !name.is_empty())
                .cloned()
                .chain(
                    prepared
                        .rules
                        .iter()
                        .filter(|name| !name.is_empty())
                        .map(|name| format!("{name}_holder")),
                )
                .map(|name| native_name("source_ruleset", &name))
                .collect();
            for name in authored.sorts.values().chain(authored.callables.values()) {
                if private.contains(name) {
                    return Err(TransportError(format!(
                        "authored Core name {name:?} collides with a private source ruleset"
                    )));
                }
            }
        }
        let mut constructor_cost_tables = HashMap::new();
        {
            // Retain the exact registration link, not a private-name heuristic.
            // Sites retain original request indices, whereas `lowered` has
            // already filtered compatible resupply. Pair prepared commands at
            // their common site instead of indexing that filtered view.
            let constructors: HashMap<_, _> = prepared
                .installations
                .iter()
                .filter_map(
                    |installation| match (&installation.site, &installation.command) {
                        (
                            pb::maintenance_site::Target::Declaration(index),
                            Some(Command::Constructor { name, .. }),
                        ) => Some((*index, name.clone())),
                        _ => None,
                    },
                )
                .collect();
            for installation in &prepared.installations {
                if installation.declaration.is_none()
                    && let pb::maintenance_site::Target::Declaration(index) = &installation.site
                    && let Some(constructor) = constructors.get(index)
                    && let Some(Command::Function {
                        name, hidden: true, ..
                    }) = &installation.command
                    && *name == crate::set_cost::get_cost_table_name(constructor)
                {
                    constructor_cost_tables.insert(name.clone(), constructor.clone());
                }
            }
            for declaration in &prepared.definitions.declarations {
                if let Some(pb::declaration::Kind::Constructor(constructor)) = &declaration.kind {
                    let constructor = native_name("call", &constructor.name);
                    let helper = crate::set_cost::get_cost_table_name(&constructor);
                    if self
                        .session
                        .graph
                        .get_function(&helper)
                        .is_some_and(|function| function.is_hidden())
                    {
                        constructor_cost_tables.insert(helper, constructor);
                    }
                }
            }
        }
        if self.dialect == Dialect::Experimental {
            for (helper, constructor) in &constructor_cost_tables {
                let alias = crate::set_cost::get_cost_table_name(
                    authored
                        .callables
                        .get(constructor)
                        .ok_or_else(|| TransportError("missing source constructor alias".into()))?,
                );
                if occupied
                    .insert(alias.clone(), helper.clone())
                    .is_some_and(|old| old != *helper)
                    || self.session.graph.get_sort_by_name(&alias).is_some()
                    || self.session.graph.get_function(&alias).is_some()
                    || self.session.graph.type_info().is_primitive(&alias)
                {
                    return Err(TransportError(format!(
                        "dynamic-cost source alias {alias:?} collides with a native name"
                    )));
                }
                authored.callables.insert(helper.clone(), alias);
            }
        }
        let source = render_prepared(
            &lowered,
            &definitions,
            &prepared,
            self.dialect,
            &authored,
            &declaration_order,
            &constructor_cost_tables,
            self.session.extension.as_deref(),
        )?;
        // The renderer's graph is always NORMAL and receives inert definitions
        // only: registration compiles rules/merges, but no action/helper runs.
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
        // Retain inert definitions only, never scheduler work. Preparation of
        // the next phase reads this same native binding metadata. The cloned
        // Session is adopted only after text and all registrations succeeded.
        for command in &lowered.commands {
            if let Some(pb::command::Kind::BindScheduler(bind)) = &command.kind {
                let (scheduler, resource_limited) =
                    wire_back_off(bind).map_err(|error| TransportError(error.0.message))?;
                let id = session.graph.add_scheduler(Box::new(scheduler));
                session
                    .graph
                    .extension_state_or_default::<PermanentSchedulerState>()
                    .insert(
                        bind.name.clone(),
                        SchedulerBinding {
                            id,
                            resource_limited,
                        },
                    );
            }
        }
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

// Project canonical cost actions through the real native macros, retaining
// addressed arguments across the paired storage cleanup. No helper name is
// interpreted without its prepared constructor-registration link.
fn source_cost_actions(
    program: &pb::Program,
    action: &pb::Action,
    occurrence: usize,
    request: u64,
    in_rule: bool,
    helpers: &HashMap<String, String>,
    native_spans: &NativeSpans,
) -> Result<Vec<Action>, String> {
    let span = native_span(program, action.span.as_ref(), native_spans)?;
    // Project authored binders before introducing any private capture name.
    // Mapping the completed head would let an authored wire variable capture
    // the generated Let, unlike the runtime's ordinary SSA lowering.
    let expr = |index| -> Result<Expr, String> {
        let expr = expression(program, index, &mut HashSet::new(), native_spans)?;
        Ok(if in_rule {
            expr.map_symbols(&mut |name| name, &mut |name: String| {
                native_name("var", &name)
            })
        } else {
            expr
        })
    };
    match &action.kind {
        Some(pb::action::Kind::SetCost(set)) => {
            let target = set.target.as_ref().ok_or("missing cost target")?;
            if !helpers.values().any(|name| *name == target.func) {
                return Err("missing prepared constructor-cost helper".into());
            }
            Ok(vec![Action::Expr(
                span.clone(),
                Expr::Call(
                    span.clone(),
                    "set-cost".into(),
                    vec![
                        Expr::Call(
                            span.clone(),
                            target.func.clone(),
                            target
                                .args
                                .iter()
                                .map(|arg| expr(*arg))
                                .collect::<Result<_, _>>()?,
                        ),
                        expr(set.cost.ok_or("missing cost value")?)?,
                    ],
                ),
            )])
        }
        Some(pb::action::Kind::Delete(call)) if helpers.values().any(|name| *name == call.func) => {
            let (helper, _) = helpers
                .iter()
                .find(|(_, name)| **name == call.func)
                .expect("known helper role");
            let mut actions = Vec::new();
            let mut key = Vec::new();
            for (index, argument) in call.args.iter().enumerate() {
                let name = format!("__egglog_source_delete_{request}_{occurrence}_{index}");
                actions.push(Action::Let(span.clone(), name.clone(), expr(*argument)?));
                key.push(Expr::Var(span.clone(), name));
            }
            actions.push(Action::Change(
                span.clone(),
                ast::Change::Delete,
                call.func.clone(),
                key.clone(),
            ));
            actions.push(Action::Change(
                span,
                ast::Change::Delete,
                helper.clone(),
                key,
            ));
            Ok(actions)
        }
        _ => {
            let actions = lower_action(program, action, native_spans)?;
            Ok(if in_rule {
                ast::GenericActions(actions)
                    .map_symbols(&mut |name| name, &mut |name: String| {
                        native_name("var", &name)
                    })
                    .0
            } else {
                actions
            })
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn render_prepared(
    program: &pb::Program,
    rule_program: &pb::Program,
    prepared: &Prepared,
    dialect: Dialect,
    authored: &NativeNames,
    declaration_order: &[usize],
    constructor_cost_tables: &HashMap<String, String>,
    extension: Option<&dyn NativeExtension>,
) -> Result<String, TransportError> {
    let native_spans = &prepared.context.native_spans;
    // Canonical rules and the submitted program have independent file indices.
    let rule_spans = NativeSpans::default();
    let result = (|| -> Result<Vec<Command>, String> {
        if program.ir_version != 1 {
            return Err("unsupported source IR version".into());
        }
        validate_union_occurrences(program)?;
        let mut native = match dialect {
            Dialect::Experimental => crate::new_experimental_egraph(),
            Dialect::Core => EGraph::default(),
        };
        if let Some(extension) = extension {
            extension.initialize(&mut native)?;
        }
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
        for command in super::command_tree(&program.commands) {
            match &command.kind {
                Some(pb::command::Kind::BindScheduler(_)) if dialect == Dialect::Core =>
                    return Err("Core source has no named scheduler syntax".into()),
                Some(pb::command::Kind::Run(run)) if dialect == Dialect::Core && !run.scheduler.is_empty() =>
                    return Err("Core source has no named scheduler syntax".into()),
                Some(pb::command::Kind::BindScheduler(bind)) => names.push(&bind.name),
                Some(pb::command::Kind::Run(run)) if !run.scheduler.is_empty() => names.push(&run.scheduler),
                _ => (),
            }
            if let Some(pb::command::Kind::ProveExists(prove)) = &command.kind {
                names.push(prove.constructor.as_str());
            }
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
        let mut occupied: HashSet<_> = names.iter().map(|name| (*name).to_string()).collect();
        // Logical ruleset names are relocated, not interpolated as atoms.
        occupied.extend(program.rulesets.iter().filter_map(|ruleset| ruleset.name.clone()));
        let mut parser = std::mem::take(&mut native.parser);
        for name in names {
            if !matches!(parser.get_expr_from_string(None, name), Ok(Expr::Var(_, parsed)) if parsed == name) {
                return Err(format!("identifier {name:?} cannot be rendered as one native source atom"));
            }
        }
        let mut commands = vec![];
        for declaration in &program.declarations {
            if let Some(pb::declaration::Kind::EqSort(sort)) = &declaration.kind {
                commands.push(Command::Sort {
                    span: native_span(program, declaration.span.as_ref(), native_spans)?, name: sort.name.clone(), presort_and_args: None,
                    uf: None, proof_func: None, container_rebuild: None, proof_constructors: None, unionable: true,
                });
            }
        }
        commands.extend(prepared.materialized.iter().cloned());
        let table_names = project_names(&mut pb::Program::default(), &prepared.definitions).callables;
        for &index in declaration_order {
            let declaration = &program.declarations[index];
            let span = native_span(program, declaration.span.as_ref(), native_spans)?;
            let table_name = if dialect == Dialect::Experimental {
                let name = match &declaration.kind {
                    Some(pb::declaration::Kind::Constructor(table)) => Some(&table.name),
                    Some(pb::declaration::Kind::Function(table)) => Some(&table.name),
                    Some(pb::declaration::Kind::Relation(table)) => Some(&table.name),
                    _ => None,
                };
                name.map(|name| ast::TableName::Public(table_names[name].clone()))
            } else {
                None
            };
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
                        table_name,
                        schema: signature(program, &constructor.inputs, constructor.output)?,
                        cost: constructor
                            .cost
                            .map(|index| -> Result<u64, String> {
                                match expression(program, index, &mut HashSet::new(), native_spans)? {
                                    Expr::Lit(_, Literal::Int(cost)) => u64::try_from(cost)
                                        .map_err(|_| "negative constructor cost".into()),
                                    _ => Err("source constructor cost must be an inert i64".into()),
                                }
                            })
                            .transpose()?,
                        unextractable: constructor.unextractable,
                        hidden: declaration.hidden,
                        let_binding: false,
                        term_constructor: None,
                    },
                    pb::declaration::Kind::Function(function) => Command::Function {
                        span,
                        name: function.name.clone(),
                        table_name,
                        schema: signature(program, &function.inputs, function.output)?,
                        merge: function
                            .merge
                            .map(|index| expression(program, index, &mut HashSet::new(), native_spans))
                            .transpose()?,
                        hidden: declaration.hidden,
                        let_binding: false,
                        term_constructor: None,
                        unextractable: true,
                    },
                    pb::declaration::Kind::Primitive(primitive) => {
                        if dialect == Dialect::Core {
                            return Err("program-defined primitive source requires the Experimental provider".into());
                        }
                        primitive_command(program, primitive, span, native_spans)?
                    },
                    pb::declaration::Kind::Relation(relation) => Command::Relation {
                        span,
                        name: relation.name.clone(),
                        table_name,
                        inputs: relation.inputs.iter().map(|arg| sort_name(&program.sorts, arg.sort)).collect::<Result<_, _>>()?,
                    },
                    pb::declaration::Kind::HostPrimitive(_) | pb::declaration::Kind::HostSortFamily(_) => continue,
                },
            );
        }
        {
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
                if let Command::Rule { rule } = &mut command {
                    let index = prepared.rules.iter().position(|name| name == &rule.name)
                        .ok_or("missing prepared rule occurrence")?;
                    if let Some(pb::rule_decl::Kind::Rule(body)) = &rule_program.rules[index].kind {
                        let mut head = Vec::new();
                        for (index, action) in body.head.iter().enumerate() {
                            if dialect == Dialect::Experimental {
                                head.extend(source_cost_actions(rule_program, action, index, prepared.request, true, constructor_cost_tables, &rule_spans)?);
                            } else {
                                // Core has no assigned-cost storage to clean up.
                                // Project the canonical action, not native
                                // cleanup's temporary Lets after dropping only
                                // its auxiliary Delete. Preserve the prepared
                                // query, occurrence and all rule options.
                                head.extend(ast::GenericActions(lower_action(rule_program, action, &rule_spans)?)
                                    .map_symbols(&mut |name| name, &mut |name: String| native_name("var", &name)).0);
                            }
                        }
                        rule.head.0 = head;
                    }
                }
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
        }
        for (position, mut command) in program.commands.iter().enumerate() {
            let mut fail_spans = vec![];
            while let Some(pb::command::Kind::Fail(child)) = &command.kind {
                fail_spans.push(native_span(program, command.span.as_ref(), native_spans)?);
                command = child;
            }
            if !fail_spans.is_empty() && matches!(&command.kind,
                Some(pb::command::Kind::Action(pb::Action { kind: Some(pb::action::Kind::SetCost(_)), .. }))) {
                return Err("source Fail cannot wrap the native multi-command set-cost macro".into());
            }
            if !(fail_spans.is_empty() || matches!(
                &command.kind,
                Some(pb::command::Kind::Action(_)
                    | pb::command::Kind::Check(_)
                    | pb::command::Kind::Prove(_)
                    | pb::command::Kind::ProveExists(_)
                    | pb::command::Kind::Run(_)
                    | pb::command::Kind::Stats(_))
            ) || matches!(
                &command.kind,
                Some(pb::command::Kind::Repeat(_) | pb::command::Kind::Saturate(_))
            ))
            {
                return Err("Fail requires a supported native command; observation and loop wrappers are not implemented".into());
            }
            let first_command = commands.len();
            let span = native_span(program, command.span.as_ref(), native_spans)?;
            match command.kind.as_ref().ok_or("missing command kind")? {
                pb::command::Kind::Action(action) => {
                    if let Some(closed) = prepared.context.constructor_dags.get(&vec![position as u32]) {
                        commands.push(Command::ActionScope(span, ast::GenericActions(
                            constructor_dag_actions(program, action, |name| occupied.contains(name)
                                || native.get_sort_by_name(name).is_some()
                                || native.type_info().get_func_type(name).is_some()
                                || native.type_info().is_primitive(name), native_spans, closed)?.0,
                        )));
                    } else {
                        commands.extend(
                            (if dialect == Dialect::Experimental {
                                source_cost_actions(program, action, first_command, prepared.request, false, constructor_cost_tables, native_spans)?
                            } else { lower_action(program, action, native_spans)? })
                                .into_iter()
                                .map(Command::Action),
                        );
                    }
                }
                pb::command::Kind::Check(check) => {
                    commands.push(Command::Check(span, facts(program, &check.facts, native_spans)?))
                }
                pb::command::Kind::Stats(_) => {
                    commands.push(Command::PrintOverallStatistics(span, None));
                }
                pb::command::Kind::PrintSize(print) => {
                    if print.tables.len() > 1 {
                        return Err("source print-size supports at most one table".into());
                    }
                    commands.push(Command::PrintSize(span, print.tables.first().cloned()));
                }
                pb::command::Kind::BindScheduler(_) => {
                    if dialect == Dialect::Core {
                        return Err("Core source has no named scheduler syntax".into());
                    }
                    let Expr::Call(_, name, args) = source_extended_schedule(
                        program, command, &prepared.context, authored, 0,
                    )? else { unreachable!("a binding projects to a native command") };
                    commands.push(Command::UserDefined(span, name, args));
                }
                pb::command::Kind::Prove(prove) => {
                    commands.push(Command::Prove(span, facts(program, &prove.facts, native_spans)?))
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
                    if matches!(pb::Extractor::try_from(extract.extractor), Ok(pb::Extractor::Tree | pb::Extractor::GreedyDag))
                        && (dialect == Dialect::Experimental || extract.extractor == i32::from(pb::Extractor::Tree))
                        && extract.cost_model.is_empty()
                        && extract.variants > 0 =>
                {
                    if extract.roots.len() > 1 {
                        if dialect == Dialect::Core {
                            return Err("Core source has no aggregate multi-extract syntax".into());
                        }
                        let mut args = vec![Expr::Lit(span.clone(), Literal::Int(i64::from(extract.variants)))];
                        args.extend(extract.roots.iter().map(|root| {
                            // Generic command traversal skips UserDefined args;
                            // only these typed root positions contain callables.
                            Ok(expression(program, *root, &mut HashSet::new(), native_spans)?.map_symbols(
                                &mut |name: String| authored.callables.get(&name).cloned().unwrap_or(name),
                                &mut |name| name,
                            ))
                        }).collect::<Result<Vec<_>, String>>()?);
                        if extract.extractor == i32::from(pb::Extractor::GreedyDag) {
                            args.extend([Expr::Var(span.clone(), ":extractor".into()), Expr::Var(span.clone(), "greedy-dag".into())]);
                        }
                        commands.push(Command::UserDefined(span, "multi-extract".into(), args));
                        continue;
                    }
                    for root in &extract.roots {
                        let root = expression(program, *root, &mut HashSet::new(), native_spans)?;
                        let variants = Expr::Lit(span.clone(), Literal::Int(if extract.variants == 1 { 0 } else { i64::from(extract.variants) }));
                        commands.push(if extract.extractor == i32::from(pb::Extractor::GreedyDag) {
                            Command::UserDefined(span.clone(), "extract".into(), vec![root, variants,
                                Expr::Var(span.clone(), ":extractor".into()), Expr::Var(span.clone(), "greedy-dag".into())])
                        } else { Command::Extract(
                            span.clone(),
                            root, variants,
                        ) });
                    }
                }
                pb::command::Kind::KeepBest(keep) if dialect == Dialect::Experimental
                    && keep.cost_model.is_empty()
                    && matches!(pb::Extractor::try_from(keep.extractor), Ok(pb::Extractor::Tree | pb::Extractor::GreedyDag)) => {
                    let mut args = keep.tables.iter().map(|name| {
                        let alias = authored.callables.get(name).ok_or_else(|| format!("unknown keep-best table {name:?}"))?;
                        Ok(Expr::Lit(span.clone(), Literal::String(alias.clone())))
                    }).collect::<Result<Vec<_>, String>>()?;
                    if keep.extractor == i32::from(pb::Extractor::GreedyDag) {
                        args.extend([Expr::Var(span.clone(), ":extractor".into()), Expr::Var(span.clone(), "greedy-dag".into())]);
                    }
                    commands.push(Command::UserDefined(span, "keep-best".into(), args));
                }
                pb::command::Kind::Run(_)
                | pb::command::Kind::Repeat(_)
                | pb::command::Kind::Saturate(_) => {
                    let legacy_body = match &command.kind {
                        Some(pb::command::Kind::Repeat(repeat))
                            if repeat.times == Some(0) && repeat.until.is_empty() => Some(&repeat.body),
                        Some(pb::command::Kind::Saturate(saturate))
                            if saturate.until.is_empty() && saturate.max_iterations.is_some_and(|bound| (2..=u64::from(u32::MAX)).contains(&bound)) => Some(&saturate.body),
                        _ => None,
                    };
                    let legacy = matches!(&command.kind, Some(pb::command::Kind::Run(run)) if run.scheduler.is_empty())
                        || legacy_body.is_some_and(|body| matches!(body.as_slice(),
                            [pb::Command { kind: Some(pb::command::Kind::Run(run)), .. }] if run.scheduler.is_empty()));
                    if dialect == Dialect::Experimental && !legacy {
                        commands.push(Command::UserDefined(span, "run-schedule".into(), vec![
                            source_extended_schedule(program, command, &prepared.context, authored, 0)?,
                        ]));
                    } else {
                        commands.push(Command::RunSchedule(source_schedule(
                            program, command, Some(&prepared.context), native_spans,
                        )?));
                    }
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
            if dialect == Dialect::Core {
                // Ruleset positions are separate from callable heads, rule
                // labels and binders. Keep each occurrence in its prepared
                // holder and use the flattened unique selector for every root.
                match &mut *leaf {
                    Command::AddRuleset(_, name) => *name = native_name("source_ruleset", name),
                    Command::UnstableCombinedRuleset(_, name, children) => {
                        *name = native_name("source_ruleset", name);
                        for child in children { *child = native_name("source_ruleset", child); }
                    }
                    Command::Rule { rule } => rule.ruleset = native_name("source_ruleset", &rule.ruleset),
                    Command::Rewrite(name, _, _) | Command::BiRewrite(name, _) => *name = native_name("source_ruleset", name),
                    Command::RunSchedule(schedule) => {
                        let mut pending = vec![schedule];
                        while let Some(schedule) = pending.pop() {
                            match schedule {
                                ast::Schedule::Run(_, config) => config.ruleset = native_name("source_ruleset", &config.ruleset),
                                ast::Schedule::Repeat(_, _, child) | ast::Schedule::Saturate(_, child) => pending.push(child),
                                ast::Schedule::Sequence(_, children) => pending.extend(children),
                            }
                        }
                    }
                    _ => (),
                }
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
                Command::UserDefined(_, command, args) if command == "extract" => {
                    if let Some(root) = args.first_mut() {
                        *root = root.clone().map_symbols(&mut |name: String| authored.callables.get(&name).cloned().unwrap_or(name), &mut |name| name);
                    }
                }
                Command::PrintFunction(_, name, ..) => {
                    if let Some(logical) = authored.callables.get(name) {
                        *name = logical.clone();
                    }
                }
                Command::PrintSize(_, Some(name)) => {
                    let physical = native_name("call", name);
                    *name = authored.callables.get(&physical)
                        .ok_or_else(|| format!("unknown PrintSize selector {name:?}"))?.clone();
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
            if let Command::ActionScope(_, expected) = command {
                let parsed = parser.get_program_from_string(None, &command.to_string()).map_err(|error| error.to_string())?;
                let [Command::ActionScope(_, actual)] = parsed.as_slice() else {
                    return Err("action scope changes meaning when parsed as source".into());
                };
                // Display alone cannot distinguish literal kinds or NaN payloads.
                // Parse the whole lexical context, then compare exact literals.
                let literals = |actions: &ast::Actions| {
                    let mut values = Vec::new();
                    actions.clone().visit_exprs(&mut |expr| {
                        if let Expr::Lit(_, value) = &expr { values.push(value.clone()); }
                        expr
                    });
                    values
                };
                let left = literals(expected);
                let right = literals(actual);
                if command.to_string() != parsed[0].to_string()
                    || left.len() != right.len()
                    || !left.iter().zip(&right).all(|(left, right)| match (left, right) {
                        (Literal::Float(left), Literal::Float(right)) => left.0.to_bits() == right.0.to_bits(),
                        _ => left == right,
                    })
                {
                    return Err("action scope or scalar payload changes meaning when parsed as source".into());
                }
                continue;
            }
            let (actions, in_rule) = match command {
                Command::Action(action) => (std::slice::from_ref(action), false),
                Command::Rule { rule } => (rule.head.0.as_slice(), true),
                _ => continue,
            };
            for action in actions {
                let Action::Expr(_, expected) = action else { continue };
                if dialect == Dialect::Experimental
                    && matches!(expected, Expr::Call(_, name, _) if name == "set-cost")
                { continue; }
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
            // command, which cannot be proof-instrumented. Admitted legacy
            // runs need their unshadowed spelling even beneath Fail.
            let leaf = match command {
                Command::RunSchedule(ast::Schedule::Run(_, config)) => {
                    if config.until.is_some() {
                        format!("(run-schedule {config})")
                    } else {
                        format!("(run {} 1)", config.ruleset)
                    }
                }
                Command::RunSchedule(ast::Schedule::Repeat(span, bound, body))
                    if dialect == Dialect::Experimental =>
                {
                    let ast::Schedule::Sequence(_, children) = body.as_ref() else {
                        unreachable!("source_schedule supplies the loop body envelope")
                    };
                    let [ast::Schedule::Run(_, config)] = children.as_slice() else {
                        unreachable!("only legacy single-Run loops were admitted")
                    };
                    // Legacy run is parser sugar, not a dedicated AST variant.
                    // Use the native printer only; this AST is never executed.
                    Command::UserDefined(
                        span.clone(),
                        "run".into(),
                        vec![
                            Expr::Var(span.clone(), config.ruleset.clone()),
                            Expr::Lit(
                                span,
                                Literal::Int(i64::try_from(bound).expect("legacy bound checked")),
                            ),
                        ],
                    )
                    .to_string()
                }
                Command::RunSchedule(schedule) => {
                    format!("(run-schedule {})", render_schedule(&schedule))
                }
                command @ Command::Constructor { .. } if dialect == Dialect::Experimental => {
                    format!("(with-dynamic-cost {command})")
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

// Print only the existing experimental extension language. Callable names in
// condition expressions must be mapped here: native generic AST mapping skips
// UserDefined arguments, and scheduler/ruleset positions are not callables.
fn source_extended_schedule(
    program: &pb::Program,
    command: &pb::Command,
    context: &RequestOccurrences,
    authored: &NativeNames,
    depth: usize,
) -> Result<Expr, String> {
    if depth > 256 {
        return Err("source schedule nesting exceeds 256".into());
    }
    let span = native_span(program, command.span.as_ref(), &context.native_spans)?;
    let header = match &command.kind {
        Some(pb::command::Kind::Repeat(repeat)) if !repeat.until.is_empty() => {
            Some(("repeat", repeat.times, &repeat.until, &repeat.body))
        }
        Some(pb::command::Kind::Saturate(saturate))
            if saturate.max_iterations.is_some() || !saturate.until.is_empty() =>
        {
            Some((
                "saturate",
                saturate.max_iterations,
                &saturate.until,
                &saturate.body,
            ))
        }
        _ => None,
    };
    if let Some((head, bound, until, body)) = header {
        let mut args = vec![Expr::Lit(span.clone(), Literal::Unit)];
        if let Some(bound) = bound {
            args.push(Expr::Call(
                span.clone(),
                if head == "repeat" {
                    "times"
                } else {
                    "max-iterations"
                }
                .into(),
                vec![Expr::Lit(
                    span.clone(),
                    Literal::Int(
                        i64::try_from(bound)
                            .map_err(|_| "loop bound exceeds native source integer")?,
                    ),
                )],
            ));
        }
        if !until.is_empty() {
            let conditions = facts(program, until, &context.native_spans)?
                .into_iter()
                .map(|fact| {
                    let expr = match fact {
                        Fact::Fact(expr) => expr,
                        Fact::Eq(span, left, right) => {
                            Expr::Call(span, "=".into(), vec![left, right])
                        }
                    };
                    expr.map_symbols(
                        &mut |name: String| authored.callables.get(&name).cloned().unwrap_or(name),
                        &mut |name| name,
                    )
                })
                .collect();
            args.push(Expr::Call(span.clone(), "until".into(), conditions));
        }
        args.push(Expr::Call(
            span.clone(),
            "body".into(),
            body.iter()
                .map(|child| source_extended_schedule(program, child, context, authored, depth + 1))
                .collect::<Result<Vec<_>, _>>()?,
        ));
        return Ok(Expr::Call(span, head.into(), args));
    }
    let (head, args) = match command.kind.as_ref().ok_or("missing schedule kind")? {
        pb::command::Kind::Fail(child) => (
            "fail",
            vec![source_extended_schedule(
                program,
                child,
                context,
                authored,
                depth + 1,
            )?],
        ),
        pb::command::Kind::Action(action) => {
            let [action]: [Action; 1] = lower_action(program, action, &context.native_spans)?
                .try_into()
                .map_err(|_| "source schedule action requires one native action")?;
            let action = action.map_symbols(
                &mut |name: String| authored.callables.get(&name).cloned().unwrap_or(name),
                &mut |name| name,
            );
            match action {
                Action::Expr(_, expr) => ("eval", vec![expr]),
                Action::Set(_, name, args, value) => {
                    ("set", vec![Expr::Call(span.clone(), name, args), value])
                }
                Action::Change(_, change, name, args) => (
                    if change == ast::Change::Delete {
                        "delete"
                    } else {
                        "subsume"
                    },
                    vec![Expr::Call(span.clone(), name, args)],
                ),
                Action::Union(_, left, right) => ("union", vec![left, right]),
                Action::Panic(_, message) => (
                    "panic",
                    vec![Expr::Lit(span.clone(), Literal::String(message))],
                ),
                Action::Let(..) => return Err("source schedule has no global Let action".into()),
            }
        }
        pb::command::Kind::Run(run) => {
            let name = match run
                .ruleset
                .as_ref()
                .and_then(|r| r.kind.as_ref())
                .ok_or("missing ruleset reference")?
            {
                pb::ruleset_ref::Kind::Name(name) => context.names.get(name),
                pb::ruleset_ref::Kind::Index(index) => context.rulesets.get(*index as usize),
            }
            .ok_or("invalid source ruleset reference")?;
            if name == ":until" {
                return Err("experimental run cannot spell a ruleset named :until".into());
            }
            let mut args = vec![];
            let head = if run.scheduler.is_empty() {
                "run"
            } else {
                args.push(Expr::Var(span.clone(), run.scheduler.clone()));
                "run-with"
            };
            args.push(Expr::Var(span.clone(), name.clone()));
            (head, args)
        }
        pb::command::Kind::BindScheduler(bind) => {
            let Some(pb::scheduler::Kind::BackOff(options)) =
                bind.scheduler.as_ref().and_then(|s| s.kind.as_ref())
            else {
                return Err("source scheduler kind is unsupported".into());
            };
            let mut args = vec![];
            for (tag, value) in [
                (":match-limit", options.match_limit),
                (":ban-length", options.ban_length),
                (":node-limit", options.node_limit),
            ] {
                if let Some(value) = value {
                    args.extend([
                        Expr::Var(span.clone(), tag.into()),
                        Expr::Lit(
                            span.clone(),
                            Literal::Int(
                                i64::try_from(value).map_err(
                                    |_| "scheduler option exceeds native source integer",
                                )?,
                            ),
                        ),
                    ]);
                }
            }
            (
                "let-scheduler",
                vec![
                    Expr::Var(span.clone(), bind.name.clone()),
                    Expr::Call(span.clone(), "back-off".into(), args),
                ],
            )
        }
        pb::command::Kind::Repeat(repeat) if repeat.until.is_empty() => {
            let count = repeat.times.ok_or("missing Repeat count")?;
            let mut args = vec![];
            let head = if count == 1 {
                "seq"
            } else {
                args.push(Expr::Lit(
                    span.clone(),
                    Literal::Int(
                        i64::try_from(count)
                            .map_err(|_| "Repeat count exceeds native source integer")?,
                    ),
                ));
                "repeat"
            };
            for child in &repeat.body {
                args.push(source_extended_schedule(
                    program,
                    child,
                    context,
                    authored,
                    depth + 1,
                )?);
            }
            (head, args)
        }
        pb::command::Kind::Saturate(saturate) => {
            let args = saturate
                .body
                .iter()
                .map(|child| source_extended_schedule(program, child, context, authored, depth + 1))
                .collect::<Result<Vec<_>, _>>()?;
            ("saturate", args)
        }
        pb::command::Kind::PrintSize(print) if print.tables.len() <= 1 => {
            let args = print
                .tables
                .iter()
                .map(|name| {
                    let physical = native_name("call", name);
                    Ok(Expr::Var(
                        span.clone(),
                        authored
                            .callables
                            .get(&physical)
                            .ok_or_else(|| format!("unknown PrintSize selector {name:?}"))?
                            .clone(),
                    ))
                })
                .collect::<Result<Vec<_>, String>>()?;
            ("print-size", args)
        }
        _ => return Err("source schedule body has no supported native projection".into()),
    };
    Ok(Expr::Call(span, head.into(), args))
}

// Preserve the wire distinction between exact Repeat1 (an explicit seq) and
// bounded Saturate1 (a native repeat). The executor's normalization deliberately
// erases that syntactic distinction, so it is not the source inverse.
fn source_schedule(
    program: &pb::Program,
    command: &pb::Command,
    context: Option<&RequestOccurrences>,
    native_spans: &NativeSpans,
) -> Result<ast::Schedule, String> {
    let span = native_span(program, command.span.as_ref(), native_spans)?;
    if let Some(pb::command::Kind::Repeat(repeat)) = &command.kind
        && repeat.times == Some(1)
        && !repeat.until.is_empty()
    {
        let [child] = repeat.body.as_slice() else {
            return Err("source loop-until requires one conditional Run".into());
        };
        if !matches!(&child.kind, Some(pb::command::Kind::Run(run)) if run.scheduler.is_empty()) {
            return Err("source loop-until requires one conditional Run without scheduler".into());
        }
        let ast::Schedule::Run(_, mut config) =
            source_schedule(program, child, context, native_spans)?
        else {
            unreachable!("conditional child is a Run")
        };
        config.until = Some(facts(program, &repeat.until, native_spans)?);
        return Ok(ast::Schedule::Run(span, config));
    }
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
        .map(|child| source_schedule(program, child, context, native_spans))
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
        ast::Schedule::Run(_, config) => return config.to_string(),
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
