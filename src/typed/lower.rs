use super::{
    Action, CallableRef, Fact, Ruleset, Schedule, SortRef, TypedError,
    decl::{CallKind, CallableDef, SortKind},
    expr::{Expr, Identity, NodeKind, VariableKey},
    program::{Definition, DefinitionKind},
    rule::{RuleData, ScheduleNode},
    session::LoweringLimits,
};
use egglog::ast::{self as ast, Command};
use egglog::util::FreshGen;
use std::{
    any::TypeId,
    collections::{HashMap, HashSet, VecDeque},
    sync::Arc,
};

#[derive(Clone)]
pub(crate) struct Installed {
    pub poisoned: bool,
    pub sorts: HashMap<Arc<str>, SortRef>,
    pub declarations: HashMap<Arc<str>, CallableDef>,
    pub captures: HashMap<Arc<str>, (Expr, String)>,
    pub globals: HashMap<String, SortRef>,
    pub rules: HashMap<Identity<RuleData>, String>,
    pub groups: HashMap<Vec<Identity<RuleData>>, String>,
}

impl Default for Installed {
    fn default() -> Self {
        Self {
            poisoned: false,
            sorts: [
                "i64", "f64", "bool", "String", "Unit", "BigInt", "BigRat", "Rational",
            ]
            .into_iter()
            .map(|name| (name.into(), SortRef::builtin(name)))
            .collect(),
            declarations: HashMap::new(),
            captures: HashMap::new(),
            globals: HashMap::new(),
            rules: HashMap::new(),
            groups: HashMap::new(),
        }
    }
}

pub(crate) enum Commit {
    None,
    Sort(SortRef),
    Declaration(CallableDef),
    Capture(Arc<str>, Expr, String),
    Global(String, SortRef),
    Rule(Identity<RuleData>, String),
    Group(Vec<Identity<RuleData>>, String),
}
impl Commit {
    pub fn apply(self, state: &mut Installed) {
        match self {
            Self::None => {}
            Self::Sort(s) => {
                state.sorts.insert(s.name.clone(), s);
            }
            Self::Declaration(d) => {
                state.declarations.insert(d.callable.name.clone(), d);
            }
            Self::Capture(n, e, b) => {
                state.captures.insert(n, (e, b));
            }
            Self::Global(name, sort) => {
                state.globals.insert(name, sort);
            }
            Self::Rule(id, n) => {
                state.rules.insert(id, n);
            }
            Self::Group(ids, n) => {
                state.groups.insert(ids, n);
            }
        }
    }
}
pub(crate) struct Planner<'a> {
    pub symbol_gen: egglog::util::SymbolGen,
    pub state: Installed,
    pub commands: Vec<(Command, Commit)>,
    pub limits: LoweringLimits,
    sources: HashSet<TypeId>,
    setup: HashMap<usize, ast::Expr>,
    setup_references: HashMap<usize, usize>,
    variables: HashMap<VariableKey, (SortRef, String)>,
    type_info: Option<&'a egglog::TypeInfo>,
}
impl<'a> Planner<'a> {
    pub fn new(core: &'a mut egglog::EGraph, limits: LoweringLimits) -> Self {
        let state = core
            .extension_state::<Installed>()
            .cloned()
            .unwrap_or_default();
        let mut symbol_gen = core.parser.symbol_gen.clone();
        for name in core.get_function_names() {
            symbol_gen.reserve(&name);
        }
        for sort in core.get_arcsorts_by(|_| true) {
            symbol_gen.reserve(sort.name());
        }
        Self {
            symbol_gen,
            state,
            type_info: Some(core.type_info()),
            ..Self::empty(limits)
        }
    }
    pub fn empty(limits: LoweringLimits) -> Self {
        Self {
            symbol_gen: egglog::util::SymbolGen::new(
                egglog::util::INTERNAL_SYMBOL_PREFIX.to_owned(),
            ),
            state: Installed::default(),
            commands: vec![],
            limits,
            sources: HashSet::new(),
            setup: HashMap::new(),
            setup_references: HashMap::new(),
            variables: HashMap::new(),
            type_info: None,
        }
    }
    pub fn fresh(&mut self, label: &str) -> String {
        self.symbol_gen.fresh(&format!("$typed_{label}_"))
    }
    pub fn emit(&mut self, command: Command, commit: Commit) -> Result<(), TypedError> {
        if self.commands.len() >= self.limits.max_commands {
            return Err(TypedError::LoweringLimit(
                "emitted command limit exceeded".into(),
            ));
        }
        self.commands.push((command, commit));
        Ok(())
    }
    pub fn install(&mut self, definitions: &[Definition]) -> Result<(), TypedError> {
        for definition in definitions {
            match &definition.0 {
                DefinitionKind::Sort(sort) => {
                    self.sort(sort)?;
                }
                DefinitionKind::Callable(callable) => self.collect([], [callable.clone()])?,
                DefinitionKind::Ruleset(rules) => {
                    self.group(rules)?;
                }
            }
        }
        Ok(())
    }
    pub fn register(&mut self, actions: &[Action]) -> Result<(), TypedError> {
        self.collect(
            actions.iter().flat_map(Action::expressions).cloned(),
            actions.iter().filter_map(|action| match action {
                Action::Set(callable, ..) | Action::Change(_, callable, _) => {
                    Some(callable.clone())
                }
                _ => None,
            }),
        )?;
        self.top_actions(actions)
    }
    fn sort(&mut self, sort: &SortRef) -> Result<String, TypedError> {
        self.symbol_gen.reserve(sort.name());
        if let Some(old) = self.state.sorts.get(&sort.name) {
            if old != sort {
                return Err(TypedError::Invalid(format!(
                    "incompatible sorts named {}",
                    sort.name()
                )));
            }
            return Ok(sort.name().into());
        }
        if matches!(sort.kind, SortKind::Builtin) {
            let n = sort.name().to_owned();
            self.state.sorts.insert(sort.name.clone(), sort.clone());
            return Ok(n);
        }
        if self.state.declarations.contains_key(&sort.name)
            || self.state.globals.contains_key(sort.name())
            || self.state.rules.values().any(|name| name == sort.name())
            || self.state.groups.values().any(|name| name == sort.name())
            || self.type_info.is_some_and(|info| {
                info.get_sort_by_name(sort.name()).is_some()
                    || info.get_func_type(sort.name()).is_some()
            })
        {
            return Err(TypedError::Invalid(format!(
                "sort name {} is already in use",
                sort.name()
            )));
        }
        let presort_and_args = if let SortKind::Container { family, arguments } = &sort.kind {
            let mut args = vec![];
            for arg in arguments {
                args.push(ast::Expr::Var(super::origin(), self.sort(arg)?));
            }
            Some(((*family).into(), args))
        } else {
            None
        };
        let name = sort.name().to_owned();
        self.state.sorts.insert(sort.name.clone(), sort.clone());
        self.emit(
            Command::Sort {
                span: super::origin(),
                name: name.clone(),
                presort_and_args,
                uf: None,
                proof_func: None,
                container_rebuild: None,
                proof_constructors: None,
                unionable: true,
            },
            Commit::Sort(sort.clone()),
        )?;
        Ok(name)
    }
    pub fn collect(
        &mut self,
        roots: impl IntoIterator<Item = Expr>,
        heads: impl IntoIterator<Item = CallableRef>,
    ) -> Result<(), TypedError> {
        let mut todo: Vec<Expr> = roots.into_iter().collect();
        todo.reverse();
        let mut calls: VecDeque<_> = heads.into_iter().collect();
        let mut seen = HashSet::new();
        let mut defs = vec![];
        let mut edges = 0usize;
        loop {
            while let Some(expr) = todo.pop() {
                if !seen.insert(expr.id()) {
                    continue;
                }
                if matches!(expr.node().kind, NodeKind::Frozen(_)) {
                    return Err(TypedError::Invalid(
                        "frozen references cannot be submitted to a live e-graph".into(),
                    ));
                }
                if seen.len() > self.limits.max_nodes {
                    return Err(TypedError::LoweringLimit(
                        "authoring node limit exceeded".into(),
                    ));
                }
                self.sort(&expr.node().sort)?;
                if let NodeKind::Call(f, _) = &expr.node().kind {
                    calls.push_back(f.clone());
                }
                edges = edges
                    .checked_add(expr.children().len())
                    .ok_or_else(|| TypedError::LoweringLimit("edge count overflow".into()))?;
                if edges > self.limits.max_edges {
                    return Err(TypedError::LoweringLimit(
                        "authoring edge limit exceeded".into(),
                    ));
                }
                todo.extend(expr.children().iter().rev().cloned());
            }
            let Some(call) = calls.pop_front() else {
                break;
            };
            let Some(source) = call.source else {
                continue;
            };
            if !self.sources.insert(source.token) {
                continue;
            }
            let def = (source.resolve)().clone();
            self.symbol_gen.reserve(call.name());
            for sort in def.inputs.iter().chain(std::iter::once(&def.output)) {
                self.sort(sort)?;
            }
            if let Some(old) = self.state.declarations.get(&call.name) {
                if old != &def {
                    return Err(TypedError::Invalid(format!(
                        "incompatible definitions for {}",
                        call.name()
                    )));
                }
            } else {
                if call.name() == "unstable-fresh!" {
                    return Err(TypedError::Invalid(
                        "callable name unstable-fresh! is reserved for the native fresh macro"
                            .into(),
                    ));
                }
                if self.state.sorts.contains_key(&call.name)
                    || self.state.globals.contains_key(call.name())
                    || self.state.rules.values().any(|name| name == call.name())
                    || self.state.groups.values().any(|name| name == call.name())
                    || self.type_info.is_some_and(|info| {
                        info.get_sort_by_name(call.name()).is_some()
                            || info.get_func_type(call.name()).is_some()
                            || info.is_primitive(call.name())
                    })
                {
                    return Err(TypedError::Invalid(format!(
                        "callable name {} is already in use",
                        call.name()
                    )));
                }
                self.state
                    .declarations
                    .insert(call.name.clone(), def.clone());
                defs.push(def.clone());
            }
            if let Some(merge) = def.merge {
                todo.push(merge);
            }
        }
        // Dependencies used by a merge must have been declared before its function.
        // Otherwise preserve first-use order. Unreferenced declarations are not
        // installed; native extraction ties may observe this declaration order.
        let mut pending = defs;
        let new_names: HashSet<_> = pending.iter().map(|d| d.callable.name.clone()).collect();
        let mut available: HashSet<_> = self
            .state
            .declarations
            .keys()
            .filter(|name| !new_names.contains(*name))
            .cloned()
            .collect();
        while !pending.is_empty() {
            let mut progress = false;
            let mut next = vec![];
            for def in pending {
                let mut needed = HashSet::new();
                let mut todo = def.merge.iter().collect::<Vec<_>>();
                let mut seen = HashSet::new();
                while let Some(x) = todo.pop() {
                    if !seen.insert(x.id()) {
                        continue;
                    }
                    if let NodeKind::Call(f, _) = &x.node().kind
                        && f.source.is_some()
                    {
                        needed.insert(f.name.clone());
                    }
                    todo.extend(x.children());
                }
                if needed.iter().any(|n| !available.contains(n)) {
                    next.push(def);
                    continue;
                }
                let name = def.callable.name().to_owned();
                let schema = ast::Schema {
                    input: def.inputs.iter().map(|s| s.name().to_owned()).collect(),
                    output: def.output.name().to_owned(),
                };
                let command = match def.callable.kind {
                    CallKind::Constructor => Command::Constructor {
                        span: super::origin(),
                        name: name.clone(),
                        schema,
                        cost: def.cost,
                        unextractable: def.unextractable,
                        hidden: false,
                        let_binding: false,
                        term_constructor: None,
                    },
                    CallKind::Relation => Command::Relation {
                        span: super::origin(),
                        name: name.clone(),
                        inputs: schema.input,
                    },
                    CallKind::Function => Command::Function {
                        span: super::origin(),
                        name: name.clone(),
                        schema,
                        merge: def.merge.as_ref().map(|e| self.tree(e, true)).transpose()?,
                        hidden: false,
                        let_binding: false,
                        term_constructor: None,
                        unextractable: false,
                    },
                    CallKind::Primitive { .. } => unreachable!(),
                };
                available.insert(def.callable.name.clone());
                self.emit(command, Commit::Declaration(def))?;
                progress = true;
            }
            if !progress {
                return Err(TypedError::Invalid(
                    "cyclic merge declaration dependencies".into(),
                ));
            }
            pending = next;
        }
        Ok(())
    }
    fn leaf(&self, e: &Expr, merge: bool) -> Result<Option<ast::Expr>, TypedError> {
        let span = e.node().origin.clone();
        if merge
            && matches!(
                e.node().kind,
                NodeKind::Variable(_) | NodeKind::Capture { .. }
            )
        {
            return Err(TypedError::Invalid(
                "merge expressions cannot contain query variables or captures".into(),
            ));
        }
        Ok(match &e.node().kind {
            NodeKind::Literal(v) => Some(ast::Expr::Lit(span, v.clone())),
            NodeKind::Variable(key) => {
                let (sort, name) = self.variables.get(key).ok_or_else(|| {
                    TypedError::Invalid("variable outside its lowered query".into())
                })?;
                if sort != &e.node().sort {
                    return Err(TypedError::Invalid(format!(
                        "variable {key:?} has conflicting sorts {} and {}",
                        sort.name(),
                        e.node().sort.name(),
                    )));
                }
                Some(ast::Expr::Var(span, name.clone()))
            }
            NodeKind::MergeVariable(n) if merge => Some(ast::Expr::Var(span, (*n).into())),
            NodeKind::MergeVariable(_) => {
                return Err(TypedError::Invalid("merge variable outside merge".into()));
            }
            NodeKind::Capture { name, initializer } => {
                let Some((old, n)) = self.state.captures.get(name) else {
                    return Err(TypedError::Invalid(format!(
                        "capture {name} has not been registered"
                    )));
                };
                if old != initializer {
                    return Err(TypedError::Invalid(format!("incompatible capture {name}")));
                }
                Some(ast::Expr::Call(span, n.clone(), vec![]))
            }
            NodeKind::Call(..) => None,
            NodeKind::Frozen(_) => {
                return Err(TypedError::Invalid(
                    "frozen references cannot be submitted to a live e-graph".into(),
                ));
            }
        })
    }
    pub fn tree(&self, root: &Expr, merge: bool) -> Result<ast::Expr, TypedError> {
        let mut stack = vec![(root, false, 0usize)];
        let mut output = vec![];
        let mut count = 0usize;
        while let Some((e, done, depth)) = stack.pop() {
            if done {
                let NodeKind::Call(f, xs) = &e.node().kind else {
                    unreachable!()
                };
                let args = output.split_off(output.len() - xs.len());
                output.push(ast::Expr::Call(
                    e.node().origin.clone(),
                    f.name().into(),
                    args,
                ));
                continue;
            }
            count += 1;
            if count > self.limits.max_expanded_nodes || depth > self.limits.max_ast_depth {
                return Err(TypedError::LoweringLimit(
                    "bounded expression expansion exceeded".into(),
                ));
            }
            if let Some(leaf) = self.leaf(e, merge)? {
                output.push(leaf);
            } else {
                stack.push((e, true, depth));
                stack.extend(e.children().iter().rev().map(|x| (x, false, depth + 1)));
            }
        }
        Ok(output.pop().unwrap())
    }
    pub fn query(
        &mut self,
        facts: &[Fact],
        rule_scope: bool,
    ) -> Result<Vec<ast::Fact>, TypedError> {
        if facts.len() > self.limits.max_expanded_nodes {
            return Err(TypedError::LoweringLimit(
                "query fact limit exceeded".into(),
            ));
        }
        let mut memo = HashMap::<usize, ast::Expr>::new();
        let mut result = vec![];
        self.variables.clear();
        for root in facts.iter().flat_map(Fact::expressions) {
            let mut stack = vec![(root, false)];
            while let Some((e, done)) = stack.pop() {
                if memo.contains_key(&e.id()) {
                    continue;
                }
                if rule_scope && matches!(e.node().kind, NodeKind::Capture { .. }) {
                    return Err(TypedError::Invalid(
                        "captures are not permitted inside rules".into(),
                    ));
                }
                if let NodeKind::Variable(key) = &e.node().kind
                    && !self.variables.contains_key(key)
                {
                    let name = self.fresh("v");
                    self.variables
                        .insert(key.clone(), (e.node().sort.clone(), name));
                }
                if let Some(leaf) = self.leaf(e, false)? {
                    memo.insert(e.id(), leaf);
                    continue;
                }
                if !done {
                    stack.push((e, true));
                    stack.extend(e.children().iter().rev().map(|x| (x, false)));
                } else {
                    let NodeKind::Call(f, xs) = &e.node().kind else {
                        unreachable!()
                    };
                    let var = ast::Expr::Var(e.node().origin.clone(), self.fresh("query"));
                    let call = ast::Expr::Call(
                        e.node().origin.clone(),
                        f.name().into(),
                        xs.iter().map(|x| memo[&x.id()].clone()).collect(),
                    );
                    if result.len().saturating_add(facts.len()) >= self.limits.max_expanded_nodes {
                        return Err(TypedError::LoweringLimit(
                            "query fact limit exceeded".into(),
                        ));
                    }
                    result.push(ast::Fact::Eq(e.node().origin.clone(), var.clone(), call));
                    memo.insert(e.id(), var);
                }
            }
        }
        for fact in facts {
            result.push(match fact {
                Fact::Eq(a, b) => ast::Fact::Eq(
                    super::origin(),
                    memo[&a.id()].clone(),
                    memo[&b.id()].clone(),
                ),
                Fact::Expr(e) => ast::Fact::Fact(memo[&e.id()].clone()),
            });
        }
        Ok(result)
    }
    fn slot(&mut self, sort: &SortRef, initializer: ast::Expr) -> Result<String, TypedError> {
        let name = self.fresh("global");
        self.state.globals.insert(name.clone(), sort.clone());
        self.emit(
            Command::Function {
                span: super::origin(),
                name: name.clone(),
                schema: ast::Schema {
                    input: vec![],
                    output: sort.name().into(),
                },
                merge: None,
                hidden: false,
                let_binding: true,
                term_constructor: None,
                unextractable: true,
            },
            Commit::Global(name.clone(), sort.clone()),
        )?;
        self.emit(
            Command::Action(ast::Action::Set(
                super::origin(),
                name.clone(),
                vec![],
                initializer,
            )),
            Commit::None,
        )?;
        Ok(name)
    }
    fn validate_capture_context(&self, roots: &[&Expr]) -> Result<(), TypedError> {
        let ineligible = roots.iter().any(|root| !root.node().shareable);
        let mut todo: Vec<_> = roots.iter().rev().map(|root| (*root, ineligible)).collect();
        let mut seen = HashSet::new();
        while let Some((expr, ineligible)) = todo.pop() {
            if !seen.insert((expr.id(), ineligible)) {
                continue;
            }
            if let NodeKind::Capture { name, initializer } = &expr.node().kind {
                if let Some((old, _)) = self.state.captures.get(name) {
                    if old != initializer {
                        return Err(TypedError::Invalid(format!("incompatible capture {name}")));
                    }
                    continue;
                }
                if ineligible {
                    return Err(TypedError::Invalid(format!(
                        "fresh capture {name} is nested in a state-reading or fallible expression; register(capture) first to choose an explicit evaluation boundary"
                    )));
                }
                // A top-level capture is its own initializing action. Fresh
                // captures deeper in an ineligible initializer cannot be split
                // out of that action without changing native read visibility.
                todo.push((initializer, !initializer.node().shareable));
            } else {
                todo.extend(
                    expr.children()
                        .iter()
                        .rev()
                        .map(|child| (child, ineligible)),
                );
            }
        }
        Ok(())
    }
    pub fn materialize(&mut self, root: &Expr) -> Result<String, TypedError> {
        self.validate_capture_context(&[root])?;
        // Capture dependencies initialize in authored child-before-parent order.
        let mut captures = vec![(root, false)];
        let mut seen = HashSet::new();
        while let Some((e, done)) = captures.pop() {
            if done {
                if let NodeKind::Capture { name, initializer } = &e.node().kind {
                    if let Some((old, _)) = self.state.captures.get(name) {
                        if old != initializer {
                            return Err(TypedError::Invalid(format!(
                                "incompatible capture {name}"
                            )));
                        }
                        continue;
                    }
                    let ast::Expr::Call(_, slot, _) = self.setup_expression(initializer, true)?
                    else {
                        unreachable!()
                    };
                    self.state
                        .captures
                        .insert(name.clone(), (initializer.clone(), slot.clone()));
                    self.commands.last_mut().unwrap().1 =
                        Commit::Capture(name.clone(), initializer.clone(), slot);
                }
                continue;
            }
            if !seen.insert(e.id()) {
                continue;
            }
            captures.push((e, true));
            captures.extend(e.children().iter().rev().map(|x| (x, false)));
        }
        if let NodeKind::Capture { name, .. } = &root.node().kind {
            return Ok(self.state.captures[name].1.clone());
        }
        let ast::Expr::Call(_, slot, _) = self.setup_expression(root, true)? else {
            unreachable!()
        };
        Ok(slot)
    }
    pub fn prepare_setup(&mut self, roots: &[&Expr]) {
        self.setup_references.clear();
        let mut pending = roots.to_vec();
        for root in roots {
            *self.setup_references.entry(root.id()).or_default() += 1;
        }
        let mut seen = HashSet::new();
        while let Some(expr) = pending.pop() {
            if !seen.insert(expr.id()) {
                continue;
            }
            if matches!(&expr.node().kind, NodeKind::Capture { name, .. } if self.state.captures.contains_key(name))
            {
                continue;
            }
            for child in expr.children() {
                *self.setup_references.entry(child.id()).or_default() += 1;
                pending.push(child);
            }
        }
    }
    fn setup_expression(&mut self, root: &Expr, root_slot: bool) -> Result<ast::Expr, TypedError> {
        let mut pending = vec![root];
        let mut seen = HashSet::new();
        while let Some(e) = pending.pop() {
            if !seen.insert(e.id()) {
                continue;
            }
            if matches!(
                e.node().kind,
                NodeKind::Variable(_) | NodeKind::MergeVariable(_)
            ) {
                return Err(TypedError::Invalid(
                    "variables cannot be evaluated at top level".into(),
                ));
            }
            if !matches!(e.node().kind, NodeKind::Capture { .. }) {
                pending.extend(e.children());
            }
        }
        if !root.node().shareable {
            self.setup.clear();
            let expr = self.tree(root, false)?;
            if !root_slot {
                return Ok(expr);
            }
            let name = self.slot(&root.node().sort, expr)?;
            return Ok(ast::Expr::Call(root.node().origin.clone(), name, vec![]));
        }
        // Only bound values survive a setup region. Inline ASTs are temporary,
        // bounded trees; a shared non-leaf is bound before either consumer can
        // duplicate it. A root always gets an expected-sort slot of its own.
        let mut inline = HashMap::<usize, (ast::Expr, usize, usize)>::new();
        let mut stack = vec![(root, false)];
        while let Some((e, done)) = stack.pop() {
            if inline.contains_key(&e.id()) {
                continue;
            }
            if let Some(value) = self.setup.get(&e.id()) {
                inline.insert(e.id(), (value.clone(), 0, 1));
                continue;
            }
            if let Some(leaf) = self.leaf(e, false)? {
                inline.insert(e.id(), (leaf, 0, 1));
                continue;
            }
            if !done {
                stack.push((e, true));
                stack.extend(e.children().iter().rev().map(|x| (x, false)));
            } else {
                let NodeKind::Call(f, xs) = &e.node().kind else {
                    unreachable!()
                };
                let call = ast::Expr::Call(
                    e.node().origin.clone(),
                    f.name().into(),
                    xs.iter().map(|x| inline[&x.id()].0.clone()).collect(),
                );
                let depth = xs.iter().map(|x| inline[&x.id()].1 + 1).max().unwrap_or(0);
                let size = xs
                    .iter()
                    .fold(1usize, |size, x| size.saturating_add(inline[&x.id()].2));
                if depth > self.limits.max_ast_depth || size > self.limits.max_expanded_nodes {
                    return Err(TypedError::LoweringLimit(
                        "eligible setup expression limit exceeded".into(),
                    ));
                }
                if (root_slot && e.id() == root.id())
                    || self.setup_references.get(&e.id()).copied().unwrap_or(1) > 1
                    || depth == self.limits.max_ast_depth
                    || size == self.limits.max_expanded_nodes
                {
                    let slot = self.slot(&e.node().sort, call)?;
                    let value = ast::Expr::Call(e.node().origin.clone(), slot.clone(), vec![]);
                    self.setup.insert(e.id(), value.clone());
                    if e.id() == root.id() {
                        return Ok(value);
                    }
                    inline.insert(e.id(), (value, 0, 1));
                } else {
                    inline.insert(e.id(), (call, depth, size));
                }
            }
        }
        let value = inline.remove(&root.id()).unwrap().0;
        if !root_slot {
            return Ok(value);
        }
        let name = self.slot(&root.node().sort, value)?;
        Ok(ast::Expr::Call(root.node().origin.clone(), name, vec![]))
    }
    fn action(
        &mut self,
        action: &Action,
        locals: bool,
        setup: bool,
    ) -> Result<Vec<ast::Action>, TypedError> {
        let mut output = vec![];
        let mut memo = HashMap::<usize, ast::Expr>::new();
        let mut values = vec![];
        let mut expanded = 0usize;
        for root in action.expressions() {
            if !locals {
                values.push(if !setup {
                    self.tree(root, false)?
                } else if matches!(action, Action::Effect(_)) {
                    let NodeKind::Call(head, children) = &root.node().kind else {
                        unreachable!()
                    };
                    let args = children
                        .iter()
                        .map(|child| self.setup_expression(child, false))
                        .collect::<Result<_, _>>()?;
                    ast::Expr::Call(root.node().origin.clone(), head.name().into(), args)
                } else {
                    self.setup_expression(root, false)?
                });
                continue;
            }
            let mut stack = vec![(root, false)];
            let mut results = vec![];
            while let Some((e, done)) = stack.pop() {
                if !done {
                    if e.node().shareable
                        && let Some(v) = memo.get(&e.id())
                    {
                        results.push(v.clone());
                        continue;
                    }
                    expanded += 1;
                    if expanded > self.limits.max_expanded_nodes {
                        return Err(TypedError::LoweringLimit(
                            "rule action expansion exceeded".into(),
                        ));
                    }
                    if matches!(&e.node().kind, NodeKind::Capture { .. }) {
                        return Err(TypedError::Invalid(
                            "captures are not permitted inside rules".into(),
                        ));
                    }
                    if let Some(leaf) = self.leaf(e, false)? {
                        results.push(leaf);
                        continue;
                    }
                    stack.push((e, true));
                    stack.extend(e.children().iter().rev().map(|x| (x, false)));
                } else {
                    let NodeKind::Call(f, xs) = &e.node().kind else {
                        unreachable!()
                    };
                    let args = results.split_off(results.len() - xs.len());
                    let name = self.fresh("local");
                    output.push(ast::Action::Let(
                        e.node().origin.clone(),
                        name.clone(),
                        ast::Expr::Call(e.node().origin.clone(), f.name().into(), args),
                    ));
                    let value = ast::Expr::Var(e.node().origin.clone(), name);
                    if e.node().shareable {
                        memo.insert(e.id(), value.clone());
                    }
                    results.push(value);
                }
            }
            values.push(results.pop().unwrap());
        }
        let mut values = values.into_iter();
        let span = super::origin();
        output.push(match action {
            Action::Expr(_) | Action::Effect(_) => ast::Action::Expr(span, values.next().unwrap()),
            Action::Union(..) => {
                ast::Action::Union(span, values.next().unwrap(), values.next().unwrap())
            }
            Action::Set(f, args, _) => {
                let input = values.by_ref().take(args.len()).collect();
                ast::Action::Set(span, f.name().into(), input, values.next().unwrap())
            }
            Action::Change(c, f, _) => {
                ast::Action::Change(span, *c, f.name().into(), values.collect())
            }
            Action::Panic(s) => ast::Action::Panic(span, s.clone()),
            Action::Invalid(message) => return Err(TypedError::Invalid(message.clone())),
        });
        Ok(output)
    }
    pub fn top_actions(&mut self, actions: &[Action]) -> Result<(), TypedError> {
        let mut index = 0;
        while index < actions.len() {
            if matches!(&actions[index], Action::Expr(root) if root.node().shareable) {
                let end = (index..actions.len())
                    .find(|i| !matches!(&actions[*i], Action::Expr(root) if root.node().shareable))
                    .unwrap_or(actions.len());
                let roots: Vec<_> = actions[index..end]
                    .iter()
                    .flat_map(Action::expressions)
                    .collect();
                self.prepare_setup(&roots);
                for action in &actions[index..end] {
                    self.top_action(action)?;
                }
                index = end;
            } else {
                if let Action::Expr(root) = &actions[index] {
                    self.prepare_setup(&[root]);
                }
                self.top_action(&actions[index])?;
                index += 1;
            }
        }
        Ok(())
    }
    fn top_action(&mut self, action: &Action) -> Result<(), TypedError> {
        if let Action::Expr(root) = action {
            self.materialize(root)?;
            return Ok(());
        }
        // An effect head itself is a write, not an expression moved across that
        // write. Its argument trees still must preserve their original boundary.
        let roots = match action {
            Action::Effect(root) => root.children().iter().collect(),
            _ => action.expressions(),
        };
        self.validate_capture_context(&roots)?;
        self.setup.clear();
        let eligible = roots.iter().all(|root| root.node().shareable);
        self.prepare_setup(&roots);
        for e in action.expressions() {
            let mut todo = vec![e];
            let mut seen = HashSet::new();
            while let Some(x) = todo.pop() {
                if !seen.insert(x.id()) {
                    continue;
                }
                if matches!(
                    x.node().kind,
                    NodeKind::Variable(_) | NodeKind::MergeVariable(_)
                ) {
                    return Err(TypedError::Invalid(
                        "variables cannot be evaluated in top-level actions".into(),
                    ));
                }
                if let NodeKind::Capture { .. } = &x.node().kind {
                    self.materialize(x)?;
                } else {
                    todo.extend(x.children().iter().rev());
                }
            }
        }
        let actions = self.action(action, false, eligible)?;
        for action in actions {
            self.emit(Command::Action(action), Commit::None)?;
        }
        self.setup.clear();
        Ok(())
    }
    pub fn group(&mut self, group: &Ruleset) -> Result<String, TypedError> {
        let ids: Vec<_> = group.rules.iter().map(|r| r.data.clone()).collect();
        if let Some(n) = self.state.groups.get(&ids) {
            return Ok(n.clone());
        }
        for rule in group.rules.iter() {
            if self.state.rules.contains_key(&rule.data) {
                continue;
            }
            let data = &rule.data.0;
            self.collect(
                data.facts
                    .iter()
                    .flat_map(Fact::expressions)
                    .chain(data.actions.iter().flat_map(Action::expressions))
                    .cloned(),
                data.actions.iter().filter_map(|a| match a {
                    Action::Set(f, ..) | Action::Change(_, f, _) => Some(f.clone()),
                    _ => None,
                }),
            )?;
            let name = self.fresh(&format!(
                "singleton_{}",
                rule.label.as_deref().unwrap_or("anonymous")
            ));
            self.emit(
                Command::AddRuleset(super::origin(), name.clone()),
                Commit::None,
            )?;
            let body = self.query(&data.facts, true)?;
            let mut head = vec![];
            for action in &data.actions {
                head.extend(self.action(action, true, false)?);
                if head.len() > self.limits.max_expanded_nodes {
                    return Err(TypedError::LoweringLimit(
                        "rule action limit exceeded".into(),
                    ));
                }
            }
            let native = ast::GenericRule {
                span: super::origin(),
                head: ast::GenericActions(head),
                body,
                name: self.fresh(&format!(
                    "rule_{}",
                    rule.label.as_deref().unwrap_or("anonymous")
                )),
                ruleset: name.clone(),
                eval_mode: if data.naive {
                    ast::RuleEvalMode::Naive
                } else {
                    ast::RuleEvalMode::Seminaive
                },
                no_decomp: data.no_decomp,
                include_subsumed: data.include_subsumed,
            };
            self.state.rules.insert(rule.data.clone(), name.clone());
            self.emit(
                Command::Rule { rule: native },
                Commit::Rule(rule.data.clone(), name),
            )?;
        }
        let name = self.fresh(&format!(
            "group_{}",
            group.label.as_deref().unwrap_or("anonymous")
        ));
        self.emit(
            Command::UnstableCombinedRuleset(
                super::origin(),
                name.clone(),
                ids.iter().map(|id| self.state.rules[id].clone()).collect(),
            ),
            Commit::Group(ids.clone(), name.clone()),
        )?;
        self.state.groups.insert(ids, name.clone());
        Ok(name)
    }
    pub fn schedule(
        &mut self,
        schedule: &Schedule,
        depth: usize,
    ) -> Result<ast::Schedule, TypedError> {
        if depth > self.limits.max_ast_depth {
            return Err(TypedError::LoweringLimit("schedule depth exceeded".into()));
        }
        let span = super::origin();
        Ok(match schedule.0.as_ref() {
            ScheduleNode::Run(g, f) => {
                let name = self.group(g)?;
                self.collect(f.iter().flat_map(Fact::expressions).cloned(), [])?;
                ast::Schedule::Run(
                    span,
                    ast::GenericRunConfig {
                        ruleset: name,
                        until: if f.is_empty() {
                            None
                        } else {
                            Some(self.query(f, false)?)
                        },
                    },
                )
            }
            ScheduleNode::Repeat(n, s) => {
                ast::Schedule::Repeat(span, *n, Box::new(self.schedule(s, depth + 1)?))
            }
            ScheduleNode::Saturate(s) => {
                ast::Schedule::Saturate(span, Box::new(self.schedule(s, depth + 1)?))
            }
            ScheduleNode::Sequence(xs) => ast::Schedule::Sequence(
                span,
                xs.iter()
                    .map(|x| self.schedule(x, depth + 1))
                    .collect::<Result<_, _>>()?,
            ),
            ScheduleNode::Invalid(message) => return Err(TypedError::Invalid(message.clone())),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cloned_native_state_owns_installed_rule_identity() -> Result<(), TypedError> {
        use crate::typed::{EGraph, EGraphOptions, rule, ruleset};

        let group = ruleset(rule((), ()));
        let weak = Arc::downgrade(&group.rules[0].data.0);
        let mut graph = EGraph::new(EGraphOptions::default());
        graph.run(&group)?;
        let mut cloned = EGraph {
            core: graph.core.clone(),
            options: graph.options.clone(),
        };
        cloned.run(group.clone().label("renamed"))?;
        let installed = cloned.core.extension_state::<Installed>().unwrap();
        assert_eq!(installed.rules.len(), 1);
        assert_eq!(installed.groups.len(), 1);
        assert!(installed.rules.contains_key(&group.rules[0].data));
        drop(group);
        drop(graph);
        assert!(weak.upgrade().is_some());
        drop(cloned);
        assert!(weak.upgrade().is_none());
        Ok(())
    }

    fn install_two_sort_query(
        names: [&str; 2],
    ) -> Result<Vec<egglog::CommandOutput>, egglog::Error> {
        let span = super::super::origin();
        let mut core = egglog::EGraph::default();
        let mut commands = vec![];
        for name in ["A", "B"] {
            commands.push(Command::Sort {
                span: span.clone(),
                name: name.into(),
                presort_and_args: None,
                uf: None,
                proof_func: None,
                container_rebuild: None,
                proof_constructors: None,
                unionable: true,
            });
        }
        for (name, sort) in names.into_iter().zip(["A", "B"]) {
            commands.push(Command::Constructor {
                span: span.clone(),
                name: name.into(),
                schema: ast::Schema {
                    input: vec!["i64".into()],
                    output: sort.into(),
                },
                cost: None,
                unextractable: false,
                hidden: false,
                let_binding: false,
                term_constructor: None,
            });
        }
        let mut body = vec![];
        for (i, name) in [names[0], names[0], names[0], names[1]]
            .into_iter()
            .enumerate()
        {
            body.push(ast::Fact::Eq(
                span.clone(),
                ast::Expr::Var(span.clone(), format!("v{i}")),
                ast::Expr::Call(
                    span.clone(),
                    name.into(),
                    vec![ast::Expr::Lit(span.clone(), ast::Literal::Int(i as i64))],
                ),
            ));
        }
        commands.push(Command::Rule {
            rule: ast::GenericRule {
                span,
                head: ast::GenericActions(vec![]),
                body,
                name: "regression".into(),
                ruleset: "".into(),
                eval_mode: ast::RuleEvalMode::Seminaive,
                no_decomp: false,
                include_subsumed: false,
            },
        });
        core.run_program(commands)
    }

    #[test]
    fn generated_names_do_not_collide_with_secondary_core_counters() {
        // Native generation must disambiguate arbitrary public name hints too.
        install_two_sort_query(["@$typed_call", "@$typed_call2"]).unwrap();
        let mut core = egglog::EGraph::default();
        let mut planner = Planner::new(&mut core, LoweringLimits::default());
        let first = planner.fresh("call");
        let _ = planner.fresh("call");
        let third = planner.fresh("call");
        install_two_sort_query([&first, &third]).unwrap();
    }
}
