//! Effect-safe extraction for languages that thread an explicit state.
//!
//! Mark state-carrying e-classes with `(set-effectful Sort e)` and subregion
//! arguments with `:regions`, then use `(extract e :extractor effsafe)` or
//! `(print-function Ctor :extractor effsafe)`. Pure terms are extracted from
//! the state chain chosen for their region.
//!
//! See `docs/effsafe-extract.md` for the language interface and the statewalk
//! algorithm of Flatt et al., "Efficient Extraction for Effectful E-graphs"
//! (OOPSLA 2026, <https://doi.org/10.1145/3839530>).

mod build;
mod checks;
mod cost;
mod greedy;
mod persistent;
mod region;
mod set_effectful;
mod statewalk;
mod term_graph;
mod to_term;

use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::sync::Arc;

use egglog::ast::{Command, Expr, Literal, Macro, ParseError, Parser, PrintFunctionMode, Sexp};
use egglog::extract::{DagCostModel, TreeCostModel, TreeCostModelFromDag};
use egglog::{CommandOutput, EGraph, Error, TermDag, TermId, UserDefinedCommand, span};
use egglog_ast::span::Span;
use rustc_hash::FxHashMap;

use crate::DynamicCostModel;
use term_graph::{Extraction, SortId, TermGraph};

pub use build::Roots;
pub use cost::{Cost, RegionBoundary};
pub use set_effectful::{SetEffectful, effectful_relation};
pub use statewalk::StatewalkOptions;

/// Region annotations and extraction options for the language.
#[derive(Clone, Debug, Default)]
pub struct EffsafeConfig {
    /// Constructor name to the argument positions that start subregions.
    /// Positions may be in any order; duplicates are ignored.
    pub regions: HashMap<String, Vec<usize>>,
    /// Sort name to a replacement for every child value of that sort.
    /// Extraction does not descend into these values. Each replacement must
    /// be a well-typed constructor application with literal or constructor
    /// arguments; extraction returns an error otherwise.
    ///
    /// Placeholders can produce terms outside the requested e-class. The
    /// caller must restore any information needed to preserve meaning.
    pub placeholders: HashMap<String, Expr>,
    /// Include subsumed e-nodes, which are skipped by default.
    pub include_subsumed: bool,
    /// Optimizations used when searching each region's statewalk.
    pub statewalk: StatewalkOptions,
}

/// Configuration and cost models, cloned and snapshotted with the e-graph.
/// Change the models with [`set_effsafe_cost_models`].
#[derive(Clone)]
pub struct EffsafeState {
    /// Annotations from `:regions` / `effsafe-regions`, and placeholders.
    pub config: EffsafeConfig,
    /// Marginal costs within a region: e-nodes, base values and containers.
    pub cost_model: Arc<dyn DagCostModel<Cost> + Send + Sync>,
    /// Combines the costs of children at `:regions` positions with the node's own cost.
    pub boundary: Arc<dyn RegionBoundary>,
}

impl Default for EffsafeState {
    fn default() -> Self {
        EffsafeState {
            config: EffsafeConfig::default(),
            cost_model: Arc::new(DynamicCostModel),
            boundary: Arc::new(TreeCostModelFromDag(DynamicCostModel)),
        }
    }
}

impl Debug for EffsafeState {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        f.debug_struct("EffsafeState")
            .field("config", &self.config)
            .finish_non_exhaustive()
    }
}

/// The effect-safe extraction state of `egraph`, created with the default
/// cost models if the e-graph has none yet.
pub fn effsafe_state(egraph: &mut EGraph) -> &mut EffsafeState {
    egraph.extension_state_or_default::<EffsafeState>()
}

/// Use `cost_model` for marginal costs within regions and `boundary` to
/// compose subregion costs at region boundaries.
///
/// The boundary model receives child costs at `:regions` positions and `0`
/// elsewhere. Its fold must include the node's own cost; ordinary children
/// are charged separately in the enclosing region. Each annotated child is
/// charged per occurrence, including pure children.
///
/// Defaults use [`DynamicCostModel`] and [`TreeCostModelFromDag`], which sums
/// the annotated child costs. Use saturating arithmetic in custom folds.
pub fn set_effsafe_cost_models<B>(
    egraph: &mut EGraph,
    cost_model: impl DagCostModel<Cost> + Send + Sync + 'static,
    boundary: B,
) where
    B: TreeCostModel<Cost> + Send + Sync + 'static,
    B::EnodeCost: Clone + Send + Sync + 'static,
{
    let state = effsafe_state(egraph);
    state.cost_model = Arc::new(cost_model);
    state.boundary = Arc::new(boundary);
}

/// Result of an effect-safe extraction: one term per root.
#[derive(Debug)]
pub struct EffsafeExtractOutput {
    /// Term storage shared by every root.
    pub termdag: TermDag,
    /// Root terms, in request order (or e-class order for a whole constructor).
    pub terms: Vec<TermId>,
    /// Cost per root under the configured models: shared terms are charged
    /// once within each region, and annotated children once per occurrence.
    pub costs: Vec<Cost>,
}

impl Display for EffsafeExtractOutput {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if let [term] = self.terms[..] {
            return writeln!(f, "{}", self.termdag.to_string(term));
        }
        writeln!(f, "(")?;
        for &term in &self.terms {
            writeln!(f, "   {}", self.termdag.to_string(term))?;
        }
        writeln!(f, ")")
    }
}

/// Extract `roots` effect-safely. Effectful e-classes are those marked with
/// `set-effectful`. `cost_model` gives each e-node's marginal cost within its
/// region; `boundary` composes subregion costs (see [`set_effsafe_cost_models`]).
/// Returns an extraction error if a region does not have exactly one entry.
pub fn extract_effsafe(
    egraph: &EGraph,
    roots: &Roots,
    config: &EffsafeConfig,
    cost_model: &dyn DagCostModel<Cost>,
    boundary: &dyn RegionBoundary,
) -> Result<EffsafeExtractOutput, Error> {
    extract_effsafe_with_limit(egraph, roots, config, cost_model, boundary, None)
}

fn extract_effsafe_with_limit(
    egraph: &EGraph,
    roots: &Roots,
    config: &EffsafeConfig,
    cost_model: &dyn DagCostModel<Cost>,
    boundary: &dyn RegionBoundary,
    max_roots: Option<usize>,
) -> Result<EffsafeExtractOutput, Error> {
    let t0 = std::time::Instant::now();
    let (g, root_classes) = build::build(egraph, config, cost_model, boundary, roots, max_roots)?;
    let t_build = t0.elapsed();
    let t1 = std::time::Instant::now();
    let extractions = region::extract_all(&g, boundary, &root_classes, config.statewalk)?;
    let t_regions = t1.elapsed();
    if log::log_enabled!(log::Level::Debug) {
        let enodes: usize = g.classes.iter().map(|c| c.enodes.len()).sum();
        log::debug!(
            "effsafe build={:.1}ms regions={:.1}ms classes={} enodes={} roots={}",
            t_build.as_secs_f64() * 1e3,
            t_regions.as_secs_f64() * 1e3,
            g.len(),
            enodes,
            root_classes.len()
        );
    }
    let mut termdag = TermDag::default();
    let mut placeholders: FxHashMap<SortId, TermId> = FxHashMap::default();
    for (sort_id, sort) in g.sorts.iter().enumerate() {
        if let Some(expr) = config.placeholders.get(sort.name()) {
            placeholders.insert(sort_id, termdag.expr_to_term(expr));
        }
    }
    let terms = extractions
        .iter()
        .map(|e| to_term::extraction_to_term(&g, egraph, &placeholders, e, &mut termdag))
        .collect();
    let costs = extractions
        .iter()
        .map(|e| program_cost(&g, boundary, e))
        .collect();
    Ok(EffsafeExtractOutput {
        termdag,
        terms,
        costs,
    })
}

/// Price the selected program as a DAG within regions and a tree across
/// `:regions` boundaries, including boundaries whose children are pure.
fn program_cost(g: &TermGraph, boundary: &dyn RegionBoundary, nodes: &Extraction) -> Cost {
    // Children precede parents, so boundary costs are ready before use.
    let mut is_region_root = vec![false; nodes.len()];
    is_region_root[nodes.len() - 1] = true;
    for node in nodes {
        let enode = g.enode(node.class, node.node);
        for &i in &enode.regions {
            is_region_root[node.children[i]] = true;
        }
    }
    let mut cost_of_root: Vec<Option<Cost>> = vec![None; nodes.len()];
    let mut seen = vec![usize::MAX; nodes.len()];
    for root in (0..nodes.len()).filter(|&r| is_region_root[r]) {
        let mut total: Cost = 0;
        let mut stack = vec![root];
        while let Some(id) = stack.pop() {
            if seen[id] == root {
                continue;
            }
            seen[id] = root;
            let node = &nodes[id];
            let enode = g.enode(node.class, node.node);
            let cost = if enode.regions.is_empty() {
                enode.cost
            } else {
                let mut by_position = vec![0; enode.arity];
                for (&i, &position) in enode.regions.iter().zip(&enode.region_positions) {
                    by_position[position] = cost_of_root[node.children[i]]
                        .expect("regions children are priced before their parents");
                }
                let annotation = enode
                    .boundary
                    .as_deref()
                    .expect("regions carry an annotation");
                boundary.fold(annotation, &by_position)
            };
            total = total.saturating_add(cost);
            for (i, &child) in node.children.iter().enumerate() {
                if !enode.regions.contains(&i) {
                    stack.push(child);
                }
            }
        }
        cost_of_root[root] = Some(total);
    }
    cost_of_root[nodes.len() - 1].expect("the root is priced")
}

/// Remove a trailing `:include-subsumed` flag and report whether it was present.
pub(crate) fn split_include_subsumed(args: &[Expr]) -> (&[Expr], bool) {
    match args {
        [rest @ .., Expr::Var(_, flag)] if flag == ":include-subsumed" => (rest, true),
        _ => (args, false),
    }
}

/// Run effect-safe extraction for a command, with the e-graph's models.
pub(crate) fn extract_with_options(
    egraph: &mut EGraph,
    include_subsumed: bool,
    roots: &Roots,
    max_roots: Option<usize>,
) -> Result<EffsafeExtractOutput, Error> {
    let mut state = effsafe_state(egraph).clone();
    state.config.include_subsumed |= include_subsumed;
    extract_effsafe_with_limit(
        egraph,
        roots,
        &state.config,
        state.cost_model.as_ref(),
        state.boundary.as_ref(),
        max_roots,
    )
}

fn usage(span: Span, msg: &str) -> Error {
    Error::ParseError(ParseError(span, msg.to_string()))
}

fn expect_name(expr: &Expr, what: &str) -> Result<String, Error> {
    match expr {
        Expr::Var(_, name) => Ok(name.clone()),
        other => Err(usage(
            other.span(),
            &format!("expected the name of a {what}, got {other}"),
        )),
    }
}

/// `(effsafe-regions <constructor> <position>...)`: the arguments of
/// `constructor` at these zero-based positions start subregions.
pub struct EffsafeRegions;

impl UserDefinedCommand for EffsafeRegions {
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        let [name, positions @ ..] = args else {
            return Err(usage(
                span!(),
                "usage: (effsafe-regions <constructor> <position>...)",
            ));
        };
        let name = expect_name(name, "constructor")?;
        let Some(func) = egraph.get_function(&name) else {
            return Err(usage(
                args[0].span(),
                &format!("{name} is not a declared constructor"),
            ));
        };
        let arity = func.func_type().input.len();
        let mut parsed = Vec::with_capacity(positions.len());
        for pos in positions {
            let Expr::Lit(_, Literal::Int(p)) = pos else {
                return Err(usage(
                    pos.span(),
                    "region positions must be integer literals",
                ));
            };
            if *p < 0 || *p as usize >= arity {
                return Err(usage(
                    pos.span(),
                    &format!("{name} has {arity} arguments; position {p} is out of range"),
                ));
            }
            parsed.push(*p as usize);
        }
        parsed.sort_unstable();
        parsed.dedup();
        effsafe_state(egraph).config.regions.insert(name, parsed);
        Ok(vec![])
    }
}

/// `print-function` with `:extractor effsafe`: prints the effect-safe
/// extraction of every e-class holding an e-node of the table. Without the
/// option it is egglog's `print-function`.
pub struct PrintFunction;

impl UserDefinedCommand for PrintFunction {
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        let (args, include_subsumed) = split_include_subsumed(args);
        let [name, rest @ ..] = args else {
            return Err(usage(
                span!(),
                "usage: (print-function <table> [n] [:file \"f\"] [:mode csv|default] [:extractor effsafe] [:include-subsumed])",
            ));
        };
        let name = expect_name(name, "table")?;
        let mut rows: Option<usize> = None;
        let mut file: Option<String> = None;
        let mut mode = PrintFunctionMode::Default;
        let mut effsafe = false;
        let mut rest = rest;
        if let [Expr::Lit(_, Literal::Int(n)), tail @ ..] = rest {
            rows =
                Some(usize::try_from(*n).map_err(|_| {
                    usage(rest[0].span(), "the number of rows must be non-negative")
                })?);
            rest = tail;
        }
        while let [Expr::Var(span, option), value, tail @ ..] = rest {
            match (option.as_str(), value) {
                (":file", Expr::Lit(_, Literal::String(f))) => file = Some(f.clone()),
                (":mode", Expr::Var(_, m)) if m == "csv" => mode = PrintFunctionMode::CSV,
                (":mode", Expr::Var(_, m)) if m == "default" => mode = PrintFunctionMode::Default,
                (":extractor", Expr::Var(_, e)) if e == "effsafe" => effsafe = true,
                _ => {
                    return Err(usage(
                        span.clone(),
                        "unknown option to print-function; supported: `:mode csv|default`, \
                         `:file \"<filename>\"`, `:extractor effsafe`, `:include-subsumed`",
                    ));
                }
            }
            rest = tail;
        }
        if let [extra, ..] = rest {
            return Err(usage(extra.span(), "unexpected argument to print-function"));
        }
        let file = file
            .map(|f| {
                let path = std::path::PathBuf::from(&f);
                std::fs::File::create(&path)
                    .map(|file| (file, path.clone()))
                    .map_err(|e| Error::IoError(path, e, span!()))
            })
            .transpose()?;

        if !effsafe {
            if include_subsumed {
                return Err(usage(
                    span!(),
                    ":include-subsumed is only supported with :extractor effsafe",
                ));
            }
            return Ok(egraph
                .print_function(&name, rows, file, span!(), mode)?
                .into_iter()
                .collect());
        }
        let Some(function) = egraph.get_function(&name).cloned() else {
            return Err(usage(
                args[0].span(),
                &format!("{name} is not a declared table"),
            ));
        };
        let output =
            extract_with_options(egraph, include_subsumed, &Roots::Constructor(&name), rows)?;
        let terms: Vec<(TermId, TermId)> = output.terms.iter().map(|&t| (t, t)).collect();
        let result = CommandOutput::PrintFunction(function, output.termdag, terms, mode);
        if let Some((mut file, path)) = file {
            use std::io::Write;
            write!(file, "{result}").map_err(|e| Error::IoError(path, e, span!()))?;
            return Ok(vec![]);
        }
        Ok(vec![result])
    }
}

/// Add `:regions (<position>...)` to constructor and datatype declarations.
struct RegionsAnnotation {
    head: &'static str,
}

// `Sexp` does not implement `Clone`.
fn clone_sexp(sexp: &Sexp) -> Sexp {
    match sexp {
        Sexp::Literal(lit, span) => Sexp::Literal(lit.clone(), span.clone()),
        Sexp::Atom(atom, span) => Sexp::Atom(atom.clone(), span.clone()),
        Sexp::List(items, span) => Sexp::List(items.iter().map(clone_sexp).collect(), span.clone()),
    }
}

/// Remove `:regions (...)` from a declaration's option list. Returns the
/// remaining s-expressions and the positions, if the option was present.
fn strip_regions(items: &[Sexp]) -> Result<(Vec<Sexp>, Option<Vec<i64>>), ParseError> {
    let Some(i) = items
        .iter()
        .position(|s| matches!(s, Sexp::Atom(a, _) if a == ":regions"))
    else {
        return Ok((items.iter().map(clone_sexp).collect(), None));
    };
    let Some(Sexp::List(positions, _)) = items.get(i + 1) else {
        return Err(ParseError(
            items[i].span(),
            "expected a list of positions after :regions, e.g. :regions (2 3)".to_string(),
        ));
    };
    let positions = positions
        .iter()
        .map(|p| match p {
            Sexp::Literal(Literal::Int(n), _) => Ok(*n),
            other => Err(ParseError(
                other.span(),
                "region positions must be integer literals".to_string(),
            )),
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut rest: Vec<Sexp> = items[..i].iter().map(clone_sexp).collect();
    rest.extend(items[i + 2..].iter().map(clone_sexp));
    Ok((rest, Some(positions)))
}

fn regions_command(span: Span, constructor: &str, positions: &[i64]) -> Command {
    let mut args = vec![Expr::Var(span.clone(), constructor.to_string())];
    args.extend(
        positions
            .iter()
            .map(|&p| Expr::Lit(span.clone(), Literal::Int(p))),
    );
    Command::UserDefined(span, "effsafe-regions".to_string(), args)
}

/// Strip `:regions` from the variant lists in `items[skip..]`, collecting an
/// `effsafe-regions` command for each annotated variant.
fn strip_variants(
    items: &[Sexp],
    skip: usize,
    region_commands: &mut Vec<Command>,
) -> Result<Vec<Sexp>, ParseError> {
    let mut rest = Vec::with_capacity(items.len());
    for (i, item) in items.iter().enumerate() {
        match item {
            Sexp::List(variant, vspan) if i >= skip => {
                let (stripped, positions) = strip_regions(variant)?;
                if let (Some(positions), Some(Sexp::Atom(name, _))) = (positions, variant.first()) {
                    region_commands.push(regions_command(vspan.clone(), name, &positions));
                }
                rest.push(Sexp::List(stripped, vspan.clone()));
            }
            other => rest.push(clone_sexp(other)),
        }
    }
    Ok(rest)
}

impl Macro<Vec<Command>> for RegionsAnnotation {
    fn name(&self) -> &str {
        self.head
    }

    fn parse(
        &self,
        args: &[Sexp],
        span: Span,
        _parser: &mut Parser,
    ) -> Result<Vec<Command>, ParseError> {
        let mut region_commands = Vec::new();
        let stripped: Vec<Sexp> = match self.head {
            "constructor" => {
                let (rest, positions) = strip_regions(args)?;
                if let (Some(positions), Some(Sexp::Atom(name, _))) = (positions, args.first()) {
                    region_commands.push(regions_command(span.clone(), name, &positions));
                }
                rest
            }
            "datatype" => {
                // (datatype Name (Variant Sort... :regions (...))...)
                strip_variants(args, 1, &mut region_commands)?
            }
            _ => {
                // (datatype* (Name (Variant ...)...) (sort Name (Container ...))...)
                let mut rest = Vec::with_capacity(args.len());
                for arg in args {
                    match arg {
                        Sexp::List(items, dspan) if !matches!(items.first(), Some(Sexp::Atom(head, _)) if head == "sort") =>
                        {
                            let items = strip_variants(items, 1, &mut region_commands)?;
                            rest.push(Sexp::List(items, dspan.clone()));
                        }
                        other => rest.push(clone_sexp(other)),
                    }
                }
                rest
            }
        };
        // Parse the plain declaration with a macro-free parser, so this macro
        // does not recurse into itself.
        let mut items = vec![Sexp::Atom(self.head.to_string(), span.clone())];
        items.extend(stripped);
        let mut commands = Parser::default().parse_command(&Sexp::List(items, span))?;
        commands.extend(region_commands);
        Ok(commands)
    }
}

/// Register `:regions`, `effsafe-regions`, `set-effectful`, and
/// `print-function` with `:extractor effsafe`.
///
/// Also register [`crate::add_set_cost`] to enable `extract :extractor effsafe`.
/// [`crate::new_experimental_egraph`] registers both. See
/// [`set_effsafe_cost_models`] to customize the default dynamic cost models.
pub fn add_effsafe_extract(egraph: &mut EGraph) {
    egraph.parser.add_command_macro(Arc::new(RegionsAnnotation {
        head: "constructor",
    }));
    egraph
        .parser
        .add_command_macro(Arc::new(RegionsAnnotation { head: "datatype" }));
    egraph
        .parser
        .add_command_macro(Arc::new(RegionsAnnotation { head: "datatype*" }));
    let commands: [(&str, Arc<dyn UserDefinedCommand>); 2] = [
        ("effsafe-regions", Arc::new(EffsafeRegions)),
        ("print-function", Arc::new(PrintFunction)),
    ];
    for (name, command) in commands {
        egraph.add_command(name.into(), command).unwrap();
    }
    egraph.command_macros_mut().register(Arc::new(SetEffectful));
}
