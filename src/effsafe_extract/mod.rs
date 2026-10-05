//! Effect-safe extraction: `(extract e :extractor effsafe)`,
//! `(print-function Ctor :extractor effsafe)`, `(set-effectful e)`, and the
//! `:regions` annotation on `constructor` and `datatype` declarations
//! (lowered to `effsafe-regions`).
//!
//! This is the *statewalk DP* of Flatt et al., "Efficient Extraction for
//! Effectful E-graphs" (OOPSLA 2026, <https://doi.org/10.1145/3839530>).
//! See `docs/effsafe-extract.md` for the language-level description. In short:
//! the program marks effectful e-classes with `set-effectful`, annotates which
//! constructor arguments start subregions, and the extractor chooses one
//! effectful e-node per e-class along each region's *statewalk* such that the
//! pure terms those e-nodes need are extractable from the chosen state.

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
use std::sync::Arc;

use egglog::ast::{Command, Expr, Literal, Macro, ParseError, Parser, PrintFunctionMode, Sexp};
use egglog::extract::{DagCostModel, TreeCostModelFromDag};
use egglog::{CommandOutput, EGraph, Error, TermDag, TermId, UserDefinedCommand, span};
use egglog_ast::span::Span;
use rustc_hash::FxHashMap;

pub use build::Roots;
pub use cost::{Cost, RegionBoundary};
pub use set_effectful::{SetEffectful, effectful_relation};
pub use statewalk::StatewalkOptions;

/// The language's effect annotations, collected from `:regions` and
/// `effsafe-placeholder` as the program runs.
#[derive(Clone, Debug, Default)]
pub struct EffsafeConfig {
    /// Constructor name to the argument positions that start subregions.
    pub regions: HashMap<String, Vec<usize>>,
    /// Sort name to the constructor application that stands in for every value
    /// of that sort. Extraction does not descend into these sorts; the
    /// replacement must be a nullary-or-not constructor of the sort (checked
    /// when extraction runs). Set from Rust by embedders whose terms refer
    /// back to the region they are in (eggcc's contexts); there is no egglog
    /// command for it, since it changes the extracted term's meaning.
    pub placeholders: HashMap<String, Expr>,
    /// Extract from subsumed e-nodes too. egglog's own extractors skip them;
    /// a program whose rules subsume e-nodes for reasons other than
    /// extraction can opt back in with a trailing `:include-subsumed`.
    pub include_subsumed: bool,
}

/// Everything effect-safe extraction keeps on an e-graph: the annotations and
/// the cost models. Stored as egglog extension state, so it is cloned and
/// snapshotted with the e-graph. Change the models with
/// [`set_effsafe_cost_models`].
#[derive(Clone)]
pub struct EffsafeState {
    /// Annotations from `:regions` / `effsafe-regions`, and placeholders.
    pub config: EffsafeConfig,
    /// Marginal costs within a region: e-nodes, base values and containers.
    pub cost_model: Arc<dyn DagCostModel<Cost> + Send + Sync>,
    /// How an e-node's subregions' costs compose with its own (a
    /// [`TreeCostModel`](egglog::extract::TreeCostModel) at region boundaries).
    pub boundary: Arc<dyn RegionBoundary>,
}

impl Default for EffsafeState {
    fn default() -> Self {
        EffsafeState {
            config: EffsafeConfig::default(),
            cost_model: Arc::new(crate::DynamicCostModel),
            boundary: Arc::new(TreeCostModelFromDag(crate::DynamicCostModel)),
        }
    }
}

impl std::fmt::Debug for EffsafeState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
/// `boundary` is a [`TreeCostModel`](egglog::extract::TreeCostModel): for an
/// e-node with `:regions` children its `enode_cost` annotation is kept, and
/// `fold_enode_cost` is called with the subregions' costs in their argument
/// positions and `0` for every other child. The result replaces the e-node's
/// marginal cost in the enclosing region, whose DAG then charges the ordinary
/// children. The default is the dynamic cost model (`:cost` and `set-cost`)
/// wrapped in `TreeCostModelFromDag`, which adds the subregions up. A compiler
/// embedding egglog can supply heuristics such as charging only the more
/// expensive branch of a conditional or weighting a loop body.
pub fn set_effsafe_cost_models<B>(
    egraph: &mut EGraph,
    cost_model: impl DagCostModel<Cost> + Send + Sync + 'static,
    boundary: B,
) where
    B: egglog::extract::TreeCostModel<Cost> + Send + Sync + 'static,
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
    /// Per root, the sum of the marginal costs of the distinct e-nodes in its
    /// extracted DAG (subregion folds are not included).
    pub costs: Vec<Cost>,
}

impl std::fmt::Display for EffsafeExtractOutput {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
pub fn extract_effsafe(
    egraph: &EGraph,
    roots: &Roots,
    config: &EffsafeConfig,
    cost_model: &dyn DagCostModel<Cost>,
    boundary: &dyn RegionBoundary,
) -> Result<EffsafeExtractOutput, Error> {
    let t0 = std::time::Instant::now();
    let (g, root_classes) = build::build(egraph, config, cost_model, boundary, roots)?;
    let t_build = t0.elapsed();
    let t1 = std::time::Instant::now();
    let extractions =
        region::extract_all(&g, boundary, &root_classes, StatewalkOptions::default())?;
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
    let mut placeholders: FxHashMap<term_graph::SortId, TermId> = FxHashMap::default();
    for (sort_id, sort) in g.sorts.iter().enumerate() {
        if let Some(expr) = config.placeholders.get(sort.name()) {
            placeholders.insert(sort_id, termdag.expr_to_term(expr));
        }
    }
    let terms = extractions
        .iter()
        .map(|e| {
            to_term::extraction_to_term(&g, egraph, &placeholders, &e.extraction, &mut termdag)
        })
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

/// The cost of an extracted program under the same model the search used:
/// within each region the distinct e-nodes' marginal costs are summed (a DAG
/// cost), and an e-node with subregions is charged its boundary fold of the
/// subregions' costs, once per occurrence, in place of its marginal cost.
fn program_cost(
    g: &term_graph::TermGraph,
    boundary: &dyn RegionBoundary,
    placed: &region::PlacedExtraction,
) -> Cost {
    let nodes = &placed.extraction;
    // Subregions are placed before the nodes that use them, so a region's
    // total is complete by the time a parent node folds it.
    let mut region_total: FxHashMap<usize, Cost> = FxHashMap::default();
    for (i, en) in nodes.iter().enumerate() {
        let enode = g.enode(en.class, en.node);
        let cost = if enode.regions.is_empty() {
            enode.cost
        } else {
            let mut by_position = vec![0; enode.children.len()];
            for &p in &enode.regions {
                let child = en.children[p];
                if g.is_effectful(nodes[child].class) {
                    by_position[p] = region_total[&placed.region_of_node[child]];
                }
            }
            let annotation = enode
                .boundary
                .as_deref()
                .expect("regions carry an annotation");
            boundary.fold(annotation, &by_position)
        };
        let total = region_total.entry(placed.region_of_node[i]).or_insert(0);
        *total = total.saturating_add(cost);
    }
    region_total[&placed.region_of_node[nodes.len() - 1]]
}

/// Split a trailing `:include-subsumed` flag, which lets effect-safe
/// extraction extract from subsumed e-nodes, off a command's arguments.
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
) -> Result<EffsafeExtractOutput, Error> {
    let mut state = effsafe_state(egraph).clone();
    state.config.include_subsumed |= include_subsumed;
    extract_effsafe(
        egraph,
        roots,
        &state.config,
        state.cost_model.as_ref(),
        state.boundary.as_ref(),
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
        let output = extract_with_options(egraph, include_subsumed, &Roots::Constructor(&name))?;
        let mut terms: Vec<(TermId, TermId)> = output.terms.iter().map(|&t| (t, t)).collect();
        if let Some(n) = rows {
            terms.truncate(n);
        }
        let result = CommandOutput::PrintFunction(function, output.termdag, terms, mode);
        if let Some((mut file, path)) = file {
            use std::io::Write;
            write!(file, "{result}").map_err(|e| Error::IoError(path, e, span!()))?;
            return Ok(vec![]);
        }
        Ok(vec![result])
    }
}

/// Parse-time macro that lets `constructor` and `datatype` declarations carry
/// `:regions (<position>...)`. The option is stripped, the declaration is
/// parsed as usual, and an `effsafe-regions` command follows it.
struct RegionsAnnotation {
    head: &'static str,
}

/// `Sexp` is not `Clone`; copy one by hand.
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
            _ => {
                // (datatype Name (Variant Sort... :regions (...))...)
                let mut rest = Vec::with_capacity(args.len());
                for (i, arg) in args.iter().enumerate() {
                    match arg {
                        Sexp::List(variant, vspan) if i > 0 => {
                            let (items, positions) = strip_regions(variant)?;
                            if let (Some(positions), Some(Sexp::Atom(name, _))) =
                                (positions, variant.first())
                            {
                                region_commands.push(regions_command(
                                    vspan.clone(),
                                    name,
                                    &positions,
                                ));
                            }
                            rest.push(Sexp::List(items, vspan.clone()));
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

/// Register effect-safe extraction on an e-graph: the `:regions` annotation
/// (and `effsafe-regions`, its lowering), `set-effectful`, and
/// `print-function` with `:extractor effsafe`. The `:extractor effsafe` of
/// `extract` lives in the dynamic-cost `extract` command (`set_cost.rs`).
/// Cost models default to the dynamic cost model with summed subregions; see
/// [`set_effsafe_cost_models`].
pub fn add_effsafe_extract(egraph: &mut EGraph) {
    egraph.parser.add_command_macro(Arc::new(RegionsAnnotation {
        head: "constructor",
    }));
    egraph
        .parser
        .add_command_macro(Arc::new(RegionsAnnotation { head: "datatype" }));
    let commands: [(&str, Arc<dyn UserDefinedCommand>); 2] = [
        ("effsafe-regions", Arc::new(EffsafeRegions)),
        ("print-function", Arc::new(PrintFunction)),
    ];
    for (name, command) in commands {
        egraph.add_command(name.into(), command).unwrap();
    }
    egraph.command_macros_mut().register(Arc::new(SetEffectful));
}
