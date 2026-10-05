//! Effect-safe extraction: `effsafe-extract`, `effsafe-extract-all`,
//! `effsafe-regions`, `effsafe-placeholder`, and the `:regions` annotation on
//! `constructor` and `datatype` declarations.
//!
//! This is the *statewalk DP* of Flatt et al., "Efficient Extraction for
//! Effectful E-graphs" (OOPSLA 2026, <https://doi.org/10.1145/3839530>).
//! See `docs/effsafe-extract.md` for the language-level description. In short:
//! the program marks effectful e-classes in a relation, annotates which
//! constructor arguments start subregions, and the extractor chooses one
//! effectful e-node per e-class along each region's *statewalk* such that the
//! pure terms those e-nodes need are extractable from the chosen state.

mod build;
mod checks;
mod cost;
mod greedy;
mod persistent;
mod region;
mod statewalk;
mod term_graph;
mod to_term;

use std::collections::HashMap;
use std::sync::Arc;

use egglog::ast::{Command, Expr, Literal, Macro, ParseError, Parser, Sexp};
use egglog::extract::DagCostModel;
use egglog::{CommandOutput, EGraph, Error, TermDag, TermId, UserDefinedCommand, span};
use egglog_ast::span::Span;
use rustc_hash::FxHashMap;

pub use build::Roots;
pub use cost::{Cost, RegionCostModel, SumRegions};
pub use statewalk::StatewalkOptions;

/// The language's effect annotations, collected from `:regions` and
/// `effsafe-placeholder` as the program runs.
#[derive(Clone, Debug, Default)]
pub struct EffsafeConfig {
    /// Constructor name to the argument positions that start subregions.
    pub regions: HashMap<String, Vec<usize>>,
    /// Sort name to the term that stands in for every value of that sort.
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
    /// Annotations from `:regions`, `effsafe-regions` and `effsafe-placeholder`.
    pub config: EffsafeConfig,
    /// Prices e-nodes, base values and containers.
    pub cost_model: Arc<dyn DagCostModel<Cost> + Send + Sync>,
    /// Folds subregion costs into their parent e-node's cost.
    pub region_costs: Arc<dyn RegionCostModel>,
}

impl Default for EffsafeState {
    fn default() -> Self {
        EffsafeState {
            config: EffsafeConfig::default(),
            cost_model: Arc::new(crate::DynamicCostModel),
            region_costs: Arc::new(SumRegions),
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

/// Use `cost_model` and `region_costs` for effect-safe extraction on `egraph`.
///
/// The default is the dynamic cost model (`:cost` and `set-cost`) with
/// subregion costs summed. A compiler embedding egglog can supply heuristics
/// that are not expressible as annotations, such as charging only the more
/// expensive branch of a conditional.
pub fn set_effsafe_cost_models(
    egraph: &mut EGraph,
    cost_model: impl DagCostModel<Cost> + Send + Sync + 'static,
    region_costs: impl RegionCostModel + 'static,
) {
    let state = effsafe_state(egraph);
    state.cost_model = Arc::new(cost_model);
    state.region_costs = Arc::new(region_costs);
}

/// Output of `effsafe-extract` and `effsafe-extract-all`: one term per root.
#[derive(Debug)]
pub struct EffsafeExtractOutput {
    /// Term storage shared by every root.
    pub termdag: TermDag,
    /// Root terms, in request order (or e-class order for `effsafe-extract-all`).
    pub terms: Vec<TermId>,
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

/// Extract `roots` effect-safely.
///
/// `effectful` names the relation holding the effectful e-classes.
/// `cost_model` gives each e-node's marginal cost; `region_costs` folds the
/// costs of an e-node's subregions into its own.
pub fn extract_effsafe(
    egraph: &EGraph,
    effectful: &str,
    roots: &Roots,
    config: &EffsafeConfig,
    cost_model: &dyn DagCostModel<Cost>,
    region_costs: &dyn RegionCostModel,
) -> Result<EffsafeExtractOutput, Error> {
    let t0 = std::time::Instant::now();
    let (g, root_classes) = build::build(egraph, config, cost_model, effectful, roots)?;
    let t_build = t0.elapsed();
    let t1 = std::time::Instant::now();
    let extractions = region::extract_all(
        &g,
        egraph,
        region_costs,
        &root_classes,
        StatewalkOptions::default(),
    )?;
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
        .map(|e| to_term::extraction_to_term(&g, egraph, &placeholders, e, &mut termdag))
        .collect();
    Ok(EffsafeExtractOutput { termdag, terms })
}

/// Split a trailing `:include-subsumed` flag off a command's arguments.
fn split_include_subsumed(args: &[Expr]) -> (&[Expr], bool) {
    match args.split_last() {
        Some((Expr::Var(_, flag), rest)) if flag == ":include-subsumed" => (rest, true),
        _ => (args, false),
    }
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

/// `(effsafe-placeholder <sort> <expr>)`: extraction does not descend into
/// values of `sort`; every such child becomes `expr` in the output.
pub struct EffsafePlaceholder;

impl UserDefinedCommand for EffsafePlaceholder {
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        let [sort, expr] = args else {
            return Err(usage(span!(), "usage: (effsafe-placeholder <sort> <expr>)"));
        };
        let sort = expect_name(sort, "sort")?;
        if egraph.get_sort_by_name(&sort).is_none() {
            return Err(usage(
                args[0].span(),
                &format!("{sort} is not a declared sort"),
            ));
        }
        effsafe_state(egraph)
            .config
            .placeholders
            .insert(sort, expr.clone());
        Ok(vec![])
    }
}

/// `(effsafe-extract <effectful-relation> <expr>...)`.
pub struct EffsafeExtract;

impl UserDefinedCommand for EffsafeExtract {
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        let (args, include_subsumed) = split_include_subsumed(args);
        let [relation, exprs @ ..] = args else {
            return Err(usage(
                span!(),
                "usage: (effsafe-extract <effectful-relation> <expr>... [:include-subsumed])",
            ));
        };
        if exprs.is_empty() {
            return Err(usage(
                relation.span(),
                "effsafe-extract needs at least one expression",
            ));
        }
        let relation = expect_name(relation, "relation")?;
        let values = exprs
            .iter()
            .map(|e| egraph.eval_expr(e))
            .collect::<Result<Vec<_>, _>>()?;
        let mut state = effsafe_state(egraph).clone();
        state.config.include_subsumed |= include_subsumed;
        let output = extract_effsafe(
            egraph,
            &relation,
            &Roots::Values(values),
            &state.config,
            state.cost_model.as_ref(),
            state.region_costs.as_ref(),
        )?;
        Ok(vec![CommandOutput::UserDefined(Arc::new(output))])
    }
}

/// `(effsafe-extract-all <effectful-relation> <constructor>)`: extract every
/// e-class holding an e-node of `constructor`.
pub struct EffsafeExtractAll;

impl UserDefinedCommand for EffsafeExtractAll {
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        let (args, include_subsumed) = split_include_subsumed(args);
        let [relation, constructor] = args else {
            return Err(usage(
                span!(),
                "usage: (effsafe-extract-all <effectful-relation> <constructor> [:include-subsumed])",
            ));
        };
        let relation = expect_name(relation, "relation")?;
        let constructor = expect_name(constructor, "constructor")?;
        let mut state = effsafe_state(egraph).clone();
        state.config.include_subsumed |= include_subsumed;
        let output = extract_effsafe(
            egraph,
            &relation,
            &Roots::Constructor(&constructor),
            &state.config,
            state.cost_model.as_ref(),
            state.region_costs.as_ref(),
        )?;
        Ok(vec![CommandOutput::UserDefined(Arc::new(output))])
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
/// and the `effsafe-*` commands. Cost models default to the dynamic cost
/// model with summed subregions; see [`set_effsafe_cost_models`].
pub fn add_effsafe_extract(egraph: &mut EGraph) {
    egraph.parser.add_command_macro(Arc::new(RegionsAnnotation {
        head: "constructor",
    }));
    egraph
        .parser
        .add_command_macro(Arc::new(RegionsAnnotation { head: "datatype" }));
    let commands: [(&str, Arc<dyn UserDefinedCommand>); 4] = [
        ("effsafe-regions", Arc::new(EffsafeRegions)),
        ("effsafe-placeholder", Arc::new(EffsafePlaceholder)),
        ("effsafe-extract", Arc::new(EffsafeExtract)),
        ("effsafe-extract-all", Arc::new(EffsafeExtractAll)),
    ];
    for (name, command) in commands {
        egraph.add_command(name.into(), command).unwrap();
    }
}
