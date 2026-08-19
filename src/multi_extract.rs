//! An implementation of multi-extraction for egraphs.
//! Adds support for extracting multiple terms with a single command,
//! reducing the overhead of creating an extractor for each term.
//! The syntax for multi-extraction is `(multi-extract n t1 ... tm)`,
//! where n must be a positive i64.
//! Use `(multi-extract n t1 ... tm :extractor greedy-dag)` to charge shared
//! subterms once when ranking each expression's variants.
//! Tree extraction returns up to n lowest-cost root variants of each term.
//! Greedy-DAG extraction is a heuristic: it ranks root enodes after reconciling
//! greedy child snapshots and is not globally optimal.
//! `(multi-extract 1 t)` is equivalent to `(extract t)`. Unlike
//! `(extract t 0)`, `(multi-extract 0 t)` is rejected.

use crate::greedy_dag_extract::{extract_variants_greedy_dag, split_trailing_extractor};
use egglog::{
    ArcSort, CommandOutput, EGraph, Error, TermDag, TermId, TypeError, UserDefinedCommand, Value,
    ast::{Expr, ParseError},
    extract::{CombinableCost, Cost, ExtractedTermVariants, MarginalCostModel, TotalCostModel},
    prelude::span,
};
use log::log_enabled;

#[derive(Debug)]
pub struct MultiExtractOutput {
    termdag: TermDag,
    terms: Vec<Vec<TermId>>,
}

impl std::fmt::Display for MultiExtractOutput {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "(")?;
        for variants in &self.terms {
            writeln!(f, "   (")?;
            for expr in variants {
                writeln!(f, "      {}", self.termdag.to_string(*expr))?;
            }
            writeln!(f, "   )")?;
        }
        writeln!(f, ")")
    }
}

type GreedyDagExtractFn<C, CM> =
    fn(&EGraph, Vec<(ArcSort, Value)>, usize, CM) -> Result<ExtractedTermVariants<C>, Error>;

/// A user-defined multi-extract command using `CM` for tree extraction.
///
/// [`MultiExtract::new`] accepts any total tree cost model.
/// [`MultiExtract::with_greedy_dag`] additionally enables the
/// `:extractor greedy-dag` syntax when the model also supplies marginal costs.
pub struct MultiExtract<C: Cost, CM: TotalCostModel<C> + Clone> {
    cost_model: CM,
    greedy_dag_extract: Option<GreedyDagExtractFn<C, CM>>,
}

impl<C: Cost, CM: TotalCostModel<C> + Clone> MultiExtract<C, CM> {
    /// Creates a tree-only multi-extract command for `cost_model`.
    pub fn new(cost_model: CM) -> Self {
        MultiExtract {
            cost_model,
            greedy_dag_extract: None,
        }
    }
}

impl<C: CombinableCost, CM: MarginalCostModel<C> + TotalCostModel<C> + Clone> MultiExtract<C, CM> {
    /// Creates a multi-extract command that also accepts `:extractor greedy-dag`.
    pub fn with_greedy_dag(cost_model: CM) -> Self {
        Self {
            cost_model,
            greedy_dag_extract: Some(extract_variants_greedy_dag::<C, CM>),
        }
    }
}

impl<C: Cost, CM: TotalCostModel<C> + Clone + Send + Sync + 'static> UserDefinedCommand
    for MultiExtract<C, CM>
{
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        let (args, use_greedy_dag) = split_trailing_extractor(args)?;

        if args.len() < 2 {
            let span = args.first().map(Expr::span).unwrap_or_else(|| span!());
            return Err(Error::ParseError(ParseError(
                span,
                "multi-extract expects at least a variant count and one expression".into(),
            )));
        }

        let (variants_sort, variants_value) = egraph.eval_expr(&args[0])?;
        if variants_sort.name() != "i64" {
            return Err(Error::TypeError(TypeError::Mismatch {
                expr: args[0].clone(),
                expected: egraph.get_arcsort_by(|s| s.name() == "i64"),
                actual: variants_sort,
            }));
        }

        let n: i64 = egraph.value_to_base(variants_value);
        if n < 0 {
            return Err(Error::ParseError(ParseError(
                args[0].span(),
                "Cannot extract negative number of variants".into(),
            )));
        }
        if n == 0 {
            return Err(Error::ParseError(ParseError(
                args[0].span(),
                "multi-extract requires a positive number of variants".into(),
            )));
        }

        let roots: Vec<_> = args[1..]
            .iter()
            .map(|arg| egraph.eval_expr(arg))
            .collect::<Result<_, _>>()?;

        let extracted = if use_greedy_dag {
            let extract = self.greedy_dag_extract.ok_or_else(|| {
                Error::ExtractError(
                    "this multi-extract cost model does not support greedy-DAG extraction"
                        .to_owned(),
                )
            })?;
            extract(egraph, roots, n as usize, self.cost_model.clone())
        } else {
            egraph.extract_variants(roots, n as usize, self.cost_model.clone())
        }?;

        let terms: Vec<Vec<_>> = extracted
            .variants
            .into_iter()
            .map(|variants| variants.into_iter().map(|variant| variant.term).collect())
            .collect();

        if log_enabled!(log::Level::Info) {
            log::info!(
                "extracted up to {} variants for each of {} expressions",
                n,
                terms.len()
            );
        }

        Ok(vec![CommandOutput::UserDefined(std::sync::Arc::from(
            MultiExtractOutput {
                termdag: extracted.termdag,
                terms,
            },
        ))])
    }
}
