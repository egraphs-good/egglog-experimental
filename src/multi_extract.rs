//! Extract multiple terms or variants with one extractor pass.
//!
//! `(multi-extract n term...)` prints the `n` lowest-cost variants of every
//! term. `n` must be a positive `i64`; `(multi-extract 1 term)` is equivalent
//! to best extraction.
//! Use `(multi-extract n term... :extractor greedy-dag)` to charge shared
//! subterms once within each ranked variant. Greedy-DAG extraction is a
//! heuristic rather than a globally optimal k-best extractor.

use crate::greedy_dag_extract::{extract_variants_greedy_dag, split_trailing_extractor};
use egglog::{
    ArcSort, CommandOutput, EGraph, Error, TermDag, TermId, TypeError, UserDefinedCommand, Value,
    ast::{Expr, ParseError},
    extract::{Cost, DagCostModel, ExtractedTermVariants, MonoidCost, TreeCostModel},
    prelude::span,
};
use log::log_enabled;

/// Displayable output produced by [`MultiExtract`].
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

/// User-defined command implementing `(multi-extract n term...)` with a
/// caller-provided tree cost model.
///
/// The positive `i64` value `n` is the number of variants returned for each
/// term. All terms share one extractor computation. [`MultiExtract::new`]
/// supports tree extraction, while [`MultiExtract::with_greedy_dag`] also
/// accepts `:extractor greedy-dag` when the model also implements
/// [`DagCostModel`].
pub struct MultiExtract<C: Cost, CM: TreeCostModel<C> + Clone> {
    cost_model: CM,
    greedy_dag_extract: Option<GreedyDagExtractFn<C, CM>>,
}

impl<C: Cost, CM: TreeCostModel<C> + Clone> MultiExtract<C, CM> {
    /// Creates a tree-only multi-extract command for `cost_model`.
    pub fn new(cost_model: CM) -> Self {
        MultiExtract {
            cost_model,
            greedy_dag_extract: None,
        }
    }
}

impl<C: MonoidCost, CM: DagCostModel<C> + TreeCostModel<C> + Clone> MultiExtract<C, CM> {
    /// Creates a multi-extract command that also accepts `:extractor greedy-dag`.
    pub fn with_greedy_dag(cost_model: CM) -> Self {
        Self {
            cost_model,
            greedy_dag_extract: Some(extract_variants_greedy_dag::<C, CM>),
        }
    }
}

impl<C: Cost, CM: TreeCostModel<C> + Clone + Send + Sync + 'static> UserDefinedCommand
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
            egraph.extract_variants_with_cost_model(roots, n as usize, self.cost_model.clone())
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
