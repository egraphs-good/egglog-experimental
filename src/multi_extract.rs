//! Extract multiple terms or variants with one extractor pass.
//!
//! `(multi-extract n term...)` prints the `n` lowest-cost variants of every
//! term. `n` must be a positive `i64`; `(multi-extract 1 term)` is equivalent
//! to best extraction.
//! Use `(multi-extract n term... :extractor greedy-dag)` to charge shared
//! subterms once within each ranked variant. Greedy-DAG extraction is a
//! heuristic rather than a globally optimal k-best extractor.

use crate::greedy_dag_extract::{extract_variants_greedy_dag_by_root, split_trailing_extractor};
use egglog::{
    CommandOutput, EGraph, Error, TermDag, TermId, TypeError, UserDefinedCommand,
    ast::{Expr, ParseError},
    extract::{DagCostModel, MonoidCost, TreeCostModelFromDag, TreeExtractor},
    prelude::span,
};
use log::log_enabled;
use std::marker::PhantomData;

/// Legacy aggregate output previously produced by [`MultiExtract`].
///
/// `multi-extract` now returns one standard [`CommandOutput::ExtractVariants`]
/// for each requested root. This type remains public for source compatibility.
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

/// User-defined command implementing `(multi-extract n term...)` with a
/// caller-provided marginal cost model.
///
/// The positive `i64` value `n` is the number of variants returned for each
/// term. All terms share one extractor computation, but each root is
/// reconstructed into its own [`TermDag`] and returned as a standard
/// [`CommandOutput::ExtractVariants`]. Tree extraction adapts the model with
/// [`TreeCostModelFromDag`]; `:extractor greedy-dag` uses its marginal costs
/// directly.
pub struct MultiExtract<C: MonoidCost, CM: DagCostModel<C> + Clone> {
    cost_model: CM,
    // Extracted costs are temporary, so this marker should not impose their
    // ownership or auto-trait properties on the registered command.
    _cost: PhantomData<fn() -> C>,
}

impl<C: MonoidCost, CM: DagCostModel<C> + Clone> MultiExtract<C, CM> {
    /// Creates a multi-extract command for `cost_model`.
    pub fn new(cost_model: CM) -> Self {
        MultiExtract {
            cost_model,
            _cost: PhantomData,
        }
    }
}

impl<C: MonoidCost, CM: DagCostModel<C> + Clone + Send + Sync + 'static> UserDefinedCommand
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

        let root_count = roots.len();
        let extracted = if use_greedy_dag {
            extract_variants_greedy_dag_by_root(egraph, roots, n as usize, self.cost_model.clone())?
        } else {
            let root_sorts = roots.iter().map(|(sort, _)| sort.clone()).collect();
            let extractor = TreeExtractor::compute_costs_from_rootsorts(
                Some(root_sorts),
                egraph,
                TreeCostModelFromDag(self.cost_model.clone()),
            );
            roots
                .into_iter()
                .map(|(sort, value)| {
                    let mut termdag = TermDag::default();
                    let variants =
                        extractor.extract_variants_with_sort(&mut termdag, value, n as usize, sort);
                    (termdag, variants)
                })
                .collect()
        };

        let outputs = extracted
            .into_iter()
            .map(|(termdag, variants)| {
                CommandOutput::ExtractVariants(
                    termdag,
                    variants.into_iter().map(|variant| variant.term).collect(),
                )
            })
            .collect();

        if log_enabled!(log::Level::Info) {
            log::info!(
                "extracted up to {} variants for each of {} expressions",
                n,
                root_count
            );
        }

        Ok(outputs)
    }
}
