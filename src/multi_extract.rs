//! Extract multiple terms or variants with one extractor pass.
//!
//! `(multi-extract n [:dag] term... [:extractor greedy-dag])` prints the `n`
//! lowest-cost variants of every term. `n` must be a positive `i64`;
//! `(multi-extract 1 term)` is equivalent to best extraction.
//!
//! With `:dag`, the output is one
//! `(let ((name def) ...) ((variant ...) ...))` s-expression in which subterms
//! shared across all variants of all terms are let-bound once, instead of every
//! variant being expanded to a tree.
//!
//! Use `(multi-extract n term... :extractor greedy-dag)` to charge shared
//! subterms once within each ranked variant. Greedy-DAG extraction is a
//! heuristic rather than a globally optimal k-best extractor.

use crate::greedy_dag_extract::{extract_variants_greedy_dag, split_trailing_extractor};
use egglog::{
    CommandOutput, EGraph, Error, TermDag, TermId, TypeError, UserDefinedCommand,
    ast::{Expr, ParseError},
    extract::{DagCostModel, MonoidCost, TreeCostModelFromDag},
    prelude::span,
};
use log::log_enabled;
use std::marker::PhantomData;

/// Displayable output produced by [`MultiExtract`].
#[derive(Debug)]
pub struct MultiExtractOutput {
    termdag: TermDag,
    terms: Vec<Vec<TermId>>,
    dag: bool,
}

impl std::fmt::Display for MultiExtractOutput {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.dag {
            let roots: Vec<TermId> = self.terms.iter().flatten().copied().collect();
            let (bindings, rendered) =
                crate::dag_print::render_terms_with_shared_lets(&self.termdag, &roots);
            writeln!(f, "(let (")?;
            for (name, def) in &bindings {
                writeln!(f, "   ({name} {def})")?;
            }
            writeln!(f, " )")?;
            writeln!(f, " (")?;
            let mut next = rendered.iter();
            for variants in &self.terms {
                writeln!(f, "   (")?;
                for _ in variants {
                    writeln!(f, "      {}", next.next().unwrap())?;
                }
                writeln!(f, "   )")?;
            }
            writeln!(f, " ))")
        } else {
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
}

/// User-defined command implementing
/// `(multi-extract n [:dag] term... [:extractor greedy-dag])` with a
/// caller-provided marginal cost model.
///
/// The positive `i64` value `n` is the number of variants returned for each
/// term. All terms share one extractor computation. Tree extraction adapts the
/// model with [`TreeCostModelFromDag`]; `:extractor greedy-dag` uses its
/// marginal costs directly.
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

        let Some((variants_expr, mut terms)) = args.split_first() else {
            return Err(Error::ParseError(ParseError(
                span!(),
                "multi-extract expects at least a variant count and one expression".into(),
            )));
        };
        let dag = matches!(terms.first(), Some(Expr::Var(_, option)) if option == ":dag");
        if dag {
            terms = &terms[1..];
        }
        if terms.is_empty() {
            return Err(Error::ParseError(ParseError(
                variants_expr.span(),
                "multi-extract expects at least a variant count and one expression".into(),
            )));
        }

        let (variants_sort, variants_value) = egraph.eval_expr(variants_expr)?;
        if variants_sort.name() != "i64" {
            return Err(Error::TypeError(TypeError::Mismatch {
                expr: variants_expr.clone(),
                expected: egraph.get_arcsort_by(|s| s.name() == "i64"),
                actual: variants_sort,
            }));
        }

        let n: i64 = egraph.value_to_base(variants_value);
        if n < 0 {
            return Err(Error::ParseError(ParseError(
                variants_expr.span(),
                "Cannot extract negative number of variants".into(),
            )));
        }
        if n == 0 {
            return Err(Error::ParseError(ParseError(
                variants_expr.span(),
                "multi-extract requires a positive number of variants".into(),
            )));
        }

        let roots: Vec<_> = terms
            .iter()
            .map(|arg| egraph.eval_expr(arg))
            .collect::<Result<_, _>>()?;

        let extracted = if use_greedy_dag {
            extract_variants_greedy_dag(egraph, roots, n as usize, self.cost_model.clone())
        } else {
            egraph.extract_variants_with_cost_model(
                roots,
                n as usize,
                TreeCostModelFromDag(self.cost_model.clone()),
            )
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
                dag,
            },
        ))])
    }
}
