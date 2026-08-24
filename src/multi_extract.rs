//! Extract multiple terms or variants with one extractor pass.
//!
//! `(multi-extract n [:dag] term...)` prints the `n` lowest-cost variants of
//! every term. `n` must be a positive `i64`; `(multi-extract 1 term)` is
//! equivalent to best extraction.
//!
//! With `:dag`, the output is one
//! `(let ((name def) ...) ((variant ...) ...))` s-expression in which
//! subterms shared across all variants of all terms are let-bound once (see
//! [`crate::dag_print`]), instead of every variant being expanded to a tree.

use egglog::{
    CommandOutput, EGraph, Error, TermDag, TermId, TypeError, UserDefinedCommand,
    ast::{Expr, ParseError},
    extract::{Cost, CostModel, Extractor},
    prelude::span,
};
use log::log_enabled;
use std::{fmt::Debug, marker::PhantomData};

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
            let (bindings, rendered) = crate::render_terms_with_shared_lets(&self.termdag, &roots);
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

/// User-defined command implementing `(multi-extract n term...)` with a
/// caller-provided cost model.
///
/// The positive `i64` value `n` is the number of variants returned for each
/// term. All terms share one extractor computation.
pub struct MultiExtract<C: Cost + Ord + Eq + Clone + Debug + Send + Sync, CM: CostModel<C> + Clone>
{
    cost_model: CM,
    _cost_t: PhantomData<C>,
}

impl<C: Cost + Ord + Eq + Clone + Debug + Send + Sync, CM: CostModel<C> + Clone>
    MultiExtract<C, CM>
{
    /// Creates a multi-extraction command that uses `cost_model`.
    pub fn new(cost_model: CM) -> Self {
        MultiExtract {
            cost_model,
            _cost_t: PhantomData,
        }
    }
}

impl<
    C: Cost + Ord + Eq + Clone + Debug + Send + Sync,
    CM: CostModel<C> + Clone + Send + Sync + 'static,
> UserDefinedCommand for MultiExtract<C, CM>
{
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        // `:dag` may appear anywhere among the arguments.
        let mut dag = false;
        let args: Vec<Expr> = args
            .iter()
            .filter(|arg| match arg {
                Expr::Var(_, v) if v == ":dag" => {
                    dag = true;
                    false
                }
                _ => true,
            })
            .cloned()
            .collect();
        let args = args.as_slice();
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

        let (sorts, values): (Vec<_>, Vec<_>) = args[1..]
            .iter()
            .map(|arg| egraph.eval_expr(arg))
            .collect::<Result<_, _>>()?;

        let mut termdag = TermDag::default();
        let extractor = Extractor::compute_costs_from_rootsorts(
            Some(sorts.clone()),
            egraph,
            self.cost_model.clone(),
        );

        let terms: Vec<Vec<_>> = values
            .into_iter()
            .zip(sorts)
            .map(|(value, sort)| {
                extractor
                    .extract_variants_with_sort(egraph, &mut termdag, value, n as usize, sort)
                    .into_iter()
                    .map(|e| e.1)
                    .collect()
            })
            .collect();

        if log_enabled!(log::Level::Info) {
            log::info!(
                "extracted {} variants for each of {} expressions",
                n,
                terms.len()
            );
        }

        Ok(vec![CommandOutput::UserDefined(std::sync::Arc::from(
            MultiExtractOutput {
                termdag,
                terms,
                dag,
            },
        ))])
    }
}
