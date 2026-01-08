use egglog::{
    CommandOutput, EGraph, Error, Term, TermDag, TypeError, UserDefinedCommand,
    ast::Expr,
    extract::{Extractor, TreeAdditiveCostModel},
};
use log::log_enabled;

#[derive(Debug)]
pub struct MultiExtractOutput {
    termdag: TermDag,
    terms: Vec<Vec<Term>>,
}

impl std::fmt::Display for MultiExtractOutput {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "(")?;
        for variants in &self.terms {
            writeln!(f, "   (")?;
            for expr in variants {
                writeln!(f, "      {}", self.termdag.to_string(expr))?;
            }
            writeln!(f, "   )")?;
        }
        writeln!(f, ")")
    }
}

pub struct MultiExtract;

impl UserDefinedCommand for MultiExtract {
    fn update(
        &self,
        egraph: &mut EGraph,
        args: &[Expr],
    ) -> Result<Option<CommandOutput>, egglog::Error> {
        assert!(args.len() >= 2);

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
            panic!("Cannot extract negative number of variants");
        }

        let (sorts, values): (Vec<_>, Vec<_>) = args[1..]
            .iter()
            .map(|arg| egraph.eval_expr(arg))
            .collect::<Result<_, _>>()?;

        let mut termdag = TermDag::default();
        let extractor = Extractor::compute_costs_from_rootsorts(
            Some(sorts.clone()),
            egraph,
            TreeAdditiveCostModel {},
        );

        let terms: Vec<_> = values
            .into_iter()
            .zip(sorts)
            .map(|(value, sort)| {
                extractor
                    .extract_variants_with_sort(egraph, &mut termdag, value, n as usize, sort)
                    .iter()
                    .map(|e| e.1.clone())
                    .collect::<Vec<_>>()
            })
            .collect();

        if log_enabled!(log::Level::Info) {
            log::info!(
                "extracted {} total variants across all expressions",
                terms.len()
            );
        }

        Ok(Some(CommandOutput::UserDefined(std::sync::Arc::from(
            MultiExtractOutput { termdag, terms },
        ))))
    }
}
