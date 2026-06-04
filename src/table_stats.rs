//! `(print-table-stats <table>?)` — per-column statistics for function tables.
//!
//! For each function table, this command reports:
//! 1. The number of distinct values in every column (including the output column).
//! 2. For every ordered pair of distinct columns `(source, target)`, the
//!    min / 25th percentile / median / mean / 75th percentile / max of the
//!    *out-degree* — i.e. for each value in `source`, the number of distinct
//!    values seen in `target` across rows sharing that source value.
//! 3. For tables with two or more input columns, the same statistics for
//!    `(output -> combined inputs)` — i.e. for each output value, the number
//!    of distinct input tuples that produce it.
//!
//! Without arguments, every non-hidden, non-let-binding function is reported
//! (alphabetically). With one argument (an unquoted function name) only that
//! function is reported.

use egglog::{
    CommandOutput, EGraph, Error, FunctionRow, TypeError, UserDefinedCommand, Value, ast::Expr,
    prelude::Span,
};
use egglog_ast::generic_ast::GenericExpr;
use std::{
    collections::{HashMap, HashSet},
    fmt::{Display, Formatter},
    sync::Arc,
};

/// Min/max/mean and 25th/50th/75th percentile statistics over the out-degrees
/// of a (set of) source column(s) with respect to a (set of) target column(s).
#[derive(Clone, Debug)]
pub struct OutDegreeStats {
    /// The smallest number of distinct target-tuple values observed for any
    /// single source-key value.
    pub min: usize,
    /// The largest number of distinct target-tuple values observed for any
    /// single source-key value.
    pub max: usize,
    /// The mean number of distinct target-tuple values across all source-key
    /// values.
    pub mean: f64,
    /// The 25th percentile (linear interpolation between adjacent ranks).
    pub p25: f64,
    /// The 50th percentile / median (linear interpolation between adjacent
    /// ranks).
    pub median: f64,
    /// The 75th percentile (linear interpolation between adjacent ranks).
    pub p75: f64,
}

/// A single out-degree entry: for each distinct combination of source-column
/// values, how many distinct combinations of target-column values were
/// observed.
#[derive(Clone, Debug)]
pub struct PairOutDegree {
    /// Column indices that together form the "source" key.
    pub source: Vec<usize>,
    /// Column indices that together form the "target" tuple counted per
    /// source key.
    pub target: Vec<usize>,
    /// Out-degree statistics across all distinct source-key values.
    pub stats: OutDegreeStats,
}

/// Per-column statistics for a single function table.
#[derive(Clone, Debug)]
pub struct TableStats {
    /// The display name of the function table.
    pub name: String,
    /// Number of rows in the table.
    pub size: usize,
    /// Column type names, in column order. The final entry corresponds to
    /// the output column.
    pub column_types: Vec<String>,
    /// Number of distinct values seen in each column, in column order.
    pub distinct_counts: Vec<usize>,
    /// Out-degree statistics. Includes every ordered pair of distinct
    /// columns `(source, target)` plus, when the table has at least two
    /// input columns, the extra entry `(output -> combined inputs)`.
    pub out_degrees: Vec<PairOutDegree>,
}

/// Output wrapper for `Vec<TableStats>`. Renders as an indented
/// S-expression so it composes with the rest of egglog's output format.
#[derive(Debug)]
pub struct TableStatsOutput {
    pub stats: Vec<TableStats>,
}

/// User-defined command implementing `(print-table-stats <name>?)`.
pub struct PrintTableStatsCommand;

impl OutDegreeStats {
    fn from_counts(counts: &[usize]) -> Self {
        if counts.is_empty() {
            return OutDegreeStats {
                min: 0,
                max: 0,
                mean: 0.0,
                p25: 0.0,
                median: 0.0,
                p75: 0.0,
            };
        }
        let sum: u128 = counts.iter().map(|c| *c as u128).sum();
        OutDegreeStats {
            min: *counts.first().unwrap(),
            max: *counts.last().unwrap(),
            mean: (sum as f64) / (counts.len() as f64),
            p25: percentile(counts, 0.25),
            median: percentile(counts, 0.5),
            p75: percentile(counts, 0.75),
        }
    }
}

/// Compute the `p`-th percentile (`0 <= p <= 1`) of a non-empty,
/// ascending-sorted slice using linear interpolation between adjacent ranks
/// (matching numpy's default convention).
fn percentile(sorted: &[usize], p: f64) -> f64 {
    debug_assert!(!sorted.is_empty());
    debug_assert!((0.0..=1.0).contains(&p));
    let n = sorted.len();
    if n == 1 {
        return sorted[0] as f64;
    }
    let idx = p * (n - 1) as f64;
    let lower = idx.floor() as usize;
    let upper = idx.ceil() as usize;
    if lower == upper {
        sorted[lower] as f64
    } else {
        let frac = idx - lower as f64;
        sorted[lower] as f64 + frac * (sorted[upper] as f64 - sorted[lower] as f64)
    }
}

fn fmt_col_set(f: &mut Formatter<'_>, cols: &[usize]) -> std::fmt::Result {
    if cols.len() == 1 {
        write!(f, "{}", cols[0])
    } else {
        write!(f, "(")?;
        for (k, c) in cols.iter().enumerate() {
            if k > 0 {
                write!(f, " ")?;
            }
            write!(f, "{c}")?;
        }
        write!(f, ")")
    }
}

impl Display for OutDegreeStats {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(min {}) (p25 {:.4}) (median {:.4}) (mean {:.4}) (p75 {:.4}) (max {})",
            self.min, self.p25, self.median, self.mean, self.p75, self.max
        )
    }
}

impl TableStats {
    fn fmt_indented(&self, f: &mut Formatter<'_>, indent: usize) -> std::fmt::Result {
        let body = " ".repeat(indent + 2);
        let item = " ".repeat(indent + 4);
        write!(f, "({}", self.name)?;
        write!(f, "\n{body}(size {})", self.size)?;
        write!(f, "\n{body}(columns")?;
        for (idx, (ty, count)) in self
            .column_types
            .iter()
            .zip(self.distinct_counts.iter())
            .enumerate()
        {
            write!(f, "\n{item}({idx} {ty} {count})")?;
        }
        write!(f, ")")?;
        if !self.out_degrees.is_empty() {
            write!(f, "\n{body}(out-degrees")?;
            for entry in &self.out_degrees {
                write!(f, "\n{item}(")?;
                fmt_col_set(f, &entry.source)?;
                write!(f, " ")?;
                fmt_col_set(f, &entry.target)?;
                write!(f, " {})", entry.stats)?;
            }
            write!(f, ")")?;
        }
        write!(f, ")")
    }
}

impl Display for TableStats {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.fmt_indented(f, 0)
    }
}

impl Display for TableStatsOutput {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "(")?;
        for (i, table) in self.stats.iter().enumerate() {
            if i > 0 {
                write!(f, "\n ")?;
            }
            table.fmt_indented(f, 1)?;
        }
        writeln!(f, ")")
    }
}

/// Compute per-column statistics for a single function table identified by
/// its internal name.
fn compute_table_stats(egraph: &EGraph, func_name: &str) -> Result<TableStats, Error> {
    let func = egraph
        .get_function(func_name)
        .ok_or_else(|| TypeError::UnboundFunction(func_name.to_owned(), Span::Panic))?;
    let schema = func.schema();
    let mut column_types: Vec<String> = schema.input.iter().map(|s| s.name().to_owned()).collect();
    column_types.push(schema.output.name().to_owned());
    let n_cols = column_types.len();
    let n_inputs = schema.input.len();
    let output_col = n_cols - 1;
    let track_combined = n_inputs >= 2;

    let mut size: usize = 0;
    let mut distinct: Vec<HashSet<Value>> = (0..n_cols).map(|_| HashSet::default()).collect();
    let mut pair_maps: HashMap<(usize, usize), HashMap<Value, HashSet<Value>>> = HashMap::default();
    for i in 0..n_cols {
        for j in 0..n_cols {
            if i != j {
                pair_maps.insert((i, j), HashMap::default());
            }
        }
    }
    let mut output_to_inputs_map: HashMap<Value, HashSet<Vec<Value>>> = HashMap::default();

    egraph.function_for_each(func_name, |row: FunctionRow<'_>| {
        size += 1;
        let vals = row.vals;
        debug_assert_eq!(vals.len(), n_cols);
        for (i, v) in vals.iter().enumerate() {
            distinct[i].insert(*v);
        }
        for i in 0..n_cols {
            for j in 0..n_cols {
                if i != j {
                    pair_maps
                        .get_mut(&(i, j))
                        .unwrap()
                        .entry(vals[i])
                        .or_default()
                        .insert(vals[j]);
                }
            }
        }
        if track_combined {
            let inputs: Vec<Value> = vals[..n_inputs].to_vec();
            output_to_inputs_map
                .entry(vals[output_col])
                .or_default()
                .insert(inputs);
        }
    })?;

    let distinct_counts: Vec<usize> = distinct.iter().map(|s| s.len()).collect();

    let mut out_degrees: Vec<PairOutDegree> = Vec::new();
    for i in 0..n_cols {
        for j in 0..n_cols {
            if i == j {
                continue;
            }
            let inner = pair_maps.get(&(i, j)).unwrap();
            let mut counts: Vec<usize> = inner.values().map(|tgt_set| tgt_set.len()).collect();
            counts.sort_unstable();
            out_degrees.push(PairOutDegree {
                source: vec![i],
                target: vec![j],
                stats: OutDegreeStats::from_counts(&counts),
            });
        }
    }
    if track_combined {
        let mut counts: Vec<usize> = output_to_inputs_map
            .values()
            .map(|tgt_set| tgt_set.len())
            .collect();
        counts.sort_unstable();
        out_degrees.push(PairOutDegree {
            source: vec![output_col],
            target: (0..n_inputs).collect(),
            stats: OutDegreeStats::from_counts(&counts),
        });
    }

    Ok(TableStats {
        name: func_name.to_owned(),
        size,
        column_types,
        distinct_counts,
        out_degrees,
    })
}

/// Compute per-column statistics for the given function table, or for every
/// non-hidden, non-let-binding function when `sym` is `None`.
pub fn print_table_stats(egraph: &EGraph, sym: Option<&str>) -> Result<Vec<TableStats>, Error> {
    let mut results: Vec<TableStats> = Vec::new();
    if let Some(sym) = sym {
        let func = egraph
            .get_function(sym)
            .ok_or_else(|| TypeError::UnboundFunction(sym.to_owned(), Span::Panic))?;
        if func.is_let_binding() {
            return Err(Error::BackendError(format!(
                "print-table-stats: function `{sym}` is a let-binding and cannot be reported"
            )));
        }
        let mut stats = compute_table_stats(egraph, func.name())?;
        stats.name = func.name().to_owned();
        results.push(stats);
    } else {
        let mut names: Vec<(String, String)> = egraph
            .get_function_names()
            .into_iter()
            .filter_map(|name| {
                egraph
                    .get_function(&name)
                    .filter(|f| !f.is_let_binding())
                    .map(|_| (name.clone(), name))
            })
            .collect();
        names.sort_by(|a, b| a.0.cmp(&b.0));
        for (display_name, internal_name) in names {
            let mut stats = compute_table_stats(egraph, &internal_name)?;
            stats.name = display_name;
            results.push(stats);
        }
    }
    Ok(results)
}

impl UserDefinedCommand for PrintTableStatsCommand {
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        let name: Option<String> = match args {
            [] => None,
            [arg] => match arg {
                GenericExpr::Var(_, n) => Some(n.clone()),
                _ => {
                    return Err(Error::BackendError(format!(
                        "{}\nprint-table-stats expects an unquoted table name",
                        arg.span()
                    )));
                }
            },
            _ => {
                return Err(Error::BackendError(format!(
                    "{}\nusage: (print-table-stats <table name>?)",
                    args[1].span()
                )));
            }
        };
        let stats = print_table_stats(egraph, name.as_deref())?;
        Ok(vec![CommandOutput::UserDefined(Arc::new(
            TableStatsOutput { stats },
        ))])
    }
}
