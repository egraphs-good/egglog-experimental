use std::collections::HashMap;

use egglog::{CommandOutput, SerializeConfig, UserDefinedCommand, ast::Expr};

/// A custom command that prints detailed egraph statistics.
pub struct EgraphDetailedStats;

#[derive(Debug, Clone)]
struct DetailedStatsOutput {
    min: usize,
    max: usize,
    median: f64,
    average: f64,
    num_eclasses: usize,
    total_nodes: usize,
}

impl std::fmt::Display for DetailedStatsOutput {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "((num-eclasses {}) (total-nodes {}) (min-eclass-size {}) (max-eclass-size {}) (median-eclass-size {:.2}) (average-eclass-size {:.2}))",
            self.num_eclasses, self.total_nodes, self.min, self.max, self.median, self.average
        )
    }
}

impl UserDefinedCommand for EgraphDetailedStats {
    fn update(
        &self,
        egraph: &mut egglog::EGraph,
        _args: &[Expr],
    ) -> Result<Option<CommandOutput>, egglog::Error> {
        // Use the serialize API to get eclass information
        // This iterates over all rows and groups them by eclass
        let serialized = egraph.serialize(SerializeConfig::default());

        // Count nodes per eclass from the serialized egraph
        let mut eclass_sizes: HashMap<String, usize> = HashMap::new();

        for node in serialized.egraph.nodes.values() {
            // Skip dummy nodes (used for omitted nodes)
            if node.op == "[...]" {
                continue;
            }
            *eclass_sizes.entry(node.eclass.to_string()).or_insert(0) += 1;
        }

        if eclass_sizes.is_empty() {
            let output = DetailedStatsOutput {
                min: 0,
                max: 0,
                median: 0.0,
                average: 0.0,
                num_eclasses: 0,
                total_nodes: 0,
            };
            log::info!("{}", output);
            return Ok(Some(CommandOutput::UserDefined(std::sync::Arc::new(output))));
        }

        let mut sizes: Vec<usize> = eclass_sizes.values().copied().collect();
        sizes.sort();

        let min = *sizes.first().unwrap();
        let max = *sizes.last().unwrap();
        let total_nodes: usize = sizes.iter().sum();
        let num_eclasses = sizes.len();
        let average = total_nodes as f64 / num_eclasses as f64;

        // Calculate median
        let median = if sizes.len() % 2 == 0 {
            let mid = sizes.len() / 2;
            (sizes[mid - 1] + sizes[mid]) as f64 / 2.0
        } else {
            sizes[sizes.len() / 2] as f64
        };

        let output = DetailedStatsOutput {
            min,
            max,
            median,
            average,
            num_eclasses,
            total_nodes,
        };

        log::info!("{}", output);
        Ok(Some(CommandOutput::UserDefined(std::sync::Arc::new(output))))
    }
}
