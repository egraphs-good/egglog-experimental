use egglog_experimental::typed::{EGraph, binding};
use prost::Message;

#[path = "constant_folding.rs"]
#[expect(
    dead_code,
    reason = "The standalone main is not the capture entry point."
)]
mod authoring;
mod snapshot;

use authoring::Math;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let output = std::env::args()
        .nth(1)
        .ok_or("expected output history.pb path")?;
    let mut graph = EGraph::with_recording(true)?;
    authoring::run_example(&mut graph)?;
    let frozen = graph.freeze()?;
    snapshot::assert_graph(&frozen, &binding::<Math>("sum"))?;
    std::fs::write(output, graph.history()?.encode_to_vec())?;
    Ok(())
}
