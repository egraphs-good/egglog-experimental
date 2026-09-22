use egglog_experimental::typed::{native, prelude::*};
fn main() {
    let core = egglog::EGraph::default();
    let _escaped = native::with_frozen(&core, &[], FreezeLimits::default(), |snapshot, _| {
        Ok(snapshot.eclasses().next().unwrap().value())
    });
}
