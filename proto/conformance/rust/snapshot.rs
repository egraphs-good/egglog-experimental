use egglog_experimental::typed::{Snapshot, builtins::I64};

use super::Math;

/// Validate the original typed freeze, including actual class identities.
pub fn assert_graph(snapshot: &Snapshot, sum: &Math) -> Result<(), Box<dyn std::error::Error>> {
    // Inspect the original returned typed view, preserving its class references.
    assert_eq!(snapshot.eclasses().len(), 3);
    let root = snapshot.class_of(&snapshot.lookup(sum)?)?;
    let producers: Vec<_> = root.nodes().collect();
    assert_eq!(producers.len(), 2);
    let num = producers.iter().find(|node| node.name() == "Num").unwrap();
    assert!(!num.is_subsumed());
    assert_eq!(
        i64::try_from(&num.args().next().unwrap().try_typed::<I64>()?)?,
        5
    );
    let add = producers.iter().find(|node| node.name() == "Add").unwrap();
    assert!(add.is_subsumed());
    let children: Vec<_> = add.eclass_children().collect();
    assert_eq!(children.len(), 2);
    assert_ne!(children[0], children[1]);
    for (child, expected) in children.into_iter().zip([2, 3]) {
        assert_ne!(child, root);
        let nodes: Vec<_> = child.nodes().collect();
        assert_eq!(nodes.len(), 1);
        assert_eq!(nodes[0].name(), "Num");
        assert!(!nodes[0].is_subsumed());
        assert_eq!(
            i64::try_from(&nodes[0].args().next().unwrap().try_typed::<I64>()?)?,
            expected
        );
    }
    let rows: Vec<_> = snapshot.rows().collect();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].name(), "value");
    assert_eq!(rows[0].args().next().unwrap().class(), Some(root));
    assert_eq!(
        i64::try_from(&rows[0].value().unwrap().try_typed::<I64>()?)?,
        5
    );
    Ok(())
}
