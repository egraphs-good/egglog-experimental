// Freeze once, then choose roots and traverse without consulting a live graph.
// Rust adds this traversal to Python's rootless owned-snapshot shape.
use egglog_experimental::typed::builtins as egg;
use egglog_experimental::typed::prelude::*;

#[sort]
pub struct Term;

#[declarations]
impl Term {
    pub fn leaf(value: egg::I64) -> Term;
    pub fn pair(left: Term, right: Term) -> Term;
}

#[declarations]
impl Term {
    #[function(no_merge)]
    pub fn weight(&self) -> egg::I64;
}

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let leaf = Term::leaf(7);
    let output = let_("output", Term::pair(&leaf, &leaf));
    let outside = let_("outside", Term::leaf(99));
    let saved_children = let_("children", egg::Vec::of([&leaf, &leaf]));
    let outputs = [&output, &outside, &output];
    let mut egraph = EGraph::default();
    egraph.register((&output, &outside, &saved_children, set(leaf.weight(), 7)))?;

    // There is no roots parameter: the unselected class is present as well.
    let frozen = egraph.freeze()?;
    let root: Term = frozen.lookup(&output)?;
    let other: Term = frozen.lookup(&outside)?;
    assert_ne!(root, other);
    let node = frozen
        .nodes(&root)?
        .next()
        .expect("the Pair constructor is present");
    assert!(!frozen.is_subsumed(&node)?);
    let (left, right) = get_args(&node, |left: &Term, right: &Term| Term::pair(left, right))?
        .expect("the selected node is Pair");
    assert_eq!(left, right);
    // A stored class has alternatives; it is not itself a selected constructor.
    assert!(
        get_args(&root, |left: &Term, right: &Term| {
            Term::pair(left, right)
        })?
        .is_none()
    );

    // The caller retains order and duplicates, and may choose another list later.
    let roots = outputs
        .into_iter()
        .map(|expr| frozen.lookup(expr))
        .collect::<Result<std::vec::Vec<_>, _>>()?;
    assert_eq!(roots[0], roots[2]);
    assert_eq!(roots.len(), 3);
    // Decode exact stored scalar fields explicitly, without tree extraction.
    let leaf_node = frozen.nodes(&left)?.next().unwrap();
    let (value,) = get_args(&leaf_node, |value: &egg::I64| Term::leaf(value))?
        .expect("the selected child node is Leaf");
    assert_eq!(i64::try_from(&value)?, 7);

    // Container decoding is shallow: its children still refer to this snapshot.
    let observed_children = frozen.lookup(&saved_children)?;
    let children = std::vec::Vec::<Term>::try_from(&observed_children)?;
    assert_eq!(children, [left.clone(), right]);

    // Function rows expose typed arguments and outputs, not constructor producers.
    let weights = frozen.table(|term: &Term| term.weight())?;
    let mut rows = weights.into_iter();
    let row = rows.next().expect("the weight table has one row");
    assert_eq!(row.args.0, left);
    assert_eq!(i64::try_from(&row.output)?, 7);
    assert!(!row.subsumed);
    assert!(rows.next().is_none());
    let leaves = frozen.table(|value: &egg::I64| Term::leaf(value))?;
    assert_eq!(leaves.into_iter().count(), 2);

    egraph.push()?;
    egraph.register(union(&output, leaf))?;
    let cyclic = egraph.freeze()?;
    let cyclic_root = cyclic.lookup(&output)?;
    assert_ne!(cyclic_root, root); // Identity includes the snapshot, not just an ID.
    let mut has_cycle = false;
    for node in cyclic.nodes(&cyclic_root)? {
        if let Some((left, right)) =
            get_args(&node, |left: &Term, right: &Term| Term::pair(left, right))?
        {
            has_cycle |= left == cyclic_root || right == cyclic_root;
        }
    }
    assert!(has_cycle);
    egraph.pop()?;
    drop(egraph);

    assert_eq!(frozen.lookup(&output)?, root);
    assert_eq!(frozen.nodes(&root)?.count(), 1);
    assert_eq!(cyclic.lookup(&output)?, cyclic_root);
    assert_eq!(frozen.nodes(&children[0])?.count(), 1);
    assert!(frozen.lookup(&Term::leaf(7)).is_err());
    assert!(
        frozen
            .lookup(&let_("not-installed", Term::leaf(8)))
            .is_err()
    );
    assert!(
        frozen
            .lookup(&let_("primitive", egg::I64::from(7)))
            .is_err()
    );
    assert!(frozen.nodes(&cyclic_root).is_err());
    Ok(())
}
