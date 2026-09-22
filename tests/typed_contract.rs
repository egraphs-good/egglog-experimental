#![cfg(feature = "typed")]

use egglog_experimental::typed::{builtins as egg, prelude::*};

#[sort]
pub struct Term;
#[declarations]
impl Term {
    pub fn Num(value: egg::I64) -> Self;
    pub fn Pair(left: Term, right: Term) -> Self;
}

#[relation]
pub fn Pending(key: egg::I64);
#[function(no_merge)]
pub fn Current(key: egg::I64) -> egg::I64;
#[function(no_merge)]
pub fn Observed(position: egg::I64, key: egg::I64) -> egg::I64;

#[constructor]
pub fn Empty() -> Term;

#[relation]
pub fn Ready();
#[function(no_merge)]
pub fn Latest() -> Term;

#[test]
fn decode_error_conversion_preserves_its_message_and_allocation() {
    let message = String::from("exact decode failure: \0 λ");
    let allocation = message.as_ptr();
    let error = TypedError::from(DecodeError(message));
    let TypedError::Decode(message) = error else {
        panic!("decode errors retain their category");
    };
    assert_eq!(message, "exact decode failure: \0 λ");
    assert_eq!(message.as_ptr(), allocation);
}

#[test]
fn row_mutations_accept_owned_and_borrowed_call_roots() -> Result<(), TypedError> {
    let relation = Pending(1);
    let function = Current(1);
    let constructor = Term::Num(1);
    for (owned, borrowed) in [
        (delete(relation.clone()), delete(&relation)),
        (subsume(relation.clone()), subsume(&relation)),
        (delete(function.clone()), delete(&function)),
        (subsume(function.clone()), subsume(&function)),
        (delete(constructor.clone()), delete(&constructor)),
        (subsume(constructor.clone()), subsume(&constructor)),
    ] {
        let (Action::Change(a, head_a, args_a), Action::Change(b, head_b, args_b)) =
            (owned, borrowed)
        else {
            panic!("direct calls produce row mutations");
        };
        assert_eq!(a, b);
        assert_eq!(head_a, head_b);
        assert_eq!(args_a, args_b);
    }
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register((&relation, Pending(2), set(&function, 7)))?;
    graph.register((delete(&relation), delete(Pending(2)), delete(&function)))?;
    assert!(!graph.check(&relation)?);
    assert!(!graph.check(Pending(2))?);
    assert!(!graph.check(&function)?);
    Ok(())
}

#[test]
fn registration_and_rule_actions_share_recursive_borrowed_inputs() -> Result<(), TypedError> {
    use egglog_experimental::typed::{Direct, IntoActions};
    // This collection cannot be cloned. Only the individual borrowed action is
    // copied into the operation, so adapting a collection never requires Clone.
    struct NotClone(Action);
    impl IntoActions<Direct> for &NotClone {
        fn into_actions(self) -> Vec<Action> {
            vec![self.0.clone()]
        }
    }
    let mut graph = EGraph::new(EGraphOptions::default());
    let first = set(Current(0), 1);
    let last = delete(Current(0));
    let pending = Pending(1);
    let actions = vec![&first];
    let relations = vec![&pending];
    let no_clone = vec![NotClone(set(Current(1), 3))];
    let leaves = (&last, &pending);
    let nested = (&actions, (&relations, (&no_clone, &leaves)));
    graph.register(&nested)?;
    assert!(!graph.check(Current(0,))?);
    assert!(graph.check(eq(Current(1,), 3))?);
    graph.run(ruleset(rule((), &nested)))?;
    assert!(graph.check((Pending(1,), eq(Current(1,), 3)))?);
    let thirty_two = (
        &pending, &pending, &pending, &pending, &pending, &pending, &pending, &pending, &pending,
        &pending, &pending, &pending, &pending, &pending, &pending, &pending, &pending, &pending,
        &pending, &pending, &pending, &pending, &pending, &pending, &pending, &pending, &pending,
        &pending, &pending, &pending, &pending, &pending,
    );
    graph.register(&thirty_two)?;
    graph.run(ruleset(rule((), &thirty_two)))?;
    Ok(())
}

mod labels_a {
    use super::*;
    #[constructor(name = "labels::Leaf", cost = 2)]
    pub fn Leaf(value: egg::I64) -> Term;
    #[relation(name = "labels::Seen")]
    pub fn Seen(value: Term);
    #[function(name = "labels::Value", no_merge)]
    pub fn Value(key: egg::I64) -> egg::I64;
}
mod labels_b {
    use super::*;
    #[constructor(name = "labels::Leaf", cost = 2)]
    pub fn Leaf(integer: egg::I64) -> Term;
    #[relation(name = "labels::Seen")]
    pub fn Seen(term: Term);
    #[function(name = "labels::Value", no_merge)]
    pub fn Value(index: egg::I64) -> egg::I64;
}
mod labels_conflict {
    use super::*;
    #[constructor(name = "labels::Leaf", cost = 3)]
    pub fn Leaf(integer: egg::I64) -> Term;
}

#[test]
fn argument_labels_are_authoring_only_across_callable_kinds() -> Result<(), TypedError> {
    let a = labels_a::Leaf(7);
    let b = labels_b::Leaf(7);
    assert_eq!(a, b);
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register((
        &a,
        &b,
        labels_a::Seen(&a),
        labels_b::Seen(&b),
        set(labels_a::Value(7), 11),
        set(labels_b::Value(7), 11),
    ))?;
    let frozen = graph.freeze()?;
    for name in ["labels::Leaf", "labels::Seen", "labels::Value"] {
        let tables: Vec<_> = frozen.tables().filter(|t| t.name() == name).collect();
        assert_eq!(tables.len(), 1);
        assert_eq!(tables[0].rows().len(), 1);
    }
    let before = graph.num_tuples()?;
    assert!(matches!(
        graph.register(labels_conflict::Leaf(8,)),
        Err(TypedError::Invalid(_))
    ));
    assert_eq!(graph.num_tuples()?, before);
    Ok(())
}

#[test]
fn statistics_are_immutable_cumulative_observations() -> Result<(), TypedError> {
    let empty = EGraph::new(EGraphOptions {
        lowering_limits: LoweringLimits {
            max_commands: 0,
            ..LoweringLimits::default()
        },
        ..EGraphOptions::default()
    });
    assert!(empty.stats()?.iterations.is_empty());

    let mut graph = EGraph::new(EGraphOptions::default());
    let group = ruleset(|key: &egg::I64| rule(Pending(key), set(Current(key), key)));
    graph.register(Pending(1))?;
    let run_one = graph.run(&group)?;
    let borrowed: &EGraph = &graph;
    let first = borrowed.stats()?;
    assert_eq!(first.num_matches_per_rule, run_one.num_matches_per_rule);
    assert!(!first.iterations.is_empty());
    graph.register(Pending(2))?;
    let run_two = graph.run(&group)?;
    let second = graph.stats()?;
    assert_eq!(
        second.iterations.len(),
        first.iterations.len() + run_two.iterations.len()
    );
    for (name, count) in &second.num_matches_per_rule {
        assert_eq!(
            *count,
            first.num_matches_per_rule.get(name).copied().unwrap_or(0)
                + run_two.num_matches_per_rule.get(name).copied().unwrap_or(0)
        );
    }
    let unchanged = graph.stats()?;
    assert_eq!(second.num_matches_per_rule, unchanged.num_matches_per_rule);
    assert_eq!(
        second.search_and_apply_time_per_rule,
        unchanged.search_and_apply_time_per_rule
    );
    assert!(std::sync::Arc::ptr_eq(
        &second.iterations[0],
        &unchanged.iterations[0]
    ));
    graph.push()?;
    assert!(graph.register(panic("statistics health check")).is_err());
    assert!(matches!(graph.stats(), Err(TypedError::NeedsRestore)));
    graph.pop()?;
    assert_eq!(
        graph.stats()?.num_matches_per_rule,
        second.num_matches_per_rule
    );
    Ok(())
}
#[sort]
pub struct Flag;
#[declarations]
impl Flag {
    pub fn On() -> Self;
}

#[test]
fn partial_calls_and_projection_have_exact_owned_sorts() -> Result<(), TypedError> {
    let left = Term::Num(7);
    let right = var::<Term>("right");
    let partial = Term::Pair(&left, &right);
    let fields: (Term, Term) = get_args(&partial, |a: &Term, b: &Term| Term::Pair(a, b))?.unwrap();
    assert_eq!(fields.0, left);
    assert_eq!(fields.1, right);
    let numeric = Observed(7, var::<egg::I64>("key"));

    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register((
        Term::Pair(&left, &left),
        Pending(7),
        set(Current(7), 9),
        set(Observed(7, 3), 11),
        Empty(),
        Ready(),
        set(Latest(), &left),
    ))?;
    assert!(graph.check((
        &partial,
        Pending(var::<egg::I64>("pending")),
        eq(Current(var::<egg::I64>("current")), 9),
        eq(&numeric, 11),
        Ready(),
        eq(Latest(), &left),
    ))?);
    assert_eq!(get_args(&Empty(), Empty)?, Some(()));
    assert_eq!(get_args(&Flag::On(), Flag::On)?, Some(()));
    Ok(())
}

#[test]
fn borrowed_inputs_keep_owned_expression_and_projection_types() -> Result<(), TypedError> {
    fn reflexive<S: EgglogValue>(value: &S) -> Fact {
        eq(value, value)
    }

    let mut graph = EGraph::new(EGraphOptions::default());
    let value = egg::I64::from(7);
    let leaf = Term::Num(&value);
    assert_eq!(leaf, Term::Num(7));
    let root = Term::Pair(&leaf, leaf.clone());
    assert_eq!(root, Term::Pair(&leaf, &leaf));
    let fields: (Term, Term) = get_args(&root, |a: &Term, b: &Term| Term::Pair(a, b))?.unwrap();
    let _: Term = fields.0;
    let _: Term = fields.1;
    let saved: Term = let_("borrowed-root", &root);
    graph.register((
        &saved,
        Pending(&value),
        set(Current(&value), &value),
        Empty(),
    ))?;
    assert!(graph.check((
        eq(Current(7), &value),
        eq(&value, value.clone()),
        eq(value.clone(), &value),
        reflexive(&leaf),
        ne(&value, 8),
    ))?);
    graph.register((union(&leaf, &leaf), union(leaf.clone(), &leaf)))?;
    let group = ruleset(|term: &Term, key: &egg::I64| {
        let query = eq(term, Term::Num(key));
        let row = Pending(key);
        let action = set(Current(key), key);
        let facts = [query.clone()];
        let actions = vec![action.clone()];
        (
            rule((&query, &row), (term, &action, &row)),
            rule(&query, &action),
            rewrite(Term::Pair(term, term), term),
            rewrite(Term::Pair(term, term), Term::Pair(term, Term::Num(0))),
            rewrite(Term::Pair(term, Term::Num(0)), Term::Pair(term, term)),
            rule(&facts, &actions),
        )
    });
    assert_eq!(ruleset((&group, &group)).len(), group.len());
    let closed = rule((), ());
    assert_eq!(ruleset((&closed, &closed)).len(), 1);
    let facts = vec![eq(&value, 7)];
    assert!(graph.check(&facts)?);
    graph.run(&group)?;
    assert!(graph.check(eq(Current(7,), 7))?);

    // Input borrowing never creates a borrowed expression graph. The cloned
    // handle remains usable after the original handle is gone.
    let shared = Term::from(&root);
    drop(root);
    assert_eq!(
        get_args(&shared, |a: &Term, b: &Term| Term::Pair(a, b))?
            .unwrap()
            .0,
        leaf
    );
    Ok(())
}

#[test]
fn extraction_methods_preserve_cost_order_and_shared_reconstruction() -> Result<(), TypedError> {
    let leaf = let_("extraction-leaf", Term::Num(7));
    let pair = let_("extraction-pair", Term::Pair(leaf.clone(), leaf.clone()));
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register((&leaf, &pair))?;

    let best: Term = graph.extract(&pair)?;
    let (with_cost, cost): (Term, egglog_experimental::typed::DefaultCost) =
        graph.extract_with_cost(&pair)?;
    assert_eq!(best, with_cost);
    // Tree cost charges both occurrences of the shared Num and its literal.
    assert_eq!(cost, 5);
    let roots = [pair.clone(), leaf.clone(), pair];
    let forest: Vec<Term> = graph.extract_many(&roots)?;
    assert_eq!(forest, [best.clone(), graph.extract(&leaf)?, best]);
    let fields = get_args(&forest[0], |a: &Term, b: &Term| Term::Pair(a, b))?.unwrap();
    assert_eq!(fields.0, forest[1]);
    assert_eq!(fields.1, forest[1]);
    assert!(graph.extract_many::<Term>(&[])?.is_empty());
    let borrowed = [&roots[0], &roots[1], &roots[0]];
    assert_eq!(graph.extract_many(&borrowed)?, forest);
    assert_eq!(graph.extract_many(borrowed.as_slice())?, forest);
    Ok(())
}

mod first {
    use super::*;
    #[sort(name = "collision::Term")]
    pub struct Value;
    #[constructor(name = "collision::Leaf")]
    pub fn Leaf(value: egg::I64) -> Value;
}
mod second {
    use super::*;
    #[sort(name = "collision::Term")]
    pub struct Value;
    #[constructor(name = "collision::Leaf")]
    pub fn Leaf(value: egg::String) -> Value;
}

fn self_merge(old: egg::I64, new: egg::I64) -> egg::I64 {
    SelfMerge(old) + new
}
#[function(merge = self_merge)]
pub fn SelfMerge(key: egg::I64) -> egg::I64;

fn cycle_a(old: egg::I64, new: egg::I64) -> egg::I64 {
    CycleB(old) + new
}
fn cycle_b(old: egg::I64, new: egg::I64) -> egg::I64 {
    CycleA(old) + new
}
#[function(merge = cycle_a)]
pub fn CycleA(key: egg::I64) -> egg::I64;
#[function(merge = cycle_b)]
pub fn CycleB(key: egg::I64) -> egg::I64;

fn expanding_merge(mut old: egg::I64, new: egg::I64) -> egg::I64 {
    for _ in 0..20 {
        old = old.clone() + old;
    }
    old + new
}
#[function(merge = expanding_merge)]
pub fn Expanded(key: egg::I64) -> egg::I64;

#[test]
fn incompatible_reachable_definitions_reject_complete_batch_before_writes() -> Result<(), TypedError>
{
    let mut graph = EGraph::new(EGraphOptions::default());
    let result = graph.register((
        Term::Num(7),
        first::Leaf(1),
        second::Leaf("different signature"),
    ));
    assert!(matches!(result, Err(TypedError::Invalid(_))));
    assert_eq!(graph.num_tuples()?, 0);
    assert!(graph.check(())?);
    graph.register(first::Leaf(2))?;
    Ok(())
}

#[test]
fn public_native_names_are_verbatim_and_do_not_capture_internal_globals() -> Result<(), TypedError>
{
    #[sort(name = "Σ sort / (exact)\n")]
    struct Named;
    #[constructor(name = "λ call / (exact)\n")]
    fn named(value: egg::I64) -> Named;
    #[constructor(name = "@$typed_global_")]
    fn internal_spelling(value: egg::I64) -> Named;
    #[constructor(name = "%typed_v_0")]
    fn former_binder_spelling(value: egg::I64) -> Named;
    #[constructor(name = "@$typed_v_")]
    fn binder_spelling(value: egg::I64) -> Named;

    let root = let_("root", named(7));
    let internal = internal_spelling(9);
    let mut graph = EGraph::default();
    graph.register((&root, &internal))?;
    graph.run(ruleset(|value: &egg::I64| {
        rule(
            eq(value, 11),
            (former_binder_spelling(value), binder_spelling(value)),
        )
    }))?;
    assert!(graph.check((former_binder_spelling(11), binder_spelling(11)))?);
    assert_eq!(graph.extract(&root)?, named(7));
    assert!(graph.check(eq(&internal, internal_spelling(9)))?);
    graph.push()?;
    graph.register(named(8))?;
    graph.pop()?;
    assert!(graph.check(eq(&root, named(7)))?);
    let raw = graph.into_raw();
    assert!(raw.get_sort_by_name("Σ sort / (exact)\n").is_some());
    for name in [
        "λ call / (exact)\n",
        "@$typed_global_",
        "%typed_v_0",
        "@$typed_v_",
    ] {
        let signature = raw.get_function(name).unwrap().func_type();
        assert_eq!(signature.name, name);
        assert_eq!(signature.output.name(), "Σ sort / (exact)\n");
        assert_eq!(signature.input[0].name(), "i64");
    }
    Ok(())
}

#[test]
fn pending_sort_callable_and_container_name_conflicts_are_atomic() -> Result<(), TypedError> {
    #[sort(name = "shared-name")]
    struct SharedName;
    #[constructor]
    fn shared_sort() -> SharedName;
    #[constructor(name = "shared-name")]
    fn shared_call() -> Term;
    #[sort(name = "Vec<i64>")]
    struct WrongVec;
    #[constructor]
    fn wrong_vec() -> WrongVec;

    for pair in [
        [Action::from(shared_sort()), Action::from(shared_call())],
        [Action::from(shared_call()), Action::from(shared_sort())],
        [
            Action::from(wrong_vec()),
            Action::from(egg::Vec::<egg::I64>::empty()),
        ],
        [
            Action::from(egg::Vec::<egg::I64>::empty()),
            Action::from(wrong_vec()),
        ],
    ] {
        let mut graph = EGraph::default();
        assert!(matches!(graph.register(pair), Err(TypedError::Invalid(_))));
        assert_eq!(graph.num_tuples()?, 0);
        assert!(graph.check(())?);
    }
    Ok(())
}

#[test]
fn merge_self_and_transitive_cycles_are_preflight_errors() -> Result<(), TypedError> {
    let mut graph = EGraph::new(EGraphOptions::default());
    for action in [set(SelfMerge(1), 2), set(CycleA(1), 2)] {
        assert!(matches!(
            graph.register(action),
            Err(TypedError::Invalid(_))
        ));
        assert_eq!(graph.num_tuples()?, 0);
        assert!(graph.check(())?);
    }
    Ok(())
}

#[test]
fn shared_merge_expansion_is_bounded_before_execution() -> Result<(), TypedError> {
    let mut options = EGraphOptions::default();
    options.lowering_limits.max_expanded_nodes = 64;
    let mut graph = EGraph::new(options);
    assert!(matches!(
        graph.register((Term::Num(1,), set(Expanded(0,), 1))),
        Err(TypedError::LoweringLimit(_))
    ));
    assert_eq!(graph.num_tuples()?, 0);
    assert!(graph.check(())?);
    Ok(())
}

#[test]
fn shared_rhs_reads_preserve_native_rule_visibility() -> Result<(), TypedError> {
    // Deliberate legacy differential oracle, never an execution fallback. Native
    // rule visibility differs from separate top-level action commands: both
    // reads see the old row even though the eventual Current value becomes 20.
    let mut native = egglog_experimental::new_experimental_egraph();
    native
        .parse_and_run_program(
            None,
            r#"
        (relation Pending (i64))
        (function Current (i64) i64 :no-merge)
        (function Observed (i64 i64) i64 :no-merge)
        (Pending 1)
        (set (Current 1) 10)
        (rule ((Pending key))
              ((set (Observed 0 key) (Current key))
               (delete (Current key))
               (set (Current key) 20)
               (set (Observed 1 key) (Current key))) :naive)
        (run 1)
        (check (= (Observed 0 1) 10) (= (Observed 1 1) 10) (= (Current 1) 20))
    "#,
        )
        .unwrap();
    let mut graph = EGraph::new(EGraphOptions::default());
    graph.register((Pending(1), set(Current(1), 10)))?;
    let group = ruleset(|key: &egg::I64| {
        let value = Current(key.clone());
        rule(
            Pending(key.clone()),
            (
                set(Observed(0, key.clone()), value.clone()),
                delete(Current(key.clone())),
                set(Current(key.clone()), 20),
                set(Observed(1, key), value),
            ),
        )
        .naive()
    });
    graph.run(&group)?;
    assert!(graph.check((
        eq(Observed(0, 1), 10),
        eq(Observed(1, 1), 10),
        eq(Current(1,), 20),
    ))?);
    Ok(())
}

#[test]
fn clone_identity_labels_and_scope_installation_are_distinct() -> Result<(), TypedError> {
    let group = ruleset(|value: &Term| {
        let step = rule(eq(value.clone(), Term::Num(1)), union(value, Term::Num(2)));
        assert_eq!(
            ruleset((step.clone(), step.clone().label("diagnostic"))).len(),
            1
        );
        assert_eq!(ruleset((step.clone(), step.clone().naive())).len(), 2);
        step
    });
    let mut graph = EGraph::new(EGraphOptions::default());
    let root = let_("scope-root", Term::Num(1));
    graph.register(&root)?;
    for _ in 0..2 {
        graph.push()?;
        graph.run(&group)?;
        assert!(graph.check(eq(root.clone(), Term::Num(2,)))?);
        graph.pop()?;
        assert!(!graph.check(eq(root.clone(), Term::Num(2,)))?);
    }
    Ok(())
}

#[test]
fn borrowed_registration_and_maximum_stable_adapters_work() -> Result<(), TypedError> {
    let mut graph = EGraph::new(EGraphOptions::default());
    let actions = vec![set(Current(1), 1), set(Current(2), 2)];
    let rows = [Pending(1), Pending(2)];
    let terms = [Term::Num(1), Term::Num(2)];
    let borrowed_terms = [&terms[0], &terms[1]];
    let borrowed_vector = borrowed_terms.to_vec();
    let success: () = graph.register((
        (),
        &actions,
        actions.as_slice(),
        &rows,
        rows.as_slice(),
        &terms,
        borrowed_terms,
        &borrowed_terms,
        borrowed_terms.as_slice(),
        &borrowed_vector,
        borrowed_vector.as_slice(),
        borrowed_vector.clone(),
        [(borrowed_terms.as_slice(), &rows[0])],
    ))?;
    let () = success;
    graph.register((
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
    ))?;
    let max_arity = ruleset(
        |a0: &egg::I64,
         a1: &egg::I64,
         a2: &egg::I64,
         a3: &egg::I64,
         a4: &egg::I64,
         a5: &egg::I64,
         a6: &egg::I64,
         a7: &egg::I64,
         a8: &egg::I64,
         a9: &egg::I64,
         a10: &egg::I64,
         a11: &egg::I64,
         a12: &egg::I64,
         a13: &egg::I64,
         a14: &egg::I64,
         a15: &egg::I64,
         a16: &egg::I64,
         a17: &egg::I64,
         a18: &egg::I64,
         a19: &egg::I64,
         a20: &egg::I64,
         a21: &egg::I64,
         a22: &egg::I64,
         a23: &egg::I64,
         a24: &egg::I64,
         a25: &egg::I64,
         a26: &egg::I64,
         a27: &egg::I64,
         a28: &egg::I64,
         a29: &egg::I64,
         a30: &egg::I64,
         a31: &egg::I64| {
            let facts: Vec<_> = [
                a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
                a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31,
            ]
            .into_iter()
            .enumerate()
            .map(|(i, value)| eq(value, i as i64))
            .collect();
            rule(facts, ())
        },
    );
    graph.run(ruleset((rule((), ()), max_arity)))?;
    assert!(graph.check((Pending(1,), Pending(2,)))?);
    Ok(())
}

#[test]
fn independent_hundred_thousand_node_spines_compare_hash_and_drop_iteratively() {
    use std::hash::{Hash, Hasher};
    let leaf = Term::Num(0);
    let mut left = leaf.clone();
    let mut right = Term::Num(0);
    for _ in 0..100_000 {
        left = Term::Pair(left, leaf.clone());
        right = Term::Pair(right, leaf.clone());
    }
    // The two spines are independently allocated, not two clones of one root.
    assert_eq!(left, right);
    let mut left_hash = std::collections::hash_map::DefaultHasher::new();
    let mut right_hash = std::collections::hash_map::DefaultHasher::new();
    left.hash(&mut left_hash);
    right.hash(&mut right_hash);
    assert_eq!(left_hash.finish(), right_hash.finish());
    assert!(format!("{left:?}").len() < 20_000);
    drop(left);
    std::thread::spawn(move || drop(right)).join().unwrap();
}

#[test]
fn wide_authoring_diagnostics_are_bounded_too() {
    let wide = egg::Vec::<egg::I64>::of(vec![egg::I64::from(0); 100_000]);
    assert!(format!("{wide:?}").len() < 20_000);
}
