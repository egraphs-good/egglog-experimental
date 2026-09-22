#![cfg(feature = "typed")]
#![expect(
    clippy::duplicate_mod,
    reason = "each standalone tutorial retains its own arithmetic theory module"
)]

// Import each standalone example as an ordinary module and run its exact main.
macro_rules! example_tests {
    ($(($name:ident, $path:literal)),+ $(,)?) => {$ (
        #[path = $path]
        mod $name;

        #[test]
        fn $name() {
            $name::main().expect(concat!("typed example failed: ", stringify!($name)));
        }
    )+};
}

example_tests!(
    (antiunify, "../examples/typed_antiunify.rs"),
    (array, "../examples/typed_array.rs"),
    (bdd, "../examples/typed_bdd.rs"),
    (bignum, "../examples/typed_bignum.rs"),
    (birewrite, "../examples/typed_birewrite.rs"),
    (combinators, "../examples/typed_combinators.rs"),
    (cyk, "../examples/typed_cyk.rs"),
    (datatypes, "../examples/typed_datatypes.rs"),
    (eqsat_basic, "../examples/typed_eqsat_basic.rs"),
    (eqsolve, "../examples/typed_eqsolve.rs"),
    (fibonacci, "../examples/typed_fibonacci.rs"),
    (fusion, "../examples/typed_fusion.rs"),
    (herbie, "../examples/typed_herbie.rs"),
    (herbie_tutorial, "../examples/typed_herbie_tutorial.rs"),
    (knapsack, "../examples/typed_knapsack.rs"),
    (lambda, "../examples/typed_lambda.rs"),
    (
        levenshtein_distance,
        "../examples/typed_levenshtein_distance.rs"
    ),
    (list, "../examples/typed_list.rs"),
    (math, "../examples/typed_math.rs"),
    (matrix, "../examples/typed_matrix.rs"),
    (multiset, "../examples/typed_multiset.rs"),
    (naturals, "../examples/typed_naturals.rs"),
    (path, "../examples/typed_path.rs"),
    (path_union, "../examples/typed_path_union.rs"),
    (pathproof, "../examples/typed_pathproof.rs"),
    (points_to, "../examples/typed_points_to.rs"),
    (prims, "../examples/typed_prims.rs"),
    (push_pop, "../examples/typed_push_pop.rs"),
    (resolution, "../examples/typed_resolution.rs"),
    (rw_analysis, "../examples/typed_rw_analysis.rs"),
    (schedule_demo, "../examples/typed_schedule_demo.rs"),
    (set, "../examples/typed_set.rs"),
    (subsume, "../examples/typed_subsume.rs"),
    (towers_of_hanoi, "../examples/typed_towers_of_hanoi.rs"),
    (typecheck, "../examples/typed_typecheck.rs"),
    (typeinfer, "../examples/typed_typeinfer.rs"),
    (
        unification_points_to,
        "../examples/typed_unification_points_to.rs"
    ),
    (unify, "../examples/typed_unify.rs"),
    (bool, "../examples/typed_bool.rs"),
    (ndarrays, "../examples/typed_ndarrays.rs"),
    (tutorial_basics, "../examples/typed_tutorial_basics.rs"),
    (tutorial_datalog, "../examples/typed_tutorial_datalog.rs"),
    (tutorial_analysis, "../examples/typed_tutorial_analysis.rs"),
    (
        tutorial_scheduling,
        "../examples/typed_tutorial_scheduling.rs"
    ),
    (
        tutorial_extraction,
        "../examples/typed_tutorial_extraction.rs"
    ),
    (freeze, "../examples/typed_freeze.rs"),
);
