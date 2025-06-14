#[test]
fn test_extract() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    let result = egraph
        .parse_and_run_program(
            None,
            "
        (with-dynamic-cost
            (datatype E (Add E E) (Sub E E :cost 200) (Num i64))
        )

        (union (Num 2) (Add (Num 1) (Num 1)))
        (set-cost (Num 2) 1000)
        (set-cost (Num 1) 100)
        (extract (Num 2))

        (push)
        (set-cost (Add (Num 1) (Num 1)) 801)
        (extract (Num 2))
        (pop)

        (push)
        (set-cost (Add (Num 1) (Num 1)) 799)
        (extract (Num 2))
        (pop)

        ;; 200 + 1 + 1 > 1 + 100 + 100
        (union (Num 2) (Sub (Num 5) (Num 3)))
        (extract (Num 2))
        (set-cost (Sub (Num 5) (Num 3)) 198)
        ;; 198 + 1 + 1 < 1 + 100 + 100
        (extract (Num 2))",
        )
        .unwrap();

    assert_eq!(result.len(), 5);
    assert_eq!(result[0], "(Add (Num 1) (Num 1))");
    assert_eq!(result[1], "(Num 2)");
    assert_eq!(result[2], "(Add (Num 1) (Num 1))");
    assert_eq!(result[3], "(Add (Num 1) (Num 1))");
    assert_eq!(result[4], "(Sub (Num 5) (Num 3))");
}

#[test]
fn test_extract_set_cost_multiple_times_should_fail() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            "(with-dynamic-cost
                (datatype E (Add E E) (Sub E E :cost 200) (Num i64))
            )
            (set-cost (Num 2) 1000)",
        )
        .unwrap();

    egraph
        .parse_and_run_program(None, "(set-cost (Num 2) 1000)")
        .unwrap();

    let result = egraph.parse_and_run_program(None, "(set-cost (Num 2) 1)");
    assert!(result.is_err());
}

#[test]
fn test_extract_set_cost_decls() {
    let mut egraph = egglog_experimental::new_experimental_egraph();

    egraph
        .parse_and_run_program(
            None,
            "(with-dynamic-cost
                (datatype E (Add E E) (Sub E E :cost 200) (Num i64))
                (constructor Mul (E E) E :cost 100)
                (datatype* 
                  (E2 (Add2 E2 E2) (Sub2 E2 E2 :cost 200) (List VecE2) (Num2 i64))
                  (sort VecE2 (Vec E2))
                )
                (constructor Mul2 (E2 E2) E2)
            )
            (set-cost (Num 2) 1000)
            (set-cost (Num2 2) 1000)
            (set-cost (Mul (Num 2) (Num 2)) 1000)
            (set-cost (Sub2 (Num2 2) (Num2 2)) 1000)",
        )
        .unwrap();
}
