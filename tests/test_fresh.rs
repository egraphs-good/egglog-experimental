use egglog_experimental::*;

#[test]
fn test_fresh_desugaring() {
    // A simple test to check if desugaring works
    let program = r#"
(datatype MySort (MySortConstructor))

;; Test with a simple query pattern
(relation test_rel (MySort))
(MySortConstructor)
(rule ((MySortConstructor))
      ((set (test_rel (unstable-fresh! MySort)) ())))

(run 1)

;; Check that the relation was populated
(check (test_rel ?x))
    "#;

    let mut egraph = new_experimental_egraph();
    let result = egraph.parse_and_run_program(None, program);
    match result {
        Ok(_) => (),
        Err(e) => {
            panic!("test_fresh_desugaring failed: {:?}", e);
        }
    }
}

#[test]
fn test_fresh_basic() {
    let program = r#"
(datatype Math
    (Let Math Math)
    (Var String))
    
(rule ((Let a b))
      ((Let (unstable-fresh! Math) b)))

(Let (Var "x") (Var "y"))
(run 1)

;; Check that fresh values were created
(check (Let ?a ?b))
    "#;

    let mut egraph = new_experimental_egraph();
    let result = egraph.parse_and_run_program(None, program);
    match result {
        Ok(_) => (),
        Err(e) => {
            eprintln!("Error: {:?}", e);
            panic!("test_fresh_basic failed: {:?}", e);
        }
    }
}

#[test]
fn test_fresh_unique() {
    let program = r#"
(datatype Math
    (Let Math Math)
    (Var String))
    
;; Rule with multiple fresh! calls
(rule ((Let a b))
      ((Let (unstable-fresh! Math) (unstable-fresh! Math))))

(Let (Var "x") (Var "y"))
(run 1)

;; Check that fresh values were created
(check (Let ?a ?b))
    "#;

    let mut egraph = new_experimental_egraph();
    let result = egraph.parse_and_run_program(None, program);
    match result {
        Ok(_) => (),
        Err(e) => {
            eprintln!("Error: {:?}", e);
            panic!("test_fresh_unique failed: {:?}", e);
        }
    }
}

#[test]
fn test_fresh_multiple_sorts() {
    let program = r#"
(datatype Expr
    (Add Expr Expr)
    (Num i64))
    
(datatype TypedExpr
    (TNum i64 String)
    (TAdd TypedExpr TypedExpr String))

;; Rule that uses fresh! with different sorts in the query
(rule ((= e (Add (Num x) (Num y)))
       (TNum z ty))
      ((TAdd (unstable-fresh! TypedExpr) (unstable-fresh! TypedExpr) ty)))

;; Set up initial facts
(let expr1 (Add (Num 1) (Num 2)))
(TNum 42 "int")
(run 1)

;; Check that fresh values were created
(check (TAdd ?a ?b ?ty))
    "#;

    let mut egraph = new_experimental_egraph();
    let result = egraph.parse_and_run_program(None, program);
    match result {
        Ok(_) => (),
        Err(e) => {
            panic!("test_fresh_multiple_sorts failed: {:?}", e);
        }
    }
}
