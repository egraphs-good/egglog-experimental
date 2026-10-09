use egglog::CommandOutput;
use egglog_experimental::new_experimental_egraph;

fn extract(program: &str) -> String {
    let outputs = new_experimental_egraph()
        .parse_and_run_program(None, program)
        .unwrap();
    let [CommandOutput::ExtractBest(dag, _, term)] = outputs.as_slice() else {
        panic!("expected one extraction, got {outputs:?}");
    };
    dag.to_string(*term)
}

#[test]
fn satellite_can_be_the_extraction_root() {
    for count in [6, 7, 8] {
        let mut program = String::from(
            "(datatype E (A) (S i64 E) (Back E))\n\
             (let a (A))\n(set-effectful E a)\n",
        );
        for i in 0..count {
            program.push_str(&format!(
                "(let s{i} (S {i} a))\n(set-effectful E s{i})\n(union a (Back s{i}))\n"
            ));
        }
        let last = count - 1;
        program.push_str(&format!("(extract s{last} :extractor effsafe)\n"));
        assert_eq!(extract(&program), format!("(S {last} (A))"));
    }
}

#[test]
fn satellite_return_can_depend_on_another_satellite() {
    for count in [6, 7, 8] {
        let mut program = String::from(
            "(datatype E (A) (Read E) (Pair E E) (Back E E) (Return E E))\n\
             (let a (A))\n(set-effectful E a)\n",
        );
        for i in 0..count {
            program.push_str(&format!(
                "(constructor S{i} (E) E)\n(let s{i} (S{i} a))\n(set-effectful E s{i})\n"
            ));
        }
        let last = count - 1;
        // Each visit unlocks a read, but only the last satellite can return
        // to a before any other satellite has been visited.
        for i in 0..count {
            program.push_str(&format!(
                "(union a (Back s{i} (Pair (Read s{i}) (Read s{last}))))\n"
            ));
        }
        program.push_str(&format!(
            "(let root (Return a (Read s{last})))\n\
             (set-effectful E root)\n(extract root :extractor effsafe)\n"
        ));
        let read = format!("(Read (S{last} (A)))");
        assert_eq!(
            extract(&program),
            format!("(Return (Back (S{last} (A)) (Pair {read} {read})) {read})")
        );
    }
}
