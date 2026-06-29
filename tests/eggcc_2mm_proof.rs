use std::path::Path;
use std::process::Command;

fn run_fixture_with_proofs(fixture_name: &str) -> String {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let fixture = manifest_dir.join("tests/fixtures").join(fixture_name);
    let program = std::fs::read_to_string(&fixture).expect("read eggcc 2mm fixture");

    let output = Command::new(env!("CARGO_BIN_EXE_egglog-experimental"))
        .arg("--proofs")
        .arg(&fixture)
        .output()
        .expect("run egglog-experimental --proofs on eggcc 2mm fixture");

    assert!(
        output.status.success(),
        "egglog-experimental --proofs failed with status {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    program
}

#[test]
fn eggcc_2mm_container_helpers_run_with_proofs() {
    let program = run_fixture_with_proofs("eggcc-2mm-container-helpers.egg");

    for required in [
        "pair-min-by-second-i64",
        "maybe-either-i64-bool-min",
        "maybe-either-i64-bool-max",
        "maybe-some",
        "either-left",
        "either-right",
        "either-unwrap-left",
        "either-unwrap-right",
    ] {
        assert!(
            program.contains(required),
            "fixture should exercise {required}"
        );
    }
}

#[test]
#[ignore = "full eggcc proof canary is too slow for default debug-profile CI"]
fn eggcc_2mm_full_export_runs_with_proofs() {
    let program = run_fixture_with_proofs("eggcc-2mm-pass1-merge-old.egg");

    assert!(
        !program.contains(":no-merge"),
        "full eggcc export should not use :no-merge"
    );
    assert!(
        program.contains(":merge old"),
        "full eggcc export should pin former no-merge functions to :merge old"
    );
}
