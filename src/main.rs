fn main() {
    let proof_mode = std::env::args().any(|arg| {
        matches!(
            arg.as_str(),
            "--proofs" | "--proof-testing" | "--term-encoding"
        )
    });
    let egraph = if proof_mode {
        egglog_experimental::new_experimental_egraph_for_proofs()
    } else {
        egglog_experimental::new_experimental_egraph()
    };
    egglog::cli(egraph)
}
