//! Existing native proof output <-> structurally validated generated messages.
//! This is not a proof checker. Native proof validity depends on its program and
//! trusted host validators, which are not serialized by ProofResult.
use super::pb;
use egglog::{
    Term,
    proof::{Justification, ProofId, ProofStore},
};
#[cfg(test)]
use prost::Message;
use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

/// Allocate one wire ID per native identity, before visiting any outgoing edge.
/// The append-only queue gives deterministic traversal and preserves sharing.
struct Ids<T> {
    ids: HashMap<T, u32>,
    queue: Vec<T>,
}

impl<T: Copy + Eq + Hash> Ids<T> {
    fn intern(&mut self, native: T) -> Result<u32, String> {
        if let Some(id) = self.ids.get(&native) {
            return Ok(*id);
        }
        let id = u32::try_from(self.queue.len()).map_err(|_| "proof arena exceeds u32 indices")?;
        self.ids.insert(native, id);
        self.queue.push(native);
        Ok(id)
    }
}

/// Export an existing returned native root. Neither the EGraph nor a renderer
/// is used. The caller must supply a root belonging to this native ProofStore.
pub fn export(store: &ProofStore, root: ProofId) -> Result<pb::ProofResult, String> {
    use pb::{proof_step::Justification as W, proof_term::Kind as T};
    let mut proof_ids = Ids {
        ids: HashMap::new(),
        queue: Vec::new(),
    };
    let mut term_ids = Ids {
        ids: HashMap::new(),
        queue: Vec::new(),
    };
    let mut result = pb::ProofResult {
        root: Some(proof_ids.intern(root)?),
        ..Default::default()
    };
    let mut cursor = 0;
    while cursor < proof_ids.queue.len() {
        let proof = store.get(proof_ids.queue[cursor]);
        let lhs = Some(term_ids.intern(proof.lhs())?);
        let rhs = Some(term_ids.intern(proof.rhs())?);
        let justification = match proof.justification() {
            Justification::Fiat => W::Fiat(pb::Unit {}),
            Justification::Eval => W::Eval(pb::Unit {}),
            Justification::Rule {
                name,
                premise_proofs,
                substitution,
            } => {
                let premise_proofs = premise_proofs
                    .iter()
                    .map(|id| proof_ids.intern(*id))
                    .collect::<Result<_, _>>()?;
                let mut bindings: Vec<_> = substitution.iter().collect();
                bindings.sort_unstable_by(|(a, _), (b, _)| a.cmp(b));
                let substitution = bindings
                    .into_iter()
                    .map(|(name, id)| {
                        Ok(pb::ProofBinding {
                            name: name.clone(),
                            term: Some(term_ids.intern(*id)?),
                        })
                    })
                    .collect::<Result<_, String>>()?;
                W::Rule(pb::ProofRule {
                    name: name.clone(),
                    premise_proofs,
                    substitution,
                })
            }
            Justification::MergeFn {
                function,
                old_proof,
                new_proof,
            } => W::MergeFn(pb::ProofMergeFn {
                function: function.clone(),
                old_proof: Some(proof_ids.intern(*old_proof)?),
                new_proof: Some(proof_ids.intern(*new_proof)?),
            }),
            Justification::Trans(left, right) => W::Trans(pb::ProofTrans {
                left: Some(proof_ids.intern(*left)?),
                right: Some(proof_ids.intern(*right)?),
            }),
            Justification::Sym(id) => W::Sym(proof_ids.intern(*id)?),
            Justification::Congr {
                proof,
                child_index,
                child_proof,
            } => W::Congr(pb::ProofCongr {
                proof: Some(proof_ids.intern(*proof)?),
                child_index: Some(
                    u32::try_from(*child_index)
                        .map_err(|_| "congruence child index exceeds u32")?,
                ),
                child_proof: Some(proof_ids.intern(*child_proof)?),
            }),
            Justification::ContainerNormalize { proof } => {
                W::ContainerNormalize(proof_ids.intern(*proof)?)
            }
        };
        result.proofs.push(pb::ProofStep {
            lhs,
            rhs,
            justification: Some(justification),
        });
        cursor += 1;
    }
    cursor = 0;
    while cursor < term_ids.queue.len() {
        let kind = match store.term_dag().get(term_ids.queue[cursor]) {
            Term::Lit(literal) => {
                let (_, scalar) = super::value::Scalar::from_literal(literal)?;
                T::PrimitiveValue(scalar.encode()?)
            }
            Term::Var(name) => T::Var(name.clone()),
            Term::App(head, children) => T::App(pb::ProofApp {
                head: head.clone(),
                children: children
                    .iter()
                    .map(|id| term_ids.intern(*id))
                    .collect::<Result<_, _>>()?,
            }),
        };
        result.terms.push(pb::ProofTerm { kind: Some(kind) });
        cursor += 1;
    }
    validate(&result)?;
    Ok(result)
}

/// Decode actual protobuf bytes and reject unsafe/incomplete graph structure.
/// A successful return is inert proof data, NOT a checked native certificate.
#[cfg(test)]
fn decode(bytes: &[u8]) -> Result<pb::ProofResult, String> {
    let result = pb::ProofResult::decode(bytes).map_err(|e| format!("protobuf decode: {e}"))?;
    validate(&result)?;
    Ok(result)
}

/// Check required presence, oneofs, bounds, unique substitution keys, acyclicity
/// and exact reachability. No rule/proposition/normalizer semantics are checked.
pub fn validate(result: &pb::ProofResult) -> Result<(), String> {
    use pb::{proof_step::Justification as W, proof_term::Kind as T};
    let root = result.root.ok_or("missing proof root")? as usize;
    let mut proof_edges = Vec::with_capacity(result.proofs.len());
    let mut term_roots = Vec::new();
    for proof in &result.proofs {
        term_roots.push(proof.lhs.ok_or("missing lhs")? as usize);
        term_roots.push(proof.rhs.ok_or("missing rhs")? as usize);
        let mut edges = Vec::new();
        match proof
            .justification
            .as_ref()
            .ok_or("missing justification")?
        {
            W::Fiat(_) | W::Eval(_) => {}
            W::Rule(rule) => {
                edges.extend(rule.premise_proofs.iter().map(|x| *x as usize));
                let mut names = HashSet::new();
                for binding in &rule.substitution {
                    if !names.insert(&binding.name) {
                        return Err("duplicate substitution name".into());
                    }
                    term_roots.push(binding.term.ok_or("missing substitution term")? as usize);
                }
            }
            W::MergeFn(merge) => {
                edges.push(merge.old_proof.ok_or("missing old proof")? as usize);
                edges.push(merge.new_proof.ok_or("missing new proof")? as usize);
            }
            W::Trans(trans) => {
                edges.push(trans.left.ok_or("missing left proof")? as usize);
                edges.push(trans.right.ok_or("missing right proof")? as usize);
            }
            W::Sym(id) | W::ContainerNormalize(id) => edges.push(*id as usize),
            W::Congr(congr) => {
                edges.push(congr.proof.ok_or("missing congruence proof")? as usize);
                congr.child_index.ok_or("missing congruence child index")?;
                edges.push(congr.child_proof.ok_or("missing congruence child proof")? as usize);
            }
        }
        proof_edges.push(edges);
    }
    closed_dag(&proof_edges, &[root], "proof")?;
    let mut term_edges = Vec::with_capacity(result.terms.len());
    for term in &result.terms {
        term_edges.push(match term.kind.as_ref().ok_or("missing term kind")? {
            T::App(app) => app.children.iter().map(|x| *x as usize).collect(),
            T::PrimitiveValue(value) => {
                super::value::Scalar::decode(None, value)?;
                Vec::new()
            }
            T::Var(_) => Vec::new(),
        });
    }
    closed_dag(&term_edges, &term_roots, "term")
}

/// Shared iterative DFS: white/gray/black states detect cycles even when arena
/// indices are not topological. Cursor frames keep stack size O(depth), not
/// O(edges), and validate references before any indexing.
fn closed_dag(edges: &[Vec<usize>], roots: &[usize], kind: &str) -> Result<(), String> {
    let mut color = vec![0_u8; edges.len()];
    for &root in roots {
        if root >= edges.len() {
            return Err(format!("{kind} root out of bounds"));
        }
        if color[root] == 2 {
            continue;
        }
        color[root] = 1;
        let mut stack = vec![(root, 0)];
        while let Some((node, cursor)) = stack.last_mut() {
            if *cursor == edges[*node].len() {
                color[*node] = 2;
                stack.pop();
                continue;
            }
            let child = edges[*node][*cursor];
            *cursor += 1;
            if child >= edges.len() {
                return Err(format!("{kind} edge out of bounds"));
            }
            match color[child] {
                0 => {
                    color[child] = 1;
                    stack.push((child, 0));
                }
                1 => return Err(format!("{kind} cycle")),
                _ => {}
            }
        }
    }
    if color.contains(&0) {
        return Err(format!("unreachable {kind} node"));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use egglog::{
        CommandOutput, EGraph,
        proof::{ProofId, ProofStore},
    };
    use egglog::{Term, TermId, proof::Justification};
    use prost::Message;
    use std::collections::{BTreeSet, HashMap};

    use super::pb;
    use crate::protobuf::proof as wire;

    const SIMPLE: &str = r###"(datatype Math
      (Num i64))


    (Num 2)

    (prove (Num 2))

    "###;
    const SUBSTITUTION: &str = r###"(relation Strings (String String))

    (Strings "hello" "world")

    (rule ((Strings a b)
           (= res (+ a " " b)))
          ((Strings "found" "hello world"))
          :name "r1")

    (run 1)

    (prove (Strings "found" "hello world"))"###;
    const CONTAINER: &str = r###";; Container proof: a collapsing (Set Math).
    ;;
    ;; `(set-of (A) (B))` and `(set-of (B))` start as distinct sets, each held by a
    ;; `Holds` constructor. Unioning A and B collapses `{A, B}` to a singleton, so
    ;; the two sets (and the two `Holds` terms) become equal.
    ;;
    ;; The proof exercises the container rebuild path: a `Congr` chain rebuilds the
    ;; set's element to its union-find leader, producing the (non-canonical)
    ;; `set-of(A, A)`, and the container normalization (sort + dedup) reduces it to
    ;; `set-of(A)` to match the canonical value.

    (sort Math)
    (constructor A () Math)
    (constructor B () Math)
    (sort MathSet (Set Math))
    (constructor Holds (MathSet) Math)

    (Holds (set-of (A) (B)))
    (Holds (set-of (B)))
    (union (A) (B))
    (run 1)

    (prove (= (Holds (set-of (A) (B))) (Holds (set-of (B)))))
    "###;
    const COMMUTE: &str = r###"
    (datatype Math
      (Add i64 i64)
      (Num i64))

    ;; Commutativity
    (rule ((Add a b)) ((union (Add a b) (Add b a))) :name "rw1")

    ;; Constant folding with an extra condition, forcing commute first
    (rule ((Add a b)
           (> a b))
          ((union (Add a b) (Num (+ a b)))) :name "rw2")

    ;; 2 + 3
    (let start (Add 2 3))

    (run 2)

    ;; 2 + 3 = 5 by
    ;; 2 + 3 = 3 + 2 (commute)
    ;; 3 + 2 = 5 (constant fold)
    (prove (= (Add 2 3) (Num 5)))"###;
    // The existing BigInt merge fixture is not proof-supported: from-string lacks
    // a validator. Keep its conflicting-write shape with supported i64 primitives.
    const MERGE: &str = r#"
    (function f (i64) i64 :merge (* old new))
    (set (f 1) 5)
    (set (f 1) 2)
    (set (f 1) 3)
    (check (= (f 1) 30))
    "#;
    const EVAL: &str = r#"
    (datatype E (Mk i64))
    (sort EV (Vec E))
    (relation SeedElem (E))
    (relation Done ())
    (SeedElem (Mk 1))
    (rule ((SeedElem e) (= xs (vec-of e))) ((Done)) :name "container-body")
    (run 1)
    (prove (Done))
    "#;
    const LITERALS: &str = r#"
    (datatype Payload (I i64) (F f64) (B bool) (S String) (U Unit))
    (I -9223372036854775808)
    (F -0.0)
    (B true)
    (S "")
    (U ())
    (prove (I -9223372036854775808))
    (prove (F -0.0))
    (prove (B true))
    (prove (S ""))
    (prove (U ()))
    "#;

    fn native_proofs(source: &str, proof_testing: bool) -> Vec<(ProofStore, ProofId)> {
        let mut graph = EGraph::new_with_proofs();
        if proof_testing {
            graph = graph.with_proof_testing();
        }
        let outputs = graph.parse_and_run_program(None, source).unwrap();
        drop(graph);
        let proofs: Vec<_> = outputs
            .into_iter()
            .filter_map(|output| match output {
                CommandOutput::ProveExists {
                    proof_store,
                    proof_id,
                } => Some((proof_store, proof_id)),
                _ => None,
            })
            .collect();
        assert!(!proofs.is_empty());
        proofs
    }

    #[test]
    fn native_outputs_are_owned() {
        for (name, source) in [
            ("simple", SIMPLE),
            ("substitution", SUBSTITUTION),
            ("container", CONTAINER),
        ] {
            for (store, root) in native_proofs(source, false) {
                let proof = store.get(root);
                println!(
                    "{name}: {:?} = {:?}",
                    store.term_dag().get(proof.lhs()),
                    store.term_dag().get(proof.rhs())
                );
            }
        }
    }

    #[derive(Default, Debug)]
    struct Coverage {
        kinds: BTreeSet<&'static str>,
        proof_reuses: usize,
        term_reuses: usize,
        bindings: usize,
    }

    /// Independent paired traversal, not export-again equality: check a bijection
    /// between reachable native identities and wire IDs and compare every payload.
    fn assert_same_graph(store: &ProofStore, root: ProofId, wire: &pb::ProofResult) -> Coverage {
        use pb::{proof_step::Justification as W, proof_term::Kind as T};
        let mut coverage = Coverage::default();
        let mut seen_proofs = HashMap::new();
        let mut native_for_proof = vec![None; wire.proofs.len()];
        let mut proofs = vec![(root, wire.root.unwrap())];
        let mut terms = Vec::new();
        while let Some((native, wire_id)) = proofs.pop() {
            if let Some(previous) = seen_proofs.insert(native, wire_id) {
                assert_eq!(previous, wire_id, "duplicated native proof identity");
                coverage.proof_reuses += 1;
                continue;
            }
            assert!(
                native_for_proof[wire_id as usize].replace(native).is_none(),
                "collapsed distinct proofs"
            );
            let n = store.get(native);
            let w = &wire.proofs[wire_id as usize];
            terms.push((n.lhs(), w.lhs.unwrap()));
            terms.push((n.rhs(), w.rhs.unwrap()));
            coverage.kinds.insert(
                match (n.justification(), w.justification.as_ref().unwrap()) {
                    (Justification::Fiat, W::Fiat(_)) => "Fiat",
                    (Justification::Eval, W::Eval(_)) => "Eval",
                    (
                        Justification::Rule {
                            name,
                            premise_proofs,
                            substitution,
                        },
                        W::Rule(rule),
                    ) => {
                        assert_eq!(name, &rule.name);
                        assert_eq!(premise_proofs.len(), rule.premise_proofs.len());
                        proofs.extend(
                            premise_proofs
                                .iter()
                                .copied()
                                .zip(rule.premise_proofs.iter().copied()),
                        );
                        assert_eq!(substitution.len(), rule.substitution.len());
                        assert!(
                            rule.substitution
                                .windows(2)
                                .all(|pair| pair[0].name < pair[1].name)
                        );
                        for binding in &rule.substitution {
                            terms.push((
                                *substitution.get(&binding.name).unwrap(),
                                binding.term.unwrap(),
                            ));
                        }
                        coverage.bindings += substitution.len();
                        "Rule"
                    }
                    (
                        Justification::MergeFn {
                            function,
                            old_proof,
                            new_proof,
                        },
                        W::MergeFn(merge),
                    ) => {
                        assert_eq!(function, &merge.function);
                        proofs.extend([
                            (*old_proof, merge.old_proof.unwrap()),
                            (*new_proof, merge.new_proof.unwrap()),
                        ]);
                        "MergeFn"
                    }
                    (Justification::Trans(left, right), W::Trans(trans)) => {
                        proofs
                            .extend([(*left, trans.left.unwrap()), (*right, trans.right.unwrap())]);
                        "Trans"
                    }
                    (Justification::Sym(proof), W::Sym(id)) => {
                        proofs.push((*proof, *id));
                        "Sym"
                    }
                    (
                        Justification::Congr {
                            proof,
                            child_index,
                            child_proof,
                        },
                        W::Congr(congr),
                    ) => {
                        assert_eq!(*child_index, congr.child_index.unwrap() as usize);
                        proofs.extend([
                            (*proof, congr.proof.unwrap()),
                            (*child_proof, congr.child_proof.unwrap()),
                        ]);
                        "Congr"
                    }
                    (Justification::ContainerNormalize { proof }, W::ContainerNormalize(id)) => {
                        proofs.push((*proof, *id));
                        "ContainerNormalize"
                    }
                    pair => panic!("justification mismatch: {pair:?}"),
                },
            );
        }
        assert_eq!(seen_proofs.len(), wire.proofs.len());
        let mut seen_terms: HashMap<TermId, u32> = HashMap::new();
        let mut native_for_term = vec![None; wire.terms.len()];
        while let Some((native, wire_id)) = terms.pop() {
            if let Some(previous) = seen_terms.insert(native, wire_id) {
                assert_eq!(previous, wire_id, "duplicated native term identity");
                coverage.term_reuses += 1;
                continue;
            }
            assert!(
                native_for_term[wire_id as usize].replace(native).is_none(),
                "collapsed distinct terms"
            );
            match (
                store.term_dag().get(native),
                wire.terms[wire_id as usize].kind.as_ref().unwrap(),
            ) {
                (Term::Lit(literal), T::PrimitiveValue(value)) => {
                    assert_eq!(
                        super::super::value::Scalar::from_literal(literal)
                            .unwrap()
                            .1,
                        super::super::value::Scalar::decode(None, value).unwrap()
                    );
                }
                (Term::Var(a), T::Var(b)) => assert_eq!(a, b),
                (Term::App(a, children), T::App(app)) => {
                    assert_eq!(a, &app.head);
                    assert_eq!(children.len(), app.children.len());
                    terms.extend(children.iter().copied().zip(app.children.iter().copied()));
                }
                pair => panic!("term mismatch: {pair:?}"),
            }
        }
        assert_eq!(seen_terms.len(), wire.terms.len());
        coverage
    }

    #[test]
    fn native_proof_bytes_preserve_fields_and_sharing() {
        let mut all = BTreeSet::new();
        let mut shared_proofs = 0;
        let mut bindings = 0;
        for (name, source, proof_testing) in [
            ("simple", SIMPLE, false),
            ("substitution", SUBSTITUTION, false),
            ("container", CONTAINER, false),
            ("commute", COMMUTE, false),
            ("merge", MERGE, true),
            ("eval", EVAL, false),
            ("literals", LITERALS, false),
        ] {
            for (store, root) in native_proofs(source, proof_testing) {
                let exported = wire::export(&store, root).unwrap();
                let bytes = exported.encode_to_vec();
                let decoded = wire::decode(&bytes).unwrap();
                assert_eq!(exported, decoded);
                assert_eq!(bytes, wire::export(&store, root).unwrap().encode_to_vec());
                let coverage = assert_same_graph(&store, root, &decoded);
                println!(
                    "{name}: {} bytes, {} terms, {} proofs; {coverage:?}",
                    bytes.len(),
                    decoded.terms.len(),
                    decoded.proofs.len()
                );
                shared_proofs += coverage.proof_reuses;
                bindings += coverage.bindings;
                all.extend(coverage.kinds);
            }
        }
        assert!(shared_proofs > 0);
        assert!(bindings > 0);
        assert_eq!(
            all,
            [
                "Fiat",
                "Rule",
                "MergeFn",
                "Trans",
                "Sym",
                "Congr",
                "ContainerNormalize",
                "Eval"
            ]
            .into_iter()
            .collect()
        );
    }

    #[test]
    fn malformed_native_proof_mutations_are_rejected() {
        use pb::{proof_step::Justification as W, proof_term::Kind as T};
        let (store, root) = native_proofs(SUBSTITUTION, false).pop().unwrap();
        let good = wire::export(&store, root).unwrap();
        assert!(wire::decode(&good.encode_to_vec()[..good.encoded_len() - 1]).is_err());
        let mut bad = good.clone();
        bad.root = None;
        assert!(
            wire::decode(&bad.encode_to_vec())
                .unwrap_err()
                .contains("missing proof root")
        );
        let mut bad = good.clone();
        bad.root = Some(u32::MAX);
        assert!(
            wire::decode(&bad.encode_to_vec())
                .unwrap_err()
                .contains("out of bounds")
        );
        let mut bad = good.clone();
        bad.proofs[0].lhs = None;
        assert!(
            wire::decode(&bad.encode_to_vec())
                .unwrap_err()
                .contains("missing lhs")
        );
        let mut bad = good.clone();
        bad.proofs[0].rhs = None;
        assert!(
            wire::decode(&bad.encode_to_vec())
                .unwrap_err()
                .contains("missing rhs")
        );
        let mut bad = good.clone();
        bad.proofs[0].lhs = Some(u32::MAX);
        assert!(
            wire::decode(&bad.encode_to_vec())
                .unwrap_err()
                .contains("out of bounds")
        );
        let mut bad = good.clone();
        bad.proofs[0].justification = None;
        assert!(
            wire::decode(&bad.encode_to_vec())
                .unwrap_err()
                .contains("missing justification")
        );
        let mut bad = good.clone();
        bad.terms[0].kind = None;
        assert!(
            wire::decode(&bad.encode_to_vec())
                .unwrap_err()
                .contains("missing term kind")
        );
        let mut bad = good.clone();
        bad.proofs[0].justification = Some(W::Sym(0));
        assert!(
            wire::decode(&bad.encode_to_vec())
                .unwrap_err()
                .contains("proof cycle")
        );
        let mut bad = good.clone();
        bad.proofs[0].justification = Some(W::Sym(u32::MAX));
        assert!(
            wire::decode(&bad.encode_to_vec())
                .unwrap_err()
                .contains("out of bounds")
        );
        let mut bad = good.clone();
        bad.terms[0].kind = Some(T::App(pb::ProofApp {
            head: "cycle".into(),
            children: vec![0],
        }));
        assert!(
            wire::decode(&bad.encode_to_vec())
                .unwrap_err()
                .contains("term cycle")
        );
        let mut bad = good.clone();
        bad.terms[0].kind = Some(T::App(pb::ProofApp {
            head: "bad-ref".into(),
            children: vec![u32::MAX],
        }));
        assert!(
            wire::decode(&bad.encode_to_vec())
                .unwrap_err()
                .contains("out of bounds")
        );
        let mut bad = good.clone();
        bad.terms.push(good.terms[0].clone());
        assert!(
            wire::decode(&bad.encode_to_vec())
                .unwrap_err()
                .contains("unreachable term")
        );
        let mut bad = good.clone();
        bad.proofs.push(good.proofs[0].clone());
        assert!(
            wire::decode(&bad.encode_to_vec())
                .unwrap_err()
                .contains("unreachable proof")
        );
        let mut bad = good.clone();
        let rule = bad
            .proofs
            .iter_mut()
            .find_map(|p| match p.justification.as_mut() {
                Some(W::Rule(r)) if !r.substitution.is_empty() => Some(r),
                _ => None,
            })
            .unwrap();
        rule.substitution.push(rule.substitution[0].clone());
        assert!(
            wire::decode(&bad.encode_to_vec())
                .unwrap_err()
                .contains("duplicate substitution")
        );
        let mut bad = good;
        let rule = bad
            .proofs
            .iter_mut()
            .find_map(|p| match p.justification.as_mut() {
                Some(W::Rule(r)) if !r.substitution.is_empty() => Some(r),
                _ => None,
            })
            .unwrap();
        rule.substitution[0].term = None;
        assert!(
            wire::decode(&bad.encode_to_vec())
                .unwrap_err()
                .contains("missing substitution term")
        );
    }

    #[test]
    fn nested_required_fields_are_checked() {
        use pb::proof_step::Justification as W;
        for (source, proof_testing) in [(MERGE, true), (CONTAINER, false)] {
            let (store, root) = native_proofs(source, proof_testing).pop().unwrap();
            let good = wire::export(&store, root).unwrap();
            let mut tested = 0;
            for (index, proof) in good.proofs.iter().enumerate() {
                let missing: Vec<W> = match proof.justification.as_ref().unwrap() {
                    W::MergeFn(m) => vec![
                        W::MergeFn(pb::ProofMergeFn {
                            old_proof: None,
                            ..m.clone()
                        }),
                        W::MergeFn(pb::ProofMergeFn {
                            new_proof: None,
                            ..m.clone()
                        }),
                    ],
                    W::Trans(t) => vec![
                        W::Trans(pb::ProofTrans { left: None, ..*t }),
                        W::Trans(pb::ProofTrans { right: None, ..*t }),
                    ],
                    W::Congr(c) => vec![
                        W::Congr(pb::ProofCongr { proof: None, ..*c }),
                        W::Congr(pb::ProofCongr {
                            child_index: None,
                            ..*c
                        }),
                        W::Congr(pb::ProofCongr {
                            child_proof: None,
                            ..*c
                        }),
                    ],
                    _ => Vec::new(),
                };
                for replacement in missing {
                    let mut bad = good.clone();
                    bad.proofs[index].justification = Some(replacement);
                    assert!(
                        wire::decode(&bad.encode_to_vec())
                            .unwrap_err()
                            .contains("missing")
                    );
                    tested += 1;
                }
            }
            assert!(tested > 0);
        }
    }

    #[test]
    fn arena_order_is_not_part_of_proof_identity() {
        use pb::{proof_step::Justification as W, proof_term::Kind as T};
        let (store, root) = native_proofs(CONTAINER, false).pop().unwrap();
        let mut reversed = wire::export(&store, root).unwrap();
        let last_proof = reversed.proofs.len() as u32 - 1;
        let last_term = reversed.terms.len() as u32 - 1;
        reversed.proofs.reverse();
        reversed.terms.reverse();
        reversed.root = reversed.root.map(|id| last_proof - id);
        for term in &mut reversed.terms {
            if let Some(T::App(app)) = &mut term.kind {
                for id in &mut app.children {
                    *id = last_term - *id;
                }
            }
        }
        for proof in &mut reversed.proofs {
            proof.lhs = proof.lhs.map(|id| last_term - id);
            proof.rhs = proof.rhs.map(|id| last_term - id);
            match proof.justification.as_mut().unwrap() {
                W::Fiat(_) | W::Eval(_) => {}
                W::Rule(rule) => {
                    for id in &mut rule.premise_proofs {
                        *id = last_proof - *id;
                    }
                    for binding in &mut rule.substitution {
                        binding.term = binding.term.map(|id| last_term - id);
                    }
                }
                W::MergeFn(merge) => {
                    merge.old_proof = merge.old_proof.map(|id| last_proof - id);
                    merge.new_proof = merge.new_proof.map(|id| last_proof - id);
                }
                W::Trans(trans) => {
                    trans.left = trans.left.map(|id| last_proof - id);
                    trans.right = trans.right.map(|id| last_proof - id);
                }
                W::Sym(id) | W::ContainerNormalize(id) => *id = last_proof - *id,
                W::Congr(congr) => {
                    congr.proof = congr.proof.map(|id| last_proof - id);
                    congr.child_proof = congr.child_proof.map(|id| last_proof - id);
                }
            }
        }
        let decoded = wire::decode(&reversed.encode_to_vec()).unwrap();
        assert_ne!(decoded.root, Some(0));
        assert_same_graph(&store, root, &decoded);
    }
}
