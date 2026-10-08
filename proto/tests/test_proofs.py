"""Proof wire/CEL checks only; these do not execute or check native proofs."""

import unittest

from protobuf import Oneof
from protovalidate import ValidationError, validate

from gen.python.egglog.v1 import egglog_pb as ir


class ProofSchemaTests(unittest.TestCase):
    def test_execution_modes_roundtrip_in_creation_and_snapshot(self):
        for mode in ir.ExecutionMode:
            with self.subTest(mode=mode):
                options = ir.EGraphOptions(cost_sort=0, execution_mode=mode)
                sorts = [ir.Sort(kind=Oneof("family", ir.HostSort(name="i64")))]
                request = ir.CreateEGraphRequest(options=options, sorts=sorts)
                snapshot = ir.EGraphSnapshot(
                    options=options, program=ir.Program(ir_version=1, sorts=sorts)
                )
                for message in (request, snapshot):
                    validate(message)
                    self.assertEqual(type(message).from_binary(message.to_binary()), message)
        self.assertEqual(
            ir.EGraphOptions(cost_sort=0).execution_mode,
            ir.ExecutionMode.NORMAL,
        )

    def test_unknown_execution_mode_is_rejected(self):
        with self.assertRaises(ValidationError):
            validate(ir.EGraphOptions(cost_sort=0, execution_mode=99))

    def test_proof_commands_roundtrip(self):
        program = ir.Program(
            ir_version=1,
            commands=[
                ir.Command(kind=Oneof("prove", ir.Prove(facts=[]))),
                ir.Command(kind=Oneof("prove_exists", ir.ProveExists(constructor="Goal"))),
            ],
        )
        validate(program)
        self.assertEqual(ir.Program.from_binary(program.to_binary()), program)
        with self.assertRaises(ValidationError):
            validate(ir.ProveExists())

    def test_all_native_terms_and_justifications_roundtrip(self):
        terms = [
            ir.ProofTerm(kind=Oneof("i64", -(2**63))),
            ir.ProofTerm(kind=Oneof("f64_bits", 0x7FF8000000000042)),
            ir.ProofTerm(kind=Oneof("string", "")),
            ir.ProofTerm(kind=Oneof("bool", False)),
            ir.ProofTerm(kind=Oneof("unit", ir.Unit())),
            ir.ProofTerm(kind=Oneof("var", "x")),
            ir.ProofTerm(kind=Oneof("app", ir.ProofApp(head="f", children=[0, 0, 1, 2, 3, 4, 5]))),
        ]
        justifications = [
            Oneof("fiat", ir.Unit()),
            Oneof("rule", ir.ProofRule(
                name="rule-name", premise_proofs=[0, 0],
                substitution=[ir.ProofBinding(name="x", term=0)],
            )),
            Oneof("merge_fn", ir.ProofMergeFn(function="f", old_proof=0, new_proof=1)),
            Oneof("trans", ir.ProofTrans(left=0, right=1)),
            Oneof("sym", 3),
            Oneof("congr", ir.ProofCongr(proof=0, child_index=0, child_proof=1)),
            Oneof("container_normalize", 5),
            Oneof("eval", ir.Unit()),
            Oneof("rule", ir.ProofRule(premise_proofs=list(range(8)))),
        ]
        result = ir.ProofResult(
            terms=terms,
            proofs=[ir.ProofStep(lhs=6, rhs=6, justification=j) for j in justifications],
            root=8,
        )
        response = ir.RunProgramResponse(outputs=[ir.CommandOutput(
            kind=Oneof("proof", result), location=ir.CommandLocation(path=[0]),
        )])
        validate(response)
        decoded = ir.RunProgramResponse.from_binary(response.to_binary())
        self.assertEqual(decoded, response)
        self.assertEqual(decoded.outputs[0].kind.value.terms[1].kind.value, 0x7FF8000000000042)

    def test_required_proof_indices_and_oneofs(self):
        invalid = [
            ir.ProofResult(), ir.ProofTerm(),
            ir.ProofStep(lhs=0, rhs=0),
            ir.ProofStep(rhs=0, justification=Oneof("fiat", ir.Unit())),
            ir.ProofStep(lhs=0, justification=Oneof("fiat", ir.Unit())),
            ir.ProofMergeFn(function="f", old_proof=0),
            ir.ProofMergeFn(function="f", new_proof=0),
            ir.ProofTrans(left=0), ir.ProofTrans(right=0),
            ir.ProofCongr(proof=0, child_proof=0),
            ir.ProofCongr(child_index=0, child_proof=0),
            ir.ProofCongr(proof=0, child_index=0),
            ir.ProofBinding(name="x"),
        ]
        for message in invalid:
            with self.subTest(message=message), self.assertRaises(ValidationError):
                validate(message)

    def test_root_term_and_substitution_bounds(self):
        term = ir.ProofTerm(kind=Oneof("i64", 0))
        fiat = Oneof("fiat", ir.Unit())
        invalid = [
            ir.ProofResult(terms=[term], proofs=[ir.ProofStep(lhs=0, rhs=0, justification=fiat)], root=1),
            ir.ProofResult(terms=[term], proofs=[ir.ProofStep(lhs=1, rhs=0, justification=fiat)], root=0),
            ir.ProofResult(terms=[term], proofs=[ir.ProofStep(lhs=0, rhs=1, justification=fiat)], root=0),
            ir.ProofResult(
                terms=[ir.ProofTerm(kind=Oneof("app", ir.ProofApp(head="f", children=[1])))],
                proofs=[ir.ProofStep(lhs=0, rhs=0, justification=fiat)], root=0,
            ),
            ir.ProofResult(terms=[term], proofs=[ir.ProofStep(
                lhs=0, rhs=0, justification=Oneof("rule", ir.ProofRule(
                    substitution=[ir.ProofBinding(name="x", term=1)],
                )),
            )], root=0),
        ]
        for message in invalid:
            with self.subTest(message=message), self.assertRaises(ValidationError):
                validate(message)

    def test_every_justification_reference_is_checked(self):
        invalid = [
            Oneof("rule", ir.ProofRule(premise_proofs=[1])),
            Oneof("merge_fn", ir.ProofMergeFn(function="f", old_proof=1, new_proof=0)),
            Oneof("merge_fn", ir.ProofMergeFn(function="f", old_proof=0, new_proof=1)),
            Oneof("trans", ir.ProofTrans(left=1, right=0)),
            Oneof("trans", ir.ProofTrans(left=0, right=1)),
            Oneof("sym", 1),
            Oneof("congr", ir.ProofCongr(proof=1, child_index=0, child_proof=0)),
            Oneof("congr", ir.ProofCongr(proof=0, child_index=0, child_proof=1)),
            Oneof("container_normalize", 1),
        ]
        for justification in invalid:
            message = ir.ProofResult(
                terms=[ir.ProofTerm(kind=Oneof("i64", 0))],
                proofs=[ir.ProofStep(lhs=0, rhs=0, justification=justification)], root=0,
            )
            with self.subTest(justification=justification), self.assertRaises(ValidationError):
                validate(message)

    def test_duplicate_substitution_names_are_rejected(self):
        with self.assertRaises(ValidationError):
            validate(ir.ProofRule(substitution=[
                ir.ProofBinding(name="x", term=0), ir.ProofBinding(name="x", term=1),
            ]))

    def test_nested_run_wire_capacity(self):
        # Structural acceptance does not require maintenance runs to be emitted.
        # Command matching belongs to the shared adapter, not this wire test.
        response = ir.RunProgramResponse(
            outputs=[ir.CommandOutput(
                kind=Oneof("run", ir.RunOutcome(updated=True)),
                location=ir.CommandLocation(path=[0, 1], iterations=[2]),
            )],
        )
        validate(response)
        self.assertEqual(ir.RunProgramResponse.from_binary(response.to_binary()), response)
        with self.assertRaises(ValidationError):
            validate(ir.CommandOutput(
                kind=Oneof("loop", ir.LoopOutcome(
                    iterations=1, termination=ir.TerminationReason.COUNT_REACHED,
                )),
                location=ir.CommandLocation(path=[0, 1], iterations=[2]),
            ))

    def test_proof_failure_classification(self):
        for reason in ir.ProofFailureReason:
            if reason == ir.ProofFailureReason.UNSPECIFIED:
                continue
            with self.subTest(reason=reason):
                error = ir.Error(
                    code=ir.ErrorCode.PROOF_FAILED, message="native diagnostic",
                    proof_failure=ir.ProofFailure(reason=reason, constructor="Goal"),
                )
                validate(error)
                self.assertEqual(ir.Error.from_binary(error.to_binary()), error)
        invalid = [
            ir.ProofFailure(), ir.ProofFailure(reason=99),
            ir.Error(code=ir.ErrorCode.PROOF_FAILED, message="missing detail"),
            ir.Error(code=ir.ErrorCode.CHECK_FAILED, message="wrong detail", proof_failure=ir.ProofFailure(
                reason=ir.ProofFailureReason.PROOFS_NOT_ENABLED,
            )),
        ]
        for message in invalid:
            with self.subTest(message=message), self.assertRaises(ValidationError):
                validate(message)


if __name__ == "__main__":
    unittest.main()
