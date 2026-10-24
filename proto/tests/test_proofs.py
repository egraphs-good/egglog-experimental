"""Proof/response wire checks; no native proof or registration execution."""

import json
import unittest

from protobuf import Oneof
from protovalidate import ValidationError, validate

from gen.python.egglog.v1 import egglog_pb as ir


class ExpectedFailureSchemaTests(unittest.TestCase):
    def test_nested_fail_roundtrips_with_distinct_wrapper_and_leaf_spans(self):
        for kind in (
            Oneof("check", ir.Check()),
            Oneof("prove", ir.Prove()),
            Oneof("prove_exists", ir.ProveExists(constructor="Goal")),
            Oneof("action", ir.Action(kind=Oneof("panic", "expected"))),
            Oneof("run", ir.Run(groups=[""])),
        ):
            with self.subTest(kind=kind.field):
                command = ir.Command(kind=kind, span=ir.Span(start=12, end=19))
                for start in (6, 0):
                    command = ir.Command(
                        kind=Oneof("fail", command), span=ir.Span(start=start, end=20),
                    )
                program = ir.Program(
                    files=[ir.SourceFile(name="expected.egg")],
                    commands=[command],
                )
                validate(program)
                for decoded in (
                    ir.Program.from_binary(program.to_binary()),
                    ir.Program.from_json(program.to_json()),
                ):
                    validate(decoded)
                    self.assertEqual(decoded, program)
                    self.assertEqual(decoded.commands[0].kind.value.kind.value.kind, kind)
                self.assertEqual(
                    json.loads(program.to_json())["commands"][0]["fail"]["fail"]["span"]["start"],
                    12,
                )

    def test_fail_uses_tag_16_and_requires_a_command_at_every_depth(self):
        nested = ir.Command(kind=Oneof("fail", ir.Command(kind=Oneof(
            "fail", ir.Command(kind=Oneof("check", ir.Check())),
        ))))
        self.assertEqual(nested.to_binary(), bytes.fromhex("8201058201021200"))
        for encoded in ("", "820100", "820103820100", "820103a20100"):
            # The last child contains unknown arm 20, not an expected failure.
            with self.subTest(encoded=encoded), self.assertRaises(ValidationError):
                validate(ir.Command.from_binary(bytes.fromhex(encoded)))
        for invalid in (
            ir.Command(),
            ir.Command(kind=Oneof("action", ir.Action())),
            ir.Command(kind=Oneof("prove_exists", ir.ProveExists())),
            ir.Command(kind=Oneof("check", ir.Check()), span=ir.Span(start=2, end=1)),
        ):
            for _ in range(2):
                invalid = ir.Command(kind=Oneof("fail", invalid))
            with self.subTest(command=invalid), self.assertRaises(ValidationError):
                validate(ir.Program(commands=[invalid]))

    def test_fail_and_loop_nesting_keep_existing_location_shape(self):
        leaf = ir.Command(kind=Oneof("fail", ir.Command(kind=Oneof("check", ir.Check()))))
        for kind in (
            Oneof("loop", ir.Loop(body=[leaf], max_iterations=1)),
            Oneof("loop", ir.Loop(body=[leaf])),
        ):
            with self.subTest(kind=kind.field):
                program = ir.Program(commands=[
                    ir.Command(kind=Oneof("fail", ir.Command(kind=kind))),
                ])
                validate(program)
                self.assertEqual(ir.Program.from_binary(program.to_binary()), program)
        # Wrappers add no list indices or loop coordinates. Request matching,
        # catch behavior, and output suppression still require the adapter.
        error = ir.Error(
            code=ir.ErrorCode.RUNTIME_FAILURE, message="expected failure did not occur",
            location=ir.CommandLocation(path=[0, 0], iterations=[0]),
        )
        validate(error)
        self.assertEqual(ir.Error.from_binary(error.to_binary()), error)
        for location in (
            ir.CommandLocation(path=[0, 0], iterations=[]),
            ir.CommandLocation(path=[0, 0], iterations=[0, 0]),
        ):
            with self.subTest(location=location), self.assertRaises(ValidationError):
                validate(location)

    def test_existing_command_arm_bytes_are_unchanged(self):
        # Captured from immutable S1fc before adding Command.fail.
        cases = [
            ("action", ir.Action(kind=Oneof("panic", "expected")), "0a0a22086578706563746564"),
            ("check", ir.Check(), "1200"),
            ("run", ir.Run(groups=[""]), "1a020a00"),
            ("bind_scheduler", ir.BindScheduler(
                name="s", scheduler=ir.Scheduler(kind=Oneof("back_off", ir.BackOff())),
            ), "22070a017312020a00"),
            ("keep_best", ir.KeepBest(tables=["C"], extractor=ir.Extractor.TREE), "2a050a01431001"),
            ("extract", ir.Extract(roots=[0], variants=1, extractor=ir.Extractor.TREE), "32070a010010011801"),
            ("freeze", ir.Freeze(), "3a00"),
            ("print_size", ir.PrintSize(), "4200"),
            ("print_function", ir.PrintFunction(table="C"), "4a030a0143"),
            ("print_table_stats", ir.PrintTableStats(), "5200"),
            ("loop", ir.Loop(max_iterations=0), "5a021800"),
            ("prove", ir.Prove(), "7200"),
            ("prove_exists", ir.ProveExists(constructor="C"), "7a030a0143"),
        ]
        for field, payload, encoded in cases:
            with self.subTest(field=field):
                command = ir.Command(kind=Oneof(field, payload))
                validate(command)
                self.assertEqual(command.to_binary(), bytes.fromhex(encoded))
                self.assertEqual(ir.Command.from_binary(bytes.fromhex(encoded)), command)


class AdditiveSchemaTests(unittest.TestCase):
    def test_add_rules_has_tag_18_and_keeps_bulk_order_and_duplicates(self):
        for group, rules in (("", []), ("g", [0]), ("snowman-☃", [2, 0, 2])):
            with self.subTest(group=group, rules=rules):
                command = ir.Command(kind=Oneof("add_rules", ir.AddRules(group=group, rules=rules)))
                validate(command)
                self.assertTrue(command.to_binary().startswith(b"\x92\x01"))
                for decoded in (
                    ir.Command.from_binary(command.to_binary()),
                    ir.Command.from_json(command.to_json()),
                ):
                    self.assertEqual(decoded, command)
        self.assertEqual(ir.Command(kind=Oneof("add_rules", ir.AddRules())).to_binary(), b"\x92\x01\x00")

    def test_add_rules_references_the_program_rule_arena(self):
        rule = ir.Rule(kind=Oneof("rule", ir.RuleBody()), eval_mode=ir.RuleEvalMode.SEMINAIVE)
        program = ir.Program(rules=[rule], commands=[
            ir.Command(kind=Oneof("add_rules", ir.AddRules(group="g", rules=[0, 0]))),
        ])
        validate(program)
        self.assertEqual(ir.Program.from_binary(program.to_binary()), program)
        program.commands[0].kind.value.rules.append(1)
        with self.assertRaises(ValidationError):
            validate(program)

    def test_run_groups_distinguish_empty_default_and_unknown_selections(self):
        for groups in ([], [""], ["unknown"], ["a", "b", "a"], ["", "snowman-☃"]):
            with self.subTest(groups=groups):
                run = ir.Run(groups=groups)
                validate(run)
                for decoded in (ir.Run.from_binary(run.to_binary()), ir.Run.from_json(run.to_json())):
                    self.assertEqual(decoded, run)
                    self.assertEqual(decoded.groups, groups)
        self.assertEqual(ir.Run().to_binary(), b"")
        self.assertEqual(ir.Run(groups=[""]).to_binary(), b"\x0a\x00")

    def test_rule_values_do_not_require_registration_commands(self):
        program = ir.Program(rules=[
            ir.Rule(kind=Oneof("rule", ir.RuleBody()), eval_mode=ir.RuleEvalMode.SEMINAIVE),
        ])
        validate(program)
        self.assertEqual(ir.Program.from_binary(program.to_binary()), program)
        self.assertEqual(program.commands, [])

    def test_successful_response_needs_no_registration_confirmation(self):
        response = ir.RunProgramOutput()
        validate(response)
        self.assertEqual(response.to_binary(), b"")
        self.assertEqual(ir.RunProgramOutput.from_json(response.to_json()), response)


class ProofSchemaTests(unittest.TestCase):
    def test_execution_modes_roundtrip_in_creation_and_snapshot(self):
        for mode in ir.ExecutionMode:
            with self.subTest(mode=mode):
                options = ir.EGraphOptions(cost_sort=0, execution_mode=mode)
                sorts = [ir.Sort(kind=Oneof("application", ir.SortApplication(name="i64")))]
                request = ir.CreateEGraphRequest(options=options, sorts=sorts)
                snapshot = ir.EGraphSnapshot(
                    options=options, program=ir.Program(sorts=sorts)
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
        response = ir.RunProgramOutput(
            outputs=[ir.CommandOutput(
                kind=Oneof("proof", result), location=ir.CommandLocation(path=[0]),
            )],
        )
        validate(response)
        decoded = ir.RunProgramOutput.from_binary(response.to_binary())
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

    def test_nested_proofs_are_allowed_but_control_outcomes_are_top_level(self):
        proof = ir.ProofResult(
            terms=[ir.ProofTerm(kind=Oneof("i64", 0))],
            proofs=[ir.ProofStep(lhs=0, rhs=0, justification=Oneof("fiat", ir.Unit()))],
            root=0,
        )
        response = ir.RunProgramOutput(
            outputs=[ir.CommandOutput(
                kind=Oneof("proof", proof),
                location=ir.CommandLocation(path=[0, 1], iterations=[2]),
            )],
        )
        validate(response)
        self.assertEqual(ir.RunProgramOutput.from_binary(response.to_binary()), response)
        for kind in (
            Oneof("run", ir.RunResult(updated=True)),
        ):
            validate(ir.CommandOutput(
                kind=kind, location=ir.CommandLocation(path=[0]),
            ))
            with self.subTest(kind=kind), self.assertRaises(ValidationError):
                validate(ir.CommandOutput(
                    kind=kind,
                    location=ir.CommandLocation(path=[0, 1], iterations=[2]),
                ))

    def test_minimal_error_preserves_class_and_location(self):
        for code in (ir.ErrorCode.INVALID_PROGRAM, ir.ErrorCode.CHECK_FAILED, ir.ErrorCode.RUNTIME_FAILURE):
            error = ir.Error(code=code, message="native diagnostic", location=ir.CommandLocation(path=[1]))
            validate(error)
            self.assertEqual(ir.Error.from_binary(error.to_binary()), error)
        for code in (ir.ErrorCode.UNSPECIFIED, 99):
            with self.assertRaises(ValidationError):
                validate(ir.Error(code=code, message="invalid class"))


if __name__ == "__main__":
    unittest.main()
