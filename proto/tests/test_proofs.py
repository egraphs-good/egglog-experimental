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
            Oneof("run", ir.Run(rulesets=[ir.RulesetSelection(kind=Oneof("name", ""))])),
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
            ("run", ir.Run(), "1a00"),
            ("bind_scheduler", ir.BindScheduler(
                name="s", back_off=ir.BackOff(),
            ), "22050a01731200"),
            ("keep_best", ir.KeepBest(tables=["C"], extractor=ir.Extractor.TREE), "2a050a01431001"),
            ("extract", ir.Extract(roots=[0], variants=1, extractor=ir.Extractor.TREE), "32070a010010011801"),
            ("freeze", ir.Freeze(), "3a00"),
            ("table_sizes", ir.GetTableSizes(), "4200"),
            ("table_rows", ir.GetTableRows(table="C"), "4a030a0143"),
            ("table_stats", ir.GetTableStats(), "5200"),
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


class RulesetSchemaTests(unittest.TestCase):
    def test_bindings_use_program_tag_7_and_keep_order_and_duplicates(self):
        rule = ir.Rule(kind=Oneof("rule", ir.RuleBody()), eval_mode=ir.RuleEvalMode.SEMINAIVE)
        for name, rules in (("", []), ("g", [rule]), ("snowman-☃", [rule, rule, rule])):
            with self.subTest(name=name, rules=rules):
                program = ir.Program(rulesets=[ir.RulesetBinding(
                    name=name, value=ir.Ruleset(rules=rules),
                )])
                validate(program)
                self.assertTrue(program.to_binary().startswith(b"\x3a"))
                for decoded in (
                    ir.Program.from_binary(program.to_binary()),
                    ir.Program.from_json(program.to_json()),
                ):
                    self.assertEqual(decoded, program)
        self.assertEqual(ir.Program(rulesets=[
            ir.RulesetBinding(value=ir.Ruleset()),
        ]).to_binary(), bytes.fromhex("3a021200"))

    def test_binding_values_are_required_and_names_are_unique_per_program(self):
        for name in ("", "g"):
            with self.subTest(name=name):
                with self.assertRaises(ValidationError):
                    validate(ir.RulesetBinding(name=name))
                with self.assertRaises(ValidationError):
                    validate(ir.Program(rulesets=[
                        ir.RulesetBinding(name=name, value=ir.Ruleset()),
                        ir.RulesetBinding(name=name, value=ir.Ruleset()),
                    ]))
        validate(ir.Program(rulesets=[
            ir.RulesetBinding(value=ir.Ruleset()),
            ir.RulesetBinding(name="g", value=ir.Ruleset()),
        ]))

    def test_bindings_and_literal_selections_validate_rule_values_and_roots(self):
        invalid_rules = [
            ir.Rule(),
            ir.Rule(kind=Oneof("rule", ir.RuleBody(query=[0])), eval_mode=ir.RuleEvalMode.SEMINAIVE),
            ir.Rule(kind=Oneof("rule", ir.RuleBody(head=[ir.Action(kind=Oneof("term", 0))])),
                    eval_mode=ir.RuleEvalMode.SEMINAIVE),
            ir.Rule(kind=Oneof("rewrite", ir.Rewrite(lhs=0, rhs=0)),
                    eval_mode=ir.RuleEvalMode.SEMINAIVE),
            ir.Rule(kind=Oneof("birewrite", ir.BiRewrite(lhs=0, rhs=0)),
                    eval_mode=ir.RuleEvalMode.SEMINAIVE),
        ]
        for rule in invalid_rules:
            ruleset = ir.Ruleset(rules=[rule])
            for program in (
                ir.Program(rulesets=[ir.RulesetBinding(name="g", value=ruleset)]),
                ir.Program(commands=[ir.Command(kind=Oneof("run", ir.Run(rulesets=[
                    ir.RulesetSelection(kind=Oneof("ruleset", ruleset)),
                ])))]),
            ):
                with self.subTest(rule=rule, program=program), self.assertRaises(ValidationError):
                    validate(program)

    def test_run_selections_distinguish_empty_default_unknown_and_literals(self):
        rule = ir.Rule(kind=Oneof("rule", ir.RuleBody()), eval_mode=ir.RuleEvalMode.SEMINAIVE)
        names = [ir.RulesetSelection(kind=Oneof("name", name)) for name in ("", "unknown", "a", "b")]
        literal = ir.RulesetSelection(kind=Oneof("ruleset", ir.Ruleset(rules=[rule, rule])))
        empty = ir.RulesetSelection(kind=Oneof("ruleset", ir.Ruleset()))
        for selections in ([], [names[0]], [names[1]], [names[2], names[3], names[2]],
                           [literal, names[0], empty, literal]):
            with self.subTest(selections=selections):
                run = ir.Run(rulesets=selections, scheduler="s")
                validate(run)
                for decoded in (ir.Run.from_binary(run.to_binary()), ir.Run.from_json(run.to_json())):
                    self.assertEqual(decoded, run)
                    self.assertEqual(decoded.rulesets, selections)
        self.assertEqual(ir.Run().to_binary(), b"")
        self.assertEqual(ir.Run(rulesets=[names[0]]).to_binary(), bytes.fromhex("0a021200"))
        self.assertEqual(ir.Run(rulesets=[empty]).to_binary(), bytes.fromhex("0a020a00"))
        self.assertEqual(ir.Run(scheduler="s").to_binary(), bytes.fromhex("120173"))
        with self.assertRaises(ValidationError):
            validate(ir.Run(rulesets=[ir.RulesetSelection()]))

    def test_nested_literal_rule_shapes_validate_even_in_zero_iteration_bodies(self):
        for rule in (ir.Rule(), ir.Rule(kind=Oneof("rule", ir.RuleBody()))):
            run = ir.Command(kind=Oneof("run", ir.Run(rulesets=[
                ir.RulesetSelection(kind=Oneof("ruleset", ir.Ruleset(rules=[rule]))),
            ])))
            for command in (
                ir.Command(kind=Oneof("fail", run)),
                ir.Command(kind=Oneof("loop", ir.Loop(body=[run], max_iterations=0))),
            ):
                with self.subTest(command=command), self.assertRaises(ValidationError):
                    validate(ir.Program(commands=[command]))

    def test_standalone_rule_values_need_no_program_arena_or_registration_command(self):
        rule = ir.Rule(kind=Oneof("rule", ir.RuleBody()), eval_mode=ir.RuleEvalMode.SEMINAIVE)
        validate(rule)
        self.assertEqual(ir.Rule.from_binary(rule.to_binary()), rule)
        self.assertNotIn("rules", ir.Program.__annotations__)
        self.assertFalse(hasattr(ir, "AddRules"))
        self.assertFalse(hasattr(ir, "Scheduler"))
        with self.assertRaises(ValidationError):
            validate(ir.Command.from_binary(bytes.fromhex("920100")))
        with self.assertRaises(TypeError):
            ir.BindScheduler(name="s", scheduler=ir.BackOff())

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
