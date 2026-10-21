"""Proof/response wire checks; no native proof or publication execution."""

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
            Oneof("run", ir.Run(ruleset=ir.RulesetRef(kind=Oneof("name", "")))),
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
        for encoded in ("", "820100", "820103820100", "820103920100"):
            # The last child contains unknown arm 18, not an expected failure.
            with self.subTest(encoded=encoded), self.assertRaises(ValidationError):
                validate(ir.Command.from_binary(bytes.fromhex(encoded)))
        for invalid in (
            ir.Command(),
            ir.Command(kind=Oneof("action", ir.Action())),
            ir.Command(kind=Oneof("run", ir.Run())),
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
            Oneof("repeat", ir.Repeat(body=[leaf], times=1)),
            Oneof("saturate", ir.Saturate(body=[leaf], max_iterations=1)),
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
            code=ir.ErrorCode.EVALUATION_FAILED, message="expected failure did not occur",
            location=ir.CommandLocation(path=[0, 0], iterations=[0]),
        )
        validate(error)
        self.assertEqual(ir.Error.from_binary(error.to_binary()), error)
        validate(ir.StaticCommandPath(path=[0, 0]))
        validate(ir.RunSummary(command_path=[0, 0], invocations=1))
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
            ("run", ir.Run(ruleset=ir.RulesetRef(kind=Oneof("name", ""))), "1a040a021200"),
            ("bind_scheduler", ir.BindScheduler(
                name="s", scheduler=ir.Scheduler(kind=Oneof("back_off", ir.BackOff())),
            ), "22070a017312020a00"),
            ("keep_best", ir.KeepBest(tables=["C"], extractor=ir.Extractor.TREE), "2a050a01431001"),
            ("extract", ir.Extract(roots=[0], variants=1, extractor=ir.Extractor.TREE), "32070a010010011801"),
            ("freeze", ir.Freeze(), "3a00"),
            ("print_size", ir.PrintSize(), "4200"),
            ("print_function", ir.PrintFunction(table="C"), "4a030a0143"),
            ("print_table_stats", ir.PrintTableStats(), "5200"),
            ("repeat", ir.Repeat(times=0), "5a021800"),
            ("saturate", ir.Saturate(), "6200"),
            ("prove", ir.Prove(), "7200"),
            ("prove_exists", ir.ProveExists(constructor="C"), "7a030a0143"),
        ]
        for field, payload, encoded in cases:
            with self.subTest(field=field):
                command = ir.Command(kind=Oneof(field, payload))
                validate(command)
                self.assertEqual(command.to_binary(), bytes.fromhex(encoded))
                self.assertEqual(ir.Command.from_binary(bytes.fromhex(encoded)), command)


class PublicationSchemaTests(unittest.TestCase):
    def test_ruleset_publication_absence_is_not_an_empty_confirmation(self):
        absent = ir.RunProgramResponse.from_binary(b"")
        self.assertFalse(absent.has_field("ruleset_publication"))
        self.assertNotIn("rulesetPublication", json.loads(absent.to_json()))
        with self.assertRaises(ValidationError):
            validate(absent)
        present = ir.RunProgramResponse(ruleset_publication=ir.RulesetPublication())
        validate(present)
        self.assertEqual(present.to_binary(), b"\x42\x00")
        self.assertEqual(json.loads(present.to_json())["rulesetPublication"], {})
        for decoded in (
            ir.RunProgramResponse.from_binary(present.to_binary()),
            ir.RunProgramResponse.from_json(present.to_json()),
        ):
            self.assertTrue(decoded.has_field("ruleset_publication"))
            self.assertEqual(decoded.ruleset_publication.names, [])
            self.assertEqual(decoded, present)

    def test_ruleset_publication_names_roundtrip_including_the_default_name(self):
        for names in ([], [""], ["named"], ["", "named", "snowman-☃"]):
            with self.subTest(names=names):
                response = ir.RunProgramResponse(ruleset_publication=ir.RulesetPublication(names=names))
                validate(response)
                for decoded in (
                    ir.RunProgramResponse.from_binary(response.to_binary()),
                    ir.RunProgramResponse.from_json(response.to_json()),
                ):
                    self.assertEqual(decoded, response)
                    self.assertEqual(decoded.ruleset_publication.names, names)
        self.assertEqual(ir.RulesetPublication(names=[""]).to_binary(), b"\x0a\x00")

    def test_ruleset_publication_rejects_duplicate_names(self):
        for names in (["named", "named"], ["", ""], ["first", "second", "first"]):
            for message in (
                ir.RulesetPublication(names=names),
                ir.RunProgramResponse(ruleset_publication=ir.RulesetPublication(names=names)),
            ):
                with self.subTest(names=names, message=type(message).__name__), self.assertRaises(ValidationError):
                    validate(message)

    def test_ruleset_publication_presence_is_independent_of_profile_and_error(self):
        cases = [
            (None, ["", "complete"]),
            (ir.Error(code=ir.ErrorCode.INVALID_PROGRAM, message="preparation failed"), []),
            (ir.Error(code=ir.ErrorCode.UNKNOWN_NAME, message="preparation failed"), []),
            (ir.Error(code=ir.ErrorCode.CHECK_FAILED, message="command failed", location=ir.CommandLocation(path=[0])), ["complete"]),
        ]
        for error, names in cases:
            for profile in (None, ir.ProfileSummary(complete=error is None)):
                with self.subTest(error=error, profile=profile):
                    response = ir.RunProgramResponse(
                        error=error, profile=profile,
                        ruleset_publication=ir.RulesetPublication(names=names),
                    )
                    validate(response)
                    self.assertEqual(ir.RunProgramResponse.from_binary(response.to_binary()), response)
                    response.ruleset_publication = None
                    with self.assertRaises(ValidationError):
                        validate(response)

    def test_ruleset_publication_membership_needs_the_submitted_request(self):
        # Like MaintenanceSite request bounds, request-name membership and
        # truthful completion cannot be checked by response-only CEL. A reader
        # must reject this name if it was not submitted, despite valid shape.
        validate(ir.RunProgramResponse(ruleset_publication=ir.RulesetPublication(names=["not-in-request"])))


class ProofSchemaTests(unittest.TestCase):
    def test_execution_modes_roundtrip_in_creation_and_snapshot(self):
        for mode in ir.ExecutionMode:
            with self.subTest(mode=mode):
                options = ir.EGraphOptions(cost_sort=0, execution_mode=mode)
                sorts = [ir.Sort(kind=Oneof("family", ir.HostSort(name="i64")))]
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
        response = ir.RunProgramResponse(
            ruleset_publication=ir.RulesetPublication(),
            outputs=[ir.CommandOutput(
                kind=Oneof("proof", result), location=ir.CommandLocation(path=[0]),
            )],
        )
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

    def test_nested_proofs_are_allowed_but_control_outcomes_are_top_level(self):
        proof = ir.ProofResult(
            terms=[ir.ProofTerm(kind=Oneof("i64", 0))],
            proofs=[ir.ProofStep(lhs=0, rhs=0, justification=Oneof("fiat", ir.Unit()))],
            root=0,
        )
        response = ir.RunProgramResponse(
            ruleset_publication=ir.RulesetPublication(),
            outputs=[ir.CommandOutput(
                kind=Oneof("proof", proof),
                location=ir.CommandLocation(path=[0, 1], iterations=[2]),
            )],
        )
        validate(response)
        self.assertEqual(ir.RunProgramResponse.from_binary(response.to_binary()), response)
        for kind in (
            Oneof("run", ir.RunOutcome(updated=True)),
            Oneof("loop", ir.LoopOutcome(
                iterations=1, termination=ir.TerminationReason.COUNT_REACHED,
            )),
        ):
            validate(ir.CommandOutput(
                kind=kind, location=ir.CommandLocation(path=[0]),
            ))
            with self.subTest(kind=kind), self.assertRaises(ValidationError):
                validate(ir.CommandOutput(
                    kind=kind,
                    location=ir.CommandLocation(path=[0, 1], iterations=[2]),
                ))

    def test_maintenance_sites_roundtrip_with_zero_index_presence(self):
        targets = [
            Oneof("command", ir.StaticCommandPath(path=[0])),
            Oneof("command", ir.StaticCommandPath(path=[2, 1])),
            Oneof("declaration", 0), Oneof("sort", 0), Oneof("ruleset", 0),
        ]
        response = ir.RunProgramResponse(
            ruleset_publication=ir.RulesetPublication(),
            profile=ir.ProfileSummary(
                complete=True,
                runs=[ir.RunSummary(command_path=[0], invocations=1)],
                maintenance=[ir.MaintenanceSummary(
                    site=ir.MaintenanceSite(target=target), invocations=1,
                    search_and_apply_nanos=0,
                ) for target in targets],
            ),
        )
        validate(response)
        decoded = ir.RunProgramResponse.from_binary(response.to_binary())
        self.assertEqual(decoded, response)
        self.assertEqual([row.site.target for row in decoded.profile.maintenance], targets)
        for row in decoded.profile.maintenance:
            self.assertTrue(row.has_field("search_and_apply_nanos"))
            self.assertFalse(row.has_field("merge_nanos"))

    def test_maintenance_requires_site_arm_path_and_positive_invocations(self):
        invalid = [
            ir.MaintenanceSummary(invocations=1),
            ir.MaintenanceSummary(site=ir.MaintenanceSite(), invocations=1),
            ir.MaintenanceSite(),
            # Unknown oneof field 5 is not a recognized site, even at index zero.
            ir.MaintenanceSite.from_binary(b"\x28\x00"),
            ir.StaticCommandPath(),
            ir.MaintenanceSummary(site=ir.MaintenanceSite(
                target=Oneof("command", ir.StaticCommandPath()),
            ), invocations=1),
            ir.MaintenanceSummary(site=ir.MaintenanceSite(target=Oneof("declaration", 0))),
        ]
        for message in invalid:
            with self.subTest(message=message), self.assertRaises(ValidationError):
                validate(message)

    def test_duplicate_maintenance_sites_are_rejected(self):
        for target in (
            Oneof("command", ir.StaticCommandPath(path=[2, 1])),
            Oneof("declaration", 0), Oneof("sort", 0), Oneof("ruleset", 0),
        ):
            profile = ir.ProfileSummary(maintenance=[
                ir.MaintenanceSummary(site=ir.MaintenanceSite(target=target), invocations=1),
                ir.MaintenanceSummary(
                    site=ir.MaintenanceSite(target=target), invocations=2, merge_nanos=5,
                ),
            ])
            with self.subTest(target=target), self.assertRaises(ValidationError):
                validate(profile)

    def test_maintenance_site_bounds_need_the_submitted_program(self):
        # No request Program is present in a response. These are structurally
        # valid sites; an adapter must separately check bounds and path kinds.
        for target in (
            Oneof("command", ir.StaticCommandPath(path=[99, 88])),
            Oneof("declaration", 99), Oneof("sort", 99), Oneof("ruleset", 99),
        ):
            validate(ir.ProfileSummary(maintenance=[ir.MaintenanceSummary(
                site=ir.MaintenanceSite(target=target), invocations=1,
            )]))

    def test_profile_preserves_a_failed_request_prefix(self):
        response = ir.RunProgramResponse(
            ruleset_publication=ir.RulesetPublication(),
            outputs=[ir.CommandOutput(
                kind=Oneof("run", ir.RunOutcome(updated=True)),
                location=ir.CommandLocation(path=[0]),
            )],
            error=ir.Error(
                code=ir.ErrorCode.PROOF_FAILED, message="missing witness",
                location=ir.CommandLocation(path=[1]),
                proof_failure=ir.ProofFailure(
                    reason=ir.ProofFailureReason.QUERY_DID_NOT_MATCH,
                ),
            ),
            profile=ir.ProfileSummary(
                complete=False,
                runs=[ir.RunSummary(command_path=[0], invocations=1, merge_nanos=0)],
                maintenance=[ir.MaintenanceSummary(
                    site=ir.MaintenanceSite(target=Oneof(
                        "command", ir.StaticCommandPath(path=[1]),
                    )),
                    invocations=2,
                )],
            ),
        )
        validate(response)
        self.assertEqual(ir.RunProgramResponse.from_binary(response.to_binary()), response)
        response.profile.complete = True
        with self.assertRaises(ValidationError):
            validate(response)

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
