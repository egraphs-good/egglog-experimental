"""Actual-report wire shapes and validation, independently of native execution."""

import unittest

from protobuf import Oneof
from protovalidate import ValidationError, validate

from gen.python.egglog.v1 import egglog_pb as ir


class ReportSchemaTests(unittest.TestCase):
    def test_success_and_error_frames_are_exclusive_with_authored_context(self):
        output = ir.RunProgramOutput(outputs=[ir.CommandOutput(
            kind=Oneof("run", ir.RunResult(updated=True)), location=ir.CommandLocation(path=[0]),
        )])
        frames = [
            ir.RunProgramResponse(result=Oneof("output", output)),
            ir.RunProgramResponse(result=Oneof("error", ir.Error(
                code=ir.ErrorCode.RUNTIME_FAILURE, message="failed",
                location=ir.CommandLocation(path=[1]),
                context=ir.Program(commands=[ir.Command(kind=Oneof("action", ir.Action(
                    kind=Oneof("panic", "failed"),
                )))]),
                site=ir.ErrorSite(path=[5, 0, 1]),
            ))),
        ]
        for frame in frames:
            validate(frame)
            self.assertEqual(type(frame).from_binary(frame.to_binary()), frame)
            self.assertEqual(type(frame).from_json(frame.to_json()), frame)
        with self.assertRaises(ValidationError):
            validate(ir.RunProgramResponse())
        complete = ir.RunProgramResponse(result=Oneof("output", ir.RunProgramOutput()))
        validate(complete)
        self.assertEqual(complete.to_binary(), b"\x0a\x00")

    def test_error_site_requires_its_context_and_local_node_bounds(self):
        context = ir.Program(
            sorts=[ir.Sort(kind=Oneof("primitive", ir.PrimitiveSortRef(name="i64")))],
            nodes=[ir.Node(kind=Oneof("primitive_value", ir.PrimitiveValue(value=Oneof("i64", 1))))],
        )
        for program, site, accepted in (
            (None, None, True),
            (context, None, True),
            (None, ir.ErrorSite(path=[2, 0]), False),
            (context, ir.ErrorSite(), False),
            (context, ir.ErrorSite(path=[2, 0]), True),
            (context, ir.ErrorSite(path=[2, 0], node_id=0), True),
            (context, ir.ErrorSite(path=[2, 0], node_id=1), False),
        ):
            error = ir.Error(
                code=ir.ErrorCode.RUNTIME_FAILURE, message="failed", context=program, site=site,
            )
            with self.subTest(context=program is not None, site=site):
                if accepted:
                    validate(error)
                    self.assertEqual(ir.Error.from_binary(error.to_binary()), error)
                    self.assertEqual(ir.Error.from_json(error.to_json()), error)
                else:
                    with self.assertRaises(ValidationError):
                        validate(error)

    def test_error_context_reuses_program_arenas_and_existing_code_records(self):
        program = ir.Program(
            sorts=[
                ir.Sort(kind=Oneof("primitive", ir.PrimitiveSortRef(name="i64"))),
                ir.Sort(kind=Oneof("eq", "E")),
            ],
            nodes=[ir.Node(kind=Oneof("primitive_value", ir.PrimitiveValue(value=Oneof("i64", 1))))],
            constructors=[ir.Constructor(name="C", output=1)],
            functions=[ir.Function(name="f")],
            relations=[ir.Relation(name="R")],
            user_defined_primitives=[ir.UserDefinedPrimitive(name="p", body=0)],
            commands=[ir.Command(kind=Oneof("action", ir.Action(kind=Oneof("term", 0))))],
            rulesets=[ir.RulesetBinding(value=ir.Ruleset(rules=[ir.Rule(
                kind=Oneof("rule", ir.RuleBody(actions=[ir.Action(kind=Oneof("term", 0))])),
                eval_mode=ir.RuleEvalMode.SEMINAIVE,
            )]))],
        )
        error = ir.Error(
            code=ir.ErrorCode.RUNTIME_FAILURE, message="failed", context=program,
            site=ir.ErrorSite(path=[7, 0, 2, 1, 0, 1, 3, 0], node_id=0),
        )
        validate(error)
        self.assertEqual(ir.Error.from_binary(error.to_binary()), error)
        self.assertEqual(error.context.rulesets[0].value.rules[0].kind.value.actions[0].kind.value, 0)
        validate(ir.EGraphSnapshot(options=ir.EGraphOptions(cost_sort=0), program=program))
        validate(ir.RunProgramOutput(nodes=program.nodes, sorts=program.sorts))

    def test_small_run_result_has_only_control_flags(self):
        for result in (
            ir.RunResult(), ir.RunResult(updated=True), ir.RunResult(can_stop=True),
        ):
            validate(result)
            self.assertEqual(type(result).from_binary(result.to_binary()), result)
        with self.assertRaises(ValidationError):
            validate(ir.RunResult(updated=True, can_stop=True))

    def test_diagnostic_is_one_opaque_document_at_any_observation_depth(self):
        diagnostic = ir.Diagnostic(
            format="application/vnd.egglog.run-report+json",
            content=b'{"iterations":[],"num_matches_per_rule":{}}',
        )
        for location in (
            ir.CommandLocation(path=[0]),
            ir.CommandLocation(path=[0, 1], iterations=[2]),
        ):
            output = ir.CommandOutput(kind=Oneof("diagnostic", diagnostic), location=location)
            validate(output)
            self.assertEqual(type(output).from_binary(output.to_binary()), output)
            self.assertEqual(type(output).from_json(output.to_json()), output)
        with self.assertRaises(ValidationError):
            validate(ir.Diagnostic(content=b"backend text"))

    def test_run_then_diagnostic_share_a_location_without_duplicate_flags(self):
        location = ir.CommandLocation(path=[0])
        response = ir.RunProgramOutput(outputs=[
            ir.CommandOutput(kind=Oneof("run", ir.RunResult(updated=True)), location=location),
            ir.CommandOutput(kind=Oneof("diagnostic", ir.Diagnostic(
                format="text/plain", content=b"backend-specific detail",
            )), location=location),
        ])
        validate(response)
        self.assertEqual(type(response).from_binary(response.to_binary()), response)

    def test_diagnostics_default_off_and_explain_selects_groups(self):
        request = ir.RunProgramRequest(egraph_id=7, program=ir.Program())
        self.assertFalse(request.diagnostics)
        request.diagnostics = True
        self.assertEqual(type(request).from_binary(request.to_binary()), request)
        command = ir.Command(kind=Oneof("explain", ir.Explain(groups=["", "unknown", "a"])))
        validate(command)
        self.assertEqual(type(command).from_binary(command.to_binary()), command)

    def test_diagnostic_bytes_preserve_non_utf8_backend_content(self):
        diagnostic = ir.Diagnostic(format="application/octet-stream", content=b"\x00\xff\x80")
        validate(diagnostic)
        self.assertEqual(type(diagnostic).from_binary(diagnostic.to_binary()), diagnostic)
        self.assertEqual(type(diagnostic).from_json(diagnostic.to_json()), diagnostic)


if __name__ == "__main__":
    unittest.main()
