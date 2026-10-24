"""Actual-report wire shapes and validation, independently of native execution."""

import unittest

from protobuf import Oneof
from protovalidate import ValidationError, validate

from gen.python.egglog.v1 import egglog_pb as ir


class ReportSchemaTests(unittest.TestCase):
    def test_success_and_error_frames_are_exclusive_and_keep_origins(self):
        output = ir.RunProgramOutput(outputs=[ir.CommandOutput(
            kind=Oneof("run", ir.RunResult(updated=True)), location=ir.CommandLocation(path=[0]),
        )])
        frames = [
            ir.RunProgramResponse(result=Oneof("output", output)),
            ir.RunProgramResponse(result=Oneof("error", ir.Error(
                code=ir.ErrorCode.RUNTIME_FAILURE, message="failed", span=ir.Span(start=0, end=1),
                location=ir.CommandLocation(path=[1]),
            )), files=[ir.SourceFile(name="rule.egg", contents="x")]),
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
