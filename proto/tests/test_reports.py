"""Actual-report wire shapes and validation, independently of native execution."""

import unittest

from protobuf import Oneof
from protovalidate import ValidationError, validate

from gen.python.egglog.v1 import egglog_pb as ir


class ReportSchemaTests(unittest.TestCase):
    def test_success_and_error_frames_are_exclusive_with_error_only_origins(self):
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

    def test_response_files_belong_only_to_the_one_located_error(self):
        for located, file_index, files, accepted in (
            (False, 0, [], True),
            (False, 0, [ir.SourceFile(name="unused")], False),
            (True, 0, [ir.SourceFile(name="used")], True),
            (True, 1, [ir.SourceFile(name="used")], False),
            (True, 0, [], False),
            (True, 0, [ir.SourceFile(name="used"), ir.SourceFile(name="unused")], False),
        ):
            error = ir.Error(code=ir.ErrorCode.RUNTIME_FAILURE, message="failed")
            if located:
                error.span = ir.Span(file=file_index)
            frame = ir.RunProgramResponse(result=Oneof("error", error), files=files)
            with self.subTest(located=located, file_index=file_index, files=len(files)):
                if accepted:
                    validate(frame)
                else:
                    with self.assertRaises(ValidationError):
                        validate(frame)
        with self.assertRaises(ValidationError):
            validate(ir.RunProgramResponse(
                result=Oneof("output", ir.RunProgramOutput()), files=[ir.SourceFile(name="unused")],
            ))

    def test_source_locations_belong_to_inputs_not_success_or_snapshot_data(self):
        program = ir.Program(
            sorts=[ir.Sort(kind=Oneof("primitive", ir.PrimitiveSortRef(name="i64")))],
            nodes=[ir.Node(kind=Oneof("primitive_value", ir.PrimitiveValue(value=Oneof("i64", 1))))],
            declarations=[ir.Declaration(kind=Oneof("function", ir.Function(name="f")))],
            commands=[ir.Command(kind=Oneof("action", ir.Action(kind=Oneof("term", 0))))],
            rulesets=[ir.RulesetBinding(value=ir.Ruleset(rules=[ir.Rule(
                kind=Oneof("rule", ir.RuleBody(head=[ir.Action(kind=Oneof("term", 0))])),
                eval_mode=ir.RuleEvalMode.SEMINAIVE,
            )]))],
        )
        options = ir.EGraphOptions(cost_sort=0)
        validate(ir.EGraphSnapshot(options=options, program=program))
        located = ir.Program.from_binary(program.to_binary())
        located.files.append(ir.SourceFile(name="input.egg", contents="x"))
        located.nodes[0].span = ir.Span(end=1)
        validate(located)
        for target in (
            lambda p: p.sorts[0], lambda p: p.nodes[0], lambda p: p.declarations[0],
            lambda p: p.commands[0], lambda p: p.commands[0].kind.value,
            lambda p: p.rulesets[0].value.rules[0],
            lambda p: p.rulesets[0].value.rules[0].kind.value.head[0],
        ):
            observed = ir.Program.from_binary(program.to_binary())
            target(observed).span = ir.Span()
            with self.assertRaises(ValidationError):
                validate(ir.EGraphSnapshot(options=options, program=observed))
        with self.assertRaises(ValidationError):
            validate(ir.EGraphSnapshot(options=options, program=located))
        with self.assertRaises(ValidationError):
            validate(ir.RunProgramOutput(nodes=located.nodes, sorts=located.sorts))

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
