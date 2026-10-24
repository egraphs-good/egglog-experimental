"""Actual-report wire shapes and validation, independently of native execution."""

import unittest

from protobuf import Oneof
from protovalidate import ValidationError, validate

from gen.python.egglog.v1 import egglog_pb as ir


class ReportSchemaTests(unittest.TestCase):
    def test_rule_catalog_roots_must_index_response_nodes(self):
        for kind in (
            Oneof("rule", ir.RuleBody(query=[99])),
            Oneof("rule", ir.RuleBody(head=[ir.Action(kind=Oneof("term", 99))])),
            Oneof("rewrite", ir.Rewrite(lhs=99, rhs=99)),
        ):
            with self.subTest(kind=kind):
                with self.assertRaises(ValidationError):
                    validate(ir.RunProgramResponse(rules=[ir.Rule(
                        kind=kind, eval_mode=ir.RuleEvalMode.SEMINAIVE,
                    )]))

    def test_rule_catalog_retains_full_rule_values_and_response_arenas(self):
        rule = ir.Rule(
            kind=Oneof("rule", ir.RuleBody(query=[0], head=[ir.Action(kind=Oneof("term", 0))])),
            eval_mode=ir.RuleEvalMode.SEMINAIVE, name="diagnostic", span=ir.Span(start=0, end=1),
        )
        response = ir.RunProgramResponse(
            rules=[rule], files=[ir.SourceFile(name="rule.egg", contents="x")],
            sorts=[ir.Sort(kind=Oneof("family", ir.HostSort(name="i64")))],
            nodes=[ir.Node(kind=Oneof("primitive_value", ir.PrimitiveValue(value=Oneof("i64", 1))))],
        )
        validate(response)
        for decoded in (
            ir.RunProgramResponse.from_binary(response.to_binary()),
            ir.RunProgramResponse.from_json(response.to_json()),
        ):
            validate(decoded)
            self.assertEqual(decoded, response)
            self.assertEqual(decoded.rules[0].kind.value.query, [0])

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
            content='{"iterations":[],"num_matches_per_rule":{}}',
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
            validate(ir.Diagnostic(content="backend text"))

    def test_run_then_diagnostic_share_a_location_without_duplicate_flags(self):
        location = ir.CommandLocation(path=[0])
        response = ir.RunProgramResponse(outputs=[
            ir.CommandOutput(kind=Oneof("run", ir.RunResult(updated=True)), location=location),
            ir.CommandOutput(kind=Oneof("diagnostic", ir.Diagnostic(
                format="text/plain", content="backend-specific detail",
            )), location=location),
        ])
        validate(response)
        self.assertEqual(type(response).from_binary(response.to_binary()), response)
        self.assertEqual(ir.RunProgramResponse(), ir.RunProgramResponse.from_binary(b""))

    def test_diagnostics_default_off_and_explain_selects_groups(self):
        request = ir.RunProgramRequest(egraph_id=7, program=ir.Program())
        self.assertFalse(request.diagnostics)
        request.diagnostics = True
        self.assertEqual(type(request).from_binary(request.to_binary()), request)
        command = ir.Command(kind=Oneof("explain", ir.Explain(groups=["", "unknown", "a"])))
        validate(command)
        self.assertEqual(type(command).from_binary(command.to_binary()), command)

    def test_error_rule_reference_uses_its_chunk_local_catalog(self):
        with self.assertRaises(ValidationError):
            validate(ir.RunProgramResponse(error=ir.Error(
                code=ir.ErrorCode.PANIC, message="failed rule", rule=0,
            )))


if __name__ == "__main__":
    unittest.main()
