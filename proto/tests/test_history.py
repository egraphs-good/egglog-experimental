"""Structured audit shape, matching outcomes and independent recording choice."""

import unittest

from protobuf import Oneof
from protovalidate import ValidationError, validate

from gen.python.egglog.v1 import egglog_pb as ir


class HistorySchemaTests(unittest.TestCase):
    def test_recording_is_default_off_outside_logical_options(self):
        self.assertFalse(ir.CreateEGraphRequest().record_history)
        self.assertEqual(ir.CreateEGraphRequest().to_binary(), b"")
        self.assertEqual(ir.CreateEGraphRequest(record_history=True).to_binary(), b"\x38\x01")
        self.assertNotIn("record_history", ir.EGraphOptions.__annotations__)

    def test_request_and_actual_response_kinds_must_match(self):
        requests = [
            ("create", ir.CreateEGraphRequest(
                sorts=[ir.Sort(kind=Oneof("family", ir.HostSort(name="i64")))],
                options=ir.EGraphOptions(cost_sort=0), record_history=True,
            )),
            ("clone", ir.CloneEGraphRequest(egraph_id=1)),
            ("destroy", ir.DestroyEGraphRequest(egraph_id=1)),
            ("return_to", ir.ReturnToEGraphRequest(active_id=2, saved_id=1)),
            ("configure_resources", ir.ConfigureEGraphResourcesRequest(
                egraph_id=1, operation=Oneof("query", ir.Unit()),
            )),
            ("run_program", ir.RunProgramRequest(egraph_id=1, program=ir.Program(), profile=True)),
        ]
        responses = [
            ir.CreateEGraphResponse(egraph_id=1), ir.CloneEGraphResponse(egraph_id=2),
            ir.DestroyEGraphResponse(), ir.ReturnToEGraphResponse(),
            ir.ConfigureEGraphResourcesResponse(threads=1),
            ir.RunProgramResponse(ruleset_publication=ir.RulesetPublication()),
        ]
        for index, (kind, request) in enumerate(requests):
            for response_index, response in enumerate(responses):
                entry = ir.HistoryEntry(
                    request=Oneof(kind, request),
                    outcome=Oneof(requests[response_index][0] + "_response", response),
                )
                with self.subTest(request=kind, response=requests[response_index][0]):
                    if index == response_index:
                        validate(entry)
                        self.assertEqual(ir.HistoryEntry.from_binary(entry.to_binary()), entry)
                    else:
                        with self.assertRaises(ValidationError):
                            validate(entry)
            for outcome in [Oneof("transport_error", "rejected"), Oneof("interrupted", ir.Unit())]:
                entry = ir.HistoryEntry(request=Oneof(kind, request), outcome=outcome)
                validate(entry)
                self.assertEqual(ir.HistoryEntry.from_binary(entry.to_binary()), entry)

    def test_entry_requires_request_and_outcome_and_history_requires_resources(self):
        for entry in [ir.HistoryEntry(), ir.HistoryEntry(
            request=Oneof("clone", ir.CloneEGraphRequest(egraph_id=1)),
        )]:
            with self.assertRaises(ValidationError):
                validate(entry)
        with self.assertRaises(ValidationError):
            validate(ir.GetHistoryResponse())
        history = ir.GetHistoryResponse(
            initial_resources=ir.ConfigureEGraphResourcesResponse(threads=2, no_decomp=True),
            closed=True,
        )
        validate(history)
        self.assertEqual(ir.GetHistoryResponse.from_binary(history.to_binary()), history)

    def test_audit_preserves_invalid_requests_without_revalidating_them(self):
        invalid = ir.RunProgramRequest(program=ir.Program(rules=[ir.Rule()]))
        with self.assertRaises(ValidationError):
            validate(invalid)
        entry = ir.HistoryEntry(
            request=Oneof("run_program", invalid),
            outcome=Oneof("run_program_response", ir.RunProgramResponse(
                ruleset_publication=ir.RulesetPublication(),
                error=ir.Error(code=ir.ErrorCode.INVALID_PROGRAM, message="missing rule mode"),
            )),
        )
        validate(entry)
        self.assertEqual(ir.HistoryEntry.from_binary(entry.to_binary()), entry)


if __name__ == "__main__":
    unittest.main()
