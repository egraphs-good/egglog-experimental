"""Actual-report wire shapes and validation, independently of native execution."""

import unittest

from protobuf import Oneof
from protovalidate import ValidationError, validate

from gen.python.egglog.v1 import egglog_pb as ir


class ReportSchemaTests(unittest.TestCase):
    def test_rule_attribution_position_keeps_tag_three(self):
        attribution = ir.RuleAttribution(
            root=ir.RulesetRef(kind=Oneof("name", "root")),
            children=[1, 2], position=3,
        )
        validate(attribution)
        self.assertEqual(attribution.to_binary(), bytes.fromhex("0a061204726f6f74120201021803"))
        self.assertEqual(ir.RuleAttribution.from_binary(attribution.to_binary()), attribution)

    def test_duration_preserves_native_range(self):
        for seconds, nanos in ((0, 0), (0, 600), (2**64 - 1, 999_999_999)):
            value = ir.ReportDuration(seconds=seconds, nanos=nanos)
            validate(value)
            self.assertEqual(type(value).from_binary(value.to_binary()), value)
        with self.assertRaises(ValidationError):
            validate(ir.ReportDuration(nanos=1_000_000_000))

    def test_direction_rows_are_distinct_and_presence_is_paired(self):
        rows = [
            ir.RuleDurationEntry(
                rule=0, direction=direction, native_name=name,
                value=ir.ReportDuration(nanos=600),
            )
            for direction, name in (
                (ir.NativeRuleDirection.FORWARD, "forward"),
                (ir.NativeRuleDirection.REVERSE, "reverse"),
            )
        ]
        report = ir.NativeRunReport(can_stop=True, search_and_apply_time_per_rule=rows)
        validate(report)
        self.assertEqual(type(report).from_binary(report.to_binary()), report)
        for row in (
            ir.RuleDurationEntry(rule=0, value=ir.ReportDuration()),
            ir.RuleDurationEntry(direction=ir.NativeRuleDirection.SINGLE, value=ir.ReportDuration()),
            ir.RuleDurationEntry(rule=0, direction=0, value=ir.ReportDuration()),
            ir.RuleDurationEntry(),
        ):
            with self.subTest(row=row), self.assertRaises(ValidationError):
                validate(row)
        with self.assertRaises(ValidationError):
            validate(ir.NativeRunReport(search_and_apply_time_per_rule=[rows[0], rows[0]]))

    def test_complete_maps_do_not_require_the_same_keys(self):
        report = ir.NativeRunReport(
            can_stop=True,
            search_and_apply_time_per_rule=[
                ir.RuleDurationEntry(native_name="query", value=ir.ReportDuration())
            ],
            num_matches_per_rule=[],
            merge_time_per_ruleset=[
                ir.RulesetDurationEntry(native_name="", value=ir.ReportDuration())
            ],
        )
        validate(report)
        self.assertEqual(type(report).from_binary(report.to_binary()), report)

    def test_plans_preserve_optional_stats_and_check_local_bounds(self):
        stage = ir.ReportStage(
            kind=Oneof("intersect", ir.ReportIntersect(scans=[
                ir.ReportScan(table="t", columns=[ir.ReportColumn(variable="x", column=-1)])
            ])),
            next=[1],
        )
        final = ir.ReportStage(kind=Oneof("fused_intersect", ir.ReportFusedIntersect(
            cover=ir.ReportScan(table="u"), to_intersect=[]
        )))
        plan = ir.ReportPlan(stages=[stage, final])
        validate(plan)
        decoded = type(plan).from_binary(plan.to_binary())
        self.assertEqual(decoded, plan)
        self.assertIsNone(decoded.stages[0].stats)
        for invalid in (
            ir.ReportPlan(stages=[stage]),
            ir.ReportPlan(stages=[ir.ReportStage()]),
            ir.ReportPlan(stages=[ir.ReportStage(kind=Oneof(
                "intersect", ir.ReportIntersect(scans=[ir.ReportScan()])
            ))]),
            ir.ReportPlan(stages=[ir.ReportStage(kind=Oneof(
                "fused_intersect", ir.ReportFusedIntersect()
            ))]),
        ):
            with self.subTest(invalid=invalid), self.assertRaises(ValidationError):
                validate(invalid)
        for plan in (None, ir.ReportPlan()):
            report = ir.NativeRuleReport(plan=plan, search_and_apply_time=ir.ReportDuration())
            validate(report)
            self.assertEqual(type(report).from_binary(report.to_binary()).plan, plan)

    def test_statistics_is_an_observation_and_detail_is_control_only(self):
        report = ir.NativeRunReport(can_stop=True)
        statistics = ir.CommandOutput(
            kind=Oneof("statistics", report), location=ir.CommandLocation(path=[0, 0], iterations=[0])
        )
        response = ir.RunProgramResponse(
            outputs=[statistics], ruleset_publication=ir.RulesetPublication()
        )
        validate(response)
        self.assertEqual(type(response).from_binary(response.to_binary()), response)
        statistics.run_report = report
        with self.assertRaises(ValidationError):
            validate(response)
        output = ir.CommandOutput(
            kind=Oneof("run", ir.RunOutcome(can_stop=True)),
            location=ir.CommandLocation(path=[0]), run_report=report,
        )
        validate(output)
        output.run_report.updated = True
        with self.assertRaises(ValidationError):
            validate(output)
        command = ir.Command(kind=Oneof("fail", ir.Command(kind=Oneof("stats", ir.Unit()))))
        validate(command)
        self.assertEqual(type(command).from_binary(command.to_binary()), command)

    def test_all_report_rule_references_use_response_catalog(self):
        report = ir.NativeRunReport(
            can_stop=True, num_matches_per_rule=[ir.RuleCountEntry(
                rule=0, direction=ir.NativeRuleDirection.SINGLE, native_name="r", value=1
            )]
        )
        response = ir.RunProgramResponse(
            outputs=[ir.CommandOutput(
                kind=Oneof("statistics", report), location=ir.CommandLocation(path=[0])
            )], ruleset_publication=ir.RulesetPublication()
        )
        with self.assertRaises(ValidationError):
            validate(response)
        response.rules.append(ir.RuleAttribution(root=ir.RulesetRef(kind=Oneof("name", "kept"))))
        validate(response)
        response.outputs[0].kind = Oneof("run", ir.RunOutcome(can_stop=True))
        response.outputs[0].run_report = report
        validate(response)
        response.rules.clear()
        with self.assertRaises(ValidationError):
            validate(response)


if __name__ == "__main__":
    unittest.main()
