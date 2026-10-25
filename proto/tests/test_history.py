"""Per-graph input Program history shapes, independent of native retention."""

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

    def test_get_history_selects_one_graph(self):
        for handle in (0, 1, 2**64 - 1):
            with self.subTest(handle=handle):
                request = ir.GetHistoryRequest(egraph_id=handle)
                validate(request)
                self.assertEqual(type(request).from_binary(request.to_binary()), request)

    def test_history_program_keeps_command_order_and_distinct_union_locations(self):
        rule = ir.Rule(
            kind=Oneof("rule", ir.RuleBody(query=[0], head=[ir.Action(kind=Oneof("term", 1))])),
            eval_mode=ir.RuleEvalMode.SEMINAIVE,
        )
        program = ir.Program(
            sorts=[ir.Sort(kind=Oneof("eq", "E"))],
            declarations=[ir.Declaration(kind=Oneof("eq_sort", ir.EqSort(name="E")))],
            nodes=[ir.Node(kind=Oneof("union", ir.Union())) for _ in range(2)],
            rulesets=[ir.RulesetBinding(name="g", value=ir.Ruleset(rules=[rule, rule]))],
            commands=[
                ir.Command(kind=Oneof("action", ir.Action(kind=Oneof("term", 0)))),
                ir.Command(kind=Oneof("freeze", ir.Freeze())),
                ir.Command(kind=Oneof("run", ir.Run(rulesets=[
                    ir.RulesetSelection(kind=Oneof("ruleset", ir.Ruleset(rules=[rule, rule]))),
                ]))),
            ],
        )
        validate(program)
        for decoded in (
            ir.Program.from_binary(program.to_binary()),
            ir.Program.from_json(program.to_json()),
        ):
            validate(decoded)
            self.assertEqual(decoded, program)
            self.assertEqual([command.kind.field for command in decoded.commands],
                             ["action", "freeze", "run"])
            self.assertEqual(decoded.rulesets[0].value.rules[0].kind.value.query, [0])
            self.assertEqual(decoded.rulesets[0].value.rules[0].kind.value.head[0].kind.value, 1)
            self.assertEqual(decoded.commands[2].kind.value.rulesets[0].kind.value.rules,
                             decoded.rulesets[0].value.rules)
            self.assertEqual(len(decoded.nodes), 2)

    def test_exported_history_uses_ordinary_program_validation(self):
        validate(ir.Program())
        with self.assertRaises(TypeError):
            ir.Program(rules=[])
        with self.assertRaises(ValidationError):
            validate(ir.Program(rulesets=[ir.RulesetBinding(value=ir.Ruleset(rules=[ir.Rule()]))]))



if __name__ == "__main__":
    unittest.main()
