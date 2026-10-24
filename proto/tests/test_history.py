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
        program = ir.Program(
            sorts=[ir.Sort(kind=Oneof("eq", "E"))],
            declarations=[ir.Declaration(kind=Oneof("eq_sort", ir.EqSort(name="E")))],
            nodes=[ir.Node(kind=Oneof("union", ir.Union())) for _ in range(2)],
            rules=[ir.Rule(
                kind=Oneof("rule", ir.RuleBody(query=[0], head=[ir.Action(kind=Oneof("term", 1))])),
                eval_mode=ir.RuleEvalMode.SEMINAIVE,
            )],
            commands=[
                ir.Command(kind=Oneof("action", ir.Action(kind=Oneof("term", 0)))),
                ir.Command(kind=Oneof("freeze", ir.Freeze())),
                ir.Command(kind=Oneof("add_rules", ir.AddRules(group="g", rules=[0, 0]))),
                ir.Command(kind=Oneof("run", ir.Run(groups=["g"]))),
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
                             ["action", "freeze", "add_rules", "run"])
            self.assertEqual(decoded.rules[0].kind.value.query, [0])
            self.assertEqual(decoded.rules[0].kind.value.head[0].kind.value, 1)
            self.assertEqual(len(decoded.nodes), 2)

    def test_exported_history_uses_ordinary_program_validation(self):
        validate(ir.Program())
        for invalid in (
            ir.Program(rules=[ir.Rule()]),
            ir.Program(commands=[ir.Command(kind=Oneof("add_rules", ir.AddRules(rules=[0])))]),
        ):
            with self.subTest(program=invalid), self.assertRaises(ValidationError):
                validate(invalid)


if __name__ == "__main__":
    unittest.main()
