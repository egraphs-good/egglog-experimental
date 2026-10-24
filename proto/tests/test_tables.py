"""Table observation wire shapes, not table installation or execution."""

import json
import unittest

from protobuf import Oneof
from protovalidate import ValidationError, validate

from gen.python.egglog.v1 import egglog_pb as ir


def table_response(rows):
    """Own both response arenas and the required output locations."""
    return ir.RunProgramResponse(
        sorts=[
            ir.Sort(kind=Oneof("family", ir.HostSort(name="Unit"))),
            ir.Sort(kind=Oneof("eq", "E")),
        ],
        nodes=[ir.Node(sort_id=0, kind=Oneof(
            "primitive_value", ir.PrimitiveValue(value=Oneof("unit", ir.Unit()))
        ))],
        outputs=[ir.CommandOutput(
            kind=Oneof("printed_function", ir.PrintedFunction(table="f", rows=rows)),
            location=ir.CommandLocation(path=[0]),
        )],
    )


class TableSchemaTests(unittest.TestCase):
    def test_reflective_prefix_is_optional_table_metadata_including_empty(self):
        for tag, table in (
            ("constructor", ir.Constructor(name="C", output=0)),
            ("function", ir.Function(name="f", output=0)),
            ("relation", ir.Relation(name="R")),
        ):
            for prefix in [None] + [
                Oneof(arm, name)
                for arm in ("public_alias", "default_name")
                for name in ("", table.name, "other-prefix")
            ]:
                declaration = ir.Declaration(kind=Oneof(tag, table), table_name=prefix)
                validate(declaration)
                for decoded in (
                    ir.Declaration.from_binary(declaration.to_binary()),
                    ir.Declaration.from_json(declaration.to_json()),
                ):
                    self.assertEqual(decoded, declaration)
                    self.assertEqual(decoded.table_name, prefix)
        with self.assertRaises(ValidationError):
            validate(ir.Declaration(kind=Oneof("eq_sort", ir.EqSort(name="S")), table_name=Oneof("public_alias", "")))

    def test_parent_key_is_nonempty_when_present_and_preserves_pendingness(self):
        for parent in (None, "Pending"):
            sort = ir.EqSort(name="S", uf_parent=parent)
            validate(sort)
            self.assertEqual(ir.EqSort.from_binary(sort.to_binary()), sort)
            self.assertEqual(sort.has_field("uf_parent"), parent is not None)
        with self.assertRaises(ValidationError):
            validate(ir.EqSort(name="S", uf_parent=""))

    def test_hidden_is_semantic_table_metadata_only(self):
        for tag, table in (
            ("constructor", ir.Constructor(name="C", output=0)),
            ("function", ir.Function(name="f", output=0)),
        ):
            declaration = ir.Declaration(kind=Oneof(tag, table), hidden=True)
            validate(declaration)
            self.assertTrue(ir.Declaration.from_binary(declaration.to_binary()).hidden)
            self.assertTrue(ir.Declaration.from_json(declaration.to_json()).hidden)
        for tag, value in (
            ("eq_sort", ir.EqSort(name="E")),
            ("relation", ir.Relation(name="R")),
            ("primitive", ir.Primitive(name="p", body=0)),
            ("host_sort_family", ir.HostSortFamily(name="F")),
            ("host_primitive", ir.HostPrimitive(name="h", typing=Oneof("signature", ir.GenericSignature(output=0)))),
        ):
            with self.subTest(tag=tag), self.assertRaises(ValidationError):
                validate(ir.Declaration(kind=Oneof(tag, value), hidden=True))

    def test_limit_presence_distinguishes_all_zero_and_positive(self):
        for limit, encoded in (
            (None, "4a030a0143"),
            (0, "4a050a01431000"),
            (1, "4a050a01431001"),
            (2**64 - 1, "4a0e0a014310ffffffffffffffffff01"),
        ):
            with self.subTest(limit=limit):
                command = ir.Command(kind=Oneof(
                    "print_function", ir.PrintFunction(table="C", max_rows=limit)
                ))
                validate(command)
                self.assertEqual(command.to_binary(), bytes.fromhex(encoded))
                for decoded in (
                    ir.Command.from_binary(command.to_binary()),
                    ir.Command.from_json(command.to_json()),
                ):
                    self.assertEqual(decoded, command)
                    print_function = decoded.kind.value
                    self.assertEqual(print_function.has_field("max_rows"), limit is not None)
                    self.assertEqual(print_function.max_rows, 0 if limit is None else limit)
                payload = json.loads(command.to_json())["printFunction"]
                if limit is None:
                    self.assertNotIn("maxRows", payload)
                else:
                    self.assertEqual(int(payload["maxRows"]), limit)

    def test_each_cell_arm_preserves_index_zero(self):
        for name, encoded in (("term", b"\x08\x00"), ("unavailable_sort", b"\x10\x00")):
            with self.subTest(name=name):
                cell = ir.TableCell(kind=Oneof(name, 0))
                validate(cell)
                self.assertEqual(cell.to_binary(), encoded)
                self.assertEqual(ir.TableCell.from_binary(encoded), cell)
                validate(table_response([ir.FunctionRow(args=[cell], output=cell)]))

    def test_mixed_cells_preserve_positions_multiplicity_and_subsumption(self):
        available = ir.TableCell(kind=Oneof("term", 0))
        unavailable = ir.TableCell(kind=Oneof("unavailable_sort", 1))
        response = table_response([
            ir.FunctionRow(args=[available, unavailable, available], output=unavailable, subsumed=True),
            ir.FunctionRow(
                args=[available, unavailable, available],
                output=ir.TableCell(kind=Oneof("term", 1)),
            ),
        ])
        response.nodes.append(ir.Node(sort_id=1, kind=Oneof("call", ir.Call(func="C"))))
        validate(response)
        for decoded in (
            ir.RunProgramResponse.from_binary(response.to_binary()),
            ir.RunProgramResponse.from_json(response.to_json()),
        ):
            self.assertEqual(decoded, response)
            self.assertEqual(decoded.outputs[0].kind.value.rows[0].args, [available, unavailable, available])
            self.assertTrue(decoded.outputs[0].kind.value.rows[0].subsumed)

    def test_cell_kind_and_row_output_are_required(self):
        valid = ir.TableCell(kind=Oneof("term", 0))
        for row in (
            ir.FunctionRow(args=[ir.TableCell()], output=valid),
            ir.FunctionRow(args=[valid], output=ir.TableCell()),
            ir.FunctionRow(args=[valid]),
        ):
            with self.subTest(row=row), self.assertRaises(ValidationError):
                validate(table_response([row]))

    def test_argument_and_output_references_use_the_correct_arena(self):
        valid = ir.TableCell(kind=Oneof("term", 0))
        for name, index in (("term", 1), ("unavailable_sort", 2)):
            invalid = ir.TableCell(kind=Oneof(name, index))
            for row in (
                ir.FunctionRow(args=[invalid], output=valid),
                ir.FunctionRow(args=[valid], output=invalid),
            ):
                with self.subTest(name=name, row=row), self.assertRaises(ValidationError):
                    validate(table_response([row]))

    def test_unavailable_sort_still_must_be_closed(self):
        response = table_response([ir.FunctionRow(output=ir.TableCell(kind=Oneof("unavailable_sort", 1)))])
        response.sorts[1] = ir.Sort(kind=Oneof("var", 0))
        with self.assertRaises(ValidationError):
            validate(response)

    def test_empty_selected_rows_need_no_cell_nodes(self):
        response = table_response([])
        response.nodes.clear()
        response.sorts.clear()
        validate(response)
        self.assertEqual(ir.RunProgramResponse.from_binary(response.to_binary()), response)

    def test_shared_bounds_rule_still_checks_table_statistics(self):
        response = table_response([])
        response.outputs.append(ir.CommandOutput(
            kind=Oneof("table_stats", ir.TableStatsResult(stats=[
                ir.TableStats(table="f", columns=[ir.ColumnStats(sort=1)])
            ])),
            location=ir.CommandLocation(path=[1]),
        ))
        validate(response)
        response.outputs[1].kind.value.stats[0].columns[0].sort = 2
        with self.assertRaises(ValidationError):
            validate(response)


if __name__ == "__main__":
    unittest.main()
