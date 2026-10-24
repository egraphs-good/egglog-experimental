"""Repeated-tail wire/CEL checks, not generic call matching or execution."""

import json
import unittest

from protobuf import Oneof
from protovalidate import ValidationError, validate

from gen.python.egglog.v1 import egglog_pb as ir


def signature_program(pattern):
    """Own the signature's sort arena and binder."""
    return ir.BuiltinCatalog(
        sorts=[
            ir.Sort(kind=Oneof("application", ir.SortApplication(name="i64"))),
            ir.Sort(kind=Oneof("var", 0)),
            ir.Sort(kind=Oneof("var", 1)),
            ir.Sort(kind=Oneof("application", ir.SortApplication(name="Map", args=[1, 2]))),
            ir.Sort(kind=Oneof("var", 2)),
        ],
        primitive_sorts=[ir.PrimitiveSort(name="i64"), ir.PrimitiveSort(name="Map", arity=2)],
        primitives=[ir.Primitive(name="test.pairs", typing=Oneof("signature", ir.GenericSignature(
            type_params=["K", "V"], inputs=[ir.Arg(name="prefix", sort=0)], output=3,
            varargs=[ir.Arg(name=f"tail{i}", sort=sort) for i, sort in enumerate(pattern)],
        )))],
    )


class SignatureSchemaTests(unittest.TestCase):
    def test_tail_width_and_order_survive_wire_roundtrip(self):
        for pattern in [[], [1], [1, 2], [1, 1], [1, 2, 1]]:
            with self.subTest(pattern=pattern):
                program = signature_program(pattern)
                validate(program)
                decoded = ir.BuiltinCatalog.from_binary(program.to_binary())
                self.assertEqual(decoded, program)
                self.assertEqual(
                    [arg.sort for arg in decoded.primitives[-1].typing.value.varargs],
                    pattern,
                )

    def test_every_tail_position_checks_sort_bounds_and_direct_binder(self):
        for position in range(3):
            for invalid_sort in [4, 99]:
                with self.subTest(position=position, invalid_sort=invalid_sort):
                    pattern = [1, 2, 1]
                    pattern[position] = invalid_sort
                    with self.assertRaises(ValidationError):
                        validate(signature_program(pattern))
        program = signature_program([1, 2])
        program.primitives[-1].typing.value.type_params = []
        with self.assertRaises(ValidationError):
            validate(program)



    def test_old_zero_tail_canonical_bytes_are_unchanged(self):
        # Captured from the published S805ce71 singular-field Python bindings.
        old = bytes.fromhex("12031201781800")
        signature = ir.GenericSignature(inputs=[ir.Arg(sort=0, name="x")], output=0)
        self.assertEqual(signature.varargs, [])
        self.assertEqual(signature.to_binary(), old)
        self.assertEqual(ir.GenericSignature.from_binary(old), signature)

    def test_old_one_tail_canonical_bytes_are_unchanged(self):
        old = bytes.fromhex("0a0154120a0801120670726566697818022208120676616c756573")
        signature = ir.GenericSignature(
            type_params=["T"], inputs=[ir.Arg(sort=1, name="prefix")], output=2,
            varargs=[ir.Arg(sort=0, name="values")],
        )
        self.assertEqual(signature.to_binary(), old)
        self.assertEqual(ir.GenericSignature.from_binary(old), signature)

    def test_protojson_tail_is_an_array_not_the_old_object(self):
        signature = ir.GenericSignature(output=0, varargs=[ir.Arg(sort=1), ir.Arg(sort=2)])
        encoded = signature.to_json()
        self.assertEqual(json.loads(encoded)["varargs"], [{"sort": 1}, {"sort": 2}])
        self.assertEqual(ir.GenericSignature.from_json(encoded), signature)
        with self.assertRaises(TypeError):
            ir.GenericSignature.from_json('{"output":0,"varargs":{"sort":1}}')

    def test_intended_draft_incompatibility_old_receiver_loses_group_width(self):
        # Actual old S805ce71 Python decoder outputs, recorded before codegen.
        # Old receivers are unsafe: these two-position patterns become one.
        # Rust's singular message decoder merges occurrences instead of
        # Python's observed last occurrence, also losing the group boundary.
        witnesses = [
            ("0a015418012208120676616c7565732208120676616c756573", "0a015418012208120676616c756573", [0, 0]),
            ("0a015418012207080112036b657922090802120576616c7565", "0a0154180122090802120576616c7565", [1, 2]),
        ]
        for group_hex, old_receiver_hex, pattern in witnesses:
            with self.subTest(pattern=pattern):
                group = bytes.fromhex(group_hex)
                decoded = ir.GenericSignature.from_binary(group)
                self.assertEqual([arg.sort for arg in decoded.varargs], pattern)
                self.assertEqual(decoded.to_binary(), group)
                collapsed = ir.GenericSignature.from_binary(bytes.fromhex(old_receiver_hex))
                self.assertEqual(len(collapsed.varargs), 1)
                self.assertNotEqual(decoded, collapsed)


if __name__ == "__main__":
    unittest.main()
