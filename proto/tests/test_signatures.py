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
        primitives=[ir.Primitive(name="test.pairs", signature=ir.GenericSignature(
            type_param_count=2, inputs=[ir.Arg(name="prefix", sort=0)], output=3,
            varargs=[ir.Arg(name=f"tail{i}", sort=sort) for i, sort in enumerate(pattern)],
        ))],
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
                    [arg.sort for arg in decoded.primitives[-1].signature.varargs],
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
        program.primitives[-1].signature.type_param_count = 0
        with self.assertRaises(ValidationError):
            validate(program)



    def test_signature_count_has_no_labels_or_kind_constraints(self):
        signature = ir.GenericSignature(type_param_count=1, inputs=[ir.Arg(sort=1)], output=1)
        self.assertEqual(ir.GenericSignature.from_binary(signature.to_binary()), signature)
        self.assertEqual(json.loads(signature.to_json())["typeParamCount"], 1)
        with self.assertRaises(TypeError):
            ir.GenericSignature(type_params=["T"])
        with self.assertRaises(TypeError):
            ir.GenericSignature(equality_type_params=[0])
        with self.assertRaises(TypeError):
            ir.Primitive(typing=Oneof("signature", signature))
        self.assertFalse(hasattr(ir, "FunctionApplication"))

    def test_protojson_tail_is_an_array_not_the_old_object(self):
        signature = ir.GenericSignature(output=0, varargs=[ir.Arg(sort=1), ir.Arg(sort=2)])
        encoded = signature.to_json()
        self.assertEqual(json.loads(encoded)["varargs"], [{"sort": 1}, {"sort": 2}])
        self.assertEqual(ir.GenericSignature.from_json(encoded), signature)
        with self.assertRaises(TypeError):
            ir.GenericSignature.from_json('{"output":0,"varargs":{"sort":1}}')



if __name__ == "__main__":
    unittest.main()
