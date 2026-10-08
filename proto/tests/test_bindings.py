"""Presentation wire/CEL checks, not callable execution or binding installation."""

import unittest

from protobuf import Oneof
from protovalidate import ValidationError, validate

from gen.python.egglog.v1 import egglog_pb as ir


def constant_program(core, **view_fields):
    """Own every sort/body reference needed by the concrete declaration fixture."""
    return ir.Program(
        ir_version=1,
        sorts=[
            ir.Sort(kind=Oneof("family", ir.HostSort(name="i64"))),
            ir.Sort(kind=Oneof("eq", "Box")),
        ],
        nodes=[ir.Node(sort_id=0, kind=Oneof("primitive_value", ir.PrimitiveValue(value=Oneof("i64", 7))))],
        declarations=[
            ir.Declaration(kind=Oneof("eq_sort", ir.EqSort(name="Box"))),
            ir.Declaration(
                kind=core,
                bindings=ir.CallableBindings(python=ir.PythonBindings(views=[
                    ir.PythonCallable(**{"kind": 7, "path": ["example", "C"], **view_fields})
                ])),
            ),
        ],
    )


class BindingSchemaTests(unittest.TestCase):
    def test_constant_roundtrips_on_concrete_nullary_callables(self):
        declarations = [
            Oneof("constructor", ir.Constructor(name="C", output=1)),
            Oneof("function", ir.Function(name="C", output=0)),
            Oneof("primitive", ir.Primitive(name="C", output=0, body=0)),
            Oneof("relation", ir.Relation(name="C")),
            Oneof("host_primitive", ir.HostPrimitive(
                name="host.C", typing=Oneof("signature", ir.GenericSignature(output=0)),
            )),
        ]
        for core in declarations:
            with self.subTest(core=core.field):
                program = constant_program(core)
                validate(program)
                decoded = ir.Program.from_binary(program.to_binary())
                self.assertEqual(decoded, program)
                view = decoded.declarations[1].bindings.python.views[0]
                self.assertEqual(view.kind, 7)
                self.assertEqual(view.path, ["example", "C"])

    def test_nullary_function_is_not_inferred_to_be_a_constant(self):
        core = Oneof("function", ir.Function(name="C", output=0))
        function = constant_program(core, kind=ir.PythonCallKind.FUNCTION)
        constant = constant_program(core)
        for program in (function, constant):
            validate(program)
            self.assertEqual(ir.Program.from_binary(program.to_binary()), program)
        self.assertNotEqual(function, constant)
        self.assertNotEqual(function.to_binary(), constant.to_binary())

    def test_constant_has_only_a_nonempty_qualified_path(self):
        invalid = [
            {"path": []}, {"path": ["example", ""]},
            {"owner": ir.BindingOwner(kind=Oneof("sort", 1))},
            {"receiver": 0},
            {"params": [ir.PythonParameter(core_input=0, name="unused")]},
            {"mutates": 0}, {"kind": 0}, {"kind": 99},
        ]
        for fields in invalid:
            with self.subTest(fields=fields), self.assertRaises(ValidationError):
                validate(constant_program(Oneof("function", ir.Function(name="C", output=0)), **fields))

    def test_constant_rejects_inputs_tails_and_generic_binders(self):
        argument = ir.Arg(name="x", sort=0)
        declarations = [
            Oneof("constructor", ir.Constructor(name="C", inputs=[argument], output=1)),
            Oneof("function", ir.Function(name="C", inputs=[argument], output=0)),
            Oneof("primitive", ir.Primitive(name="C", inputs=[argument], output=0, body=0)),
            Oneof("relation", ir.Relation(name="C", inputs=[argument])),
            *[
                Oneof("host_primitive", ir.HostPrimitive(name="host.C", typing=Oneof("signature", signature)))
                for signature in [
                    ir.GenericSignature(inputs=[argument], output=0),
                    ir.GenericSignature(varargs=argument, output=0),
                    ir.GenericSignature(type_params=["T"], output=0),
                ]
            ],
            Oneof("host_primitive", ir.HostPrimitive(name="host.C", typing=Oneof("application", ir.FunctionApplication()))),
        ]
        for core in declarations:
            with self.subTest(core=core), self.assertRaises(ValidationError):
                validate(constant_program(core))

    def test_constant_still_checks_output_sort_references(self):
        for core in [
            Oneof("constructor", ir.Constructor(name="C", output=2)),
            Oneof("function", ir.Function(name="C", output=2)),
            Oneof("primitive", ir.Primitive(name="C", output=2, body=0)),
            Oneof("host_primitive", ir.HostPrimitive(name="host.C", typing=Oneof("signature", ir.GenericSignature(output=2)))),
        ]:
            with self.subTest(core=core), self.assertRaises(ValidationError):
                validate(constant_program(core))


if __name__ == "__main__":
    unittest.main()
