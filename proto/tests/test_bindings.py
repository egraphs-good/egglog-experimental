"""Declaration/presentation wire checks, not execution or binding installation."""

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
    def test_nominal_family_and_callable_names_are_distinct(self):
        nominal = ir.Declaration(kind=Oneof("eq_sort", ir.EqSort(name="Pair")))
        family = ir.Declaration(kind=Oneof("host_sort_family", ir.HostSortFamily(name="Pair", arity=2)))
        callable_ = ir.Declaration(kind=Oneof("constructor", ir.Constructor(
            name="Pair", inputs=[ir.Arg(sort=1)], output=0,
        )))
        sorts = [
            ir.Sort(kind=Oneof("eq", "Pair")),
            ir.Sort(kind=Oneof("family", ir.HostSort(name="Pair", args=[0, 0]))),
        ]
        for declarations in ([nominal, family, callable_], [callable_, family, nominal]):
            with self.subTest(declarations=declarations):
                program = ir.Program(ir_version=1, sorts=sorts, declarations=declarations)
                validate(program)
                decoded = ir.Program.from_binary(program.to_binary())
                self.assertEqual(decoded, program)
                self.assertEqual(decoded.sorts[0].kind, Oneof("eq", "Pair"))
                self.assertEqual(decoded.sorts[1].kind.field, "family")
                self.assertEqual(decoded.sorts[1].kind.value.name, "Pair")

    def test_same_namespace_resupply_still_checks_family_arity(self):
        nominal = ir.Declaration(kind=Oneof("eq_sort", ir.EqSort(name="Pair")))
        family = ir.Declaration(kind=Oneof("host_sort_family", ir.HostSortFamily(name="Pair", arity=2)))
        # Compatible resends are allowed even without an arena use. Metadata
        # compatibility and installed-name resolution remain semantic checks.
        validate(ir.Program(ir_version=1, declarations=[nominal, family, nominal, family]))
        conflict = ir.Declaration(kind=Oneof("host_sort_family", ir.HostSortFamily(name="Pair", arity=1)))
        for declarations in ([nominal, family, conflict], [conflict, nominal, family]):
            with self.subTest(declarations=declarations), self.assertRaises(ValidationError):
                validate(ir.Program(ir_version=1, declarations=declarations))

    def test_nominal_declaration_does_not_mask_bad_family_application(self):
        for width in (0, 1, 3):
            with self.subTest(width=width), self.assertRaises(ValidationError):
                validate(ir.Program(
                    ir_version=1,
                    sorts=[
                        ir.Sort(kind=Oneof("eq", "Pair")),
                        ir.Sort(kind=Oneof("family", ir.HostSort(name="Pair", args=[0] * width))),
                    ],
                    declarations=[
                        ir.Declaration(kind=Oneof("eq_sort", ir.EqSort(name="Pair"))),
                        ir.Declaration(kind=Oneof("host_sort_family", ir.HostSortFamily(name="Pair", arity=2))),
                    ],
                ))

    def test_sort_kind_wire_tags_are_unchanged(self):
        # These existing tags already distinguish identical name spellings.
        cases = [
            (ir.Sort(kind=Oneof("eq", "Pair")), b"\x0a\x04Pair"),
            (ir.Sort(kind=Oneof("family", ir.HostSort(name="Pair", args=[0, 0]))),
             b"\x12\x0a\x0a\x04Pair\x12\x02\x00\x00"),
        ]
        for sort, encoded in cases:
            with self.subTest(sort=sort):
                self.assertEqual(sort.to_binary(), encoded)
                self.assertEqual(ir.Sort.from_binary(encoded), sort)

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

    def test_constant_preserves_an_empty_final_name(self):
        for path in [[""], ["example", ""]]:
            with self.subTest(path=path):
                program = constant_program(Oneof("function", ir.Function(name="C", output=0)), path=path)
                validate(program)
                decoded = ir.Program.from_binary(program.to_binary())
                self.assertEqual(decoded, program)
                self.assertEqual(decoded.declarations[1].bindings.python.views[0].path, path)

    def test_other_python_forms_keep_nonempty_path_components(self):
        views = [
            ir.PythonCallable(kind=ir.PythonCallKind.FUNCTION, path=[""]),
            ir.PythonCallable(kind=ir.PythonCallKind.FUNCTION, path=["example", ""]),
            ir.PythonCallable(
                kind=ir.PythonCallKind.CLASS_VARIABLE, path=[""],
                owner=ir.BindingOwner(kind=Oneof("sort", 1)),
            ),
            ir.PythonCallable(
                kind=ir.PythonCallKind.METHOD, path=[""], receiver=0,
                owner=ir.BindingOwner(kind=Oneof("sort", 1)),
            ),
        ]
        for view in views:
            with self.subTest(view=view), self.assertRaises(ValidationError):
                validate(view)
        # Initializers still derive their name and deliberately have no path.
        validate(ir.PythonCallable(
            kind=ir.PythonCallKind.INITIALIZER,
            owner=ir.BindingOwner(kind=Oneof("sort", 1)),
        ))

    def test_constant_has_a_nonempty_path_and_nonempty_qualifiers(self):
        invalid = [
            {"path": []}, {"path": ["", "C"]}, {"path": ["", ""]},
            {"path": ["example", "", "C"]}, {"path": ["example", "", ""]},
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
                    ir.GenericSignature(varargs=[argument], output=0),
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
