"""Repeated-tail wire/CEL checks, not generic call matching or execution."""

import copy
import json
import unittest

from protobuf import Oneof
from protovalidate import ValidationError, validate

from gen.python.egglog.v1 import egglog_pb as ir


def signature_program(pattern):
    """Own the signature's arena, binder and presentation-default references."""
    return ir.Program(
        ir_version=1,
        sorts=[
            ir.Sort(kind=Oneof("family", ir.HostSort(name="i64"))),
            ir.Sort(kind=Oneof("var", 0)),
            ir.Sort(kind=Oneof("var", 1)),
            ir.Sort(kind=Oneof("family", ir.HostSort(name="Map", args=[1, 2]))),
            ir.Sort(kind=Oneof("var", 2)),
        ],
        nodes=[ir.Node(sort_id=0, kind=Oneof("primitive_value", ir.PrimitiveValue(value=Oneof("i64", 7))))],
        declarations=[
            ir.Declaration(kind=Oneof("host_sort_family", ir.HostSortFamily(name="i64"))),
            ir.Declaration(kind=Oneof("host_sort_family", ir.HostSortFamily(name="Map", arity=2))),
            ir.Declaration(kind=Oneof("host_primitive", ir.HostPrimitive(
                name="test.pairs",
                typing=Oneof("signature", ir.GenericSignature(
                    type_params=["K", "V"],
                    inputs=[ir.Arg(name="prefix", sort=0)],
                    output=3,
                    varargs=[ir.Arg(name=f"tail{i}", sort=sort) for i, sort in enumerate(pattern)],
                )),
            ))),
        ],
    )


class SignatureSchemaTests(unittest.TestCase):
    def test_tail_width_and_order_survive_wire_roundtrip(self):
        for pattern in [[], [1], [1, 2], [1, 1], [1, 2, 1]]:
            with self.subTest(pattern=pattern):
                program = signature_program(pattern)
                validate(program)
                decoded = ir.Program.from_binary(program.to_binary())
                self.assertEqual(decoded, program)
                self.assertEqual(
                    [arg.sort for arg in decoded.declarations[-1].kind.value.typing.value.varargs],
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
        program.declarations[-1].kind.value.typing.value.type_params = []
        with self.assertRaises(ValidationError):
            validate(program)

    def test_all_nonempty_patterns_have_one_logical_presentation_tail(self):
        for pattern in [[], [1], [1, 2], [1, 1], [1, 2, 1]]:
            with self.subTest(pattern=pattern):
                program = signature_program(pattern)
                names = ["prefix", "entries"] if pattern else ["prefix"]
                program.declarations[-1].bindings = ir.CallableBindings(
                    python=ir.PythonBindings(views=[ir.PythonCallable(
                        kind=ir.PythonCallKind.FUNCTION, path=["test", "pairs"],
                        params=[ir.PythonParameter(core_input=i, name=name) for i, name in enumerate(names)],
                    )]),
                    rust=ir.RustBindings(views=[ir.RustCallable(
                        path=["test", "pairs"],
                        params=[ir.RustParameter(core_input=i, name=name) for i, name in enumerate(names)],
                    )]),
                )
                validate(program)
                self.assertEqual(ir.Program.from_binary(program.to_binary()), program)

    def test_tail_is_one_final_parameter_without_default_or_receiver(self):
        python = ir.PythonCallable(
            kind=ir.PythonCallKind.FUNCTION, path=["test", "pairs"],
            params=[ir.PythonParameter(core_input=0, name="prefix"), ir.PythonParameter(core_input=1, name="entries")],
        )
        rust = ir.RustCallable(
            path=["test", "pairs"],
            params=[ir.RustParameter(core_input=0, name="prefix"), ir.RustParameter(core_input=1, name="entries")],
        )
        for language, view in [("python", python), ("rust", rust)]:
            bad_views = []
            missing = copy.deepcopy(view)
            missing.params.pop()
            bad_views.append(missing)
            extra = copy.deepcopy(view)
            extra.params.append(type(view.params[0])(core_input=2, name="not_a_second_slot"))
            bad_views.append(extra)
            reversed_params = copy.deepcopy(view)
            reversed_params.params.reverse()
            bad_views.append(reversed_params)
            receiver = copy.deepcopy(view)
            receiver.path = ["pairs"]
            receiver.owner = ir.BindingOwner(kind=Oneof("sort", 0))
            receiver.params.pop()
            if language == "python":
                receiver.kind = ir.PythonCallKind.METHOD
                receiver.receiver = 1
                default = copy.deepcopy(view)
                default.params[-1].default_expr = 0
                bad_views.append(default)
            else:
                receiver.receiver = ir.RustReceiver(core_input=1)
            bad_views.append(receiver)
            for bad in bad_views:
                with self.subTest(language=language, view=bad), self.assertRaises(ValidationError):
                    program = signature_program([1, 2])
                    program.declarations[-1].bindings = ir.CallableBindings(**{
                        language: (ir.PythonBindings if language == "python" else ir.RustBindings)(views=[bad]),
                    })
                    validate(program)
            with self.subTest(language=language, spurious_tail=True), self.assertRaises(ValidationError):
                program = signature_program([])
                program.declarations[-1].bindings = ir.CallableBindings(**{
                    language: (ir.PythonBindings if language == "python" else ir.RustBindings)(views=[view]),
                })
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
