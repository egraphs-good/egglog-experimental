"""Semantic declaration namespaces and creation settings."""

import json
import unittest
from protobuf import Oneof
from protovalidate import ValidationError, validate
from gen.python.egglog.v1 import egglog_pb as ir


class SemanticHeaderTests(unittest.TestCase):
    def test_global_compilation_options_and_creation_no_decomp(self):
        for seminaive in (None, False, True):
            for no_decomp in (False, True):
                options = ir.EGraphOptions(cost_sort=0, seminaive=seminaive)
                validate(options)
                restored = ir.EGraphOptions.from_binary(options.to_binary())
                self.assertEqual(restored, options)
                self.assertEqual(restored.has_field("seminaive"), seminaive is not None)
                self.assertIs(restored.seminaive, False if seminaive is None else seminaive)
                creation = ir.CreateEGraphRequest(
                    sorts=[ir.Sort(kind=Oneof("primitive", ir.PrimitiveSortRef(name="i64")))],
                    options=options, no_decomp=no_decomp,
                )
                validate(creation)
                self.assertEqual(ir.CreateEGraphRequest.from_binary(creation.to_binary()), creation)


    def test_user_namespaces_resolve_primitive_sort_refs_ambiently(self):
        callable_ = ir.Declaration(kind=Oneof("constructor", ir.Constructor(
            name="Pair", inputs=[ir.Arg(sort=1)], output=0,
        )))
        sorts = [
            ir.Sort(kind=Oneof("eq", "Pair")),
            ir.Sort(kind=Oneof("primitive", ir.PrimitiveSortRef(name="Pair", args=[0, 0]))),
        ]
        program = ir.Program(sorts=sorts, declarations=[callable_])
        validate(program)
        self.assertEqual(ir.Program.from_binary(program.to_binary()), program)

    def test_equality_and_global_setup_roots_need_no_declaration(self):
        program = ir.Program(
            sorts=[ir.Sort(kind=Oneof("eq", "Math"), doc="A nominal type")],
            nodes=[ir.Node(kind=Oneof("binding", name)) for name in ("", "x", "λ")],
        )
        validate(program)
        self.assertFalse(program.commands)
        self.assertFalse(program.declarations)
        self.assertEqual(ir.Program.from_binary(program.to_binary()), program)
        self.assertEqual(ir.Program.from_json(program.to_json()), program)
        self.assertFalse(hasattr(ir, "EqSort"))

    def test_global_lookup_and_lexical_variable_are_distinct(self):
        local = ir.Node(kind=Oneof("var", "x"))
        global_ = ir.Node(kind=Oneof("binding", "x"))
        for node in (local, global_):
            validate(node)
            self.assertEqual(ir.Node.from_binary(node.to_binary()), node)
        self.assertNotEqual(local, global_)
        self.assertNotEqual(local.to_binary(), global_.to_binary())

    def test_let_addresses_only_binding_nodes_and_requires_both_indices(self):
        nodes = [
            ir.Node(kind=Oneof("binding", "x")),
            ir.Node(kind=Oneof("primitive_value", ir.PrimitiveValue(value=Oneof("i64", 10)))),
        ]
        for binding, value, accepted in [(0, 1, True), (1, 0, False), (2, 1, False),
                                          (0, 2, False), (None, 1, False), (0, None, False)]:
            program = ir.Program(
                sorts=[ir.Sort(kind=Oneof("primitive", ir.PrimitiveSortRef(name="i64")))],
                nodes=nodes,
                commands=[ir.Command(kind=Oneof("let", ir.Let(binding=binding, value=value)))],
            )
            with self.subTest(binding=binding, value=value):
                if accepted:
                    validate(program)
                    self.assertEqual(ir.Program.from_binary(program.to_binary()), program)
                else:
                    with self.assertRaises(ValidationError):
                        validate(program)

    def test_open_signature_patterns_belong_only_to_builtin_catalog(self):
        with self.assertRaises(ValidationError):
            validate(ir.Program(sorts=[ir.Sort(kind=Oneof("var", 0))]))
        catalog = ir.BuiltinCatalog(
            sorts=[ir.Sort(kind=Oneof("var", 0))],
            primitives=[ir.Primitive(name="p", signature=ir.GenericSignature(
                type_param_count=1, inputs=[ir.Arg(sort=0)], output=0,
            ))],
        )
        validate(catalog)
        self.assertEqual(ir.BuiltinCatalog.from_binary(catalog.to_binary()), catalog)

    def test_sort_kind_wire_tags_are_unchanged(self):
        # These existing tags already distinguish identical name spellings.
        cases = [
            (ir.Sort(kind=Oneof("eq", "Pair")), b"\x0a\x04Pair"),
            (ir.Sort(kind=Oneof("primitive", ir.PrimitiveSortRef(name="i64"))),
             b"\x12\x05\x0a\x03i64"),
            (ir.Sort(kind=Oneof("primitive", ir.PrimitiveSortRef(name="Pair", args=[0, 0]))),
             b"\x12\x0a\x0a\x04Pair\x12\x02\x00\x00"),
        ]
        for sort, encoded in cases:
            with self.subTest(sort=sort):
                self.assertEqual(sort.to_binary(), encoded)
                self.assertEqual(ir.Sort.from_binary(encoded), sort)
                if sort.kind.field == "primitive":
                    fields = json.loads(sort.to_json())
                    self.assertEqual(fields["primitive"]["name"], sort.kind.value.name)
                    self.assertEqual(ir.Sort.from_json(sort.to_json()), sort)


if __name__ == "__main__":
    unittest.main()
