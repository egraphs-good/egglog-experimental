"""Semantic declaration namespaces and creation settings."""

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
                    sorts=[ir.Sort(kind=Oneof("application", ir.SortApplication(name="i64")))],
                    options=options, no_decomp=no_decomp,
                )
                validate(creation)
                self.assertEqual(ir.CreateEGraphRequest.from_binary(creation.to_binary()), creation)


    def test_user_namespaces_resolve_primitive_sort_applications_ambiently(self):
        nominal = ir.Declaration(kind=Oneof("eq_sort", ir.EqSort(name="Pair")))
        callable_ = ir.Declaration(kind=Oneof("constructor", ir.Constructor(
            name="Pair", inputs=[ir.Arg(sort=1)], output=0,
        )))
        sorts = [
            ir.Sort(kind=Oneof("eq", "Pair")),
            ir.Sort(kind=Oneof("application", ir.SortApplication(name="Pair", args=[0, 0]))),
        ]
        for declarations in ([nominal, callable_], [callable_, nominal]):
            program = ir.Program(sorts=sorts, declarations=declarations)
            validate(program)
            self.assertEqual(ir.Program.from_binary(program.to_binary()), program)

    def test_open_signature_patterns_belong_only_to_builtin_catalog(self):
        with self.assertRaises(ValidationError):
            validate(ir.Program(sorts=[ir.Sort(kind=Oneof("var", 0))]))
        catalog = ir.BuiltinCatalog(
            sorts=[ir.Sort(kind=Oneof("var", 0))],
            primitives=[ir.Primitive(name="p", typing=Oneof("signature", ir.GenericSignature(
                type_params=["T"], inputs=[ir.Arg(sort=0)], output=0,
            )))],
        )
        validate(catalog)
        self.assertEqual(ir.BuiltinCatalog.from_binary(catalog.to_binary()), catalog)

    def test_sort_kind_wire_tags_are_unchanged(self):
        # These existing tags already distinguish identical name spellings.
        cases = [
            (ir.Sort(kind=Oneof("eq", "Pair")), b"\x0a\x04Pair"),
            (ir.Sort(kind=Oneof("application", ir.SortApplication(name="Pair", args=[0, 0]))),
             b"\x12\x0a\x0a\x04Pair\x12\x02\x00\x00"),
        ]
        for sort, encoded in cases:
            with self.subTest(sort=sort):
                self.assertEqual(sort.to_binary(), encoded)
                self.assertEqual(ir.Sort.from_binary(encoded), sort)


if __name__ == "__main__":
    unittest.main()
