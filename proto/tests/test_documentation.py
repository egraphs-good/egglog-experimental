"""Declaration documentation presence; no new semantic or resupply policy."""

import json
import unittest

from protobuf import Oneof
from protovalidate import validate

from gen.python.egglog.v1 import egglog_pb as ir


class DocumentationSchemaTests(unittest.TestCase):
    def test_callable_and_sort_docs_preserve_all_three_states(self):
        kinds = [
            Oneof("function", ir.Function(name="f")),
            Oneof("constructor", ir.Constructor(name="C")),
            Oneof("eq_sort", ir.EqSort(name="Box")),
        ]
        for kind in kinds:
            binaries = []
            for doc in [None, "", " docs\n"]:
                with self.subTest(kind=kind.field, doc=doc):
                    declaration = ir.Declaration(kind=kind, doc=doc)
                    validate(declaration)
                    binary = declaration.to_binary()
                    binaries.append(binary)
                    decoded = ir.Declaration.from_binary(binary)
                    self.assertEqual(decoded, declaration)
                    # protobuf-py scalar getters return their default when
                    # absent; canonical presence, not truthiness, recovers None.
                    self.assertEqual(decoded.doc if decoded.has_field("doc") else None, doc)
                    self.assertEqual(decoded.has_field("doc"), doc is not None)
                    encoded_json = declaration.to_json()
                    fields = json.loads(encoded_json)
                    self.assertEqual("doc" in fields, doc is not None)
                    if doc is not None:
                        self.assertEqual(fields["doc"], doc)
                    self.assertEqual(ir.Declaration.from_json(encoded_json), declaration)
            self.assertEqual(len(set(binaries)), 3)
        # ProtoJSON null uses ordinary unset semantics, not explicit empty.
        self.assertFalse(ir.Declaration.from_json('{"doc":null}').has_field("doc"))

    def test_old_absent_and_nonempty_canonical_bytes_are_unchanged(self):
        # Captured from the published S9f7e335 implicit-string Python decoder.
        for doc, old_hex in [
            (None, "12030a0166"),
            (" docs\n", "12030a01664a0620646f63730a"),
        ]:
            with self.subTest(doc=doc):
                declaration = ir.Declaration(kind=Oneof("function", ir.Function(name="f")), doc=doc)
                old = bytes.fromhex(old_hex)
                self.assertEqual(declaration.to_binary(), old)
                self.assertEqual(ir.Declaration.from_binary(old), declaration)

    def test_old_receiver_loses_explicit_empty_presence(self):
        present_empty = bytes.fromhex("12030a01664a00")
        # Actual old S9f7e335 Python decoder reencoded the above without field9.
        old_receiver_output = bytes.fromhex("12030a0166")
        empty = ir.Declaration.from_binary(present_empty)
        absent = ir.Declaration.from_binary(old_receiver_output)
        self.assertEqual(empty.doc, "")
        self.assertTrue(empty.has_field("doc"))
        self.assertFalse(absent.has_field("doc"))
        self.assertNotEqual(empty, absent)
        self.assertEqual(empty.to_binary(), present_empty)
        self.assertEqual(absent.to_binary(), old_receiver_output)

    def test_unrelated_rule_documentation_keeps_implicit_string_shape(self):
        self.assertEqual(ir.Ruleset().doc, "")
        self.assertEqual(ir.RuleDecl().doc, "")
        self.assertEqual(ir.Ruleset(doc="").to_binary(), ir.Ruleset().to_binary())
        self.assertEqual(ir.RuleDecl(doc="").to_binary(), ir.RuleDecl().to_binary())


if __name__ == "__main__":
    unittest.main()
