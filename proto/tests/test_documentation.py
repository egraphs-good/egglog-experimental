"""Declaration documentation presence; no new semantic or resupply policy."""

import json
import unittest

from protobuf import Oneof
from protovalidate import ValidationError, validate

from gen.python.egglog.v1 import egglog_pb as ir


class DocumentationSchemaTests(unittest.TestCase):
    def test_callable_and_sort_docs_preserve_all_three_states(self):
        kinds = [
            (ir.Function, {"name": "f"}),
            (ir.Constructor, {"name": "C"}),
            (ir.Relation, {"name": "R"}),
            (ir.UserDefinedPrimitive, {"name": "p", "body": 0}),
            (ir.Sort, {"kind": Oneof("eq", "Box")}),
        ]
        for record_type, fields in kinds:
            binaries = []
            for doc in [None, "", " docs\n"]:
                with self.subTest(kind=record_type.__name__, doc=doc):
                    declaration = record_type(**fields, doc=doc)
                    validate(declaration)
                    binary = declaration.to_binary()
                    binaries.append(binary)
                    decoded = record_type.from_binary(binary)
                    self.assertEqual(decoded, declaration)
                    # protobuf-py scalar getters return their default when
                    # absent; canonical presence, not truthiness, recovers None.
                    self.assertEqual(decoded.doc if decoded.has_field("doc") else None, doc)
                    self.assertEqual(decoded.has_field("doc"), doc is not None)
                    encoded_json = declaration.to_json()
                    encoded_fields = json.loads(encoded_json)
                    self.assertEqual("doc" in encoded_fields, doc is not None)
                    if doc is not None:
                        self.assertEqual(encoded_fields["doc"], doc)
                    self.assertEqual(record_type.from_json(encoded_json), declaration)
            self.assertEqual(len(set(binaries)), 3)
            # ProtoJSON null uses ordinary unset semantics, not explicit empty.
            self.assertFalse(record_type.from_json('{"doc":null}').has_field("doc"))

    def test_unrelated_rule_documentation_keeps_implicit_string_shape(self):
        self.assertEqual(ir.Rule().doc, "")
        self.assertEqual(ir.Rule(doc="").to_binary(), ir.Rule().to_binary())

    def test_sort_documentation_belongs_to_equality_definitions(self):
        for kind in (
            Oneof("primitive", ir.PrimitiveSortRef(name="i64")),
            Oneof("func", ir.FuncSort(result=0)),
            Oneof("var", 0),
        ):
            with self.subTest(kind=kind.field), self.assertRaises(ValidationError):
                validate(ir.Sort(kind=kind, doc="not a nominal definition"))


if __name__ == "__main__":
    unittest.main()
