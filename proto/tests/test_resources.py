"""Resource wire/validation checks, not native configuration execution."""

import unittest

from protobuf import Oneof
from protovalidate import ValidationError, validate

from gen.python.egglog.v1 import egglog_pb as ir


class ResourceSchemaTests(unittest.TestCase):
    def test_creation_accepts_closed_backend_compositions_without_declarations(self):
        request = ir.CreateEGraphRequest(
            sorts=[ir.Sort(kind=Oneof("application", ir.SortApplication(name="i64"))),
                   ir.Sort(kind=Oneof("application", ir.SortApplication(name="Pair", args=[0, 0])))],
            options=ir.EGraphOptions(cost_sort=1),
        )
        validate(request)
        self.assertEqual(type(request).from_binary(request.to_binary()), request)
        request.sorts[0] = ir.Sort(kind=Oneof("eq", "User"))
        with self.assertRaises(ValidationError):
            validate(request)
        with self.assertRaises(TypeError):
            ir.CreateEGraphRequest(declarations=[])

    def test_creation_resources_can_be_requested_together(self):
        request = ir.CreateEGraphRequest(
            sorts=[ir.Sort(kind=Oneof("application", ir.SortApplication(name="i64")))],
            options=ir.EGraphOptions(cost_sort=0), threads=0, no_decomp=True,
        )
        validate(request)
        self.assertEqual(type(request).from_binary(request.to_binary()), request)

    def test_effective_count_is_positive_uint64_not_requested_uint32(self):
        for count in (1, 2, 2**32, 2**64 - 1):
            with self.subTest(count=count):
                response = ir.CreateEGraphResponse(egraph_id=7, threads=count)
                validate(response)
                self.assertEqual(type(response).from_binary(response.to_binary()), response)
        with self.assertRaises(ValidationError):
            validate(ir.CreateEGraphResponse())
        with self.assertRaises(ValidationError):
            validate(ir.CreateEGraphResponse(egraph_id=7, threads=0))

    def test_creation_keeps_absent_auto_and_positive_request_distinct(self):
        for count in (None, 0, 1, 2**32 - 1):
            with self.subTest(count=count):
                request = ir.CreateEGraphRequest(
                    sorts=[ir.Sort(kind=Oneof("application", ir.SortApplication(name="i64")))],
                    options=ir.EGraphOptions(cost_sort=0),
                    threads=count,
                )
                validate(request)
                decoded = type(request).from_binary(request.to_binary())
                self.assertEqual(decoded.has_field("threads"), count is not None)
                if count is not None:
                    self.assertEqual(decoded.threads, count)


if __name__ == "__main__":
    unittest.main()
