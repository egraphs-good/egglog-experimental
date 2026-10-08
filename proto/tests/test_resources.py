"""Resource wire/validation checks, not native configuration execution."""

import unittest

from protobuf import Oneof
from protovalidate import ValidationError, validate

from gen.python.egglog.v1 import egglog_pb as ir


class ResourceSchemaTests(unittest.TestCase):
    def test_creation_separates_nominal_and_host_family_names(self):
        nominal = ir.Declaration(kind=Oneof("eq_sort", ir.EqSort(name="Pair")))
        family = ir.Declaration(kind=Oneof("host_sort_family", ir.HostSortFamily(name="Pair", arity=2)))
        for declarations in ([nominal, family], [family, nominal], [nominal, family, nominal, family]):
            with self.subTest(declarations=declarations):
                request = ir.CreateEGraphRequest(
                    sorts=[
                        ir.Sort(kind=Oneof("eq", "Pair")),
                        ir.Sort(kind=Oneof("family", ir.HostSort(name="Pair", args=[0, 0]))),
                    ],
                    options=ir.EGraphOptions(cost_sort=0),
                    declarations=declarations,
                )
                validate(request)
                self.assertEqual(ir.CreateEGraphRequest.from_binary(request.to_binary()), request)

    def test_creation_retains_same_family_arity_and_application_checks(self):
        nominal = ir.Declaration(kind=Oneof("eq_sort", ir.EqSort(name="Pair")))
        family = ir.Declaration(kind=Oneof("host_sort_family", ir.HostSortFamily(name="Pair", arity=2)))
        conflict = ir.Declaration(kind=Oneof("host_sort_family", ir.HostSortFamily(name="Pair", arity=1)))
        for declarations in ([nominal, family, conflict], [conflict, family, nominal]):
            with self.subTest(declarations=declarations), self.assertRaises(ValidationError):
                validate(ir.CreateEGraphRequest(
                    sorts=[ir.Sort(kind=Oneof("eq", "Pair"))],
                    options=ir.EGraphOptions(cost_sort=0), declarations=declarations,
                ))
        for width in (0, 1, 3):
            with self.subTest(width=width), self.assertRaises(ValidationError):
                validate(ir.CreateEGraphRequest(
                    sorts=[
                        ir.Sort(kind=Oneof("eq", "Pair")),
                        ir.Sort(kind=Oneof("family", ir.HostSort(name="Pair", args=[0] * width))),
                    ],
                    options=ir.EGraphOptions(cost_sort=0), declarations=[nominal, family],
                ))

    def test_creation_still_rejects_callable_declarations(self):
        with self.assertRaises(ValidationError):
            validate(ir.CreateEGraphRequest(
                sorts=[ir.Sort(kind=Oneof("eq", "Pair"))],
                options=ir.EGraphOptions(cost_sort=0),
                declarations=[
                    ir.Declaration(kind=Oneof("eq_sort", ir.EqSort(name="Pair"))),
                    ir.Declaration(kind=Oneof("host_sort_family", ir.HostSortFamily(name="Pair", arity=2))),
                    ir.Declaration(kind=Oneof("constructor", ir.Constructor(name="Pair", output=0))),
                ],
            ))

    def test_query_and_update_are_distinct_including_auto_zero(self):
        operations = [Oneof("query", ir.Unit()), *[Oneof("threads", n) for n in (0, 1, 2, 2**32 - 1)]]
        for operation in operations:
            with self.subTest(operation=operation):
                request = ir.ConfigureEGraphResourcesRequest(egraph_id=7, operation=operation)
                validate(request)
                decoded = ir.ConfigureEGraphResourcesRequest.from_binary(request.to_binary())
                self.assertEqual(decoded, request)
                self.assertEqual(decoded.operation, operation)

    def test_operation_is_required_and_unknown_operation_does_not_become_query(self):
        # Field1 handle7, then unknown length-delimited operation4 with an empty payload.
        unknown = ir.ConfigureEGraphResourcesRequest.from_binary(b"\x08\x07\x22\x00")
        self.assertIsNone(unknown.operation)
        for request in (ir.ConfigureEGraphResourcesRequest(egraph_id=7), unknown):
            with self.subTest(request=request), self.assertRaises(ValidationError):
                validate(request)

    def test_effective_count_is_positive_uint64_not_requested_uint32(self):
        for count in (1, 2, 2**32, 2**64 - 1):
            with self.subTest(count=count):
                response = ir.ConfigureEGraphResourcesResponse(threads=count)
                validate(response)
                self.assertEqual(type(response).from_binary(response.to_binary()), response)
        with self.assertRaises(ValidationError):
            validate(ir.ConfigureEGraphResourcesResponse())
        with self.assertRaises(ValidationError):
            validate(ir.ConfigureEGraphResourcesResponse(threads=0))

    def test_creation_keeps_absent_auto_and_positive_request_distinct(self):
        for count in (None, 0, 1, 2**32 - 1):
            with self.subTest(count=count):
                request = ir.CreateEGraphRequest(
                    sorts=[ir.Sort(kind=Oneof("family", ir.HostSort(name="i64")))],
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
