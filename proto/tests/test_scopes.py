"""Clone/destroy wire checks; handle liveness belongs to E."""

import unittest

from protovalidate import validate

from gen.python.egglog.v1 import egglog_pb as ir


class ScopeSchemaTests(unittest.TestCase):
    def test_clone_and_destroy_address_one_handle(self):
        for request_type in (ir.CloneEGraphRequest, ir.DestroyEGraphRequest):
            with self.subTest(request=request_type):
                request = request_type(egraph_id=2)
                validate(request)
                self.assertEqual(request.to_binary(), b"\x08\x02")
                self.assertEqual(request_type.from_binary(request.to_binary()), request)
        response = ir.DestroyEGraphResponse()
        validate(response)
        self.assertEqual(response.to_binary(), b"")
        self.assertEqual(type(response).from_binary(b""), response)


if __name__ == "__main__":
    unittest.main()
