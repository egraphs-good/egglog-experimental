"""Scope-return wire checks; handle liveness and direct pairing belong to E."""

import unittest

from protovalidate import ValidationError, validate

from gen.python.egglog.v1 import egglog_pb as ir


class ScopeSchemaTests(unittest.TestCase):
    def test_return_keeps_active_and_saved_roles_distinct(self):
        request = ir.ReturnToEGraphRequest(active_id=2, saved_id=1)
        validate(request)
        self.assertEqual(request.to_binary(), b"\x08\x02\x10\x01")
        self.assertEqual(type(request).from_binary(request.to_binary()), request)
        response = ir.ReturnToEGraphResponse()
        validate(response)
        self.assertEqual(response.to_binary(), b"")
        self.assertEqual(type(response).from_binary(b""), response)

    def test_same_handle_is_invalid_including_default_request(self):
        for handle in (0, 1, 2**64 - 1):
            with self.subTest(handle=handle), self.assertRaises(ValidationError):
                validate(ir.ReturnToEGraphRequest(active_id=handle, saved_id=handle))


if __name__ == "__main__":
    unittest.main()
