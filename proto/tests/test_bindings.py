"""Declaration/presentation wire checks, not execution or binding installation."""

import copy
import json
import os
import unittest
from pathlib import Path

from protobuf import Oneof
from protovalidate import ValidationError, validate

from gen.python.egglog.v1 import egglog_pb as ir


def constant_program(core, **view_fields):
    """Own every sort/body reference needed by the concrete declaration fixture."""
    return ir.Program(
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


def tail_view_program(language, *, repetitions=2, prefix=(), tail=(0,), slots=(0, 1), receiver=None, owner=0):
    """Own a shape-only host signature, scalar sorts, and a closed default node."""
    fields = {"path": ["test", "tail"], "tail_repetitions": repetitions}
    if receiver is not None:
        fields.update(path=["combine"], owner=ir.BindingOwner(kind=Oneof("sort", owner)))
    if language == "python":
        view = ir.PythonCallable(
            **fields, kind=ir.PythonCallKind.FUNCTION if receiver is None else ir.PythonCallKind.METHOD,
            receiver=receiver,
            params=[ir.PythonParameter(core_input=i, name=f"arg{i}") for i in slots],
        )
        bindings = ir.CallableBindings(python=ir.PythonBindings(views=[view]))
    else:
        view = ir.RustCallable(
            **fields, receiver=None if receiver is None else ir.RustReceiver(core_input=receiver),
            params=[ir.RustParameter(core_input=i, name=f"arg{i}") for i in slots],
        )
        bindings = ir.CallableBindings(rust=ir.RustBindings(views=[view]))
    return ir.Program(
        sorts=[
            ir.Sort(kind=Oneof("family", ir.HostSort(name="bool"))),
            ir.Sort(kind=Oneof("family", ir.HostSort(name="String"))),
            ir.Sort(kind=Oneof("family", ir.HostSort(name="bool"))),
        ],
        nodes=[ir.Node(sort_id=0, kind=Oneof("primitive_value", ir.PrimitiveValue(value=Oneof("bool", False))))],
        declarations=[ir.Declaration(
            kind=Oneof("host_primitive", ir.HostPrimitive(
                name="test.tail", typing=Oneof("signature", ir.GenericSignature(
                    inputs=[ir.Arg(sort=i) for i in prefix], output=0,
                    varargs=[ir.Arg(sort=i) for i in tail],
                )),
            )),
            bindings=bindings,
        )],
    )


class BindingSchemaTests(unittest.TestCase):
    def test_global_compilation_options_and_explicit_no_decomp_operations(self):
        for seminaive in (None, False, True):
            for no_decomp in (False, True):
                options = ir.EGraphOptions(cost_sort=0, seminaive=seminaive)
                validate(options)
                restored = ir.EGraphOptions.from_binary(options.to_binary())
                self.assertEqual(restored, options)
                self.assertEqual(restored.has_field("seminaive"), seminaive is not None)
                self.assertIs(restored.seminaive, False if seminaive is None else seminaive)
                creation = ir.CreateEGraphRequest(
                    sorts=[ir.Sort(kind=Oneof("family", ir.HostSort(name="i64")))],
                    options=options, no_decomp=no_decomp,
                )
                validate(creation)
                self.assertEqual(ir.CreateEGraphRequest.from_binary(creation.to_binary()), creation)
        query = ir.ConfigureEGraphResourcesRequest(egraph_id=1, operation=Oneof("query", ir.Unit()))
        disabled = ir.ConfigureEGraphResourcesRequest(egraph_id=1, operation=Oneof("no_decomp", False))
        enabled = ir.ConfigureEGraphResourcesRequest(egraph_id=1, operation=Oneof("no_decomp", True))
        self.assertEqual(len({item.to_binary() for item in (query, disabled, enabled)}), 3)
        for request in (query, disabled, enabled):
            validate(request)
            self.assertEqual(ir.ConfigureEGraphResourcesRequest.from_binary(request.to_binary()), request)
        for request in (
            ir.ConfigureEGraphResourcesRequest(egraph_id=1),
            ir.ConfigureEGraphResourcesRequest.from_binary(bytes.fromhex("08013001")),
        ):
            with self.assertRaises(ValidationError):
                validate(request)

    def test_structural_sort_text_aliases_are_optional_wire_metadata(self):
        for symbols in ([], ["A"], ["A", "Z"]):
            program = ir.Program(sorts=[
                ir.Sort(kind=Oneof("family", ir.HostSort(name="i64"))),
                ir.Sort(kind=Oneof("family", ir.HostSort(name="Maybe", args=[0])),
                        egglog_aliases=[ir.EgglogTypeBinding(symbol=s) for s in symbols]),
            ])
            validate(program)
            self.assertEqual(ir.Program.from_binary(program.to_binary()), program)
            self.assertEqual(ir.Program.from_json(program.to_json()), program)
        plain = ir.Sort(kind=Oneof("family", ir.HostSort(name="i64")))
        self.assertEqual(plain.to_binary(), bytes.fromhex("12050a03693634"))

    @unittest.skipUnless(os.environ.get("EGGLOG_TEST_BUILTIN_CATALOG"), "requires a native catalog export")
    def test_exported_append_consumes_one_tail_operand(self):
        program = ir.Program.from_binary(Path(os.environ["EGGLOG_TEST_BUILTIN_CATALOG"]).read_bytes())
        validate(program)
        append = next(d for d in program.declarations if d.kind.value.name == "egglog.core.vec.append")
        program.declarations = [append]
        self.assertEqual(append.kind.value.typing.value.inputs, [])
        self.assertEqual(len(append.kind.value.typing.value.varargs), 1)
        for language in ("python", "rust"):
            with self.subTest(language=language):
                original = copy.deepcopy(program)
                original.declarations[0].bindings = ir.CallableBindings(**{
                    language: getattr(append.bindings, language),
                })
                validate(original)
                for mutation in ("duplicate", "missing", "receiver", "group", "owner", "application"):
                    invalid = copy.deepcopy(original)
                    declaration = invalid.declarations[0]
                    view = getattr(declaration.bindings, language).views[0]
                    if mutation == "duplicate":
                        view.params[0].core_input = 0
                    elif mutation == "missing":
                        view.params.clear()
                    elif mutation == "receiver":
                        if language == "python":
                            view.receiver = 1
                        else:
                            view.receiver.core_input = 1
                    elif mutation == "group":
                        declaration.kind.value.typing.value.varargs.append(ir.Arg(sort=declaration.kind.value.typing.value.varargs[0].sort))
                    elif mutation == "owner":
                        view.owner.kind = Oneof("sort", next(i for i, s in enumerate(invalid.sorts) if s.kind.field == "family" and s.kind.value.name == "i64"))
                    else:
                        declaration.kind.value.typing = Oneof("application", ir.FunctionApplication())
                        # Application already has fixed input 0. Attempt to
                        # consume tail input 1, not its valid fixed receiver.
                        view.params[0].core_input = 2
                        view.params.insert(0, type(view.params[0])(core_input=0, name="function"))
                        if language == "python":
                            view.receiver = 1
                        else:
                            view.receiver.core_input = 1
                    with self.subTest(mutation=mutation), self.assertRaises(ValidationError):
                        validate(invalid)
        for mutation in ("property", "default", "mutation"):
            invalid = copy.deepcopy(program)
            view = invalid.declarations[0].bindings.python.views[0]
            if mutation == "property":
                view.kind = ir.PythonCallKind.PROPERTY
            elif mutation == "default":
                view.params[0].default_expr = 0
            else:
                view.mutates = 0
            with self.subTest(mutation=mutation), self.assertRaises(ValidationError):
                validate(invalid)

    def test_consuming_receiver_preserves_free_and_fixed_prefix_controls(self):
        for language in ("python", "rust"):
            for fields in [
                {"receiver": 0, "slots": (1,)},
                {"prefix": (1,), "receiver": 1, "owner": 0, "slots": (0, 2)},
                {"prefix": (0,), "receiver": 0, "slots": (1,)},
                {"slots": (0,)},
            ]:
                with self.subTest(language=language, fields=fields):
                    validate(tail_view_program(language, repetitions=None, **fields))

    def test_tail_view_absence_and_present_zero_preserve_wire_and_json_presence(self):
        for language in ("python", "rust"):
            views = []
            for repetitions, slots in ((None, (0,)), (0, ())):
                with self.subTest(language=language, repetitions=repetitions):
                    program = tail_view_program(language, repetitions=repetitions, slots=slots)
                    validate(program)
                    for decoded in (ir.Program.from_binary(program.to_binary()), ir.Program.from_json(program.to_json())):
                        self.assertEqual(decoded, program)
                        view = getattr(decoded.declarations[0].bindings, language).views[0]
                        self.assertEqual(view.has_field("tail_repetitions"), repetitions is not None)
                        # protobuf-py returns the scalar default even when the
                        # field is absent; only presence distinguishes R=0.
                        self.assertEqual(view.tail_repetitions, 0 if repetitions is None else repetitions)
                    views.append(getattr(program.declarations[0].bindings, language).views[0])
            self.assertNotIn("tailRepetitions", json.loads(views[0].to_json()))
            self.assertEqual(json.loads(views[1].to_json())["tailRepetitions"], 0)
            # The optional zero is encoded at tag 7, even though it is the
            # scalar default. Clearing it changes meaning and invalidates this
            # nullary view of the unchanged variadic signature.
            self.assertTrue(views[1].to_binary().endswith(b"\x38\x00"))
            invalid = tail_view_program(language, repetitions=None, slots=())
            with self.assertRaises(ValidationError):
                validate(invalid)

    def test_old_absent_tail_view_bytes_remain_unchanged(self):
        # Captured from beeb579's generated bindings before adding this field.
        for language, encoded in (
            ("python", "080112047465737412047461696c2a09080012056974656d73"),
            ("rust", "0a04746573740a047461696c2a09080012056974656d73"),
        ):
            with self.subTest(language=language):
                program = tail_view_program(language, repetitions=None, slots=(0,))
                view = getattr(program.declarations[0].bindings, language).views[0]
                view.params[0].name = "items"
                validate(program)
                self.assertEqual(view.to_binary(), bytes.fromhex(encoded))
                self.assertEqual(type(view).from_binary(bytes.fromhex(encoded)), view)
                # R=1 shares the old logical-slot shape but means one fixed
                # operand; dropping the new field would widen its arity.
                view.tail_repetitions = 1
                validate(program)
                self.assertEqual(view.to_binary(), bytes.fromhex(encoded) + b"\x38\x01")

    def test_fixed_tail_views_cover_prefix_and_ordered_repeated_groups(self):
        for language in ("python", "rust"):
            for repetitions, slots in ((0, (0,)), (1, (2, 0, 1)), (2, (4, 2, 0, 3, 1))):
                with self.subTest(language=language, repetitions=repetitions):
                    program = tail_view_program(language, prefix=(1,), tail=(0, 1), repetitions=repetitions, slots=slots)
                    validate(program)
                    self.assertEqual(ir.Program.from_binary(program.to_binary()), program)
                    signature = program.declarations[0].kind.value.typing.value
                    self.assertEqual([arg.sort for arg in signature.inputs], [1])
                    self.assertEqual([arg.sort for arg in signature.varargs], [0, 1])

    def test_binary_tail_receivers_and_trait_views_preserve_canonical_signature(self):
        for language in ("python", "rust"):
            for receiver in (0, 1):
                with self.subTest(language=language, receiver=receiver):
                    program = tail_view_program(language, receiver=receiver, slots=(1-receiver,))
                    signature = copy.deepcopy(program.declarations[0].kind.value.typing.value)
                    view = getattr(program.declarations[0].bindings, language).views[0]
                    if language == "python":
                        view.path = ["__or__"]
                    else:
                        view.path = ["bitor"]
                        view.borrowed_self = True
                        view.trait_impl = ir.RustTrait(
                            path=["std", "ops", "BitOr"], args=[ir.RustType(sort=0)], output_associated_type="Output",
                        )
                    validate(program)
                    decoded = ir.Program.from_binary(program.to_binary())
                    self.assertEqual(decoded, program)
                    self.assertEqual(decoded.declarations[0].kind.value.typing.value, signature)

    def test_fixed_tail_counts_reject_mismatch_incomplete_groups_and_overflow(self):
        cases = [
            {"repetitions": 0}, {"repetitions": 1}, {"repetitions": 3},
            {"repetitions": 2**31}, {"repetitions": 2**32-1},
            {"repetitions": 2**32-1, "tail": (0, 1)},
            {"repetitions": 0, "prefix": (0, 0, 0)},
            {"repetitions": 1, "tail": (0, 1), "slots": (0, 1, 2)},
        ]
        for language in ("python", "rust"):
            for fields in cases:
                with self.subTest(language=language, fields=fields), self.assertRaises(ValidationError):
                    validate(tail_view_program(language, **fields))

    def test_fixed_tail_slots_reject_missing_duplicate_and_out_of_range_inputs(self):
        cases = [
            {"slots": (0,)}, {"slots": (0, 0)}, {"slots": (0, 2)},
            {"slots": (0, 2**32-1)}, {"receiver": 0, "slots": (0,)},
            {"receiver": 2, "slots": (0,)}, {"receiver": 2**32-1, "slots": (0,)},
            {"repetitions": 0, "receiver": 0, "slots": ()},
        ]
        for language in ("python", "rust"):
            for fields in cases:
                with self.subTest(language=language, fields=fields), self.assertRaises(ValidationError):
                    validate(tail_view_program(language, **fields))

    def test_fixed_tail_views_reject_fixed_signatures_and_other_typing_forms(self):
        cores = [
            Oneof("constructor", ir.Constructor(name="test.tail", inputs=[ir.Arg(sort=0)], output=0)),
            Oneof("function", ir.Function(name="test.tail", inputs=[ir.Arg(sort=0)], output=0)),
            Oneof("relation", ir.Relation(name="test.tail", inputs=[ir.Arg(sort=0)])),
            Oneof("primitive", ir.Primitive(name="test.tail", inputs=[ir.Arg(sort=0)], output=0, body=0)),
            Oneof("host_primitive", ir.HostPrimitive(name="test.tail", typing=Oneof("application", ir.FunctionApplication()))),
        ]
        for language in ("python", "rust"):
            for repetitions in (0, 2):
                with self.subTest(language=language, repetitions=repetitions, fixed_signature=True), self.assertRaises(ValidationError):
                    validate(tail_view_program(language, repetitions=repetitions, tail=(), slots=()))
                for core in cores:
                    with self.subTest(language=language, repetitions=repetitions, core=core.field):
                        program = tail_view_program(language, repetitions=repetitions)
                        program.declarations[0].kind = core
                        with self.assertRaises(ValidationError):
                            validate(program)

    def test_fixed_tail_defaults_and_mutation_stay_on_original_fixed_inputs(self):
        program = tail_view_program("python", prefix=(0,), slots=(0, 1, 2))
        view = program.declarations[0].bindings.python.views[0]
        view.params[0].default_expr = 0
        view.mutates = 0
        validate(program)
        for slot in (1, 2):
            for field in ("default", "mutation"):
                with self.subTest(slot=slot, field=field):
                    invalid = copy.deepcopy(program)
                    invalid_view = invalid.declarations[0].bindings.python.views[0]
                    if field == "default":
                        invalid_view.params[slot].default_expr = 0
                    else:
                        invalid_view.mutates = slot
                    with self.assertRaises(ValidationError):
                        validate(invalid)
        receiver = tail_view_program("python", receiver=0, slots=(1,))
        receiver.declarations[0].bindings.python.views[0].mutates = 0
        with self.assertRaises(ValidationError):
            validate(receiver)

    def test_fixed_tail_receiver_owner_uses_effective_sort_without_arena_identity(self):
        for language in ("python", "rust"):
            # Fixed String prefix, then bool/String repeated twice. Check both
            # positions in each group and a separate equivalent bool arena slot.
            for receiver, owners in ((0, (1,)), (1, (0, 2)), (2, (1,)), (3, (0, 2)), (4, (1,))):
                for owner in owners:
                    with self.subTest(language=language, receiver=receiver, owner=owner):
                        program = tail_view_program(
                            language, prefix=(1,), tail=(0, 1), receiver=receiver, owner=owner,
                            slots=tuple(i for i in range(5) if i != receiver),
                        )
                        validate(program)
                        invalid = copy.deepcopy(program)
                        getattr(invalid.declarations[0].bindings, language).views[0].owner.kind = Oneof("sort", 0 if owner == 1 else 1)
                        with self.assertRaises(ValidationError):
                            validate(invalid)
                        invalid = copy.deepcopy(program)
                        getattr(invalid.declarations[0].bindings, language).views[0].owner.kind = Oneof("function", ir.FunctionTypeOwner())
                        with self.assertRaises(ValidationError):
                            validate(invalid)

    def test_fixed_tail_python_unused_forms_are_explicitly_unsupported(self):
        for kind in (
            ir.PythonCallKind.INITIALIZER, ir.PythonCallKind.CLASS_METHOD,
            ir.PythonCallKind.PROPERTY, ir.PythonCallKind.CLASS_VARIABLE, ir.PythonCallKind.CONSTANT,
        ):
            with self.subTest(kind=kind):
                view = ir.PythonCallable(kind=kind, path=["member"], tail_repetitions=0)
                if kind != ir.PythonCallKind.CONSTANT:
                    view.owner = ir.BindingOwner(kind=Oneof("sort", 0))
                if kind == ir.PythonCallKind.INITIALIZER:
                    view.path = []
                if kind == ir.PythonCallKind.PROPERTY:
                    view.receiver = 0
                with self.assertRaises(ValidationError):
                    validate(view)

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
                program = ir.Program(sorts=sorts, declarations=declarations)
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
        validate(ir.Program(declarations=[nominal, family, nominal, family]))
        conflict = ir.Declaration(kind=Oneof("host_sort_family", ir.HostSortFamily(name="Pair", arity=1)))
        for declarations in ([nominal, family, conflict], [conflict, nominal, family]):
            with self.subTest(declarations=declarations), self.assertRaises(ValidationError):
                validate(ir.Program(declarations=declarations))

    def test_nominal_declaration_does_not_mask_bad_family_application(self):
        for width in (0, 1, 3):
            with self.subTest(width=width), self.assertRaises(ValidationError):
                validate(ir.Program(
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
        for path in [["example", "C"], [""], ["example", ""]]:
            with self.subTest(path=path):
                function = constant_program(core, kind=ir.PythonCallKind.FUNCTION, path=path)
                constant = constant_program(core, path=path)
                for program in (function, constant):
                    validate(program)
                    self.assertEqual(ir.Program.from_binary(program.to_binary()), program)
                self.assertNotEqual(function, constant)
                self.assertNotEqual(function.to_binary(), constant.to_binary())

    def test_free_python_views_preserve_exact_final_names(self):
        for kind in (ir.PythonCallKind.FUNCTION, ir.PythonCallKind.CONSTANT):
            for path in [[""], ["example", ""], ["+"], ["example", "@internal"]]:
                with self.subTest(kind=kind, path=path):
                    program = constant_program(
                        Oneof("function", ir.Function(name="C", output=0)), kind=kind, path=path,
                    )
                    validate(program)
                    decoded = ir.Program.from_binary(program.to_binary())
                    self.assertEqual(decoded, program)
                    self.assertEqual(decoded.declarations[1].bindings.python.views[0].path, path)
                    self.assertEqual(decoded.declarations[1].kind.value.name, "C")

    def test_python_types_and_members_keep_nonempty_path_components(self):
        views = [
            ir.TypeBinding(path=[""]),
            ir.TypeBinding(path=["example", ""]),
            *[
                ir.PythonCallable(
                    kind=kind, path=[""],
                    owner=ir.BindingOwner(kind=Oneof("sort", 1)),
                    receiver=0 if kind in (ir.PythonCallKind.METHOD, ir.PythonCallKind.PROPERTY) else None,
                )
                for kind in (
                    ir.PythonCallKind.METHOD, ir.PythonCallKind.CLASS_METHOD,
                    ir.PythonCallKind.PROPERTY, ir.PythonCallKind.CLASS_VARIABLE,
                )
            ],
        ]
        for view in views:
            with self.subTest(view=view), self.assertRaises(ValidationError):
                validate(view)
        # Initializers still derive their name and deliberately have no path.
        validate(ir.PythonCallable(
            kind=ir.PythonCallKind.INITIALIZER,
            owner=ir.BindingOwner(kind=Oneof("sort", 1)),
        ))

    def test_free_python_views_have_nonempty_paths_and_qualifiers(self):
        for kind in (ir.PythonCallKind.FUNCTION, ir.PythonCallKind.CONSTANT):
            for path in [[], ["", "C"], ["", ""], ["example", "", "C"], ["example", "", ""]]:
                with self.subTest(kind=kind, path=path), self.assertRaises(ValidationError):
                    validate(constant_program(
                        Oneof("function", ir.Function(name="C", output=0)), kind=kind, path=path,
                    ))

    def test_constant_keeps_ownerless_nullary_form_restrictions(self):
        invalid = [
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
