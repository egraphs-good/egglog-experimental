"""Ordering-only comparison for the first-order constant-folding fixture.

This deliberately is not a semantic equivalence checker. Every allocated node
and sort survives; only their positions and the references to them change.
"""

from collections import defaultdict, deque

from google.protobuf import descriptor_pool, message_factory


class UnsupportedProgram(ValueError):
    """The bounded normalizer cannot assign an unambiguous rooted ordering."""


def schema_messages(generated):
    """Bridge the generated SDK descriptors to Google's schema-derived TextProto."""
    pool = descriptor_pool.DescriptorPool()
    seen = set()

    def register(file):
        if file.name not in seen:
            for dependency in file.dependencies:
                register(dependency)
            pool.AddSerializedFile(file.proto.to_binary())
            seen.add(file.name)

    register(generated.Program.desc().file)
    return {
        name: message_factory.GetMessageClass(pool.FindMessageTypeByName(f"egglog.v1.{name}"))
        for name in (
            "Program", "CreateEGraphRequest", "CreateEGraphResponse",
            "RunProgramRequest", "RunProgramResponse", "GetHistoryRequest",
        )
    }


def normalize(program):
    """Return a permutation of an admitted Program, without editing its content.

    Declarations/groups anchor the setup order by exact names. Ordered syntax
    roots then anchor node and sort locations, with allocation before traversal
    to preserve sharing and Eq cycles. Unreferenced leaves and sorts are retained;
    unrooted Call/Eq graphs are unsupported rather than searched or discarded.
    """
    if program.DESCRIPTOR.full_name != "egglog.v1.Program":
        raise TypeError("expected generated egglog.v1.Program")
    result = type(program)()
    result.CopyFrom(program)
    result.DiscardUnknownFields()
    if result != program:
        raise UnsupportedProgram("unknown protobuf fields")
    if result.user_defined_primitives:
        raise UnsupportedProgram("user-defined primitive bodies")

    names = set()
    for collection in (result.constructors, result.functions, result.relations):
        for declaration in collection:
            if declaration.name in names:
                raise UnsupportedProgram("duplicate callable names")
            names.add(declaration.name)
        collection.sort(key=lambda declaration: declaration.name)
    if len({binding.name for binding in result.rulesets}) != len(result.rulesets):
        raise UnsupportedProgram("duplicate ruleset bindings")
    result.rulesets.sort(key=lambda binding: binding.name)

    sorts = []
    sort_ids = {}
    for sort in program.sorts:
        kind = sort.WhichOneof("kind")
        if kind not in {"eq", "primitive"} or (kind == "primitive" and sort.primitive.args):
            raise UnsupportedProgram("only nominal and nullary primitive sorts are supported")

    def sort_ref(index):
        if not 0 <= index < len(program.sorts):
            raise UnsupportedProgram(f"sort reference out of bounds: {index}")
        if index not in sort_ids:
            sort_ids[index] = len(sorts)
            sorts.append(program.sorts[index])
        return sort_ids[index]

    nodes = []
    node_ids = {}
    pending = deque()

    def node_ref(index):
        if not 0 <= index < len(program.nodes):
            raise UnsupportedProgram(f"node reference out of bounds: {index}")
        if index not in node_ids:
            node_ids[index] = len(nodes)
            nodes.append(None)
            pending.append(index)
        return node_ids[index]

    def call_refs(call):
        call.args[:] = [node_ref(index) for index in call.args]

    def action_refs(action):
        kind = action.WhichOneof("kind")
        if kind == "term":
            action.term = node_ref(action.term)
        elif kind == "set":
            if not action.set.HasField("target") or not action.set.HasField("value"):
                raise UnsupportedProgram("incomplete Set")
            call_refs(action.set.target)
            action.set.value = node_ref(action.set.value)
        elif kind == "subsume":
            call_refs(action.subsume)
        else:
            raise UnsupportedProgram(f"action kind: {kind}")

    def rule_refs(rule):
        if rule.WhichOneof("kind") != "rule":
            raise UnsupportedProgram("only RuleBody rules are supported")
        rule.rule.query[:] = [node_ref(index) for index in rule.rule.query]
        for action in rule.rule.actions:
            action_refs(action)

    def command_refs(command):
        kind = command.WhichOneof("kind")
        if kind == "let":
            if not command.let.HasField("binding") or not command.let.HasField("value"):
                raise UnsupportedProgram("incomplete Let")
            command.let.binding = node_ref(command.let.binding)
            command.let.value = node_ref(command.let.value)
        elif kind == "action":
            action_refs(command.action)
        elif kind == "run":
            for selection in command.run.rulesets:
                selection_kind = selection.WhichOneof("kind")
                if selection_kind == "ruleset":
                    for rule in selection.ruleset.rules:
                        rule_refs(rule)
                elif selection_kind != "name":
                    raise UnsupportedProgram("missing ruleset selection")
        elif kind == "loop":
            for child in command.loop.body:
                command_refs(child)
            command.loop.until[:] = [node_ref(index) for index in command.loop.until]
        elif kind == "check":
            command.check.facts[:] = [node_ref(index) for index in command.check.facts]
        elif kind == "extract":
            command.extract.roots[:] = [node_ref(index) for index in command.extract.roots]
        elif kind != "freeze":
            raise UnsupportedProgram(f"command kind: {kind}")

    for collection in (result.constructors, result.functions, result.relations):
        for declaration in collection:
            declaration.inputs[:] = [sort_ref(index) for index in declaration.inputs]
            if declaration.DESCRIPTOR.name != "Relation":
                declaration.output = sort_ref(declaration.output)
            if declaration.DESCRIPTOR.name == "Constructor" and declaration.HasField("cost"):
                declaration.cost = node_ref(declaration.cost)
            if declaration.DESCRIPTOR.name == "Function" and declaration.HasField("merge"):
                raise UnsupportedProgram("function merge binders")
    for binding in result.rulesets:
        if not binding.HasField("value"):
            raise UnsupportedProgram("missing ruleset value")
        for rule in binding.value.rules:
            rule_refs(rule)
    for command in result.commands:
        command_refs(command)

    scalar_kinds = {"i64", "f64_bits", "string", "bool", "unit", "big_int", "big_rat", "rational"}

    def drain():
        while pending:
            index = pending.popleft()
            node = type(program.nodes[index])()
            node.CopyFrom(program.nodes[index])
            node.sort_id = sort_ref(node.sort_id)
            kind = node.WhichOneof("kind")
            if kind == "call":
                call_refs(node.call)
            elif kind == "eq":
                node.eq.members[:] = [node_ref(child) for child in node.eq.members]
            elif kind == "primitive_value":
                scalar = node.primitive_value.WhichOneof("value")
                if scalar not in scalar_kinds:
                    raise UnsupportedProgram(f"primitive value kind: {scalar}")
            elif kind not in {"var", "binding"}:
                raise UnsupportedProgram(f"node kind: {kind}")
            nodes[node_ids[index]] = node

    drain()
    leaves = defaultdict(list)
    for index, node in enumerate(program.nodes):
        if index in node_ids:
            continue
        kind = node.WhichOneof("kind")
        if kind not in {"var", "binding", "primitive_value"}:
            raise UnsupportedProgram("unanchored Call/Eq graph")
        if not 0 <= node.sort_id < len(program.sorts):
            raise UnsupportedProgram("unanchored leaf sort out of bounds")
        key_node = type(node)()
        key_node.CopyFrom(node)
        key_node.sort_id = 0
        leaves[(program.sorts[node.sort_id].SerializeToString(deterministic=True),
                key_node.SerializeToString(deterministic=True))].append(index)
    for key in sorted(leaves):
        group = leaves[key]
        referenced_sorts = {program.nodes[index].sort_id for index in group}
        if len(referenced_sorts) > 1:
            if not referenced_sorts <= sort_ids.keys():
                raise UnsupportedProgram("unanchored duplicate sort identities")
            group.sort(key=lambda index: sort_ids[program.nodes[index].sort_id])
        for index in group:
            node_ref(index)
        drain()
    for index in sorted(
        set(range(len(program.sorts))) - sort_ids.keys(),
        key=lambda index: program.sorts[index].SerializeToString(deterministic=True),
    ):
        sort_ref(index)
    del result.nodes[:]
    result.nodes.extend(nodes)
    del result.sorts[:]
    result.sorts.extend(sorts)
    assert len(result.nodes) == len(program.nodes)
    assert len(result.sorts) == len(program.sorts)
    return result
