"""The normalizer must expose every non-ordering change in the fixture."""

import random
import unittest

from google.protobuf import text_format
from normalizer import UnsupportedProgram, normalize, schema_messages

from gen.python.egglog.v1 import egglog_pb as generated

Program = schema_messages(generated)["Program"]


def fixture():
    return text_format.Parse('''
        sorts { eq: "Math" doc: "type metadata" }
        sorts { primitive { name: "i64" } }
        nodes { binding: "sum" }
        nodes { call { func: "Num" args: 2 } }
        nodes { sort_id: 1 primitive_value { i64: 5 } }
        nodes { var: "e" }
        nodes { eq { members: 3 members: 1 } }
        nodes { eq { members: 3 members: 1 } }
        constructors { name: "Num" inputs: 1 doc: "constructor metadata" }
        constructors { name: "Other" }
        functions { name: "value" inputs: 0 output: 1 }
        rulesets { name: "" value { rules { name: "fold" eval_mode: RULE_EVAL_MODE_SEMINAIVE
            rule { query: 4 actions { term: 5 }
                actions { set { target { func: "value" args: 3 } value: 2 } }
                actions { subsume { func: "Other" } } } } } }
        commands { let { binding: 0 value: 1 } }
        commands { run { rulesets { name: "" } } }
        commands { check { facts: 4 facts: 5 } }
        commands { extract { roots: 0 variants: 2 } }
        commands { freeze {} }
    ''', Program())


def permute(program, seed):
    """Independently permute fixture arenas and relocate every fixture reference."""
    rng = random.Random(seed)
    result = Program()
    result.CopyFrom(program)
    nodes = list(range(len(program.nodes)))
    sorts = list(range(len(program.sorts)))
    rng.shuffle(nodes)
    rng.shuffle(sorts)
    node_ids = {old: new for new, old in enumerate(nodes)}
    sort_ids = {old: new for new, old in enumerate(sorts)}
    del result.nodes[:]
    result.nodes.extend(program.nodes[index] for index in nodes)
    del result.sorts[:]
    result.sorts.extend(program.sorts[index] for index in sorts)
    for node in result.nodes:
        node.sort_id = sort_ids[node.sort_id]
        kind = node.WhichOneof("kind")
        if kind == "call":
            node.call.args[:] = [node_ids[index] for index in node.call.args]
        elif kind == "eq":
            node.eq.members[:] = [node_ids[index] for index in node.eq.members]
    for collection in (result.constructors, result.functions, result.relations):
        shuffled = list(collection)
        rng.shuffle(shuffled)
        del collection[:]
        collection.extend(shuffled)
        for declaration in collection:
            declaration.inputs[:] = [sort_ids[index] for index in declaration.inputs]
            if declaration.DESCRIPTOR.name != "Relation":
                declaration.output = sort_ids[declaration.output]
            if declaration.DESCRIPTOR.name == "Constructor" and declaration.HasField("cost"):
                declaration.cost = node_ids[declaration.cost]
    shuffled = list(result.rulesets)
    rng.shuffle(shuffled)
    del result.rulesets[:]
    result.rulesets.extend(shuffled)
    for binding in result.rulesets:
        for rule in binding.value.rules:
            rule.rule.query[:] = [node_ids[index] for index in rule.rule.query]
            for action in rule.rule.actions:
                kind = action.WhichOneof("kind")
                if kind == "term":
                    action.term = node_ids[action.term]
                elif kind == "set":
                    action.set.target.args[:] = [node_ids[index] for index in action.set.target.args]
                    action.set.value = node_ids[action.set.value]
                elif kind == "subsume":
                    action.subsume.args[:] = [node_ids[index] for index in action.subsume.args]
    for command in result.commands:
        kind = command.WhichOneof("kind")
        if kind == "let":
            command.let.binding = node_ids[command.let.binding]
            command.let.value = node_ids[command.let.value]
        elif kind == "check":
            command.check.facts[:] = [node_ids[index] for index in command.check.facts]
        elif kind == "extract":
            command.extract.roots[:] = [node_ids[index] for index in command.extract.roots]
    return result


class OrderingTests(unittest.TestCase):
    def test_permutations_and_idempotence(self):
        original = fixture()
        expected = normalize(original)
        for seed in range(30):
            actual = normalize(permute(original, seed))
            self.assertEqual(actual, expected)
            self.assertEqual(normalize(actual), actual)
        self.assertEqual(original, fixture(), "normalization mutated the input")

    def test_cardinality_aliases_cycles_and_unused_slots(self):
        original = fixture()
        original.nodes[5].eq.members.append(5)
        original.nodes.add(binding="unused")
        original.nodes.add(sort_id=1).primitive_value.i64 = 5
        original.nodes.add(sort_id=1).primitive_value.i64 = 5
        original.sorts.add(eq="Unused", doc="")
        expected = normalize(original)
        self.assertEqual(len(expected.nodes), len(original.nodes))
        self.assertEqual(len(expected.sorts), len(original.sorts))
        self.assertEqual(sum(node.WhichOneof("kind") == "eq" for node in expected.nodes), 2)
        for seed in range(20):
            self.assertEqual(normalize(permute(original, seed)), expected)
        facts = expected.rulesets[0].value.rules[0].rule
        union = facts.actions[0].term
        self.assertIn(union, expected.nodes[union].eq.members)
        self.assertNotEqual(facts.query[0], union)

    def test_every_nonordering_difference_remains_visible(self):
        original = fixture()
        expected = normalize(original)
        changes = {
            "callable name": lambda p: setattr(p.nodes[1].call, "func", "Renamed"),
            "binder name": lambda p: setattr(p.nodes[3], "var", "renamed"),
            "global name": lambda p: setattr(p.nodes[0], "binding", "renamed"),
            "documentation": lambda p: setattr(p.constructors[0], "doc", "changed"),
            "literal": lambda p: setattr(p.nodes[2].primitive_value, "i64", 6),
            "variant count": lambda p: setattr(p.commands[3].extract, "variants", 1),
            "membership": lambda p: p.rulesets.add(name="other", value=p.rulesets[0].value),
            "action order": lambda p: p.rulesets[0].value.rules[0].rule.actions.reverse(),
            "Eq sharing": lambda p: setattr(p.rulesets[0].value.rules[0].rule.actions[0], "term", 4),
            "Eq members": lambda p: p.nodes[5].eq.members.reverse(),
            "duplicate leaf": lambda p: p.nodes.add(sort_id=1).primitive_value.CopyFrom(p.nodes[2].primitive_value),
            "field presence": lambda p: setattr(p.constructors[0], "cost", 2),
        }
        for label, change in changes.items():
            with self.subTest(label=label):
                changed = fixture()
                change(changed)
                self.assertNotEqual(normalize(changed), expected)
        changed = fixture()
        run = type(changed.commands[1])()
        run.CopyFrom(changed.commands[1])
        changed.commands[1].Clear()
        changed.commands[1].loop.max_iterations = 1
        changed.commands[1].loop.body.add().CopyFrom(run)
        self.assertNotEqual(normalize(changed), expected)

    def test_duplicate_calls_are_not_merged(self):
        original = fixture()
        original.nodes.add().CopyFrom(original.nodes[1])
        original.commands[2].check.facts.append(len(original.nodes) - 1)
        actual = normalize(original)
        self.assertEqual(sum(node.WhichOneof("kind") == "call" for node in actual.nodes), 2)
        self.assertEqual(len(actual.nodes), len(original.nodes))

    def test_ordered_repeated_fields_stay_ordered(self):
        original = fixture()
        original.constructors[1].inputs.extend([0, 1])
        original.nodes[1].call.args.append(3)
        original.rulesets[0].value.rules[0].rule.query.append(5)
        other = original.rulesets[0].value.rules.add()
        other.CopyFrom(original.rulesets[0].value.rules[0])
        other.name = "second"
        original.commands[3].extract.roots.append(1)
        expected = normalize(original)
        for field in ("inputs", "args", "query", "rules", "facts", "roots", "commands"):
            with self.subTest(field=field):
                changed = Program()
                changed.CopyFrom(original)
                ordered = {
                    "inputs": changed.constructors[1].inputs,
                    "args": changed.nodes[1].call.args,
                    "query": changed.rulesets[0].value.rules[0].rule.query,
                    "rules": changed.rulesets[0].value.rules,
                    "facts": changed.commands[2].check.facts,
                    "roots": changed.commands[3].extract.roots,
                    "commands": changed.commands,
                }[field]
                ordered.reverse()
                self.assertNotEqual(normalize(changed), expected)

    def test_presence_scalar_bits_and_textproto_roundtrip(self):
        original = fixture()
        original.constructors[0].doc = ""
        original.nodes[2].primitive_value.f64_bits = 0x8000000000000000
        normalized = normalize(original)
        printed = text_format.MessageToString(normalized)
        self.assertEqual(text_format.Parse(printed, Program()), normalized)
        self.assertTrue(normalized.constructors[0].HasField("doc"))
        original.constructors[0].ClearField("doc")
        self.assertNotEqual(normalize(original), normalized)

    def test_unknown_or_unanchored_graphs_fail(self):
        original = fixture()
        original.nodes.add().eq.SetInParent()
        with self.assertRaisesRegex(UnsupportedProgram, "unanchored"):
            normalize(original)
        original = fixture()
        original.nodes[1].get_cost.func = "Num"
        with self.assertRaisesRegex(UnsupportedProgram, "node kind"):
            normalize(original)
        with self.assertRaisesRegex(UnsupportedProgram, "unknown"):
            normalize(Program.FromString(fixture().SerializeToString() + b"\xa0\x06\x01"))


if __name__ == "__main__":
    unittest.main()
