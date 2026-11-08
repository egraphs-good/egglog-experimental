"""Execute three real frontends and compare their public recorded Programs.

Run with a matching installed Python/native/SDK build and an explicitly supplied
Rust binary. This runner never builds code or repairs a producer's Program.
"""

import argparse
import difflib
import importlib.util
import subprocess
import sys
from pathlib import Path

from egglog import EGraph
from egglog.bindings import _ProtoEngine
from egglog_proto.egglog.v1 import egglog_pb as generated
from google.protobuf import text_format
from normalizer import normalize, schema_messages

HERE = Path(__file__).resolve().parent
TYPES = schema_messages(generated)
Program = TYPES["Program"]


def save_wire(directory, name, message, encoded=None):
    """Retain original wire bytes and a schema-derived, roundtrippable view."""
    encoded = message.SerializeToString() if encoded is None else encoded
    directory.mkdir(parents=True, exist_ok=True)
    (directory / f"{name}.pb").write_bytes(encoded)
    printed = text_format.MessageToString(message)
    assert text_format.Parse(printed, type(message)()) == message
    (directory / f"{name}.textproto").write_text(printed)


def execute(engine, handle, program, directory, name):
    """Capture an actual submission and require every native frame to succeed."""
    request = TYPES["RunProgramRequest"](egraph_id=handle, program=program)
    save_wire(directory, f"{name}.request", request)
    encoded_frames, host_error = engine.run(request.SerializeToString())
    assert host_error is None, host_error
    frames = []
    for index, encoded in enumerate(encoded_frames):
        frame = TYPES["RunProgramResponse"].FromString(encoded)
        save_wire(directory, f"{name}.response-{index:02d}", frame, encoded)
        assert frame.WhichOneof("result") == "output", text_format.MessageToString(frame)
        frames.append(frame)
    return frames


def create_engine(directory, recording):
    engine = _ProtoEngine()
    creation = text_format.Parse('''
        sorts { primitive { name: "i64" } }
        options { cost_sort: 0 seminaive: true }
        threads: 1
    ''', TYPES["CreateEGraphRequest"]())
    creation.record_history = recording
    save_wire(directory, "create.request", creation)
    encoded = engine.create(creation.SerializeToString())
    created = TYPES["CreateEGraphResponse"].FromString(encoded)
    save_wire(directory, "create.response", created, encoded)
    return engine, created.egraph_id


def capture_source(directory):
    engine, handle = create_engine(directory, recording=True)
    source = _ProtoEngine.source((HERE / "constant-folding.egg").read_text())
    frames = []
    index = 0
    while (submission := source.next_submission()) is not None:
        kind, encoded, pending = submission
        assert kind == "program" and pending == 0
        frames.extend(execute(engine, handle, Program.FromString(encoded), directory, f"run-{index:02d}"))
        index += 1
    # Freeze is a host observation, not Egglog syntax or a replacement frontend.
    frames.extend(execute(engine, handle, text_format.Parse("commands { freeze {} }", Program()), directory, "freeze"))
    request = TYPES["GetHistoryRequest"](egraph_id=handle)
    encoded = engine.get_history(request.SerializeToString())
    history = Program.FromString(encoded)
    save_wire(directory, "history", history, encoded)
    assert_observations(frames)
    return history


def assert_observations(frames):
    """Verify extraction cost and the returned reconstruction, without rewriting."""
    snapshots = []
    extracted = []
    reports = []
    for frame in frames:
        for output in frame.output.outputs:
            kind = output.WhichOneof("kind")
            if kind == "snapshot":
                snapshots.append(output.snapshot)
            elif kind == "run":
                reports.append(output.run)
            elif kind == "extraction":
                for root in output.extraction.roots:
                    for variant in root.variants:
                        term = frame.output.nodes[variant.term]
                        assert term.WhichOneof("kind") == "call" and term.call.func == "Num"
                        assert len(term.call.args) == 1
                        assert frame.output.nodes[term.call.args[0]].primitive_value.i64 == 5
                        assert variant.HasField("cost")
                        assert frame.output.nodes[variant.cost].primitive_value.i64 == 2
                        extracted.append("Num(5)")
    assert extracted == ["Num(5)"]
    assert len(reports) == 1 and reports[0].updated and not reports[0].can_stop
    assert len(snapshots) == 1
    assert_snapshot(snapshots[0])


def assert_snapshot(snapshot):
    """Check concrete class-reference edges, table storage and subsumption."""
    program = snapshot.program
    cost_sort = program.sorts[snapshot.options.cost_sort]
    assert cost_sort.WhichOneof("kind") == "primitive" and cost_sort.primitive.name == "i64"
    assert snapshot.options.seminaive
    lets = [command.let for command in program.commands if command.WhichOneof("kind") == "let"]
    assert len(lets) == 1 and program.nodes[lets[0].binding].binding == "sum"
    root = lets[0].value
    assert program.nodes[root].WhichOneof("kind") == "eq"
    members = {program.nodes[index].call.func: program.nodes[index].call for index in program.nodes[root].eq.members}
    assert len(program.nodes[root].eq.members) == 2 and set(members) == {"Num", "Add"}
    assert program.nodes[members["Num"].args[0]].primitive_value.i64 == 5
    children = list(members["Add"].args)
    assert len(children) == 2 and len({root, *children}) == 3
    for child, literal in zip(children, (2, 3), strict=True):
        node = program.nodes[child]
        assert node.WhichOneof("kind") == "eq" and len(node.eq.members) == 1
        producer = program.nodes[node.eq.members[0]]
        assert producer.WhichOneof("kind") == "call" and producer.call.func == "Num"
        assert len(producer.call.args) == 1
        assert program.nodes[producer.call.args[0]].primitive_value.i64 == literal
    actions = [command.action for command in program.commands if command.WhichOneof("kind") == "action"]
    terms = [action.term for action in actions if action.WhichOneof("kind") == "term"]
    assert len(actions) == 5 and len(terms) == 3 and set(terms) == {root, *children}
    sets = [action.set for action in actions if action.WhichOneof("kind") == "set"]
    assert len(sets) == 1 and sets[0].target.func == "value"
    assert list(sets[0].target.args) == [root]
    assert program.nodes[sets[0].value].primitive_value.i64 == 5
    subsumed = [action.subsume for action in actions if action.WhichOneof("kind") == "subsume"]
    assert len(subsumed) == 1 and subsumed[0].func == "Add"
    assert list(subsumed[0].args) == children
    assert len(program.rulesets) == 1 and program.rulesets[0].name == ""
    assert len(program.rulesets[0].value.rules) == 1
    assert program.rulesets[0].value.rules[0].name == "fold"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rust-binary", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True, help="raw capture directory")
    parser.add_argument("--update-expected", action="store_true", help="intentionally replace the one reviewed golden, after three-way equality")
    args = parser.parse_args()
    inputs = Program.DESCRIPTOR.fields_by_name["constructors"].message_type.fields_by_name["inputs"]
    if inputs.type != inputs.TYPE_UINT32:
        parser.error("install the matching SDK with flattened sort-index signatures")
    args.output.mkdir(parents=True, exist_ok=True)
    programs = {"source": capture_source(args.output / "source")}
    spec = importlib.util.spec_from_file_location("constant_folding", HERE / "constant_folding.py")
    example = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(example)
    graph = EGraph(record_history=True)
    try:
        example.run_example(graph)
        snapshot = graph.freeze().to_binary()
        history = graph.history().to_binary()
    finally:
        graph.close()
    programs["python"] = Program.FromString(history)
    Snapshot = type(TYPES["RunProgramResponse"]().output.outputs.add().snapshot)
    assert_snapshot(Snapshot.FromString(snapshot))
    save_wire(args.output / "python", "history", programs["python"], history)
    save_wire(args.output / "python", "snapshot", Snapshot.FromString(snapshot), snapshot)
    rust_history = args.output / "rust" / "history.pb"
    rust_history.parent.mkdir(exist_ok=True)
    subprocess.run([str(args.rust_binary.resolve()), str(rust_history.resolve())], check=True, timeout=120)
    programs["rust"] = Program.FromString(rust_history.read_bytes())
    save_wire(rust_history.parent, "history", programs["rust"], rust_history.read_bytes())
    # The typed API returns terms without costs. Verify that omitted observation
    # only by replaying the exact unchanged history on a separate fresh engine.
    replay_directory = args.output / "rust-replay"
    replay_engine, replay_handle = create_engine(replay_directory, recording=False)
    assert_observations(execute(replay_engine, replay_handle, programs["rust"], replay_directory, "run"))
    normalized = {name: normalize(program) for name, program in programs.items()}
    printed = {name: text_format.MessageToString(program) for name, program in normalized.items()}
    for name, text in printed.items():
        (args.output / name / "normalized.textproto").write_text(text)
    for name in ("python", "rust"):
        if normalized[name] != normalized["source"]:
            diff = "".join(difflib.unified_diff(printed["source"].splitlines(True), printed[name].splitlines(True), fromfile="source", tofile=name))
            raise AssertionError(f"{name} differs from Source after ordering only:\n{diff}")
        assert printed[name] == printed["source"]
    expected_path = HERE / "constant-folding.expected.textproto"
    if args.update_expected:
        expected_path.write_text(printed["source"])
    expected_text = expected_path.read_text()
    expected = text_format.Parse(expected_text, Program())
    assert normalize(expected) == expected, "expected file is not normalized"
    assert normalized["source"] == expected
    assert printed["source"] == expected_text
    print(f"Source, Python and Rust match {expected_path}; captures: {args.output}")
    print("Rust cost 2 is a separate unchanged-history replay observation; original typed snapshot assertions run in the binary.")
    print(f"Python: {sys.executable}; SDK: {generated.__file__}")


if __name__ == "__main__":
    main()
