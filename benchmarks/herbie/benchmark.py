#!/usr/bin/env python3
# /// script
# requires-python = ">=3.11"
# dependencies = ["scipy>=1.11"]
# ///
"""Compare two prebuilt CLIs on the fixed Herbie examples (macOS/Linux)."""

import argparse
import hashlib
import json
import math
import os
import platform
import signal
import statistics
import subprocess
import sys
import tempfile
import threading
import time
from contextlib import suppress
from pathlib import Path

from scipy import __version__ as scipy_version
from scipy import stats

ROOT = Path(__file__).resolve().parents[2]
FILES = [16, 15, 17, 66, 88]


def witness(output, source):
    """Preserve extract multiplicity, flags and sizes while ignoring variant order."""
    groups, flags, sizes = [], [], []
    active = None
    for line in output.splitlines():
        line = line.strip()
        if line == "(":
            assert active is None
            active = []
        elif line == ")":
            assert active is not None
            groups.append(sorted(active))
            active = None
        elif active is not None:
            active.append(line)
        elif line in ("true", "false"):
            flags.append(line)
        elif line:
            sizes.append(line)
    assert active is None
    assert len(groups) == source.count("(extract (const")
    assert len(flags) == source.count("(extract (bad-merge?))")
    return {"variants": groups, "flags": flags, "sizes": sizes}


def run(binary, workload, timeout):
    """Measure one child, capturing normal output and that child's peak RSS."""
    command = [str(binary), "--mode", "normal", "-j", "1", str(workload)]
    start = time.perf_counter()
    with tempfile.TemporaryFile() as output, tempfile.TemporaryFile() as error:
        process = subprocess.Popen(
            command,
            cwd=ROOT,
            env=dict(os.environ, RUST_LOG="error"),
            stdout=output,
            stderr=error,
            start_new_session=True,
        )
        finished, expired = threading.Event(), threading.Event()

        def expire():
            if not finished.is_set():
                expired.set()
                with suppress(ProcessLookupError):
                    os.killpg(process.pid, signal.SIGKILL)

        timer = threading.Timer(timeout, expire)
        try:
            timer.start()
            _, status, usage = os.wait4(process.pid, 0)
            process.returncode = os.waitstatus_to_exitcode(status)
        except BaseException:
            with suppress(ProcessLookupError):
                os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            raise
        finally:
            finished.set()
            timer.cancel()
            timer.join()
        wall_sec = time.perf_counter() - start
        output.seek(0)
        stdout = output.read().decode()
        error.seek(0)
        result = {
            "status": "timed-out"
            if expired.is_set()
            else "failure"
            if process.returncode
            else "success",
            "wall_sec": wall_sec,
            "max_rss_bytes": usage.ru_maxrss
            * (1 if sys.platform == "darwin" else 1024),
            "returncode": process.returncode,
        }
        if result["status"] == "success":
            try:
                parsed = witness(stdout, workload.read_text())
            except AssertionError:
                result.update(
                    status="failure",
                    error="Malformed or incomplete output witness.",
                    stdout_tail=stdout[-2000:],
                )
            else:
                result["witness_sha256"] = hashlib.sha256(
                    json.dumps(parsed, sort_keys=True).encode()
                ).hexdigest()
        else:
            result["error"] = error.read().decode(errors="replace")[-2000:]
        return result


def ratio(before, after):
    """Independent Fieller ratio with the smaller sample's Student-t critical value."""
    a, b = statistics.fmean(before), statistics.fmean(after)
    result = {"point": b / a, "ci_low": None, "ci_high": None}
    t2 = float(stats.t.ppf(0.975, min(len(before), len(after)) - 1)) ** 2
    denominator = a * a - t2 * statistics.variance(before) / len(before)
    other = b * b - t2 * statistics.variance(after) / len(after)
    discriminant = (a * b) ** 2 - denominator * other
    if denominator > 0 and discriminant >= 0:
        center, width = a * b / denominator, math.sqrt(discriminant) / denominator
        result.update(ci_low=center - width, ci_high=center + width)
    return result


def summarize(path):
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    assert rows[-1]["kind"] == "completed", (
        "Collection is incomplete; failures remain in the JSONL."
    )
    meta, summary = rows[0], []
    for name in meta["inputs"]:
        for metric in ["wall_sec", "max_rss_bytes"]:
            samples = []
            for endpoint in ["A", "B"]:
                selected = [
                    r
                    for r in rows
                    if r["kind"] == "observation"
                    and r["file"] == name
                    and r["endpoint"] == endpoint
                ]
                assert len(selected) == 2 * meta["blocks"]
                assert all(r["result"]["status"] == "success" for r in selected)
                samples.append([r["result"][metric] for r in selected])
            row = {
                "file": name,
                "metric": metric,
                "before_mean": statistics.fmean(samples[0]),
                "after_mean": statistics.fmean(samples[1]),
                "ratio": ratio(*samples),
            }
            summary.append(row)
            print(json.dumps(row))
    path.with_suffix(".summary.json").write_text(json.dumps(summary, indent=2) + "\n")


def collect(args):
    if sys.platform not in ("darwin", "linux"):
        raise SystemExit(
            "Collection requires macOS or Linux for per-child wait4 RSS accounting."
        )
    binaries = {
        "A": args.before.resolve(strict=True),
        "B": args.after.resolve(strict=True),
    }
    inputs = {
        f"rewrite{n}.egg": ROOT / f"examples/herbie/rewrite{n}.egg" for n in args.files
    }
    hashes = {
        str(p): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in [*binaries.values(), *inputs.values()]
    }
    meta = {
        "kind": "collection",
        "format_version": 1,
        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "binaries": {k: str(v) for k, v in binaries.items()},
        "inputs": list(inputs),
        "sha256": hashes,
        "blocks": args.blocks,
        "sequence": "ABBA",
        "warmups_per_endpoint_per_dump": 1,
        "mode": "normal",
        "proofs": False,
        "threads": 1,
        "timeout_sec": args.timeout,
        "host": platform.platform(),
        "python": sys.version,
        "scipy": scipy_version,
        "driver_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "environment": {
            k: v
            for k, v in os.environ.items()
            if k.startswith(("CARGO_", "RUST", "EGGLOG_"))
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x") as stream:
        stream.write(json.dumps(meta) + "\n")
        stream.flush()
        for name, workload in inputs.items():
            expected = None
            schedule = [("warmup", None, i, e) for i, e in enumerate("AB")]
            schedule += [
                ("observation", block, order, e)
                for block in range(args.blocks)
                for order, e in enumerate("ABBA")
            ]
            for kind, block, order, endpoint in schedule:
                result = run(binaries[endpoint], workload, args.timeout)
                row = {
                    "kind": kind,
                    "file": name,
                    "block": block,
                    "order": order,
                    "endpoint": endpoint,
                    "result": result,
                }
                stream.write(json.dumps(row) + "\n")
                stream.flush()
                if result["status"] != "success":
                    raise SystemExit(
                        f"{name}: {endpoint} {result['status']}; incomplete collection preserved."
                    )
                if expected is None:
                    expected = result["witness_sha256"]
                if result["witness_sha256"] != expected:
                    raise SystemExit(
                        f"{name}: output witness mismatch; incomplete collection preserved."
                    )
            print(f"{name}: {args.blocks * 2} observations per endpoint", flush=True)
        assert hashes == {
            str(p): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in [*binaries.values(), *inputs.values()]
        }
        stream.write(
            json.dumps({"kind": "completed", "integrity_verified": True}) + "\n"
        )
    summarize(args.output)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    compare = commands.add_parser("collect")
    compare.add_argument("--before", type=Path, required=True)
    compare.add_argument("--after", type=Path, required=True)
    compare.add_argument("--output", type=Path, required=True)
    compare.add_argument("--files", nargs="+", type=int, choices=FILES, default=FILES)
    compare.add_argument("--blocks", type=int, default=10)
    compare.add_argument("--timeout", type=float, default=30)
    summary = commands.add_parser("summarize")
    summary.add_argument("report", type=Path)
    args = parser.parse_args()
    if args.command == "collect":
        if (
            args.blocks < 1
            or args.timeout <= 0
            or len(set(args.files)) != len(args.files)
        ):
            parser.error("Require positive blocks/timeout and distinct files.")
        collect(args)
    else:
        summarize(args.report)
