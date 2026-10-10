#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Jeremy Chen
# SPDX-License-Identifier: Apache-2.0
"""Compare the speed of two or more checker builds on the arena corpora.

    tools/bench.py --reps 5 A=./a B=./b

Each build runs on each corpus `--reps` times, in round-robin order, so
machine load drifts across all builds instead of landing on one. The report
ranks by the median and also prints the best.

Trust the median. The best time looks attractive because noise only ever adds
time, but with few repetitions one lucky run moves it by 10 percent. Two
changes that measured as 8 percent wins on best times turned out to be noise
once the medians were compared over 9 repetitions.

The corpora come from the arena cache that tools/arena.py fills. Pick them
with --tests; the default is a spread of sizes.
"""

import argparse
import os
import statistics
import subprocess
import sys
import time
from pathlib import Path

CACHE = Path(os.environ.get("ARENA_CACHE", Path.home() / ".cache/lean-kernel-arena"))
BUILT = CACHE / "arena/_build/tests"
SMALL = CACHE / "small"

CHECKER_FLAGS = ["--stdin", "--nat-extension", "--string-extension", "--axiom-allow-all"]

DEFAULT_TESTS = ["init", "std", "cedar", "cslib", "mathlib"]


def find(name: str) -> Path:
    for candidate in (
        BUILT / f"{name}.ndjson",
        SMALL / "good" / f"{name}.ndjson",
        SMALL / "bad" / f"{name}.ndjson",
    ):
        if candidate.exists():
            return candidate
    for root in (SMALL / "good", SMALL / "bad", BUILT):
        if root.exists():
            hits = list(root.rglob(f"{name}.ndjson"))
            if hits:
                return hits[0]
    sys.exit(f"no export file for {name}; build it with tools/arena.py build {name}")


def one_run(binary: Path, path: Path, threads: int, env: dict) -> float:
    with open(path, "rb") as stdin:
        start = time.perf_counter()
        result = subprocess.run(
            [str(binary), *CHECKER_FLAGS, "--threads", str(threads), "-q"],
            stdin=stdin,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            env={**os.environ, **env},
            check=False,
        )
        elapsed = time.perf_counter() - start
    if result.returncode != 0:
        sys.exit(f"{binary} exited {result.returncode} on {path.name}")
    return elapsed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("builds", nargs="+", help="LABEL=path/to/binary")
    parser.add_argument("--reps", type=int, default=5, help="runs per build per test")
    parser.add_argument("--threads", type=int, default=4, help="checker threads")
    parser.add_argument("--tests", nargs="*", default=DEFAULT_TESTS)
    parser.add_argument(
        "--env",
        action="append",
        default=[],
        metavar="LABEL:NAME=VALUE",
        help="an extra environment variable for one build",
    )
    args = parser.parse_args()

    builds = {}
    for spec in args.builds:
        label, _, path = spec.partition("=")
        if not path:
            sys.exit(f"write builds as LABEL=path, not {spec!r}")
        builds[label] = Path(path).resolve()
    extra_env: dict[str, dict] = {label: {} for label in builds}
    for spec in args.env:
        label, _, assignment = spec.partition(":")
        name, _, value = assignment.partition("=")
        extra_env[label][name] = value

    # Warm the page cache once per test, so the first build does not pay for it.
    print(f"threads={args.threads}  reps={args.reps}\n")
    for test in args.tests:
        path = find(test)
        one_run(next(iter(builds.values())), path, args.threads, {})
        times: dict[str, list[float]] = {label: [] for label in builds}
        for _ in range(args.reps):
            for label, binary in builds.items():
                times[label].append(
                    one_run(binary, path, args.threads, extra_env[label])
                )
        size = path.stat().st_size / 1e6
        print(f"{test}  {size:.0f} MB")
        baseline = statistics.median(times[next(iter(builds))])
        for label in builds:
            best = min(times[label])
            median = statistics.median(times[label])
            delta = (median / baseline - 1) * 100
            print(
                f"  {label:14s} median={median:8.3f}s  best={best:8.3f}s"
                f"  {delta:+6.1f}%"
            )
        print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
