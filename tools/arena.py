#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Jeremy Chen
# SPDX-License-Identifier: Apache-2.0
"""Run the Lean Kernel Arena test suite against this checker.

The arena lives at <https://arena.lean-lang.org>. It runs a checker on Lean
export files and reads the exit code: 0 accept, 1 reject, 2 declined, other
error. This script does the same thing on your machine.

    tools/arena.py fetch           download the small tests and the expected outcomes
    tools/arena.py build init std  build a large corpus export with the arena tooling
    tools/arena.py run             run the checker on every export file present
    tools/arena.py run mathlib     run only the tests whose name matches an argument

`fetch` takes a few seconds. `build` needs elan and uv, clones the arena, and
can take hours for mathlib. Everything lands in the cache directory, so a
second run of the same command costs nothing.

Set ARENA_CACHE to move the cache. The default is ~/.cache/lean-kernel-arena.
Set SOKONANODAZO to name a binary other than target/release/sokonanodazo.
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
import tarfile
import time
import urllib.request
from pathlib import Path

ARENA_URL = "https://arena.lean-lang.org"
ARENA_REPO = "https://github.com/leanprover/lean-kernel-arena"
TESTS_TARBALL = f"{ARENA_URL}/lean-arena-tests.tar.gz"
RESULTS_JSON = f"{ARENA_URL}/results.json"

# The flags the arena uses for the parent checker; see checkers/sokonanoda.yaml.
CHECKER_FLAGS = [
    "--stdin",
    "--nat-extension",
    "--string-extension",
    "--axiom-allow-all",
    "--threads",
    "4",
]

REPO_ROOT = Path(__file__).resolve().parent.parent
CACHE = Path(os.environ.get("ARENA_CACHE", Path.home() / ".cache/lean-kernel-arena"))
SMALL_TESTS = CACHE / "small"
ARENA_CLONE = CACHE / "arena"
RESULTS_FILE = CACHE / "results.json"

# Exit code -> label the arena uses.
STATUS = {0: "accept", 1: "reject", 2: "declined"}


def binary() -> Path:
    path = Path(os.environ.get("SOKONANODAZO", REPO_ROOT / "target/release/sokonanodazo"))
    if not path.exists():
        sys.exit(f"no checker binary at {path}; run `devbox run build` first")
    return path


def download(url: str, dest: Path) -> None:
    dest.parent.mkdir(parents=True, exist_ok=True)
    print(f"  download {url}")
    tmp = dest.with_suffix(dest.suffix + ".part")
    with urllib.request.urlopen(url) as response, open(tmp, "wb") as out:
        shutil.copyfileobj(response, out)
    tmp.rename(dest)


def expected_outcomes() -> dict[str, dict]:
    """Name -> test metadata, from the arena's published results."""
    if not RESULTS_FILE.exists():
        download(RESULTS_JSON, RESULTS_FILE)
    data = json.loads(RESULTS_FILE.read_text())
    return {test["name"]: test for test in data["tests"]}


def cmd_fetch(_args) -> int:
    """Download the expected outcomes and the small export files."""
    if not RESULTS_FILE.exists():
        download(RESULTS_JSON, RESULTS_FILE)
    if (SMALL_TESTS / "good").is_dir():
        print(f"  small tests already in {SMALL_TESTS}")
    else:
        tarball = CACHE / "lean-arena-tests.tar.gz"
        if not tarball.exists():
            download(TESTS_TARBALL, tarball)
        print(f"  extract into {SMALL_TESTS}")
        SMALL_TESTS.mkdir(parents=True, exist_ok=True)
        with tarfile.open(tarball) as tar:
            # The `filter` argument arrived in Python 3.12.
            if sys.version_info >= (3, 12):
                tar.extractall(SMALL_TESTS, filter="data")
            else:
                tar.extractall(SMALL_TESTS)
    print(f"  {len(list(exports()))} export files available")
    return 0


def clone_arena() -> Path:
    if (ARENA_CLONE / "lka.py").exists():
        subprocess.run(["git", "pull", "--ff-only"], cwd=ARENA_CLONE, check=False)
    else:
        ARENA_CLONE.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "clone", ARENA_REPO, str(ARENA_CLONE)], check=True)
    return ARENA_CLONE


def cmd_build(args) -> int:
    """Build the export file for each named test with the arena tooling."""
    if not args.names:
        sys.exit("name at least one test, for example: arena.py build init std")
    for tool in ("elan", "uv"):
        if shutil.which(tool) is None:
            sys.exit(f"{tool} is not on PATH; run this under `devbox shell`")
    arena = clone_arena()
    failed = []
    for name in args.names:
        print(f"=== build {name} ===", flush=True)
        start = time.time()
        result = subprocess.run(
            ["uv", "run", "lka.py", "build-test", name], cwd=arena, check=False
        )
        print(f"  {name}: exit {result.returncode} in {time.time() - start:.0f}s", flush=True)
        if result.returncode != 0:
            failed.append(name)
    for name in failed:
        print(f"FAIL build {name}")
    return 1 if failed else 0


def exports() -> list[tuple[str, Path]]:
    """Every export file in the cache, as (arena test name, path) pairs.

    The small tarball lays tests out as good/<name>.ndjson or bad/<name>.ndjson
    and drops the group directory, so `bad/tutorial/140_x` arrives as
    `bad/tutorial/140_x`. The arena tooling writes `_build/tests/<name>.ndjson`.
    """
    found: dict[str, Path] = {}
    for root in (SMALL_TESTS / "good", SMALL_TESTS / "bad"):
        for path in sorted(root.rglob("*.ndjson")):
            found[str(path.relative_to(root)).removesuffix(".ndjson")] = path
    built = ARENA_CLONE / "_build/tests"
    if built.exists():
        for path in sorted(built.rglob("*.ndjson")):
            name = str(path.relative_to(built)).removesuffix(".ndjson")
            # `work/` holds the source checkouts, which carry export files of
            # their own. Only the files the arena produced are tests.
            if not name.startswith("work/"):
                found[name] = path
    return sorted(found.items())


def verdict(expected: str, code: int) -> str:
    """Compare the arena's expected outcome with an exit code."""
    if code == 2:
        return "DECLINED"
    if code not in STATUS:
        return "ERROR"
    if expected == "either":
        return "ok"
    return "ok" if STATUS[code] == expected else "WRONG"


def cmd_run(args) -> int:
    checker = binary()
    tests = expected_outcomes()
    available = exports()
    if not available:
        sys.exit("no export files; run `arena.py fetch` first")
    if args.names:
        available = [
            (name, path)
            for name, path in available
            if any(want in name for want in args.names)
        ]
    print(f"{checker}  {len(available)} tests\n")
    counts: dict[str, int] = {}
    bad: list[str] = []
    for name, path in available:
        meta = tests.get(name, {})
        expected = meta.get("outcome", "?")
        timeout = meta.get("timeout")
        start = time.time()
        with open(path, "rb") as stdin:
            try:
                code = subprocess.run(
                    [str(checker), *CHECKER_FLAGS, "-q"],
                    stdin=stdin,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.PIPE,
                    timeout=timeout,
                    check=False,
                ).returncode
            except subprocess.TimeoutExpired:
                code = -1
        elapsed = time.time() - start
        mark = verdict(expected, code)
        counts[mark] = counts.get(mark, 0) + 1
        if mark != "ok":
            bad.append(f"{name}: expected {expected}, exit {code}")
        if mark != "ok" or args.verbose or elapsed > 1:
            print(f"  {mark:9s} {name:44s} want={expected:7s} exit={code:3d} {elapsed:7.2f}s")
    print()
    print("  ".join(f"{mark}={count}" for mark, count in sorted(counts.items())))
    missing = sorted(set(tests) - {name for name, _ in exports()})
    if missing and not args.names:
        print(f"\n{len(missing)} tests have no local export file:")
        for name in missing:
            print(f"  {name}  ({tests[name].get('size_str', '?')})")
        print("Build one with: devbox run arena-build <name>")
    for line in bad:
        print(f"FAIL {line}")
    return 1 if bad else 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("fetch", help="download the small tests and expected outcomes")
    build = sub.add_parser("build", help="build a large corpus export")
    build.add_argument("names", nargs="*", help="arena test names, e.g. init std")
    run = sub.add_parser("run", help="run the checker on every export file present")
    run.add_argument("names", nargs="*", help="only run tests whose name contains this")
    run.add_argument("-v", "--verbose", action="store_true", help="print every test")
    args = parser.parse_args()
    # A devbox script forwards all of its arguments as one string, so split again.
    if hasattr(args, "names"):
        args.names = [part for name in args.names for part in name.split()]
    return {"fetch": cmd_fetch, "build": cmd_build, "run": cmd_run}[args.command](args)


if __name__ == "__main__":
    sys.exit(main())
