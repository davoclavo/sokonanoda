#!/usr/bin/env python3
"""Score the Bend 2 kernel core against the arena's tutorial corpus.

    tools/bend-corpus.py                     # build the checker, then score it
    tools/bend-corpus.py --checker ./built   # score a checker that is already built
    tools/bend-corpus.py --group tutorial    # one group; the default is all of them

The checker writes its verdict on stdout as `verdict accept`, `verdict reject`
or `verdict declined (...)`, and its exit code is 0 either way. So the verdict
is read from the output, not from the code.

A file under `good/` is expected to be accepted and one under `bad/` to be
rejected. A decline is neither right nor wrong: it is the work that remains.
The one thing that must stay at zero is a **wrong verdict**, because a wrong
accept is a false theorem and a wrong reject is a correct program refused.
"""

import argparse
import os
import subprocess
import sys
import time
from pathlib import Path

CACHE = Path(os.environ.get("ARENA_CACHE", Path.home() / ".cache/lean-kernel-arena"))
SMALL = CACHE / "small"
REPO = Path(__file__).resolve().parent.parent


def build(into: Path) -> Path:
    """Compiles the checker. The built one is about twelve times faster."""
    print("building the checker ...", file=sys.stderr)
    subprocess.run(
        [str(REPO / "tools/bend.sh"), "bend/check.bend", "-o", str(into)],
        cwd=REPO,
        check=True,
        stdout=subprocess.DEVNULL,
    )
    # This machine will not run a freshly built binary until it is signed.
    subprocess.run(["codesign", "-f", "-s", "-", str(into)], capture_output=True)
    return into


def verdict(checker: Path, export: Path, threads: int, timeout: int) -> tuple[str, float]:
    """Runs the checker on one export and returns its verdict and its time."""
    started = time.monotonic()
    try:
        done = subprocess.run(
            [str(checker), "--threads", str(threads)],
            env={**os.environ, "SOKO_EXPORT": str(export)},
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return "timeout", float(timeout)
    took = time.monotonic() - started
    for line in reversed(done.stdout.splitlines()):
        if line.startswith("verdict "):
            word = line.split()[1]
            return (word if word in ("accept", "reject", "declined") else "error"), took
    return "error", took


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--checker", help="a checker that is already built")
    parser.add_argument("--group", default="", help="only files under this group")
    parser.add_argument("--threads", type=int, default=4)
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--verbose", action="store_true", help="name every file")
    args = parser.parse_args()

    if not SMALL.is_dir():
        print(f"no corpus at {SMALL}. Run tools/arena.py fetch", file=sys.stderr)
        return 1

    checker = (
        Path(args.checker).resolve()
        if args.checker
        else build(REPO / "target/bend-checker")
    )

    cases = []
    for expected, folder in (("accept", "good"), ("reject", "bad")):
        root = SMALL / folder / args.group if args.group else SMALL / folder
        for path in sorted(root.rglob("*.ndjson")):
            cases.append((expected, path))
    if not cases:
        print("no cases matched", file=sys.stderr)
        return 1

    tally = {
        "correct accept": 0,
        "correct reject": 0,
        "honest decline": 0,
        "wrongly accepted": 0,
        "wrongly rejected": 0,
        "error or timeout": 0,
    }
    wrong = []
    total_time = 0.0
    for expected, path in cases:
        got, took = verdict(checker, path, args.threads, args.timeout)
        total_time += took
        if got in ("error", "timeout"):
            key = "error or timeout"
            wrong.append((path, expected, got))
        elif got == "declined":
            key = "honest decline"
        elif got == expected:
            key = f"correct {got}"
        else:
            key = "wrongly accepted" if got == "accept" else "wrongly rejected"
            wrong.append((path, expected, got))
        tally[key] += 1
        if args.verbose:
            print(f"  {got:9} expect {expected:7} {path.name}")

    print(f"\nagainst {len(cases)} files of the arena corpus\n")
    print(f"| {'':24} | count |")
    print("|--------------------------|-------|")
    for key, count in tally.items():
        mark = " **" if key.startswith(("wrongly", "error")) and count else "   "
        print(f"| {key:24} |{mark}{count:4} |")
    verdicts = tally["correct accept"] + tally["correct reject"]
    print(f"\n{verdicts} verdicts, all correct" if not wrong else "")
    print(f"{total_time:.1f}s total, {1000 * total_time / len(cases):.0f}ms a file")

    if wrong:
        print("\nwrong answers, which must stay at zero:")
        for path, expected, got in wrong[:20]:
            print(f"  {got:9} expect {expected:7} {path}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
