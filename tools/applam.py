#!/usr/bin/env python3
"""Build `perf/app-lam` at n levels, from the real one's prelude.

    python3 tools/applam.py <n> <out.ndjson>      # the file's own shape
    FLAT=1 python3 tools/applam.py <n> <out>      # closed innermost body
    ONE=1  python3 tools/applam.py <n> <out>      # one recursive child

The shape is the file's own: at every level `wrap2` is applied to two copies
of one lambda, and the innermost body adds every binder. Both copies are one
expression entry, which is the sharing the file is about.

This is what found the fault that file was hiding. The real one is 1.2 MB at
about four thousand levels and answers or does not; a family at twelve to
forty levels says **how** the cost grows, and the two variants say which
part of the shape it grows with. `docs/perf-plan.md` has the numbers.
"""
import json, sys

SRC = "/Users/david/.cache/lean-kernel-arena/small/good/perf/app-lam.ndjson"
WRAP2, NATADD, NAT, DAG, XNAME = 108, 61, 1, 110, 63

def main():
    n = int(sys.argv[1]); out = sys.argv[2]
    keep, maxie = [], 0
    for l in open(SRC):
        d = json.loads(l)
        if isinstance(d, dict) and "ie" in d:
            maxie = max(maxie, int(d["ie"]))
        if isinstance(d, dict) and "def" in d and d["def"].get("name") == DAG:
            continue
        keep.append(l.rstrip("\n"))
    new = []
    nxt = [maxie + 1]
    def add(entry):
        i = nxt[0]; nxt[0] += 1
        entry["ie"] = i; new.append(entry); return i
    # the innermost body: Nat.add (... (Nat.add x1 x2) ...) xn
    def sum_of(k):
        # k binders in scope; the outermost is index k-1
        acc = add({"bvar": k - 1})
        for j in range(k - 2, -1, -1):
            f = add({"const": {"name": NATADD, "us": []}})
            b = add({"bvar": j})
            a1 = add({"app": {"fn": f, "arg": acc}})
            acc = add({"app": {"fn": a1, "arg": b}})
        return acc
    nat = add({"const": {"name": NAT, "us": []}})
    w2 = add({"const": {"name": WRAP2, "us": []}})
    # a trivial second argument, for the variant that has one recursive
    # child per level instead of two
    triv_b = add({"bvar": 0})
    triv = add({"lam": {"binderInfo": "default", "body": triv_b,
                        "name": XNAME, "type": nat}})
    import os
    one = os.environ.get("ONE") == "1"
    flat = os.environ.get("FLAT") == "1"
    def level(i):
        # i binders are already in scope; build the body of level i+1 .. n
        if i == n:
            # the open body adds every binder; the flat one reads the
            # innermost binder only
            return add({"bvar": 0}) if flat else sum_of(n)
        body = level(i + 1)
        lam = add({"lam": {"binderInfo": "default", "body": body,
                           "name": XNAME, "type": nat}})
        a1 = add({"app": {"fn": w2, "arg": lam}})
        return add({"app": {"fn": a1, "arg": triv if one else lam}})
    root = level(0)
    with open(out, "w") as f:
        for l in keep:
            print(l, file=f)
        for e in new:
            print(json.dumps(e), file=f)
        print(json.dumps({"def": {"all": [DAG], "hints": {"regular": 0},
                                  "levelParams": [], "name": DAG,
                                  "safety": "safe", "type": 1,
                                  "value": root}}), file=f)

main()
