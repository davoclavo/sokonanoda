#!/usr/bin/env python3
"""Check every declaration of a large export on its own, and report the ones
the kernel gets wrong.

  BIN=<kernel binary> python3 tools/declsweep.py <export.ndjson> [--limit N]
                                                 [--start N] [--out DIR]

A corpus this kernel cannot read in sixty seconds still holds declarations it
answers wrongly, and a wrong answer matters more than a slow one. This loads
the export once, cuts each declaration out with the closure walk of
minimise.py, and checks each cut on its own. Every export in the arena's
`good` set is one Lean accepted, so a `reject` on any cut is a bug here.

A cut carries the declarations its target names, so a reject can belong to a
dependency rather than to the target. SOKO_REPORT names which one.
"""
import json, os, subprocess, sys, tempfile, collections

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

def load(src):
    meta, names, levels, exprs, decls = None, {}, {}, {}, []
    for l in open(src):
        d = json.loads(l)
        if not isinstance(d, dict):
            continue
        if "meta" in d: meta = l.rstrip("\n")
        elif "in" in d: names[int(d["in"])] = (l.rstrip("\n"), d)
        elif "il" in d: levels[int(d["il"])] = (l.rstrip("\n"), d)
        elif "ie" in d: exprs[int(d["ie"])] = (l.rstrip("\n"), d)
        else: decls.append((l.rstrip("\n"), d))
    return meta, names, levels, exprs, decls

def main():
    src = sys.argv[1]
    bin_ = os.environ["BIN"]
    limit = int(sys.argv[sys.argv.index("--limit") + 1]) if "--limit" in sys.argv else 10**9
    start = int(sys.argv[sys.argv.index("--start") + 1]) if "--start" in sys.argv else 0
    outdir = sys.argv[sys.argv.index("--out") + 1] if "--out" in sys.argv else tempfile.mkdtemp()
    os.makedirs(outdir, exist_ok=True)

    meta, names, levels, exprs, decls = load(src)
    print(f"{src}: {len(names)} names, {len(levels)} levels, "
          f"{len(exprs)} expressions, {len(decls)} declaration lines", flush=True)

    by_name = {}
    for i, (raw, d) in enumerate(decls):
        k = next(iter(d)); v = d[k]
        if k == "inductive":
            for t in v.get("types", []): by_name[int(t["name"])] = i
            for c in v.get("ctors", []): by_name[int(c["name"])] = i
            for r in v.get("recs", []): by_name[int(r["name"])] = i
        else:
            by_name[int(v["name"])] = i

    def name_str(i, seen=None):
        d = names.get(int(i))
        if d is None: return "?" + str(i)
        d = d[1]
        if "str" in d:
            p = int(d["str"]["pre"])
            return (name_str(p) + "." if p else "") + d["str"]["str"]
        if "num" in d:
            p = int(d["num"]["pre"])
            return (name_str(p) + "." if p else "") + str(d["num"]["i"])
        return "?"

    def cut(target):
        need_e, need_l, need_n = set(), set(), set()
        need_d, done_d, keep = set(), set(), {by_name[target]}
        qe, ql, qn = collections.deque(), collections.deque(), collections.deque()
        def want_e(i):
            if i not in need_e: need_e.add(i); qe.append(i)
        def want_l(i):
            if i not in need_l: need_l.add(i); ql.append(i)
        def want_n(i):
            if i not in need_n: need_n.add(i); qn.append(i)
        def expr_step(i):
            ent = exprs.get(i)
            if ent is None: return
            d = ent[1]
            if "app" in d:
                want_e(int(d["app"]["fn"])); want_e(int(d["app"]["arg"]))
            for k in ("lam", "forallE"):
                if k in d:
                    want_e(int(d[k]["type"])); want_e(int(d[k]["body"])); want_n(int(d[k]["name"]))
            if "letE" in d:
                v = d["letE"]
                want_e(int(v["type"])); want_e(int(v["value"])); want_e(int(v["body"]))
                want_n(int(v["name"]))
            if "proj" in d:
                want_e(int(d["proj"]["struct"])); want_n(int(d["proj"]["typeName"]))
                need_d.add(int(d["proj"]["typeName"]))
            if "const" in d:
                want_n(int(d["const"]["name"]))
                for u in d["const"].get("us", []): want_l(int(u))
                need_d.add(int(d["const"]["name"]))
            if "sort" in d: want_l(int(d["sort"]))
        def decl_exprs(d):
            k = next(iter(d)); v = d[k]; got = []
            if k == "inductive":
                for t in v.get("types", []): got.append(int(t["type"]))
                for c in v.get("ctors", []): got.append(int(c["type"]))
                for r in v.get("recs", []):
                    got.append(int(r["type"]))
                    for rule in r.get("rules", []): got.append(int(rule["rhs"]))
                return got
            got.append(int(v["type"]))
            if "value" in v: got.append(int(v["value"]))
            return got
        def decl_names(d):
            k = next(iter(d)); v = d[k]; got = []
            if "name" in v: got.append(int(v["name"]))
            for ps in (v.get("levelParams") or []): want_n(int(ps))
            if k == "inductive":
                for t in v.get("types", []):
                    got.append(int(t["name"]))
                    for ps in (t.get("levelParams") or []): want_n(int(ps))
                    for nm in (t.get("all") or []): got.append(int(nm))
                    for nm in (t.get("ctors") or []): got.append(int(nm))
                for c in v.get("ctors", []):
                    got.append(int(c["name"]))
                    for ps in (c.get("levelParams") or []): want_n(int(ps))
                for r in v.get("recs", []):
                    got.append(int(r["name"]))
                    for ps in (r.get("levelParams") or []): want_n(int(ps))
                    for nm in (r.get("all") or []): got.append(int(nm))
                    for rule in r.get("rules", []): got.append(int(rule["ctor"]))
            for nm in (v.get("all") or []): got.append(int(nm))
            return got
        tgt = decls[by_name[target]][1]
        for e in decl_exprs(tgt): want_e(e)
        for n in decl_names(tgt): want_n(n)
        while True:
            while qe or ql or qn:
                while qe: expr_step(qe.popleft())
                while ql:
                    i = ql.popleft(); ent = levels.get(i)
                    if ent is None: continue
                    d = ent[1]
                    if "succ" in d: want_l(int(d["succ"]))
                    for k in ("max", "imax"):
                        if k in d:
                            for x in d[k]: want_l(int(x))
                    if "param" in d: want_n(int(d["param"]))
                while qn:
                    i = qn.popleft(); ent = names.get(i)
                    if ent is None: continue
                    d = ent[1]
                    for k in ("str", "num"):
                        if k in d: want_n(int(d[k]["pre"]))
            fresh = [n for n in need_d if n not in done_d]
            if not fresh: break
            for n in fresh:
                done_d.add(n)
                j = by_name.get(n)
                if j is None or j in keep: continue
                keep.add(j)
                for e in decl_exprs(decls[j][1]): want_e(e)
                for nm in decl_names(decls[j][1]): want_n(nm)
        return need_n, need_l, need_e, keep

    targets = []
    for j, (raw, d) in enumerate(decls):
        k = next(iter(d))
        if k in ("def", "thm", "opaque", "axiom"):
            targets.append((j, int(d[k]["name"])))
        elif k == "inductive":
            for t in d[k].get("types", []): targets.append((j, int(t["name"])))
    targets = targets[start:start + limit]
    print(f"checking {len(targets)} declarations\n", flush=True)

    counts = collections.Counter(); bad = []
    for n, (j, nm) in enumerate(targets):
        need_n, need_l, need_e, keep = cut(nm)
        path = os.path.join(outdir, f"d{nm}.ndjson")
        with open(path, "w") as f:
            if meta: print(meta, file=f)
            for i in sorted(need_n):
                if i in names: print(names[i][0], file=f)
            for i in sorted(need_l):
                if i in levels: print(levels[i][0], file=f)
            for i in sorted(need_e):
                if i in exprs: print(exprs[i][0], file=f)
            for q in sorted(keep): print(decls[q][0], file=f)
        try:
            r = subprocess.run([bin_, "--threads", "4"],
                               env={**os.environ, "SOKO_EXPORT": path, "SOKO_REPORT": "1"},
                               capture_output=True, text=True, timeout=30)
            got = next((l[len("verdict "):] for l in r.stdout.splitlines()
                        if l.startswith("verdict ")), "error")
            got = "declined" if got.startswith("declined") else got
            why = [l.strip() for l in r.stdout.splitlines() if "REJECT" in l]
        except subprocess.TimeoutExpired:
            got, why = "timeout", []
        counts[got] += 1
        if got == "reject":
            bad.append((nm, name_str(nm), len(keep), why[:1]))
            print(f"  REJECT {name_str(nm)} (id {nm}, {len(keep)} decls) {why[:1]}", flush=True)
        elif n % 50 == 0:
            print(f"  .. {n}/{len(targets)} {dict(counts)}", flush=True)
        else:
            os.unlink(path)
    print(f"\n{dict(counts)}")
    print(f"{len(bad)} wrong answers, cuts kept in {outdir}")
    for nm, s, k, why in bad: print(f"  {s} (id {nm})")

main()
