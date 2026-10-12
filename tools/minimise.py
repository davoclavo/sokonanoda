#!/usr/bin/env python3
"""Cut one declaration out of an export, with everything it needs and nothing else.

  python3 minimise.py <export.ndjson> <name id> <out.ndjson> [--axioms]

A kernel that rejects declaration 11343 of a 9.8 MB export cannot be debugged
at that size. This walks the expression graph from the declaration's own type
and value, takes the closure of the expressions, levels and names it reaches,
and then the declarations those expressions name, to a fixed point.

--thm-axioms keeps every definition and turns only the theorems into axioms.
A theorem proves a proposition and proof irrelevance never unfolds its value,
so this is sound, and it is the mode to reach for: it cuts most of a corpus
away without the artefact below.

--axioms keeps only the type of every declaration the target names and emits
it as an axiom. That is far smaller, and it is enough whenever the rejection
does not need a definition unfolded.

Read an --axioms rejection carefully: it can be an artefact. Declaration
11343 of `perf/grind-ring-5` answered `reject` either way, but with --axioms
the blame fell on the constructor `HAdd.mk`, whose field is typed
`outParam (Sort (w+1))`. That is a sort only after `outParam` unfolds, and an
axiom does not unfold, so the universe check failed for a reason the real
export does not have. The full closure named the true cause.

This found the structure eta rule that was missing from reduction: the real
rejection was the theorem itself, 214 kB instead of 9.8 MB, and instant.
"""
import json, sys, collections

def main():
    src, target, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    as_axioms = "--axioms" in sys.argv
    thm_axioms = "--thm-axioms" in sys.argv
    meta = None
    names, levels, exprs, decls = {}, {}, {}, []
    for l in open(src):
        d = json.loads(l)
        if not isinstance(d, dict):
            continue
        if "meta" in d:
            meta = l.rstrip("\n")
        elif "in" in d:
            names[int(d["in"])] = (l.rstrip("\n"), d)
        elif "il" in d:
            levels[int(d["il"])] = (l.rstrip("\n"), d)
        elif "ie" in d:
            exprs[int(d["ie"])] = (l.rstrip("\n"), d)
        else:
            decls.append((l.rstrip("\n"), d))

    by_name = {}
    for i, (raw, d) in enumerate(decls):
        k = next(iter(d)); v = d[k]
        if k == "inductive":
            for t in v.get("types", []): by_name[int(t["name"])] = i
            for c in v.get("ctors", []): by_name[int(c["name"])] = i
            for r in v.get("recs", []): by_name[int(r["name"])] = i
        else:
            by_name[int(v["name"])] = i

    need_e, need_l, need_n = set(), set(), set()
    need_d, done_d = set(), set()
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
                want_e(int(d[k]["type"])); want_e(int(d[k]["body"]))
                want_n(int(d[k]["name"]))
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
        if "sort" in d:
            want_l(int(d["sort"]))

    def decl_exprs(d, types_only):
        k = next(iter(d)); v = d[k]
        got = []
        if k == "inductive":
            for t in v.get("types", []): got.append(int(t["type"]))
            for c in v.get("ctors", []): got.append(int(c["type"]))
            for r in v.get("recs", []):
                got.append(int(r["type"]))
                for rule in r.get("rules", []): got.append(int(rule["rhs"]))
            return got
        got.append(int(v["type"]))
        if not types_only and "value" in v:
            got.append(int(v["value"]))
        return got

    def decl_names(d):
        k = next(iter(d)); v = d[k]
        got = []
        if "name" in v: got.append(int(v["name"]))
        for ps in (v.get("levelParams") or []): want_l(int(ps))
        if k == "inductive":
            for t in v.get("types", []):
                got.append(int(t["name"]))
                for ps in (t.get("levelParams") or []): want_l(int(ps))
                for nm in (t.get("all") or []): got.append(int(nm))
                for nm in (t.get("ctors") or []): got.append(int(nm))
            for c in v.get("ctors", []):
                got.append(int(c["name"]))
                for ps in (c.get("levelParams") or []): want_l(int(ps))
            for r in v.get("recs", []):
                got.append(int(r["name"]))
                for ps in (r.get("levelParams") or []): want_l(int(ps))
                for nm in (r.get("all") or []): got.append(int(nm))
                for rule in r.get("rules", []): got.append(int(rule["ctor"]))
        for nm in (v.get("all") or []): got.append(int(nm))
        return got

    # the target itself
    tgt = decls[by_name[target]]
    keep = {by_name[target]}
    for e in decl_exprs(tgt[1], False): want_e(e)
    for n in decl_names(tgt[1]): want_n(n)

    while True:
        while qe or ql or qn:
            while qe: expr_step(qe.popleft())
            while ql:
                i = ql.popleft()
                ent = levels.get(i)
                if ent is None: continue
                d = ent[1]
                if "succ" in d: want_l(int(d["succ"]))
                for k in ("max", "imax"):
                    if k in d:
                        for x in d[k]: want_l(int(x))
                if "param" in d: want_n(int(d["param"]))
            while qn:
                i = qn.popleft()
                ent = names.get(i)
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
            k = next(iter(decls[j][1]))
            # an inductive block, a quotient and a recursor must stay whole;
            # anything else may become an axiom when that is asked for
            whole = k in ("inductive", "quot")
            # A theorem proves a proposition, and proof irrelevance means its
            # value is never unfolded, so dropping it is sound and is what
            # makes a cut small without the artefact that `--axioms` brings.
            drop_value = (as_axioms or (thm_axioms and k == "thm")) and not whole
            keep.add(j)
            for e in decl_exprs(decls[j][1], drop_value): want_e(e)
            for nm in decl_names(decls[j][1]): want_n(nm)

    def emit_decl(j):
        raw, d = decls[j]
        k = next(iter(d)); v = d[k]
        if k in ("inductive", "quot", "axiom"):
            return raw
        if not as_axioms and not (thm_axioms and k == "thm"):
            return raw
        return json.dumps({"axiom": {"isUnsafe": False,
                                     "levelParams": v.get("levelParams") or [],
                                     "name": v["name"], "type": v["type"]}},
                          separators=(",", ":"))

    with open(out, "w") as f:
        if meta: print(meta, file=f)
        for i in sorted(need_n):
            if i in names: print(names[i][0], file=f)
        for i in sorted(need_l):
            if i in levels: print(levels[i][0], file=f)
        for i in sorted(need_e):
            if i in exprs: print(exprs[i][0], file=f)
        for j in sorted(keep):
            if j == by_name[target]: continue
            print(emit_decl(j), file=f)
        print(decls[by_name[target]][0], file=f)
    print(f"{out}: {len(need_n)} names, {len(need_l)} levels, "
          f"{len(need_e)} expressions, {len(keep)} declarations")

main()
