# The closure plan: what the nine files need, and how to build it in stages

This is the design for the one piece of work that can take the Bend kernel in
`bend/` from 186 of 195 to the rest of them. Everything else has been
measured and rejected; `docs/perf-plan.md` carries the numbers, B20 to B24.

## What is wrong now

Reduction substitutes **eagerly**. A beta step walks the body and puts the
value at every variable, so the result is a new term, and an expression that
was one object becomes as many objects as the body has variables.

That is what the arena's hardest tests are built to punish.
`perf/shared-subterm` states

```
ldepth (perfect n leaf) = ldepth2 (perfect n leaf)
```

by `refl`, with `n` a tower of 1,100 `succ`. The recursor's own rule for a
node is

```
succ (max (rec t) (rec t))
```

The field `t` is one object, and the two `rec t` are **two computations** on
it. Four more of the nine are the `magma-*` family, which exists to punish
exactly this.

Two things that look like fixes are not, and both were measured:

**A memo from a term to its reduced form does not hit.** Given a free key --
the probe accepted a bucket's first entry with no comparison, which is what a
hash stored in each node would cost -- `perf/shared-subterm` filled 64.8 GB
and the process died. Nearly every term it stores is distinct, because each
of the two repeated computations carries its own accumulated substitution.
Two terms that mean the same thing are not the same syntax.

**Reducing the argument before substituting does not help.** What is
duplicated is the computation and not the value.

## What is needed

The shared subterm has to stay **one object through substitution**. That is a
closure: a body together with an environment, where instantiating a binder
pushes a value onto the environment instead of copying it into the body. Then
the two `rec t` read one environment slot, the first reduction **updates**
that slot, and the second finds the answer already there. The identity
problem that killed the memo does not arise, because the identity is the slot
and not the syntax.

This is lazy graph reduction, and the slot update is the whole point: it is a
memo whose key is a position rather than a term.

## The shape of it

Three new pieces, and one rule about where they may be seen.

```
# A slot of the heap holds a term and whether it has been reduced.
type HCell is Data:
  HRaw{t: Term}
  HDone{t: Term}

# The heap: a trie from a slot number to a cell, next to the next free
# number. The expression table shows the shape; see Term.bend.
type Heap is Data:
  MkHeap{cells: HTable, next: Nat}
```

and one term form:

```
  # `bd` with its free variables bound to the slots of `sl`, innermost
  # first. A variable at or beyond the length of `sl` is a variable of the
  # context the closure itself stands in.
  TClos{bd: Term, sl: List<&2, Nat>}
```

**The rule about where a closure may be seen.** `Eval.whnf` understands one.
Nothing else does. Every other pass -- `Conv.same`, `Infer.infer`,
`Term.lift`, `Term.subst`, the analysis walks -- calls `Eval.force`, which
expands a closure into an ordinary term. That is the same discipline the
reference `TRef{i, k, m}` already follows, and for the same reason: a pass
that reads a closure as a leaf would read the wrong term. The 65 wrong
answers that a reference in a type once caused are the evidence that this
discipline is not optional.

## The variable question, which is where this goes wrong

A closure's environment must cover **every** free variable of its body, or
the ones it does not cover must be shifted. Keep the first invariant:

> `TClos{bd, sl}` is well formed only when every free variable of `bd` is
> less than the length of `sl`.

Then a variable is a slot lookup and nothing else, and no shift is ever
needed. The cost is that building a closure for a beta step has to extend the
environment of the closure the body came from, which is why the machine
carries an environment rather than building one per step:

```
whnf (TClos{TApp{f, a}, sl})      = whnf (TApp{TClos{f, sl}, TClos{a, sl}})
whnf (TClos{TLam{ty, bd}, sl}) applied to one argument `arg`
                                  = whnf (TClos{bd, Con{slot(arg), sl}})
whnf (TClos{TVar{i}, sl})         = the cell of the i-th slot, reduced and
                                    written back
whnf (TClos{TConst{n, ls}, sl})   = whnf (TConst{n, ls})
```

A term that is not a closure is one whose environment is empty, so the
machine starts with `TClos{t, Nil{}}` and the invariant holds because a
declaration's value is closed.

## Why the existing rules do not change

The rules move terms about and do not look inside them: `Eval.iota_term`
takes the fields of a constructor application and rebuilds, `Eval.quot_term`
and `Eval.proj_field` likewise. A field that is a closure stays a closure and
nothing notices. What must be whnf'd before a rule fires already is: the
major premise, the arguments of a primitive, the subject of a projection.

So the work is confined to `Eval.whnf`, `Eval.force`, and one arm in every
exhaustive match over `Term`.

## The stages, each of which leaves a working kernel

1. **The types and the arms.** `HCell`, `Heap`, `TClos`, `Eval.force`, and an
   arm for `TClos` in each exhaustive match: `Term.lift`, `Term.subst`,
   `Term.occurs`, `Term.pars_ok`, `Term.has_free`, `Term.has_bvar`,
   `Term.subst_levels`, `Term.remap_levels`, `Conv.same`, `Conv.structural`,
   `Infer.infer`, `Shape.infer`, `Show.term`, and the tools. Each arm answers
   conservatively: force, or answer the unknown term. **Nothing creates a
   closure yet**, so the score must still be 186 with 0 wrong. Verify with
   `bend/main.bend` and the full sweep.

2. **The heap threaded through reduction.** `Eval.whnf` hands back a `Data`
   record of the term and the heap, the way the memo branch hands back
   `T.MkRed{term, memo}`: a Bend pair is a `Type` and may be used once, a
   `Data` record may be used twice, every self-call of `whnf` is in tail
   position so the loop never takes its own result apart, and the few nested
   reductions take it apart with a function, because only `match` is
   restricted to a parameter or a field. Still nothing creates a closure.
   The score must still be 186.

3. **The beta step creates a closure.** `T.Term.inst_at(tab, bd, a)` becomes
   a closure over a fresh slot holding `a`. Measure `perf/let-ladder`,
   `perf/church-numerals`, `perf/shift-cascade` first: they answer today, and
   they must keep answering at the same speed or better.

4. **The slot update.** Reducing the variable of a slot writes `HDone` back.
   This is the stage that is worth the whole plan, and the measurement that
   proves it is `perf/shared-subterm`: it must answer `accept` inside 50
   seconds. If it does not, stage 3 bought nothing and the branch is a
   measurement, not a merge.

5. **The remaining eight**, in the order their limits allow:
   `perf/beta-ladder` 50 s, `perf/magma-list-pair-n7` 60 s,
   `perf/magma-list-deep-n21` 80 s, `perf/app-lam` 100 s,
   `perf/magma-list-pair-n21` 260 s, `perf/magma-list-deep-n36` 390 s, and
   last `good/init-prelude` 50 s, which needs this and needs the parse to be
   faster than 30 times the Rust reader as well.

## The gate on every stage

The arena's `bad` corpus. A closure machine that is too generous accepts a
false proof, which is the one failure this kernel must never have, and a
reduction that is more generous than the rules allow is exactly how it would
happen. Run `tools/dbad.py` and the full sweep, and read the `wrong answers`
line before anything else.

Two further gates, both cheap and both learned the hard way:

- `bend/main.bend` is 17 declarations built by hand. Run it after every
  change; it has caught more than the sweep has.
- The first run of a new binary on this machine can cost tens of seconds, so
  run each binary once on a small file and report the second run. A whole
  day's conclusions were once wrong because of this.
