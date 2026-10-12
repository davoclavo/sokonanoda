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

## The machine carries the environment, not only the closure

The first attempt at stage 3 breaks on the invariant, and the way it breaks
is worth writing down because it decides the shape of the whole machine.

A beta step wants to turn `(lam ty bd) a` into `TClos{bd, [slot of a]}`. But
`bd` has free variables other than its own binder -- the ones of the context
the lambda stands in -- and the environment `[slot]` does not cover them. The
closure is ill formed, and a variable lookup would read the wrong slot.

So the environment belongs to the **machine**, not to one closure:

```
Eval.whnf_h(fuel, env, heap, sl, ctrl, sp) -> Red
```

where `sl` is the environment of `ctrl`, innermost binder first, and the
invariant holds by construction because `sl` grows exactly when the machine
goes under a binder:

| control | what the step does |
|---|---|
| `TApp{g, a}` | push `TClos{a, sl}` on the spine, control becomes `g`, `sl` unchanged |
| `TLam{ty, bd}` with an argument | take a slot for the argument, control becomes `bd`, `sl` becomes `Con{slot, sl}` |
| `TVar{i}`, `i` inside `sl` | read the slot: a reduced cell is the answer, a raw one is reduced and **written back** |
| `TVar{i}`, `i` beyond `sl` | a variable of the ambient context: the answer is `TVar{i - length sl}` |
| `TClos{bd, sl2}` | control becomes `bd` with `sl` replaced by `sl2` |
| anything else | as today, with `sl` carried along |

A spine entry is a closure, so it is self contained and the rules may treat
it as opaque -- which they already do, since `Eval.iota_term`,
`Eval.quot_term` and `Eval.proj_field` move terms about without looking
inside them.

## Reading back, and why it does not undo the sharing

The machine's answer is a term of the ambient context, so a closure cannot
escape in it. The answer is read back **one constructor deep**: the head is
explicit and every child stays a closure. That is what weak head normal form
means, and it is what keeps the sharing: `Conv` descends into a child by
reducing it, and reduction understands a closure.

A pass that is not reduction may not see one, so `Eval.force` expands a
closure whole, and that costs the size of the term. It is called where
`Conv.same`, `Infer.infer` and the analysis walks look, and nowhere else.

## The one hard case: reading back a lambda that is the answer

Every step above is mechanical except this one, and it is the step that
turns the plan from a machine into normalisation by evaluation. Get it wrong
and the kernel accepts a false proof, so it is the step to write a law for
before writing the code.

When the control is `TLam{ty, bd}` and the spine is empty, the lambda **is**
the answer, and the answer must be a term of the ambient context. The body
`bd` has a free variable 0 that the machine's environment does not cover: it
is bound by the very lambda being returned, not by a slot.

So an environment entry cannot only be a slot. It is one of two things:

```
type EEnt is Data:
  # the value of this binder lives in a heap slot
  ESlot{n: Nat}
  # this binder is rigid: it stands for a variable of the answer
  ERigid{}
```

Reading a lambda back pushes `ERigid{}` and leaves the body as a closure
over the extended environment. A variable that resolves to `ERigid` becomes
`TVar{d}` where `d` counts the rigid entries between it and the end of the
environment -- a de Bruijn **level** counted from the inside, converted back
to an index at the point it is read.

That conversion is the whole risk. Two laws worth stating in `LAWS.bend` and
proving in `PROOF.bend` before trusting it:

1. reducing a closed term with an empty environment gives the same term as
   the reduction that substitutes eagerly, for every term the regression
   tests hold;
2. a term with no closure in it reduces to the same answer whether the
   machine carries an environment or not, which is what makes stage 2
   behaviour-neutral and is already true of the code on the branch
   `closure`.

Until law 1 holds on `bend/main.bend`'s seventeen declarations **and** on the
arena's `bad` corpus, the machine is a measurement and not a merge.

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

## Stage 3, attempted: what the machine got right and where it stopped

The machine was built: `Eval.mach` carries the environment, the heap and the
depth; `Eval.force` reads an answer back; `Conv.classify_work` reduces with
it. It is about four hundred lines. Every module verifies, the laws check,
and all 17 regression tests pass on it. What follows is what the attempt
established, so the next one does not pay for it twice.

### Four bugs, three of them fixed

**A lambda handed back is applied in the wrong place.** The machine reads a
lambda back one constructor deep and the body keeps an environment whose
innermost entry is the binder with no value. Applying that lambda must put
the argument **in** that entry; extending the environment above it loses the
argument, and the variable then reads the empty entry and comes back as a
variable of the answer. `perf/church-numerals` finds this at once, because a
slot there holds a function which is reduced and then applied.

**`Eval.pick_p` runs both branches, so a slot read cost twice over.** Reading
a slot has to choose between the value already reduced and reducing it, and
both arms of a pick are evaluated. One call with the choice made inside the
arguments costs what one read should; two calls made a slot read inside a
slot read cost twice, and `good/other/nat-lit-ble` went from a tenth of a
second to past sixty.

**A rigid binder needs a level, not a flag.** A slot holds a value captured
under one set of binders and read back under a deeper one, so its variables
have to move: `(fun f => fun x => f x) #5` is `fun x => #6 #0` and not
`fun x => #5 #0`. An environment entry that only says "rigid" cannot say how
far; a depth counted from the outside says it exactly, and the read back
turns a level into an index with the depth it is at. That is the de Bruijn
conversion this plan named as the whole risk, and it was wrong on the first
try in exactly the way the plan predicted.

**A reference has to be resolved where the read back renumbers around it.**
The variables inside a table entry belong to the place it is named from.
Leaving the reference alone under a binder the read back has entered puts two
numberings in one term, and conversion then refuses a pair that is equal.
Resolving where nothing is renumbered -- a closed entry, or a read back that
has entered no binder -- is free, and that is most of them.

### The fourth: a value's scope, which is the representation

Two variants, each correct where the other is wrong:

| variant | `perf/church-numerals` | the prelude's `noConfusion_of_Nat.aux._f` |
|---|---|---|
| a slot holds a closure, reduced on first read | **accept** | reject |
| a slot holds the value read back at capture | reject | **accept** |

The second variant is right on 185 of the 186 small files and gives up the
sharing the machine was built for, because reading the argument back is
copying it.

What this says is that a `Term` with a closure in it cannot carry a value's
scope. A heap slot is read in whatever scope the reader stands in, and the
read back assigns de Bruijn levels by its own descent, so a value captured
in one scope and read in another gets indices that belong to neither. Each
of the two variants picks one of the two scopes and is wrong about the other.

A proper normalisation by evaluation keeps values in a type of their own --
a neutral with a spine, a closure with its environment, a constructor with
its arguments -- and reads back exactly once, at the depth it has reached.
Then a value is never reinterpreted, because it is never a term until the
read back makes it one. That is the next attempt, and it is a value type and
a new conversion against it, not a patch to this one.

### What to keep from this attempt

The branch `closure` holds it. Worth keeping: `Eval.force` and the level
arithmetic in `Term.bend` (`EEnt`, `ELook`, `EEnt.look`), the heap, the
`Data` record that lets reduction hand back two things, and the four
differential tests in the scratchpad that compare the machine against the
reduction that substitutes on hand-built terms -- they caught the first two
bugs in seconds and are the first thing to write next time.

`bend/cmp.bend` is also worth keeping: it walks a declaration's value and
stops at the smallest subterm where the two reducers disagree. That is what
found the fourth bug, and no amount of reasoning about de Bruijn indices
found it before the tool did.

## Stage 4: the value evaluator, and what conversion on values needs

`bend/Val.bend` is the value evaluator, and it is **verified**:
`bend/nfdiff.bend` takes every declaration's normal form twice -- once by
`Eval.whnf` driven into every subterm, once by `Val.eval` with the answer
read back -- and across the 176 small arena files that finish in thirty
seconds, 175 agree. The one that does not is the comparison running out of
its own budget on an 8.9-million-character normal form whose two forms are
identical character for character.

Four bugs the gate found in minutes, each worth knowing before writing this
again:

1. a recursor's rule takes the recursor's own arguments first, then the
   constructor's fields, then the rest. Leaving the first group out puts the
   fields where the motive belongs.
2. a quotient takes the **last** argument of the value under `Quot.mk`.
3. a projection's guard is on the field index **plus** the constructor's
   parameters.
4. structure eta belongs in the value evaluator too.

### The constraint the next step has to respect

`Val.eval` unfolds a definition as soon as it meets one, and conversion on
values cannot be built on that. The reason is in `perf/identical-nesting`:
conversion today compares two spines **before** unfolding their head, and
reduced instead "it builds twelve nested structures twice and does not finish
in six minutes". An evaluator that unfolds eagerly has already paid that cost
before conversion gets a chance to avoid it.

So the next piece is an evaluator with two modes, which is the distinction
Lean draws between `whnfCore` and `whnf`: stop at a constant that **could**
unfold, hand back the neutral, and let conversion decide. Then:

- two neutrals with the same head and the same number of arguments compare
  argument by argument, and nothing unfolds;
- a definite no there puts the unfolding back on the table, which is the
  `SEither` route `Conv.eq_all` already has;
- everything else -- eta, the K rule, proof irrelevance, a literal against a
  constructor -- is the same rule it is today, written against values.

Proof irrelevance and the K rule need the **type** of a value, which means
either inference on values or a read back at that one point. A read back
there is sound and rare, and it is the cheaper way to start.

### What is where

| branch | what it holds |
|---|---|
| `main` | 186 of 195, 0 wrong. The reference, structure eta, the tools, every measurement |
| `nbe` | `Val.bend` and `nfdiff.bend`: the verified value evaluator, called by nothing yet |
| `closure` | the closure-in-a-term attempt, and the four bugs it paid for |
| `memo` | the memo, and the 64.8 GB that closed it |

## Stage 5: conversion on values, and what the wiring measured

`bend/Vconv.bend` asks whether two values are definitionally equal, with the
shape of `Conv.eq_all`'s walk and reduction that starts without unfolding a
definition. `bend/cvdiff.bend` is its gate: for every declaration both
conversions are asked whether the type inference gives is the type the
declaration states.

| | |
|---|---|
| agree | **158** |
| differ by budget only | 19, all in the `bad` corpus |
| a yes against a no | **1**, `good/tutorial/099_ruleK` |
| too slow to compare | 3 |

Six bugs the gate found, two of them wrong accepts:

1. saying no where a head could still unfold -- two constants may be the
   same type and only a delta step shows it;
2. unfolding a neutral from the value side, which does not terminate;
3. unfolding the head and not the arguments -- `good/other/nat-lit-ble`
   needs it, because its literals arrive as `OfNat.ofNat` of a definition;
4. **proof irrelevance answering yes on its own.** Two proofs are equal when
   they prove the same proposition, so the rule leaves the two types behind
   as a pair. This was a wrong accept on
   `bad/tutorial/105_proofIrrelevanceBad`;
5. **reading a value back at depth zero** when it lives inside the
   comparison's own binders. A wrong accept on `bad/bugs/k-rec-conv`;
6. reading a term that came back out of inference, or out of the K rule, in
   an **empty** environment. Such a term is written in the comparison's
   context, so every one of its variables came back unknown. Fixing it took
   the budget differences from 31 to 19 and the proof irrelevance files from
   declined to agreed.

### What the wiring measured

With `Infer` and `Kernel` asking `Vconv` instead of `Conv`, all 17 regression
tests still pass, and the sweep says the work is not finished:

- `perf/fueled-chain` answers **reject**, which is a wrong answer and on its
  own reason enough not to merge;
- `good/other/nat-lit-*`, `perf/args-before-unfold`, `perf/beta-ladder`,
  `perf/identical-nesting`, `perf/irrelevance-before-evaluation` and
  `corner-cases/proof-param-ok` answer `declined` where they used to answer.

So the wiring is reverted and `Vconv` stands unused next to `Conv`. The three
things between here and a merge, in the order the evidence puts them:

1. **`perf/fueled-chain`'s wrong answer.** Reduce it with
   `tools/minimise.py --thm-axioms` and read it with `bend/cvdiff.bend`,
   which names the declaration and prints both sides as the value evaluator
   sees them.
2. **The declines.** Every one is a budget difference, and the budget goes on
   reading values back: proof irrelevance and the K-like rule need the type
   of each side, and inference reads a term. **Inference on values** removes
   every quote, and it is the next piece of work -- the type of a neutral is
   its head's type applied to its spine, the type of a lambda is a pi, and
   the two rules then need no read back at all.
3. **`good/tutorial/099_ruleK`.** Every condition of `Conv.k_ok` is mirrored
   and the subject's type is read in the right context now, so what is left
   is to print the type the two sides compute for the subject and compare
   them.

## Stage 6: the whole kernel on values, scored

Two more bugs, both found by running it rather than by reading it:

**A head comparison must compare levels as levels.** `max p0 p1` and
`max p1 p0` are one level written two ways, and reading them as syntax
answers no. That was the wrong answer on `perf/fueled-chain`, whose
declaration 557 turns on exactly it. The term conversion has always used
`Level.eq`.

**The two terms are written in the context.** `Vconv.eq_in` read them in an
empty environment, so every free variable came back unknown and the kernel
-- which asks with a context, unlike the gate -- answered "do not know" at
once, in a hundredth of a second. That one line was the difference between
nine files declining and the same nine accepting. The gate did not catch it
because the gate asks at the top level, where the context is empty: a gate
that only asks the easy question passes the broken code.

### The score, with the whole kernel asking the value conversion

| | terms (`main`) | values |
|---|---|---|
| correct | **186** | 179 |
| wrong | **0** | **5** |
| declined | 0 | 1 |
| out of time | 9 | 10 |

The five wrong answers name three rules that conversion on values does not
have yet:

| file | what is missing |
|---|---|
| `tutorial/112_structEta` | **structure eta in conversion.** Lean's `isDefEqEtaStruct`: a constructor application of a structure against something that is not one expands the other side into `mk x.1 ... x.n`. The value evaluator has structure eta for a recursor; conversion needs it for a comparison |
| `tutorial/099_ruleK` | the K-like rule answers no where the term conversion answers yes, with every condition of `Conv.k_ok` mirrored |
| `tutorial/107_proofIrrelevanceUnderBinder` | proof irrelevance under a binder. Structure is tried first now and irrelevance only on a no, which is what the budget needs; this file says the order is not yet right under a binder |
| `perf/magma-list-pair-n7`, `-n21` | the same three, met in a corpus |

And the timings moved both ways: `perf/shift-cascade`,
`perf/discarded-argument-match`, `perf/proj-lazy-struct` and
`perf/fueled-chain` now run out of time, which is what call by value costs on
an argument the body throws away. `good/perf/church-numerals`,
`good/other/nat-lit-*`, `perf/identical-nesting` and `perf/let-ladder`
answer, and `perf/magma-list-pair-*` get far enough to answer wrongly rather
than not at all.

So the wiring is reverted again and `main` stands at 186 with nothing wrong.
What is left is three rules and one representation decision:

1. structure eta in conversion,
2. the K-like rule's remaining difference,
3. proof irrelevance under a binder,
4. and the call-by-value question: an argument the body discards is reduced
   anyway, which is what the four new timeouts are. Lean is call by need;
   the way to it here is a slot in the environment that holds either a value
   or a term, and the branch `closure` is the record of how not to build one.

## Stage 7: sound on values, and the gap is one word

Four more bugs, each named by the file that finds it:

| bug | file |
|---|---|
| structure eta is a **conversion** rule too, not only a reduction one | `tutorial/112_structEta` |
| proof irrelevance must come **before** the structural comparison. Two proofs of one proposition are equal whatever their arguments are, so comparing arguments first answers no where irrelevance answers yes | `tutorial/107_proofIrrelevanceUnderBinder` |
| the K-like rule must put the constructor in and **run the constant rule again**. Applying a neutral only lengthens its spine, so the recursor came back unreduced | `tutorial/099_ruleK` |
| any **constant** head earns the dear route, not only a definition. A recursor stands unfired until its major premise reduces, and that may need a definition unfolded inside an argument | `perf/magma-list-pair-n7` |

With all of them in, the whole kernel on values:

| | terms (`main`) | values |
|---|---|---|
| correct | 186 | **181** |
| **wrong** | 0 | **0** |
| declined | 0 | 2 |
| out of time | 9 | 12 |

**No wrong answers.** The gap is five files and every one of them says the
same word:

| file | what it is |
|---|---|
| `perf/discarded-argument-match` | out of time. The name is the reason |
| `perf/proj-lazy-struct` | out of time |
| `perf/shift-cascade` | out of time |
| `perf/refute-cheap-last` | declined |
| `perf/repeated-subproblem` | declined |

The evaluator is **call by value**: an argument is reduced before it goes in
the environment, which is exactly what buys the sharing -- an environment
holds values, so a variable used twice costs its value once -- and exactly
what loses an argument the body throws away. Lean is call by need.

### The last piece, and why it is safe now

Call by need wants a slot that holds either a term with its environment or a
value, and an update when it is first read. That is a heap, and a heap of
**values** is sound where a heap of terms was not: the branch `closure` kept
closures in a `Term` and the same slot was read in two scopes that did not
contain each other, while a value carries no scope at all -- it is not a
term until `Val.quote` makes it one. The threading is the one already proven
twice here: hand back a `Data` record of the answer and the heap, keep every
self-call in tail position, and take the record apart with a function.

That buys the three timeouts and the two declines, which is 186 with nothing
wrong, and it is the first point at which the sharing can be asked to earn
more: `perf/shared-subterm` and the `magma-*` family are what it was built
for.

## Stage 8: laziness the cheap way, and why it is not cheap

The gap is five files and the cause is call by value, so the obvious cheap
fix is to reduce an argument only where the body uses it: push the argument
on the spine unreduced, ask `Term.has_bvar(bd, 0n)` at the binder, and give
the binder the unknown term where the answer is no.

It was built and measured, and it is a net loss:

| file | call by value | with the cheap laziness |
|---|---|---|
| `perf/church-numerals` | 0.04 s accept | **38 s** accept |
| `perf/discarded-argument-match` | out of time | out of time |
| `perf/proj-lazy-struct` | out of time | out of time |
| `perf/shift-cascade` | out of time | out of time |

Two reasons, and both are worth keeping.

**The test costs more than the argument.** `Term.has_bvar` walks the body,
and the body is walked at every beta step, so the hot path pays for a walk
to save a reduction that is usually cheap. A thousandfold slowdown on
`church-numerals` is that walk.

**It also has to be skippable, not picked.** `Val.pick` evaluates both of
its branches, so choosing between a reduced argument and nothing reduces it
either way; the choice has to be made on the **term** -- give the forcing
step the unknown term instead of the argument -- which is the same trick the
memo needed for a slot that was already reduced. Getting that wrong made the
laziness cost without saving, and the first version of this measured exactly
that.

**And the rules need forced values.** An argument waiting on the spine has no
head to match on, so a recursor's major premise, a primitive's two arguments
and a projection's subject each have to be forced before the rule looks, and
the primitive's two only where there is a primitive to take them. Missing
that gave five wrong answers, each a rule that silently did not fire.

So the cheap way is out, and the real one stands: a slot that holds either a
term with its environment or a value, **and an update when it is first
read**. The update is what makes the saving stick, and the update is what
needs the heap threaded. A heap of values is sound, which is the one thing
the branch `closure` could not say about a heap of terms.

## Stage 9: the tension the last two files sit on

The deep route unfolds a neutral's head **and its arguments**. Restricting it
to the head was tried, and the two things it does are both load bearing:

| with the arguments unfolded | with only the head |
|---|---|
| `good/other/nat-lit-ble` accepts | **rejects** |
| `good/other/nat-lit-add` accepts | **rejects** |
| `perf/magma-list-pair-n7` out of time | **rejects** |
| `perf/proj-lazy-struct` out of time | **rejects** |
| `perf/discarded-argument-match` out of time | **accepts** |
| `bad/perf/refute-cheap-last` declines | declines |
| `perf/repeated-subproblem` declines | declines |

So the argument unfolding is needed for correctness -- a primitive fires only
on two literals, and in `nat-lit-ble` they arrive as `OfNat.ofNat 1000000` of
a definition -- and it is what costs `perf/discarded-argument-match`.

Asking the **rule** to unfold what it reads, rather than unfolding every
argument of every head, is the shape that resolves it, and it was tried too:
the major premise unfolded where delta is allowed, and a primitive's two
arguments likewise. It has to be written out inside the constant rule,
because a helper that unfolded a head would have to call the evaluator and
Bend has no mutual recursion. That version rejects `nat-lit-*`,
`magma-list-pair-n7` and `proj-lazy-struct`: unfolding an argument's head
once is not the same as reducing it with every rule, which is what the walk
over the arguments did.

Both attempts are reverted. What the two of them say together is that the
deep route needs to reduce an argument **on demand and once** -- which is
call by need, which is the heap, which is the piece that has been named at
the end of every stage since the fourth. There is no cheaper arrangement of
the same rules: this stage ruled out the two obvious ones with a measurement
each.

The value kernel stands where stage 7 left it: 181 correct, nothing wrong,
two declines and twelve files out of time, with `main` at 186 and nothing
wrong.

## Stage 10: the heap, and why it had to reach the queue

An argument now takes a slot of a heap instead of reducing where it is
given. `Val.go` reads the slot where the body first asks for it, reduces the
term in the cell, and writes the value back. A body that throws the
argument away never pays for it. A body that reads it twice pays once.

### The slot, the cell and the number

```
type HCell is Data:
  HRaw{t: T.Term, en: List<&2, Val>}
  HDone{v: Val}
```

`Hp` is a trie of cells under a number, beside the next free number.
`VSlot{n}` is a value that stands for cell `n`. `VR` is the record
reduction hands back: the value, and the heap as it stands after it. A Bend
pair is a `Type` and may be used once, so the record has to be `Data`.

### The rule that decides the whole shape

**A value may not outlive its heap.** A value holds slots in the spine of a
neutral and in the environment of a lambda. Only the heap those slots came
from can read them, and a new heap gives out the same numbers again, so a
value kept past its heap reads some later slot in place of its own. The
answer is then wrong, not unknown.

Three arrangements were considered and two of them break this rule.

| arrangement | what it costs | sound |
|---|---|---|
| the heap travels with the value, through conversion as well | ~30 signatures of `Vconv.bend` | **yes** |
| conversion takes the heap read only | one parameter per function | no: a slot it allocates and drops collides with a live one |
| conversion never sees a slot, the boundary resolves them | nothing | yes, and it wins nothing: resolving is the eager work again |

The second is the trap. Reading a slot is safe to drop, because a cell is
written once and the write only replaces a term by the value it reduces to.
**Taking** a slot is not: a dropped heap forgets the number it gave out, and
the value that holds it is still in the queue.

The third is why the first is necessary rather than merely tidy. The heavy
reduction of a `decide` certificate does not happen in the first whnf of
either side. It happens in the `delta` steps that the queue takes, one
after another, and a boundary that resolves every slot before the queue
sees it has reduced every argument eagerly -- which is the machine this
stage replaced.

So the heap threads through the queue. `VSH` is a step with the heap beside
it, and `Vconv.all` carries the heap from one pair to the next. The heap
only grows, which is what makes an alternative safe: a pair that waited
reads the same cell it would have read when it went in.

### Where a slot has to go

A rule reads a value, and a slot is not one. Three arguments leave their
slots at once: the two a primitive reads as numbers, and the major premise
of a recursor or of a quotient. `Vconv.classify` forces both sides of every
pair, so no rule below it ever meets a slot -- that is one place to get
right, not thirty.

The read back resolves a slot as well, and it hands back a term, so no
value leaves it. That is why two readings side by side can start from the
same heap and why `Val.nf_in` can make a heap and drop it.

The branch that a `pick` does not take is thrown away whole. Its slots are
never read, so the numbers it took cost nothing but the taking.

## Stage 11: the value kernel passes the kernel that substitutes

| | the term kernel | the value kernel |
|---|---|---|
| correct | 186 | **188** |
| declined | 0 | **0** |
| wrong | 0 | **0** |
| past its arena limit | 10 | **8** |

Against the 196 files of the arena's tarball, each at its own limit. The two
it gains are `perf/beta-ladder`, which answers in 2.7 s, and
`perf/shared-subterm`, which answers in 17.3 s; the kernel that substitutes
answers neither in fifty seconds. `perf/repeated-subproblem`,
`perf/shift-cascade` and the three `perf/proj-*-struct` tests answer as
well, and five of those six are what the heap was built for.

What it took, after the heap itself:

1. **Five strict picks.** Each was a `pick` whose branches all did their
   work. The dearest was the type of every binder, which the reduction that
   substitutes never looks at.
2. **A budget for proof irrelevance.** Its test costs the size of the side
   and it is asked of every pair. Eighty steps of read back answer nearly
   all of them; a pair that is cut off is asked again in earnest, but only
   where everything cheaper has already said no.
3. **A pair asked once.** Two arguments in one slot are one argument, and
   `2^n` pairs become `n`.
4. **A route that cannot answer gives up its turn.** The queue took the
   alternative on a no and not on a "do not know".

What is left is eight files, and none of them is close. Four are `decide`
certificates that want the cost of one reduction step to fall.
`perf/app-lam` wants an infer cache, and so do `init-prelude` and
`perf/grind-ring-5`. A cache is the next piece of work, and the thing that
makes it hard is in the README: a de Bruijn term's type depends on the
context it is read in, so the key cannot be the term alone.
