# The kernel core in Bend 2

This is the dependently typed core of the Lean kernel, written in
[Bend 2](https://github.com/bendlang/bend) and checked by Bend's own checker.

It is a re-implementation of the middle of `sokonanodazo`, not a port of the
whole thing, and it is not a performance exercise. Read the limits below before
you read the code.

## Run it

```
SOKO_EXPORT=<a .ndjson export> bend bend/check.bend   # check a real export
bend bend/main.bend                                   # check three built-in environments
bend bend/PROOF.bend                                  # check the laws
```

From the repository root, with Bend on PATH:

```
devbox run bend-check    # a real export, named by SOKO_EXPORT
devbox run bend          # the three built-in environments
devbox run bend-proof    # the laws
devbox run bend-verdict  # the laws again, through Bend's Lean-proven kernel
```

`tools/bend.sh` builds Bend 2 from its flake into `~/.cache/bend2` the first
time and runs it after that.

### Build it instead, to run it fast

`bend file.bend` checks the file and then interprets it. Compiling it first is
about twelve times faster and takes six seconds:

```
bend bend/check.bend -o checker
SOKO_EXPORT=<an export> ./checker --threads 8
```

| | interpreted | built |
|---|---|---|
| the floor, on a 292-byte export | 279 ms | 19 ms |
| `030_peano1` | 304 ms | 25 ms |
| `112_structEta` | 514 ms | 60 ms |

Medians of three. Pass `--threads`: the default spun for thirty seconds on a
file that takes twenty milliseconds with it set, and the first run of a
freshly written binary pays a cold start that is easy to mistake for the real
cost. Both of those cost a measurement each before the numbers above settled.

A built binary alone does not rescue a test that times out. The next section
does.

`main.bend` prints:

```
good    expect accept  got accept
bad     expect reject  got reject
forward expect reject  got reject
```

`good` exercises delta on a definition, beta on its body, and conversion
against a declared type. `bad` gives a function where an element is wanted.
`forward` names a declaration that comes later, which the ordered check must
refuse.

## What is here

| File | Contents |
|---|---|
| `Level.bend` | universe levels, the smart constructors, normalization, substitution |
| `Term.bend` | terms with de Bruijn indices, lifting, instantiation, level substitution |
| `Env.bend` | declarations, and the environment as a trie on a name |
| `Table.bend` | the level and expression tables, as tries on an index |
| `Eval.bend` | weak head normal form: beta, delta, zeta, iota, projections, quotients, native `Nat` |
| `Ans.bend` | yes, no, and "I ran out of budget" |
| `Shape.bend` | the type of a term, without checking it |
| `ind.bend` | dumps an inductive block, to show the reader handles it |
| `Conv.bend` | definitional equality, as a worklist |
| `Infer.bend` | type inference for the core |
| `Bytes.bend` | a tail-recursive byte scanner, the base of the reader |
| `Reader.bend` | line splitting, line classification, field lookup by key |
| `scan.bend` | reads a real export and reports what the scanner found |
| `Parse.bend` | builds the level and expression tables and the declarations |
| `Kernel.bend` | checks an environment, with a per-declaration report |
| `read.bend` | classifies every line of a real export and tallies the kinds |
| `check.bend` | reads a real export and gives a verdict |
| `Show.bend` | prints a term, which is how the projection bug was found |
| `dbg.bend` | prints every stored type, and declared against inferred |
| `main.bend` | the driver and its hand-built test environments |
| `LAWS.bend` | the laws the kernel must obey |
| `PROOF.bend` | their proofs |

## Why it looks like this

Three of Bend's rules decide the shape of every file, and none of them are
negotiable.

**Mutual recursion is forbidden.** A kernel is mutually recursive almost
everywhere. Reduction inspects what reduction produced, conversion recurses
through conversion, and inference calls both. Two answers appear here. `Eval`
carries an explicit argument spine, so the head and its arguments travel in one
self-recursive def rather than two that call each other. `Conv` holds a queue
of pairs still to be shown equal, takes one off the front, and pushes the
subpairs it produces, which is the recursion turned inside out.

**A `match` may not scrutinize a computed value.** Every test on something just
computed goes to a helper that matches its own parameter. That is why the files
are full of small functions named `pick`, `is_pi`, `step_ok` and the like. It
is also why `Conv` and `Infer` work: the helper matches, and because it never
calls back, nothing becomes mutual.

**Termination is mandatory.** This is the deep one. A kernel's reduction does
not terminate on every input, and that is not a defect: it is why a checker
must be able to give up. So `fuel` is a real parameter here, not ceremony. It
strictly decreases on every recursive call, which is how these defs pass Bend's
check, and running out means the term is returned unreduced, which a checker
can only answer by rejecting.

Bend is also affine, so a value used twice is marked `+`, and a list whose
elements are reused is `List<&2, T>` rather than `List<T>`.

## The laws

`LAWS.bend` states structural facts the kernel leans on, and `PROOF.bend`
proves them by induction. `bend PROOF.bend` prints ALL PROOFS CHECK.

The laws proven today say that an empty level assignment leaves a level, a list
of levels, and a term alone. That sounds small, and it is, but it is the kind
of fact a kernel silently assumes: if substituting no levels changed a term,
a declaration with no level parameters could be read at the wrong type.

This is the reason to write a kernel in Bend at all. The parent is fast; Bend
is not going to beat it. What Bend offers is that a claim about the kernel can
be stated and then mechanically proven, in the same language as the code.

## What is missing

Honestly and in order of size.

**Throughput.** Nine files run past sixty seconds: `init-prelude`, which is
3.7 MB, and eight `perf` tests. Nothing else is in the way of an answer, and
no constant factor reaches them. `perf/shared-subterm` answers at a budget of
3000 and wants more than seventy seconds at 30000, so it is about a hundred
times away; `init-prelude` does not finish in nine hundred seconds. Five of
the nine are small files built to punish a kernel with no sharing in its
terms, and `docs/perf-plan.md` records two measured attempts at sharing and
why Bend charges for both.

**A string literal.** The corpus holds ten kinds of expression node and this
kernel reads nine. The one it does not is `strVal`, in 74 places across four
files, and all four of those run past the time limit for other reasons. A node
the reader does not read answers the unknown term, so such a file declines.

**A mutual block, a nested inductive, and a recursor with an unusual level
list.** The recursor derivation hands these back as `T.TUnk`, which converts
with nothing, so such a block stays trusted and the file declines rather than
accepts. None of the arena's readable good files needs them, so nothing
measures this gap yet.

**The real corpora.** The seven real-world exports are not in the arena's
tarball and cannot be read at all, for the memory reason below. That is the
gap between this kernel and the arena, and it is not a matter of a few more
rules.

Here is where the 124 `good` files small enough to read now stand:

| the answer | count |
|---|---|
| accept | **115** |
| timed out | 9 |

**Reduction throughput.** Reading was never the problem and the checking was.
Three `perf` tests still time out: `app-lam` and the two `proj-*-struct`. The
work is reduction and inference doing real work, so a faster table will not
move them. See "Making it fast" for what did move them, and for the four
places a guard was written and never reached.

**Whitespace in a reader.** A blank after a colon is handled. A blank anywhere
else is not, and the real corpora are not promised to be formatted like the
arena's tarball.

**Performance.** Bend has no `U64`, so the parent's packed pointers and
hash-consed terms cannot be carried over. The point of this folder is the
proofs, not the clock.

## The checks on an inductive block

A block states more than it proves. Ten of its claims can be settled by
reading it, with nothing derived, and together they are what took the whole
small set from 74 correct to 99. Each one is an attack the arena makes.

| The claim | What the arena sends |
|---|---|
| a constructor builds an inductive that exists | `orphan-ctor` names one that does not |
| a recursor eliminates at least one, and each exists | `orphan-rec` names none at all |
| a recursor carries the name a recursor has | `extra-rec`, `misnamed_rec_user`, `dup_rec_def2` |
| a constructor's type opens with one binder per parameter and per field | `ctor-num-fields` |
| an inductive's type is a telescope ending in a sort | `inductTooFewParams`, `inductBadNonSort2` |
| a constructor's result is its own inductive | `inductWrongCtorParams` |
| applied to its parameters in binding order | `inductWrongCtorResParams` |
| at its own level parameters in that order | `inductWrongCtorResLevel`, `reduceCtorType` |
| the inductive does not occur in its own indices | `inductInIndex` |
| every field is strictly positive | `indNeg`, `indNegReducible` |
| every field fits the inductive's universe | `typeWithTooHighTypeField`, `reflOccLeft` |
| a projection out of a proposition yields a proposition | `projProp2`, `projProp4`, `projProp5`, `proj-of-imax-prop` |
| a proposition with two constructors eliminates only into one | `large-elim-prop-bool` |

Three of them took a wrong turn first, and each wrong turn was caught by
running the kernel on all 94 good tutorial files rather than by thinking
harder.

**The universe rule, twice.** Taking the sort of the constructor's whole type
rejected seventeen correct files: the parameters are binders of that type too,
and `Prod` lives in `Type (max u v)` while its parameters live in `Type (u+1)`
and `Type (v+1)`. Checking only the fields then rejected eight more, all
propositions carrying data fields, because proof irrelevance exempts them and
`imax` does not do it for you.

**The recursor name.** Matching a recursor's name against its inductive's
would have rejected the second recursor of every mutual block, since `I1` and
`I2` yield `I1.rec` and `I2.rec` and both name both types. The rule now ignores
the prefix and asks only that the last component be `rec`.

**Positivity.** Only a domain is refused. `Nat -> I` to the right of an arrow
is an ordinary recursive field, and `List I` is the nested case Lean accepts.
Refusing either rejects types that are sound, which is worth more than a
missed attack.

## What was missing and now works

**Projections.** The term, its reduction and its type are all in. The typing
needed one fix: `proj_base` applied the constructor's type to the structure's
parameters where it had to instantiate them. A pi applied to an argument is
not a beta-redex, so reduction left it untouched and the next step looked for
a binder and found an application.

That was not what held the arena's cases back, though. Every projection test
still rejected afterwards, and narrowing by construction had run out: six
hand-built shapes all passed. Building a term printer settled it in one line.
The inferred type of `x.0` was the structure itself, which is the type of
`TVar{0}`, the fallthrough for a node the parser does not know. An earlier
edit had wired the `letE` case straight to the literal case, skipping
projections entirely. The machinery had always been correct and nothing ever
called it. Seven tests turned on that one line.

**Quotients.** All four declarations have the shape of an axiom plus a `kind`
tag, and the two reduction rules differ only in where the quotient sits among
the arguments. Six tests.

**Eta for a structure that carries data.** The rule rewrites the side that is
not a constructor application into one, taking the parameters from its type
and the fields from its own projections, and leaves the rest to the structural
case. That way the parameters are compared too and nothing in the rule has to
know they match.

**A native `Nat`.** A literal used to be desugared into that many successors
of zero, capped at 4096, and past the cap the reader answered a loose variable
that no inference accepts. The arena writes `1000000`. Now a literal is one
term carrying the names of `Nat`, `Nat.zero` and `Nat.succ`, a declaration may
carry an op code for one of eight arithmetic rules, and reduction applies the
rule to two literals.

Two things only the tests showed. Small literals stopped matching `Nat.zero`,
which broke four support definitions that had passed before, so a literal now
bridges to constructor form on demand. And the arena does not write bare
literals: the arguments arrive as `OfNat.ofNat Nat 1000000 ..`, so the rule
has to reduce them first.

## Checking a real export

`check.bend` reads an export, builds its environment, and gives a verdict. It
also prints one line per declaration, so a rejection names the declaration
that caused it.

```
$ SOKO_EXPORT=.../tutorial/030_peano1.ndjson bend bend/check.bend
declarations 7
  ok     def   1
  ok     def   9
  ok     def   13
  ok     def   14
  ok     def   15
  ok     def   16
  ok     thm   17
verdict accept
```

Against all 141 of the arena's tutorial tests, with nothing left out:

| | count |
|---|---|
| correct accept | 29 |
| correct reject | 45 |
| honest decline, an inductive block was trusted | 67 |
| wrongly rejected | **0** |
| wrongly accepted | **0** |
| error or timeout | **0** |

**Every verdict it gives is correct.** A decline is the arena's exit code 2 and
scores nothing, so 74 of the 141 are verdicts and the other 67 are the work
that remains. Nothing times out and nothing errors.

On the 37 tests that need no inductive block, it is 37 correct.

The 67 declines are all files the arena expects to be **accepted**. Deriving
the recursor and comparing it to the one the file states is what they wait on,
and nothing else is missing for them.

Every file the arena expects to be **rejected** now gets a verdict, bar one.
That took ten checks on an inductive block, each of which reads the block
rather than deriving anything; the section below lists them.

Six real bugs turned up on the way, and every one was found by reading a
failing declaration or the code, not by guessing.

**`max l l` never collapsed.** The comment on `Level.mk_max` claimed it did and
the code did not. So `Prop -> Prop` typed as `Sort (max 1 1)` where the export
declares `Sort 1`, and a correct declaration was rejected.

**`imax u u` never collapsed.** It is `u` either way, since it is zero when `u`
is zero and `max u u` otherwise. Without it a Church numeral cannot be typed,
which cost the three `peano` tests.

**Level parameters were numbered by name, not by position.** A level line
writes `LPar{j}` with `j` the export's name index, but a use site supplies
levels by position. The simplest tests passed regardless, because the identity
is correct when a declaration is used at its own parameter. `Term.remap_levels`
is the translation.

**Max compared as syntax.** `max u v` and `max v u` are the same level, and so
are `max 2 1` and `2`, but comparing syntax says otherwise. `Level.nf` now
flattens a level into atoms, each a base with a count of successors, sorts
them and collapses two atoms on one base. That makes max commutative,
associative, idempotent and absorbing in one stroke, and two closed numerals
compare by value.

**A failed inference passed for `Sort 0`.** This was the bad one. `res_ty` on a
failure returned a dummy, the dummy was `Sort 0`, and `is_sort` accepted it. So
an inference failure inside a pi or a let became a valid sort and the
declaration was **accepted**. The dummy is now a loose variable, which is
neither a sort nor a pi, and both cases guard on `res_ok` as well. `Shape.bend`
follows the same rule. A kernel accepting what it cannot type is the worst
failure there is, and it was invisible until `009_forallSortBad` was traced
declaration by declaration.

**A duplicate universe parameter went unchecked.** The Lean kernel refuses one
in `check_duplicated_univ_params`. A declaration now carries its parameter
list rather than just a count, so the check is possible.

Proof irrelevance took a small design change rather than more code. Two proofs
of one proposition are equal, and deciding that needs the type of each side, so
conversion has to ask for a type. Asking `Infer` would be a cycle, so
`Shape.bend` is inference with every conversion check removed, and `Conv`
depends on that instead. Two further points mattered: a pair on the queue now
carries its own local context, because a pair pushed from under a binder is
open; and the rule is tried before the two sides are taken apart, since once
`f (h a)` and `f (h b)` are split into function and argument, `a` against `b`
is beyond saving.

There is also a limit worth stating. The fuel cannot be large.
`Conv.eq_all` works a queue and its recursive call sits in an argument rather
than in tail position, because the verdict has to be read before the queue can
be shortened. So its depth is bounded by the fuel, and Bend's host stack gives
out near ten thousand frames. A fuel of 100000 overflows on a `let` that needs
real conversion work.

## On the whole small arena set

The tutorial subset is flattering. Across all 196 tests the arena ships in its
tarball, 195 attempted and one too large to read:

| | before the speed work | after the level rules | after the recursor | now |
|---|---|---|---|---|
| correct | 101 | 101 | 173 | **186** |
| declined | 82 | 87 | 17 | **0** |
| wrong | 0 | 0 | 0 | **1** |
| error or timeout | 11 | 7 | 5 | 8 |

The one wrong answer is `init-prelude`, and it arrived the way the other six
did: a kernel that got faster reached a declaration it had never reached
before. It rejects `Lean.Syntax.brecOn_2.go`, which is the machinery Lean
builds for a **nested** inductive, and nothing here derives one. `blame.bend`
names the pair conversion cannot settle:

```
decl 2198
  blame: ((#3 ((Array.mk Lean.Syntax) #1)) #0)
    fn   : (Pi :(Lean.Syntax.below_1 .. ((Array.mk Lean.Syntax) #1)) -> ..)
    arg  : ((PProd ..) (Lean.Syntax.below_2 ..))
```

That is the open item. The eight that are not read are all `perf` tests, plus
one more too large to read at all.

The jump in the last column is the recursor derivation, which is described
below. The middle column hides a story, and it is not what it looks like.

The speed work did not break six files. It made eight of the eleven timeouts
finish, and six of those eight answered `reject` on a file the arena expects
to accept. The committed build from before the speed work answers `reject` on
the same six when it is given ten minutes instead of sixty seconds. So those
were six wrong answers the kernel always had, and a sixty-second limit was
hiding them.

All six failed on one declaration, `Nat.div.go.match_1`, a matcher Lean builds
for a definition by well-founded recursion. Two missing level rules did it,
and `bend/blame.bend` named both in one run each. See "Two levels that are one
level" below. The kernel is back to zero wrong answers, and this time the six
files answer rather than time out.

Getting to zero wrong answers took four rounds, then a fifth. The score was 24
wrong when the three-valued answer landed; projections took it to 11,
quotients and the native `Nat` to 2, and the last two were not missing rules
at all. See below. Then the kernel got fast enough to find six more, and those
were missing rules.

The climb from 74 correct to 101 is a different story and a duller one: ten
checks on an inductive block, each worth one or two tests, none of them
needing the recursor derived. The order they landed in was the order of
cheapness, not of importance.

The seven real-world corpora are not in that tarball and cannot be read at
all, for the memory reason below. So this kernel is not ready to enter the
arena, and the gap is not a matter of a few more tests.

## Making it fast

Twenty times faster, in one afternoon, from one bug written four ways.

| | start | one walk | plus short circuits | plus the guards |
|---|---|---|---|---|
| `perf/church-numerals` | 23.8 s | 16.6 s | 7.6 s | **0.021 s** |
| `perf/let-ladder` | 10.3 s | 9.9 s | 2.3 s | **1.56 s** |
| `perf/folded-constant-last` | 0.89 s | 0.59 s | 0.30 s | **0.094 s** |
| `bad/bugs/rec-of-subst-prop` | 2.95 s | 1.19 s | 0.13 s | **0.12 s** |
| ten files together | 41.2 s | 29.8 s | 10.9 s | **2.08 s** |

Built binaries, `--threads 8`, medians of three, both columns of a comparison
measured in one run. The machine drifts enough between runs that a number from
one hour does not belong beside a number from the next.

### One bug, written four ways

Bend evaluates an argument before the match that picks an arm. So a helper
that chooses between two terms on a computed `Bool` evaluates **both** of
them. The file knew this. `Eval.quot_term` and `Eval.unfold_decl` were already
written to hand back a cheap sort on the branch that is about to be thrown
away, and a comment says why. The same bug was still live in four other
places, and each one cost more than the whole reader.

**A beta step copied the value once per variable.** `Term.subst` read the lift
through `Term.pick`, so every variable in the body walked and rebuilt the
whole value, matching or not. A body with a thousand variables copied a
thousand values to use one. This is the one that took church numerals from
7.6 seconds to 21 milliseconds.

**Proof irrelevance ran on every pair.** `Conv.maybe_proof` is a syntactic
test written to keep the inference passes off pairs that cannot be two proofs,
and `Conv.irrel` read it through `Conv.pick_step`, which evaluates both
branches. So every pair paid for the two inference passes the test was there
to prevent. The guard was right and unreachable.

**The K rule inferred the type of an argument of every application.** Not of
every recursor application: of every application, because the subject was an
argument of the pick as well.

**A conjunction cannot stop early.** `A.Ans.and(step, eq_all(rest))` has to
work the whole queue even after a definite no, because the recursive call is
an argument. A helper that matched the step would have to call `eq_all` from
above it, and Bend has no mutual recursion. The answer travels in as a
parameter instead, which a match can inspect: a definite no returns at once,
and the call becomes a tail call. The same change in `Kernel.check_from` stops
a bad file at the declaration that failed.

The lesson is not "Bend is eager". It is that in Bend a guard is only a guard
if something **matches** on it. A guard read through an argument is a comment.

### The report was most of the work

`main` called `Kernel.report` and then `Kernel.check_all`, and each one walks
the list and checks every declaration. `Kernel.why` ran on every declaration
too, through an argument of `Kernel.mark`, and for a definition it infers the
body three more times. A file was checked about five times to answer once.
That is the "one walk" column above, and it is worth 1.5x on its own.

The report is off now unless `SOKO_REPORT` is set, and it stops at the first
rejection, which is also what makes it usable: `SOKO_REPORT=1` on a 598 kB
export names the declaration that failed in a second, where the old report ran
for five minutes without finishing.

### The GPU is the wrong tool here, and Bend's own numbers say so

`bend guide` is clear that a `!` call ships work to a cube of 16384 lanes and
that the GPU wants uniform numeric work. Three things rule it out for a
kernel.

A P-core is about 75 times a GPU lane on serial work, by the shader guide's
own cost model. A value that every lane reads costs an atomic per read, and
the environment trie is exactly such a value. And the lanes must be balanced,
while the cost of checking one declaration in this corpus spans three orders
of magnitude.

Bend's own pinned benchmarks confirm the shape. On an M4 Max the two that
search rather than compute, `queens` and `lexer`, are the two the GPU loses:
0.455 s on parallel CPU against 0.933 s on the GPU, and 0.198 s against
1.075 s. A kernel is a search.

Parallel CPU is a different matter: those pins show about eleven times over
one core. But the grain has to be right. A parallel call in the application
arm of `Infer.infer`, where the function's type and the argument's type are
genuinely independent, measured 0.99x, which is a loss. The two sides are
nothing like balanced, the tasks are tiny, and the files that take the time
hold two to ten declarations, so there is no coarse grain to fork either. That
change is not in the tree.

What is left to win is algorithmic. The three tests that still time out are
`perf/app-lam` and the two `perf/proj-*-struct`.

## Deriving the recursor

A file states a recursor: its type, and one rule per constructor. Nothing
obliges it to tell the truth. The kernel used to take the statement on trust,
which is why a file with an inductive block answered `declined` and never
`accept` however much of it checked out.

`bend/Rec.bend` builds both halves from the inductive specification.

The type, for `I` with `np` parameters, `ni` indices and constructors
`C_0 .. C_{m-1}`:

```
Pi p_0 .. p_{np-1},
Pi motive : (Pi i.., Pi t : I p.. i.., Sort v),
Pi minor_0 .. minor_{m-1},
Pi i..,
Pi t : I p.. i..,
motive i.. t
```

The minor premise for `C_j : Pi p.., Pi f_0 .. f_{k-1}, I p.. a..`:

```
Pi f_0 .. f_{k-1},
Pi (one hypothesis per recursive field, in field order),
motive a.. (C_j p.. f..)
```

The rule for `C_j`, whose binder types are the same telescope:

```
Lam p.., Lam motive, Lam minor.., Lam f..,
  minor_j f.. (one recursive call per recursive field)
```

The comparison is by **conversion**, not by syntax. The exporter writes a
telescope in whatever form it reduced to: inductive 88 of
`perf/proj-lazy-struct` has a third parameter written `c87[13] S[12]` where
its recursor's is the reduced `S[12]`. An earlier attempt at a syntactic
telescope check made that file reject, and reverting it is what taught this.

| corpus | types matching | rules matching | differing | shapes not derived |
|---|---|---|---|---|
| every good file small enough to read | 374 | 374 | 0 | 0 |
| the bad files | 204 | 211 | 10 types, 17 rules | 18 |

The rules catch seven bad files the type alone does not. A shape the
derivation does not handle gives `T.TUnk`, which converts with nothing, so the
block stays trusted: a gap costs an acceptance and can never cost a false
rejection.

### Two offsets that differ by one

The hypothesis for a recursive field needs the field's type lifted and the
field's own variable indexed, and the two are not the same number. The type
was written before its own binder, so it lifts by `nf - i + k`; the variable
is bound, so it stands at `nf - 1 - i + k`.

`Bool`, `And`, `Nat` and `List` all pass with the lift wrong, because a field
type with no parameter in it does not care how far it is lifted. `rbTree` and
the four `magma` files do not, and that is how the bug was found. A second one
of the same kind: the constructor's own index arguments are arguments side by
side and not a telescope, so they all lift by the same amount.

### The tool

`bend/derive.bend` reports, per recursor, whether the derived type and every
derived rule converts with what the file states. It changes no verdict. It is
what turned "the derivation is probably right" into a number, twice.

## What Lean never looks at

A declaration the exporter marks `unsafe` or `partial` is one Lean's kernel
never reads. So a kernel that checks it is not stricter, it is wrong:
`unsafe def loop : False := loop` is a file Lean accepts, and strip the
theorem from the arena's `140_falseFromUnsafe` and this kernel answered
`reject`.

`E.DUnsafe` keeps such a declaration as its type and nothing else. What makes
that sound is the other half of Lean's rule, which this kernel did not have:
**a safe declaration may not mention an unsafe one.** `Kernel.safe_uses`
walks a declaration's type and value and looks each constant up. So
`140_falseFromUnsafe` and `141_falseFromPartial` are rejected for the reason
the arena names, where before they were rejected by accident, because the
unsafe body happens to be a forward reference to itself.

### A nested block has more than one recursor

Lean gives a block with a nested inductive several eliminators, names them
`I.rec_1`, `I.rec_2` and so on, and states more motives than the recursor
lists inductives, because each auxiliary type needs one. Two rules here were
proxies written against the arena's attacks, and both rejected such a
recursor.

`Parse.upd_rec` recorded only a name whose last component is exactly `rec`. It
takes one beginning with `rec_` now, which is looser than Lean and still
refuses the three attacks the rule is for: `extra-rec` names its rogue
eliminator `False.rogue`, and `misnamed_rec_user` and `dup_rec_def2` each name
theirs `not_rec`.

`Kernel.rec_counts_ok` compared the minor count with the constructors of the
inductives it can name, which a nested block makes impossible. The skip is
**one-sided** on purpose: a nested block states more motives than types, while
`073_BogusRecursor` states fewer, zero against one. A two-sided test let that
file through to the trust path and it answered `declined` where it had
answered `reject`.

### One commit that was half lost

"Check a file once, and stop at the first rejection" went in with only half of
itself. A `git checkout -- bend/check.bend` during a measurement in the same
iteration discarded the uncommitted entry point, and what was committed still
called `Kernel.report` and then `Kernel.check_all`. So every run for the next
several hours checked the file about five times to answer once, and every
measurement taken after it carried that.

Restoring the entry point is 1.64x. `Kernel.report` is deleted rather than
fixed, because the two walks had already drifted: the report said `ok` on a
declaration the verdict rejected, having never been given the universe and
safety rules. One walk cannot drift.

## Two attacks nobody wrote

The arena's `bad` files are an attack suite and this kernel answers all of
them. That is not the same as being sound. This repo also holds a Lean kernel
in Rust that passes the same suite, so its rejections are a second list of
things that must be refused, and two of them were holes here that let a file
be **accepted**.

**A projection naming the wrong structure.** A projection node carries a type
name of its own, and the kernel read the field out of the structure's inferred
type, so a name that did not match was never looked at. It is not harmless:
the name goes into the term, where `Conv.proj_step` compares two projections
by it and reduction reads it. `089_projProp1` with its `typeName` changed from
19 to 1 answered `accept` and now answers `reject`.

**A universe a declaration did not declare.** `Level.param_pos` numbers a
declaration's parameters by position and used to answer the raw name index for
one that was not declared. A name index smaller than the number of declared
parameters was then read as one of them, so a file could use a universe it
never declared and have it taken for a universe it did. `069_eqRec` with one
of its two `levelParams` removed answered `accept` and now answers `reject`.

Neither rule changes the score, because nothing in the corpus exercises
either. That is the point.

## The four quotient types

A quotient is not derived from anything. Lean's kernel adds `Quot`, `Quot.mk`,
`Quot.lift` and `Quot.ind` with types it writes itself, and a file states
them, so a kernel that takes the statement on trust will accept a proof the
quotient should not allow. `bend/Quo.bend` holds those four types and the
kernel compares.

Two names are needed and neither is in the kernel. `Quot` and `Quot.mk` come
from the file, by the kind each quotient line states. `Eq` comes from the
reader, which finds it by its spelling as it already finds `Nat`, `Bool` and
the eight native `Nat` definitions: the type of `Quot.lift` says that a
function respects the relation, and it says so with `Eq`.

A quotient whose type does not match leaves the file **declined**, not
rejected. The comparison depends on the reader having found `Eq`, and a reader
that missed it should cost an acceptance rather than cause a false rejection.
A file whose `Quot.lift` type is replaced by another expression answers
`declined` where it answered `accept`, which is the check working.

## Two levels that are one level

Six files answered `reject` where the arena expects `accept`, and all six
failed on `Nat.div.go.match_1`. Both causes were universe levels, and both
were a pair of levels that are equal under every assignment and are not the
same syntax.

`imax u v` is zero when `v` is zero and `max u v` otherwise. So:

- `imax 0 v` is `v`, always. Zero when `v` is zero, which is `v`, and `max 0
  v` otherwise, which is `v` as well. `Level.mk_imax` had the rule for a zero
  right side and not for a zero left side.
- `imax 1 v` is also `v`, always, and no smart constructor can see it: zero
  when `v` is zero, and `max 1 v` otherwise, which is `v` once `v` is at least
  one. This one needs the case split the Lean kernel does. Pick a parameter
  standing on the right of an imax, ask the question with it set to zero and
  again with it set to its own successor, and require both.

A motive of the form `fun n => (h : p n) -> C n h` has type `Nat -> Sort (imax
0 u)`, because its domain is a proposition, while the eliminator that takes it
declares `Nat -> Sort u`. That was the first one. The second motive in the
same declaration has type `Nat -> Sort (imax 1 (imax 1 u))`. That was the
second.

### The tool that found them

A rejection says only that a whole value is wrong, and the value here is
thousands of nodes. `bend/blame.bend` walks into the value and stops at the
smallest subterm inference calls a definite no, which is a node whose own
answer is no while no child of it is. Then it prints that node and, for an
application, the type of each side. Both bugs took one run each:

```
SOKO_EXPORT=<an export> bend bend/blame.bend
```

```
decl 631
  blame: (c106{p0} (fun :c62{} => (Pi :(... #5) #0) -> ((#5 #1) #0))))
    fn   : (Pi :(Pi :c62{} -> Sort p0) -> ...)
    arg  : (Pi :c62{} -> Sort (imax 0 p0))
```

The walk cannot ask a helper where to go and then recurse there, because a
match needs a parameter and Bend has no mutual recursion. So each step
computes the next node and the next context as values and calls itself in tail
position, and a step that finds no child to blame hands back the node it is
on, which makes the walk stand still until the last step prints it.

## Running out of budget

A kernel has three honest replies, not two: yes, no, and "I ran out of the
budget I was given". Reporting the third as a rejection is reporting falsely.
This kernel used to do that. Reduction handed back the term unreduced,
conversion compared it with something, found a difference, and the declaration
was rejected for want of budget.

Now reduction hands back `TUnk`, every function that meets it answers that it
does not know, and `Ans` carries that third value through conversion,
inference and the kernel. A definite no still wins over not knowing, because a
declaration that fails one check is wrong whatever the others would have said.
That turned five wrong answers into honest declines.

Carrying the third value is not enough on its own. The last two wrong answers
on the whole set were both this same bug surviving in a corner, and neither
was a missing rule.

**A stuck constant.** When a recursor's major premise could not be reduced,
the constant case rebuilt the constant and handed it back. A rebuilt constant
looks stuck, and two stuck terms that differ are a definite no. The projection
case had guarded this from the start and the constant case never did. That was
`folded-constant-first`.

**A pi read off an unknown.** `Infer.pi_dom` answers with the dummy when its
argument is not a pi, and the dummy is a loose variable, which converts with
nothing. So when inference of a function ran out, the argument's type was
compared against a loose variable and conversion said no. The type of
`beta-ladder` is two thousand lambdas deep against a budget of three
thousand, so it ran out exactly that way. A term reduction gave up on now
answers with itself.

Both fixes make the kernel less capable and more honest. Two rejections became
declines, which is the right direction: a decline scores nothing, and a wrong
answer is a false claim.

**A number too large to hold.** Not a budget problem but the same principle. A
Bend `Nat` holds up to 2^48-1 and Lean's prelude writes `18446744073709551616`
for the size of a `UInt64`. Reading it crashed the kernel, and a crash is the
one answer worse than not knowing. The reader now saturates at a cap and a
literal that reaches it is read as unknown.

## Reading an export

The first attempt used `String`, and it failed hard. A Bend string is a linked
list of characters, and Base's `String.lines`, `String.length` and
`String.split` recurse once per character with the call out of tail position,
so they overflow the host stack. Upstream has both bugs on file as
bendlang/bend#798 and #802. Measured here, `String.lines` dies at 50 KB, while
the smallest arena test is 3.7 MB.

The second attempt reads bytes and walks them with tail calls, which the guide
says compile to loops. That works. `scan.bend` on the smallest arena test:

| | Bend | expected |
|---|---|---|
| bytes | 3741967 | `wc -c` 3741967 |
| lines | 64110 | `wc -l` 64110 |
| first `"in":` | 1 | 1 |

0.13 s for the whole 3.7 MB file. For scale, the Rust build parses the same
file into 2106 declarations in 0.004 s, so this is roughly thirty times slower
while doing far less. That is the right trade for this folder.

`read.bend` then classifies every line of the same file. Each count matches
`grep`, and the 54799 expression lines are the exact sum of the eight node
keys `ie`, `app`, `bvar`, `const`, `lam`, `forallE`, `letE` and `proj`:

| kind | Bend | grep |
|---|---|---|
| meta | 1 | 1 |
| name | 7373 | 7373 |
| level | 113 | 113 |
| expr | 54799 | 54799 |
| axiom | 3 | 3 |
| def | 1527 | 1527 |
| thm | 154 | 154 |
| inductive | 126 | 126 |
| quot | 4 | 4 |
| opaque | 10 | 10 |
| unclassified | 0 | — |

The total is 64110, which is `wc -l`. It takes 0.51 s.

The idiom that made it work, and that every function in `Bytes.bend` follows:

1. peek at the head with a small non-recursive helper,
2. pass the answer as a parameter of the next call,
3. make that call the whole body, so it is a tail call.

Bend will not let a `match` look at a computed value and will not let two defs
call each other, so a conditional cannot sit between the recursion and the tail
position. Carrying the decision forward in a parameter is the way around both.

### The memory ceiling

A byte list is expensive. Peak resident memory is 798 MB for the 3.7 MB file
and 388 MB for a 1.2 MB one, so roughly 200 to 300 bytes of memory per byte of
input. On a 96 GiB machine that caps the input at a few hundred megabytes, and
mathlib at 6 GB would want more than a terabyte.

So holding the whole file as a cons list is a dead end for the large corpora.
The fix is to stop holding it: read in chunks with `File.read_at`, or keep the
bytes in an `Array<U32>`, which is one owner and compact. The byte list is the
last structure that is still a list; the index tables and the environment are
tries, and `Table.bend` says why they could not be `Array`.

A bug worth recording: the first search skipped to the key's first byte and
required the whole key there, with no retry. The first `"` in an export belongs
to the metadata line, so every lookup answered zero. Counting bytes and lines
was already correct, which is why cross-checking against a second key caught
it.

## Installing Bend 2

Bend 2 is not in nixpkgs. The `bend` package there at version 0.2.x is Bend 1,
a different language from the same lineage. Bend 2 ships a flake, so:

```
nix build --no-write-lock-file github:bendlang/bend -o bend-out
./bend-out/bin/bend bend/main.bend
```

The official installer is `curl -fsSL https://bend-lang.com/install.sh | sh`.

`bend PROOF.bend --verdict` rechecks the proofs with BendTT, Bend's own
kernel, which has a proof in Lean. It needs Lean v4.34.0 on PATH. The laws
here pass that gate as well, so these proofs hold under both Bend's checker
and the kernel that is proven in Lean.

```
devbox run -- elan toolchain install leanprover/lean4:v4.34.0
devbox run -- elan default leanprover/lean4:v4.34.0
devbox run bend-verdict
```
