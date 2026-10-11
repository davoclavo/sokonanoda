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

**Deriving the recursor.** The block is read, every type in it is checked, and
iota reduction works, so a recursor applied to a constructor computes. What is
not here is the one part that would let such a file be *accepted*: nothing
derives the recursor from the inductive specification and compares it to the
one the file states. Until that exists, a file with an inductive block answers
`declined` and never `accept`, and that is every one of the 67 remaining
declines in the tutorial set.

It is the largest piece of work left and the only one worth real points.

**An indexed family eliminated through its own `casesOn`.** Six files answer
`reject` where the arena expects `accept`, and all six fail on the same
declaration: `Nat.div.go.match_1`, which eliminates `Nat.le` through
`Nat.le.casesOn` with `Eq.refl` and `HEq.refl` arguments. Inference answers a
definite no on its body, and ten times the budget does not change it. These
six were hidden behind a sixty-second limit until the kernel got fast enough
to reach them. This is the largest correctness item left.

**Reduction throughput.** Reading was never the problem and the checking was.
Three `perf` tests still time out: `app-lam` and the two `proj-*-struct`. The
work is reduction and inference doing real work, so a faster table will not
move them. See "Making it fast" for what did move them, and for the four
places a guard was written and never reached.

**The imax case split.** The case split on an imax whose right side is a bare
parameter is not here, so two such atoms are still compared as syntax.

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

| | before the speed work | after |
|---|---|---|
| correct | 101 | 101 |
| declined | 82 | 85 |
| wrong | 0 | **6** |
| error or timeout | 11 | 3 |

Read that table carefully, because it is not what it looks like.

The speed work did not break six files. It made eight of the eleven timeouts
finish, and six of those eight answer `reject` on a file the arena expects to
accept. The committed build before the speed work answers `reject` on the same
six when it is given ten minutes instead of sixty seconds. So these are six
wrong answers the kernel always had, and a sixty-second limit was hiding them.

A timeout scores as an error and a wrong answer is a false claim, so this is a
score that went down and a kernel that got more honest about itself. The six
are `init-prelude`, `perf/fueled-chain` and the four `perf/magma-list-*`
tests.

What they have in common is the first declaration each one rejects:
`Nat.div.go.match_1`, a matcher that Lean builds for a definition by
well-founded recursion. Inference answers a definite no on its body, and a
budget ten times larger does not change that, so it is not the budget. The
body eliminates `Nat.le`, an inductive family with an index, through
`Nat.le.casesOn` with `Eq.refl` and `HEq.refl` arguments. That is the next
thing to fix, and it is a completeness bug, not a speed one.

Getting to zero wrong answers took four rounds. The score was 24 wrong when
the three-valued answer landed; projections took it to 11, quotients and the
native `Nat` to 2, and the last two were not missing rules at all. See below.
Then the kernel got fast enough to find six more.

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
