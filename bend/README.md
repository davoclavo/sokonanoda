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
| `Env.bend` | declarations and the environment |
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

**The checks on an inductive block.** The block is read, every type in it is
checked, and iota reduction works, so a recursor applied to a constructor
computes. What is not here is the part that makes a verdict trustworthy:
nothing derives the recursor from the inductive specification and compares the
two, and nothing checks positivity or the universe of a constructor's fields.
So such a file answers `declined`, never `accept`. The arena's `BogusRecursor`,
`indNeg` and `typeWithTooHighTypeField` are exactly the attacks that check
would stop, and all three currently decline rather than reject.

This is now the only thing between most of the declines and a verdict. It is
also the largest piece of work left.

**Scale.** The reader works, but its tables are lists, so a lookup is linear
and a file with fifty thousand expressions is far too slow. `Array` is the
answer, and it is the same change the memory ceiling below needs. Ten `perf`
tests time out for this reason and one is too large to read at all.

**The imax case split.** The case split on an imax whose right side is a bare
parameter is not here, so two such atoms are still compared as syntax.

**Performance.** Bend has no `U64`, so the parent's packed pointers and
hash-consed terms cannot be carried over, and the environment is a list
searched linearly where the parent resolves a constant in one load. The point
of this folder is the proofs, not the clock.

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
| correct reject | 29 |
| honest decline, an inductive block was trusted | 83 |
| wrongly rejected | **0** |
| wrongly accepted | **0** |
| error or timeout | **0** |

**Every verdict it gives is correct.** A decline is the arena's exit code 2 and
scores nothing, so 58 of the 141 are verdicts and the other 83 are the work
that remains. Nothing times out and nothing errors.

On the 37 tests that need no inductive block, it is 37 correct.

The single thing standing between the 83 declines and 83 verdicts is deriving
the recursor from the inductive specification and comparing the two. Nothing
else is missing for them.

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

| | count |
|---|---|
| correct | 78 |
| declined | 106 |
| wrong | **0** |
| error or timeout | 11 |

**Every verdict it gives is correct, on the whole set and not only the
tutorial part.** The 11 are ten `perf` tests that time out and one more that is
too large to read, all for the scale reason above.

Getting to zero wrong answers took four rounds. The score was 24 wrong when
the three-valued answer landed; projections took it to 11, quotients and the
native `Nat` to 2, and the last two were not missing rules at all. See below.

The seven real-world corpora are not in that tarball and cannot be read at
all, for the memory reason below. So this kernel is not ready to enter the
arena, and the gap is not a matter of a few more tests.

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
bytes in an `Array<U32>`, which is one owner and compact. That is the same
change the index tables need, so it is one step rather than two.

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
