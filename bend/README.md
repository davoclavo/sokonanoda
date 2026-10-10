# The kernel core in Bend 2

This is the dependently typed core of the Lean kernel, written in
[Bend 2](https://github.com/bendlang/bend) and checked by Bend's own checker.

It is a re-implementation of the middle of `sokonanodazo`, not a port of the
whole thing, and it is not a performance exercise. Read the limits below before
you read the code.

## Run it

```
bend bend/main.bend     # check three environments and print the verdicts
bend bend/PROOF.bend    # check the laws
```

From the repository root, with Bend on PATH:

```
devbox run bend          # the driver
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
| `Eval.bend` | weak head normal form: beta, delta, zeta |
| `Conv.bend` | definitional equality, as a worklist |
| `Infer.bend` | type inference for the core |
| `main.bend` | the driver and its three test environments |
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

**Inductive types, constructors, recursors, projections, and quotients.** This
is most of the Lean kernel by volume, and all of its hard parts: positivity,
nested inductives, recursor rules, iota reduction, large elimination, and K-like
reduction. None of it is here. What is here is the dependently typed core that
the rest is built on.

**The parser.** A Bend string is a linked list of characters, so reading the
arena's 6 GB mathlib export is out of reach. Environments are built in Bend.

**Eta, proof irrelevance, and the imax case split.** Proof irrelevance is the
interesting omission: it needs the type of a term, so adding it makes
conversion and inference mutually recursive, which Bend forbids. Breaking that
cycle is the next real design problem here, not a matter of writing more code.

**Performance.** Bend has no `U64`, so the parent's packed pointers and
hash-consed terms cannot be carried over, and the environment is a list
searched linearly where the parent resolves a constant in one load. The point
of this folder is the proofs, not the clock.

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
