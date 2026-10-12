# sokonanodazo

`sokonanodazo` is a Lean 4 kernel checker. It is a fork of
[sokonanoda](https://github.com/intgrah/sokonanoda) by Jeremy Chen, which
descends in turn from [nanoda](https://github.com/ammkrn/nanoda_lib) by ammkrn.

The checker is sokonanoda's. Read the parent's source and you have read almost
all of this one: the closure-based conversion algorithm, the packed term
representation, the interner, the session caches, the parallel driver, and the
NDJSON parser are all its work. So are the cache shapes and sizes, which this
fork leaves alone because measuring the alternatives showed the parent had
already picked well.

Three changes sit on top, and they come to roughly 200 lines. A second
implementation of the kernel core, written in Bend 2 and proven in it, lives in
`bend/`.

## What this fork changes

**It judges `unsafe` and `partial` declarations.** The parent declines any
export that declares one, so it gives no verdict on the two arena tests that
prove `False` through an unsafe definition. This fork registers such a
declaration, checks its type, never checks its value, and never unfolds it. A
safe declaration that names one is rejected, with the Lean kernel's own two
messages from `type_checker::infer_constant`. The arena suite goes from 221
correct with 2 declined to 223 correct with 0 declined.

**The session arena budget drops from 16 MiB to 2 MiB.** A smaller arena keeps
the working set in cache. The gain is real on the large corpora and absent on
the small ones: at four threads it beats 16 MiB by 10 percent on cslib and 20
percent on mathlib, and ties on std and cedar at every thread count tried.

**The thread count no longer caps itself at four.** The parent caps the default
at four cores. This fork uses every core.

## Measured effect

One machine, an Apple M3 Max with 14 cores. Medians of interleaved repeated
runs.

| Corpus | Flags | parent | this fork | Speedup |
|---|---|---|---|---|
| mathlib | `--threads 4` | 25.3 s | 23.8 s | 1.06x |
| cslib | `--threads 4` | 9.5 s | 8.5 s | 1.12x |
| mathlib | default | 28.7 s | 14.2 s | 2.0x |
| cslib | default | 11.5 s | 6.8 s | 1.7x |

Treat the single-digit figures with suspicion. Runs on this machine drift by
several percent, and `init` comes out 1 to 3 percent *slower* than the parent.

**These are wall clock times, and the arena scores an instruction count.** The
budget change trades cache hits for locality, and fewer cache hits means more
instructions. So this fork may score *worse* than the parent on the arena while
running faster in practice. Nobody has measured that; it needs `perf stat` on a
quiet Linux host. This fork is tuned for wall clock time.

Other ideas were measured and dropped: `target-cpu=native`, the parent's
`top-byte-ignore` feature, newer dependencies, allocator tuning, larger cache
tables, a union-find conversion cache, and a budget that scales with the thread
count. None beat the parent's existing choices. See
[docs/perf-plan.md](docs/perf-plan.md).

## The kernel core in Bend 2

`bend/` holds a second, independent implementation of the dependently typed
core, written in [Bend 2](https://github.com/bendlang/bend) and checked by
Bend's own checker. It is about 9,800 lines across 28 files, and it shares no
code with the Rust checker above.

It is not a port of the whole thing and not a performance exercise. Bend has no
`U64`, so the packed pointers and hash-consed terms that make the Rust checker
fast cannot be carried over. What Bend offers instead is that a claim about the
kernel can be stated and then mechanically proven, in the same language as the
code. `LAWS.bend` states the laws and `PROOF.bend` proves them by induction;
`bend PROOF.bend` prints `ALL PROOFS CHECK` only when every law holds. The three
proven today say that an empty level assignment leaves a level, a list of
levels, and a term alone. That is a small claim, and it is the kind a kernel
silently assumes: if it were false, a declaration with no level parameters could
be read at the wrong type.

Across the 196 tests in the arena's tarball it answers 186 correct, 0 declined
and 0 wrong. Nine run past sixty seconds and one is too large to read. The seven
large real-world corpora cannot be read at all, so this kernel cannot enter the
arena, and the gap is not a matter of a few more rules.

```
devbox run bend          # three built-in environments
devbox run bend-proof    # the laws
devbox run bend-check    # a real export, named by SOKO_EXPORT
```

[bend/README.md](bend/README.md) carries the detail: what each file holds, how
three of Bend's rules shape every one of them, what is still missing, and the
wrong answers that the proofs and the speed work turned up.

## Tools

`tools/` holds a harness that runs the whole 223-test arena suite on your
machine, and a benchmark tool for comparing two builds. See
[tools/README.md](tools/README.md). All 223 tests pass, including the seven
large corpora built from Lean sources: `init`, `std`, `cedar`, `con-leche`,
`cslib`, `navier-stokes-euler`, and `mathlib`.

```
devbox run build
devbox run arena-fetch
devbox run arena
```

## License

Apache-2.0, as the parent.
