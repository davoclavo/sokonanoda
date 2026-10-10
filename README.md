# sokonanodazo

`sokonanodazo` is a Lean 4 kernel checker. It is based on Jeremy Chen's
[sokonanoda](https://github.com/intgrah/sokonanoda), which is itself part of the
nanoda-family lineage that starts with ammkrn's
[nanoda](https://github.com/ammkrn/nanoda_lib).

Nearly all of the engineering here belongs to the parent. The closure-based
conversion algorithm, the packed term representation, the interner, the session
caches, the parallel driver, and the NDJSON parser are all sokonanoda's work.
The parent also chose the cache shapes and sizes that this fork leaves alone,
and several of those choices proved better than the alternatives this fork
measured.

This fork stays close to the parent. It is not an independent rewrite, and no
such claim is intended. A larger architectural change is future work rather
than something this revision contains. The diff against the parent is about 200
lines of checker code.

## What this fork changes

### It judges `unsafe` and `partial` declarations

The parent declines any export that declares one. A declined result claims
nothing about the proof, so this is honest, but it also means the checker gives
no verdict on the two arena tests that prove `False` through an unsafe
definition.

This fork registers such a declaration, checks its type, never checks its
value, and never unfolds it. A safe declaration that names one is rejected.
The Lean kernel makes the same check in `type_checker::infer_constant`, and this
fork reports it with the kernel's own two messages.

The effect on the arena is 205 correct with 0 declined, in place of 203 correct
with 2 declined.

### A smaller session arena budget

The budget drops from 16 MiB to 2 MiB. A smaller arena keeps the working set in
cache, and that is worth more than the cache entries a larger arena retains.

Measured with interleaved repeated runs, 2 MiB beats 16 MiB on every corpus and
every thread count tested. No corpus prefers the larger value.

### The thread count no longer caps itself at four

The parent takes the core count and then caps it at four. This fork uses every
core. The cap cost real time on any machine with more than four cores. The arena
published cpu-to-wall ratios of up to 5.74 for other checkers, so the arena
machine is not limited to four cores either.

### Measured effect

Parent against this fork, median of interleaved repeated runs, 14 cores.

| Corpus | Flags | parent | this fork | Speedup |
|---|---|---|---|---|
| mathlib | `--threads 4` | 25.1 s | 22.8 s | 1.10x |
| cslib | `--threads 4` | 8.9 s | 8.1 s | 1.11x |
| mathlib | default | 24.6 s | 13.6 s | 1.80x |
| cslib | default | 8.9 s | 4.7 s | 1.88x |

## What this fork tried and rejected

Each of these was measured and then dropped, so that nobody repeats the work.

| Change | Result |
|---|---|
| `-C target-cpu=native` | within 1 percent |
| The parent's `top-byte-ignore` feature on aarch64 | within 1 percent |
| Newer versions of every dependency | within 1 percent |
| mimalloc tuning through its environment variables | within 1.5 percent |
| A larger `prune_dm` cache, from 1024 up to 262144 entries | up to 19 percent **worse** |
| A larger work chunk per thread | no effect once measured correctly |

The `prune_dm` result is worth keeping. That table is cleared on every session
reset, so growing it costs more in reset time than it returns in hit rate. The
parent's 1024 entries are correct, and a smaller session budget makes a large
table worse still.

Two of these looked like 8 percent wins when measured one configuration after
another. Both vanished once the configurations were interleaved and compared on
medians. This machine shows load spikes that move a single run by a factor of
two, so any single-shot comparison here is worthless.

## Where the remaining time goes

Checking is 86 percent of mathlib's time and parsing is 14 percent. Self time
from a sampled profile, which is nearly the same shape at 1 thread and at 12.

| Function | Share |
|---|---|
| `eval_no_cache` | 22 percent |
| `eval` | 20 percent |
| `infer_nonvar` | 17 percent |
| `prune_env_cold` | 7 percent |
| `intern_frame` | 6 percent |

Parallel scaling is lossy. mathlib needs 70.9 s of CPU on 1 thread and 117.3 s
on 12. Waits are only 12 percent of samples, so this is not lock contention.
Each thread owns its caches and its arena, so every thread re-evaluates the same
common constants from cold. Sharing those results across threads is the largest
remaining opportunity, and it needs either a shared arena with concurrent
interning or a serialized representation at the thread boundary.

## Tools

`tools/` holds a harness that runs the whole 223-test arena suite on your
machine, and a benchmark tool for comparing two builds. See
[tools/README.md](tools/README.md).

```
devbox run build
devbox run arena-fetch
devbox run arena
```

All 223 arena tests pass, with 0 declined and 0 wrong. That count includes all
seven large real-world corpora, built from Lean sources and checked locally:
`init`, `std`, `cedar`, `con-leche`, `cslib`, `navier-stokes-euler`, and
`mathlib`.

## License

Apache-2.0, as the parent.
