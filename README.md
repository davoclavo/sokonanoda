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

Three changes sit on top, and they come to roughly 200 lines.

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
