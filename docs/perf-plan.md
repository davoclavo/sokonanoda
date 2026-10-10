# Performance plan

A list of performance hypotheses for this checker. Each one states a claim, a
test, and a result. Update the result after you run the test.

Status values:

- `confirmed` the test supports the claim
- `rejected` the test contradicts the claim
- `mixed` the result depends on a condition that the claim does not state
- `open` nobody ran the test yet

## The measurement rig

Record every number against a rig. A number without a rig means nothing.

| Item | Value |
|---|---|
| Machine | Apple M3 Max, 10 performance cores, 4 efficiency cores, 96 GiB |
| OS | macOS 26.2 |
| Toolchain | cargo 1.91.1, release profile from `Cargo.toml` |
| Harness | `tools/bench.py`, which interleaves builds and ranks by the median |
| Baseline commit | `22ddfed` |

Build two binaries and compare them. Never compare a number against a number
from another day.

```
cargo build --release && cp target/release/sokonanodazo /tmp/a
# apply the change
cargo build --release && cp target/release/sokonanodazo /tmp/b
python3 tools/bench.py a=/tmp/a b=/tmp/b --reps 5 --threads 4 --tests std cedar
```

Trust the median. Noise only adds time, so a best time flatters a lucky run.

## What the arena scores

**H0. The arena ranks on a retired instruction count, not on wall time.**

The arena divides a total instruction count by a fixed 6.0 Ginstr/s and calls
the result a virtual CPU time. The wall clock time appears only in a tooltip.
See <https://arena.lean-lang.org/> and
<https://github.com/leanprover/lean-kernel-arena/pull/217>.

- Status: **confirmed** from the arena documentation. 2026-10-09.
- Consequence: an optimization that cuts work scores. An optimization that only
  overlaps work does not score.
- Open follow-up: measure a real instruction count with `perf stat` on Linux.
  macOS gives no counter tool here, so every number below is a wall clock time.

**H1. Threads raise the score, because each thread repeats work.**

Each thread owns a full set of caches, so threads unfold and reduce the same
declarations twice over.

Test on cedar with `/usr/bin/time -l`.

| threads | wall | CPU | peak memory |
|---|---|---|---|
| 1 | 9.80 s | 9.56 s | 2.56 GB |
| 8 | 2.07 s | 12.72 s | 3.70 GB |

- Status: **confirmed**. 2026-10-09. Eight threads cost 33 percent more CPU.
- Action: `tools/arena.py` passes `--threads 4`, which matches
  `checkers/sokonanoda.yaml`. Measure the arena score at `--threads 1` before
  the next submission.

## Build and tuning hypotheses

**H2. The session budget must scale with the thread count.**

`SESSION_BUDGET` in `src/checker/tc.rs` is a per-thread share of one shared
cache. The committed value of 2 MiB comes from 4-thread wall times. At one
thread the threads do not compete, so a larger budget keeps more cache hits.

Test: build a 2 MiB variant and a 16 MiB variant from the same tree, then run
`tools/bench.py` at one thread and at four threads.

| corpus | threads | 2 MiB | 16 MiB | outcome |
|---|---|---|---|---|
| std | 1 | 7.250 s | 6.688 s | 16 MiB wins by 7.8 percent |
| cedar | 1 | 10.080 s | 9.883 s | 16 MiB wins by 2.0 percent |
| std | 4 | 2.247 s | 2.257 s | a tie |
| cedar | 4 | 3.518 s | 3.707 s | 2 MiB wins by 5.4 percent |

- Status: **confirmed**. 2026-10-09. The choice inverts with the thread count.
- Action: derive the budget from a cache estimate divided by `num_threads`.
  Keep 2 MiB as the floor for four threads or more.
- Open follow-up: the one-thread win points the same way as H0 and H1. Both say
  that more cache hits score better than better locality.

**H3. `-C target-cpu=native` makes the checker faster.**

| corpus | baseline | native | outcome |
|---|---|---|---|
| init | 1.272 s | 1.247 s | 2.0 percent faster |
| std | 2.093 s | 2.100 s | 0.3 percent slower |
| cedar | 3.353 s | 3.390 s | 1.1 percent slower |

- Status: **rejected** on this machine. 2026-10-09. The spread is noise.
- Open follow-up: the arena host may be x86. Retest there, where AVX2 and
  `x86-64-v3` can change the code the compiler emits.

**H4. Profile-guided optimization cuts the instruction count by 5 to 20 percent.**

A kernel checker is a compiler-like workload. rustc gains up to 15 percent and
rust-analyzer about 20 percent. BOLT added almost nothing on top of PGO in the
reports, so test PGO alone first. See
<https://kobzol.github.io/rust/cargo/2023/07/28/rust-cargo-pgo.html>.

Test with `cargo-pgo`. Train on `init` and `std`. Benchmark on `cedar` and
`cslib`, which the training run never saw.

- Status: **open**
- Cost: small. No change to the checker.
- Note: the arena builds from a recipe, so the profile must live in the repo and
  the build must apply it.
- Result:

**H5. `PROBE_CAP` and `WHNF_ADMIT_THRESHOLD` are tuned for wall time.**

`PROBE_CAP = 2048` sits in `src/checker/conv.rs`. `WHNF_ADMIT_THRESHOLD = 2`
sits in `src/checker/eval/whnf_cache.rs`. Both trade work against cache
pressure, so H0 says both need a new sweep.

Test: sweep each constant over a range at one thread and at four threads.

- Status: **open**
- Result:

## Algorithmic hypotheses

**H6. A union-find positive conversion cache cuts conversion calls by orders of magnitude.**

`conv_cache_pos` holds pairs of value ids, so it needs one entry for each pair
it proves. A union-find over value ids holds one entry for each value, and it
gives symmetry and transitivity for free. The ansatz kernel reports that a
union-find plus a negative pair cache cut one mathlib declaration from 9.6
million conversion calls to eleven thousand. See
<https://github.com/replikativ/ansatz/pull/104>.

Two steps:

1. Replace the positive pair set with a union-find over value ids. Look up a
   class representative before the negative probe too, so one negative fact
   covers a whole class.
2. Canonicalize each spine argument to its class representative before
   `app_hc` and `rigid_hc` build a value. Equal subterms then hash-cons to one
   pointer, and the `std::ptr::eq` fast path at the top of `unify` fires much
   more often. The `canon` flag and `canon_cache` give a place to hang this.

- Status: **open**
- Risk: a class must not outlive its session, and a class must respect the bvar
  depth. The value digest already carries the depth, so check that first.
- Instrument: count the calls to `unify_no_cache` before the change and after.
- Result:

**H7. Pointer compression halves the memory traffic of the hot caches.**

A session arena holds 2 MiB, so 21 bits address every value in it. `Id` carries
a 64-bit address. The hot `PtrMap` keys pay for that. `pi_hc` uses a four-word
key, which is 32 bytes before the value and the tag. A 32-bit arena offset
halves every key and doubles the entries per cache line. lazylean uses 32-bit
handles for the same reason. The `top-byte-ignore` feature shows that this repo
already works with pointer bits.

Measured sizes on the baseline commit:

| Type | Bytes |
|---|---|
| `Value` | 56 |
| `Env` | 64 |
| `Spine` | 32 |
| `Closure` | 24 |
| `Elim` | 8 |
| `Ctx` | 16 |

- Status: **open**
- Cost: large. This touches `ptrmap.rs`, `value.rs`, and every cache key.
- Note: do H6 first. H6 may change which caches stay hot.
- Result:

**H8. A fused body for each definition removes repeated matcher unfolding.**

lazylean pre-reduces each definition once, which unfolds matchers and contracts
beta-redexes, and it derives fixpoint rules for self-recursive definitions. See
<https://github.com/corun1024/lazylean>. mathlib proof terms are dominated by
`match_n` auxiliaries. Here `const_head_value_cache` is a session cache, so
every session and every thread rebuilds the same closure chain.

Test: build a global table of fused bodies for the definitions that the checker
unfolds most often. Count the unfolds first to pick the set.

- Status: **open**
- Result:

**H9. A shared whnf store removes the work that threads duplicate.**

`whnf_store` maps a digest to a full key and an `ExprPtr`. It is a pure
value-to-expression table, so it is the one cache that threads can share
through a sharded read-mostly map. This attacks H1 directly.

- Status: **open**
- Blocker: the `ExprPtr` comes from the per-thread expression interner that
  `tctx.expr_cache.clear_session()` truncates. Write only tenured entries into a
  shared permanent tier.
- Result:

**H10. Matcher-aware iota skips the intermediate recursor spine.**

Recognize a `casesOn` shape and a `match_n` shape, then jump straight to the
branch. Today the checker builds the recursor spine and then collapses it. The
arena added perf tests for projections of expensive structs, which points at the
same cost. See <https://github.com/leanprover/lean-kernel-arena/pull/257>.

- Status: **open**
- Result:

**H11. Interned level normal forms make level comparison one integer compare.**

`eq_antisymm` and `eq_antisymm_many` run on every rigid head match in
`unify_direct`. Normalize each level once into a canonical max of
`param + offset` terms, then intern it.

- Status: **open**
- Note: profile first. This may already be cheap enough to ignore.
- Result:

**H12. Huge pages cut the wall time on a multi-GB working set.**

The resident set runs from 2.6 GB to 3.7 GB on cedar, and reaches much more on
mathlib. A 2 MiB page covers 512 times the memory of a 4 KiB page. Reports give
0 to 15 percent. lazylean maps its memory once, 2 MiB aligned and pre-faulted.

- Status: **open**
- Priority: last. Huge pages do not lower the instruction count, so they do not
  move the arena score. They do help a local run.
- Result:

## Suggested order

1. H2, because the test is done and the fix is small.
2. H4, because it cuts instructions and needs no change to the checker.
3. H1, because the arena flags may cost the score for no gain.
4. H6, because it is the largest algorithmic lever.
5. H8 and H9, because both remove repeated work.
6. H7, after H6 settles which caches stay hot.
7. H5, H10, H11, then H12.

## Sources

- <https://arena.lean-lang.org/>
- <https://github.com/leanprover/lean-kernel-arena/pull/217>
- <https://github.com/leanprover/lean-kernel-arena/pull/257>
- <https://github.com/corun1024/lazylean>
- <https://github.com/replikativ/ansatz/pull/104>
- <https://kobzol.github.io/rust/cargo/2023/07/28/rust-cargo-pgo.html>
- <https://lean-lang.org/doc/reference/latest/releases/v4.29.0/>
- <https://ammkrn.github.io/type_checking_in_lean4/type_checking/definitional_equality.html>
- <https://arxiv.org/pdf/1701.04391>
- <https://link.springer.com/article/10.1007/s10990-007-9014-0>
- <https://www.abhik.ai/concepts/systems/transparent-huge-pages>
