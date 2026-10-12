# Performance plan

A list of performance hypotheses for this checker. Each one states a claim, a
test, and a result. Update the result after you run the test.

## Principles

The arena measures a weak proxy, so put these first.

1. **Consistency first.** The checker must never accept a false proof. A change
   that turns a rejection into an internal error is worse than a slow checker.
   H6 did exactly that. Run the full arena suite, which holds the `bad` tests,
   after every change.
2. **Completeness second.** A cache that drops at a fixed size can turn a term
   with heavy sharing into an exponential blow-up. Joachim Breitner raised this
   about the session budget, and con-ron hit it for real on
   `perf/magma-list-deep-n36`. Test the `perf/magma-*` family, not only the big
   corpora.
3. **Do not chase the sorted order.** The arena author states that the arena is
   not a competition, and that the instruction count rewards neither parallelism
   nor robustness. If a change only makes sense because of the metric, and looks
   odd on its own, drop it.
4. **A thread-count change is a collective question.** The arena author names it
   as the one tweak that should be discussed on Zulip rather than applied alone.
   See H1.

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

**Use 11 repetitions or more.** This machine drifts. At 5 repetitions the same
binary and the same corpus gave medians of 7.250 s and 6.417 s on two runs, a
spread of 13 percent. That spread is larger than every effect in this file. A
5-repetition run produced a false positive that 15 repetitions then killed. See
H2.

## How to profile

`devbox.json` holds samply, but samply is only on the path inside a devbox
shell. From outside, call it by its store path.

```
samply record --save-only -o prof.json.gz -- \
  ./target/release/sokonanodazo --nat-extension --string-extension \
  --axiom-allow-all -q --threads 1 <corpus>.ndjson
```

The committed release profile carries no debug info, so a profile from it shows
raw addresses and nothing else. Build a separate symbol-bearing binary into its
own target directory. Debug info does not change the generated code, so the
timings stay valid.

```
CARGO_PROFILE_RELEASE_DEBUG=1 CARGO_PROFILE_RELEASE_STRIP=false \
  CARGO_TARGET_DIR=/tmp/dbg cargo build --release
```

A fresh target directory rebuilds every dependency under fat LTO, which takes
more than 10 minutes. Keep the directory between runs.

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
- Action: **do not change the flag alone.** `tools/arena.py` passes
  `--threads 4`, which matches `checkers/sokonanoda.yaml`. The arena author
  names the thread count as the one tweak that every checker shares, and asks
  that it be settled on Zulip rather than by each author. Measure the effect,
  publish the number, and let the arena decide. See principle 4.
- Note: parallelism is practically useful and the metric does not reward it. A
  drop to one thread would raise the sorted order and make the checker worse to
  use. That is the clearest case of the trade the arena author warns about.

## Build and tuning hypotheses

**H2. The session budget must scale with the thread count.**

`SESSION_BUDGET` in `src/checker/tc.rs` is a per-thread share of one shared
cache. The committed value of 2 MiB comes from 4-thread wall times. At one
thread the threads do not compete, so a larger budget keeps more cache hits.

Test: read the budget from an environment variable, build once, then sweep.

First attempt, 5 repetitions. This looked like a win at one thread.

| corpus | threads | 2 MiB | 16 MiB | reading |
|---|---|---|---|---|
| std | 1 | 7.250 s | 6.688 s | 16 MiB wins by 7.8 percent |
| cedar | 1 | 10.080 s | 9.883 s | 16 MiB wins by 2.0 percent |

Second attempt, 15 repetitions on std at one thread. The win vanished.

| budget | median | best |
|---|---|---|
| 2 MiB | 6.390 s | 6.255 s |
| 16 MiB | 6.388 s | 6.081 s |

A full sweep at four threads, 11 repetitions, on the small corpora.

| corpus | 2 MiB | 8 MiB | 16 MiB |
|---|---|---|---|
| std | 2.092 s | 2.148 s | 2.154 s |
| cedar | 3.385 s | 3.379 s | 3.416 s |

The small corpora hide the effect. The large corpora show it, 5 repetitions at
four threads, where the medians and the best times agree.

| corpus | 2 MiB median | 16 MiB median | 2 MiB best | 16 MiB best |
|---|---|---|---|---|
| cslib | 8.251 s | 9.102 s | 8.156 s | 9.016 s |
| mathlib | 24.114 s | 29.069 s | 22.972 s | 25.198 s |

- Status: **rejected as stated, and the committed constant is right.**
  2026-10-10. The budget does not scale with the thread count. It scales with
  the size of the corpus. At 2 MiB the gain is 10 percent on cslib and 20
  percent on mathlib, and nothing on std and cedar at any thread count.
- Action: none. The change is reverted. Keep `SESSION_BUDGET` at 2 MiB.
- This confirms the README and the figure that circulates on Zulip. The first
  5-repetition run that suggested a thread-count rule was noise.
- Lesson: this run set the 11-repetition rule in the rig section above, and it
  showed that a hypothesis about the large corpora must be tested on the large
  corpora.
- Open: see H13 for whether 2 MiB costs robustness on a hard declaration.

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

Test with plain cargo. `cargo-pgo` is not needed. Train on `init` and `std`.
Benchmark on `cedar`, `cslib`, and `mathlib`, which the training run never saw.

```
SP=/tmp/pgo
RUSTFLAGS="-Cprofile-generate=$SP/data" CARGO_TARGET_DIR=$SP/gen cargo build --release
for c in init std; do
  $SP/gen/release/sokonanodazo --stdin --nat-extension --string-extension \
    --axiom-allow-all -q --threads 4 < ~/.cache/lean-kernel-arena/arena/_build/tests/$c.ndjson
done
llvm-profdata merge -o $SP/merged.profdata $SP/data/*.profraw
RUSTFLAGS="-Cprofile-use=$SP/merged.profdata" CARGO_TARGET_DIR=$SP/use cargo build --release
```

The `llvm-profdata` must match the LLVM that rustc uses. The one in a rustup
toolchain under `lib/rustlib/<target>/bin` works. Xcode also ships one.

Four threads, 11 repetitions for the first three corpora and 5 for the rest.

| corpus | baseline median | PGO median | outcome |
|---|---|---|---|
| init | 1.211 s | 1.195 s | 1.3 percent faster |
| std | 2.086 s | 2.058 s | 1.3 percent faster |
| cedar | 3.338 s | 3.269 s | 2.1 percent faster |
| cslib | 8.177 s | 8.038 s | 1.7 percent faster |
| mathlib | 23.332 s | 23.284 s | 0.2 percent faster, and 2.7 percent on best |

- Status: **confirmed, but small**. 2026-10-10. The win is 1.3 to 2.1 percent on
  four of the five corpora. It holds on `cedar` and `cslib`, which the training
  run never saw, so the profile generalizes. mathlib is memory bound, so its
  median hides the gain that its best time shows.
- Correctness: the PGO build passes the full arena suite, 223 of 223.
- One thread: inconclusive. On cedar the median says 7.4 percent slower and the
  best says 1.0 percent faster, so the 10-second runs drift too much. Repeat
  this part on a quiet Linux host with `perf stat`.
- Action: ship it, because it needs no change to the checker. The arena builds
  from a recipe, so the profile must live in the repo and the build must apply
  it. The profile data is 4.1 MB after the merge.
- Open follow-up: train on `cslib` as well, and test BOLT on top.

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

- Status: **rejected**. 2026-10-10. It is unsound in the plain form, and it buys
  almost nothing in the sound form.

### H6, what the instruments showed

Counters on cedar at one thread, before any change:

| Event | Count |
|---|---|
| `unify` calls | 21 182 517 |
| resolved by pointer equality | 9 902 570, which is 47 percent |
| cacheable pairs | 13 303 281 |
| positive cache hit | 3 497 979 |
| negative cache hit | 48 134 |
| positive cache insert | 9 526 173 |
| `unify_no_cache` calls | 12 215 921, which is 58 percent |

The pair cache is not the bottleneck. Real reduction work is. Pointer equality
already settles 47 percent of the calls, because the values are hash-consed.

### H6, the soundness failure

The plain union-find turned the arena test `bugs/rec-missing-ih` from a correct
rejection, exit 1, into an internal error, exit 3. It panicked at
`src/checker/inductive/positivity.rs:44` on an `Option::unwrap`.

The cause: definitional equality is transitive only on **well-typed** terms.
That test holds a deliberately malformed recursor, so the kernel asks def-eq
questions about ill-typed terms. A pair cache answers each question with a fact
it proved. A union-find answers with a fact it **derived**, and on an ill-typed
term that derivation is invalid. The invented equality let the positivity check
pass a gate it should have failed, and `which_valid_ind_app_v` then returned
`None` where an earlier `ensure!` had accepted.

The fix: union only a pair of closed values. `Value::is_closed` reads a bit of
the digest, so the guard is free. With the guard the test rejects again.

Two notes on the diagnosis, to save the next reader the same work.

- An earlier draft of this file blamed composition across bvar depths. That is
  wrong. `RigidHead::BVar` carries an **absolute** level and is hash-consed by
  the pair of level and type, so a value does not change meaning with the
  `depth` argument, and a conversion judgment with a free variable is parametric
  in that variable. Composing two such facts is sound.
- The closed-value guard rules out both candidate mechanisms at once, so the
  experiment did not isolate which one fired. The well-typedness reading is the
  one that the code supports.

The general rule: a cache that **stores** a proven fact is safe on malformed
input. A cache that **derives** a new fact is not, because the kernel must stay
well behaved on terms that are not well typed.

Neither this fork nor the parent composes a positive conversion fact.
`conv_cache_pos` has exactly two uses, one `contains` and one `insert`.

### H6, the sound form does not pay

Counters on cedar with the guard in place:

| Event | Count |
|---|---|
| union-find joins | 2 667 398 |
| extra hits that the pair cache missed | 51 439 |

51 439 extra hits against 13.3 million cacheable lookups is 0.39 percent, and
it costs 2.7 million joins plus one hash lookup on every cacheable miss. The
run time did not improve.

The reason is the hash-consing. Two convertible closed values that the checker
meets twice already share one pointer, so the classes stay tiny and there is
almost no transitivity to exploit. The second half of the idea, which
canonicalizes a spine argument to its class representative, has nothing to
collapse for the same reason.

- Action: reverted. The ansatz figure of 9.6 million calls down to eleven
  thousand came from a checker with no hash-consing, so it does not carry over.
- Lesson: measure the cache hit rate before you replace a cache. And run the
  `bad` tests, because this failure was invisible on every corpus.

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
- The blocker is not a lifetime. `ExprCache::clear_session` clears only the
  memo maps `inst`, `subst`, `dsubst`, and `simplify`. The interner itself is
  `TcCtx::dag`, which `Dag::new_local` builds once per thread and which lives as
  long as the thread. So a quoted `ExprPtr` stays valid across sessions. That is
  why `whnf_store` can carry the `keep` marker.
- The real blocker is that each thread interns into its **own** `Dag`, so an
  `ExprPtr` from one thread means nothing to another.
- Design: make the shared table map the `u64` digest to a compact serialized
  expression, not to an `ExprPtr`. A reading thread interns the blob into its
  own `Dag`. Interning a small blob costs far less than a repeated whnf. Shard
  the table by the low bits of the digest to keep the locks short.
- Measure first: H1 says 8 threads cost 33 percent more CPU than one thread.
  That 33 percent is the ceiling for this idea, and only a part of it is whnf.
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

## The profile

cedar, one thread, samply, 10 370 samples on the checker thread. Ignore the
main thread, which spends its whole life blocked in a join.

Self time, the top of the list:

| Share | Function |
|---|---|
| 16.97 % | `eval::eval_no_cache` |
| 14.92 % | `eval::eval` |
| 14.24 % | `infer::infer_nonvar` |
| 8.45 % | `eval::environment::prune_env_cold` |
| 8.33 % | `eval::environment::intern_frame` |
| 4.98 % | `eval::apply_many` |
| 4.06 % | `eval::neutral_app` |
| 2.63 % | `ptrmap::PtrMap::grow` |
| 2.13 % | `eval::environment::env_new` |
| 1.92 % | `value::Spine::to_vec` |
| 1.63 % | `conv::unify_general` |

Total time, which shows who drives the work:

| Share | Function |
|---|---|
| 95.37 % | `infer::infer_nonvar` |
| 63.34 % | `eval::eval` |
| 59.75 % | `conv::unify_general` |
| 42.72 % | `conv::unify_spine` |
| 38.28 % | `eval::reduction::unfold_value_go` |
| 25.29 % | `eval::reduction::iota_value` |
| 23.46 % | `eval::reduction::do_recursor_iota` |
| 23.11 % | `eval::reduction::do_proj` |

Three readings:

1. Type inference drives almost everything, at 95 percent of total time.
   Conversion is 60 percent and evaluation is 63 percent, nested inside it.
2. Conversion is cheap in **self** time, at 1.63 percent plus 0.67 percent for
   `unify_direct`. It is expensive only through what it calls. This is the same
   message the H6 counters gave. Do not optimize the conversion cache.
3. About 22 percent of self time goes to building and interning environments and
   hash-consing values: `prune_env_cold`, `intern_frame`, `env_new`, and the
   `mk_*_hc` family. That is the machinery around reduction, not reduction.

**H15. The prune cache is too small, so `prune_env_cold` runs too often.**

`prune_env_cold` is marked `#[inline(never)]` and named cold, yet it is the
fourth hottest function. The direct-mapped `prune_dm` table holds 1024 entries.

Four threads, 11 repetitions, medians.

| corpus | 2^10 | 2^12 | 2^13 | 2^14 |
|---|---|---|---|---|
| std | 2.223 s | 2.223 s | 2.232 s | 2.270 s |
| cedar | 3.476 s | 3.482 s | 3.495 s | 3.561 s |

- Status: **rejected**. 2026-10-10. The committed 2^10 is already the best size,
  and 2^14 costs 2 percent. The cold path runs because the pruning work is
  genuinely needed, not because the table misses.

**H16. `PtrMap::reset_shrink` makes a table pay for the same growth twice.**

`PtrMap::grow` holds 2.63 percent of self time. `reset_shrink` sizes a table
from the last session, so a table that grows, shrinks, and grows again pays
twice. This is the pattern the con-ron report names: a sizing rule for clearing
that disagrees with the growth rule turns clear into grow.

Test: make `reset_shrink` never shrink, so a table keeps its grown size.

| corpus | shrink, committed | never shrink |
|---|---|---|
| std | 2.153 s | 2.203 s, 2.3 percent slower |
| cedar | 3.468 s | 3.914 s, 12.9 percent slower |

- Status: **rejected**. 2026-10-10. The shrink is load bearing. A table that
  keeps its peak size loses more to cache misses, and to the larger memset on
  reset, than it saves on growth. The 2.63 percent in `grow` is the price of
  locality, and paying it is correct.
- This is the same result as H2 from the other direction. Both say that this
  checker wins by keeping its hot tables small.

**H13. The 2 MiB session budget costs robustness on a hard declaration.**

H2 shows that 2 MiB wins 10 to 20 percent on the large corpora. Joachim
Breitner warns that a cache which drops at a fixed size can make a term with
heavy sharing explode. con-ron hit this for real: a memo table that dropped at
a fixed entry count made `perf/magma-list-deep-n36` cost 128 percent of
con-leche instead of the usual 45 percent.

This checker drops its session caches only between declarations, never inside
one, so a single hard declaration keeps its caches whatever the budget is. The
risk is therefore the loss of sharing **across** declarations, not inside one.

Test the `perf/magma-*` family at several budgets and compare the instruction
counts.

- Status: **open, and not decided by the attempt below.**
- A first single run suggested a large cliff on `magma-list-pair-n21`, 26.5 s at
  2 MiB against 15.8 s at 16 MiB. Three repetitions reversed the sign: 15.9 s at
  2 MiB against 26.7 s at 16 MiB. The medians and the best times disagree in
  both directions, so the test is dominated by one heavy declaration and this
  machine cannot resolve it. A 5-run attempt at measuring the CPU time timed out
  after 10 minutes.
- Action: run this on a quiet Linux host with `perf stat`, which counts
  instructions and does not care about machine load. Do that before anyone
  defends or changes the 2 MiB constant on robustness grounds.
- Result:

## Suggested order

1. ~~H2~~ done. The committed 2 MiB constant is correct and worth 10 to 20
   percent on the large corpora. The thread-count rule is rejected.
2. ~~H4~~ done, confirmed at 1.3 to 2.1 percent. Wire the profile into the build.
3. ~~H6~~ done, rejected. Unsound in the plain form, worth 0.39 percent in the
   sound form.
4. ~~H15~~ done, rejected. The prune table is already the right size.
5. ~~H16~~ done, rejected. The table shrink is load bearing.
6. H13, because robustness outranks speed and the question is open.
7. **H7**, promoted. Every measurement in this file says the same thing: this
   checker wins by keeping its hot data small. H2, H15, and H16 all punished a
   larger table. Pointer compression is the only idea here that makes the hot
   data **smaller** without giving up a single cache entry, so it works with the
   grain of the design instead of against it. A 32-bit arena offset halves every
   `PtrMap` key, and `Value` is 56 bytes and `Env` is 64 bytes today.
8. H8 and H9, because the profile says real reduction work, not cache lookup,
   is where the time goes. Both remove repeated work.
9. H10, for the same reason, and because `do_proj` and `do_recursor_iota` hold
   23 percent of total time each.
10. H1, but raise it on Zulip first. See principle 4.
11. H5, H11, then H12.

### What six results taught

Five of the seven hypotheses tested are rejected, and the rejections agree.

- **Do not cache more.** H2, H15, and H16 each tried to keep more, and each lost
  2 to 13 percent. The small session budget, the 1024-entry prune table, and the
  shrinking `PtrMap` are all correct as committed.
- **Do not optimize the conversion cache.** H6 counters and the profile both say
  conversion costs 1.63 percent of self time. It is expensive only through what
  it calls.
- **The remaining room is less work or smaller data.** Less work is H8, H9, and
  H10. Smaller data is H7. Nothing else on this list has survived contact with a
  measurement.
- **Measure with 11 repetitions and on the corpus the claim is about.** H2 gave
  a false positive at 5 repetitions, and a false negative until it was tested on
  cslib and mathlib rather than std and cedar.

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

## The Bend kernel in bend/

A separate rig from the Rust checker above. The binary is built, not
interpreted, and every number is a median of three with `--threads 8`.

```
bend bend/check.bend -o /tmp/a            # the base
# apply the change
bend bend/check.bend -o /tmp/b
# time the two in one run, never across runs
```

| hypothesis | status | result |
|---|---|---|
| B1 the GPU helps | rejected | a P-core is ~75x a lane on serial work, a shared `+` value costs an atomic per read, and Bend's own pins lose on `queens` and `lexer`, the two benches that search |
| B2 a parallel call in the application arm helps | rejected | 0.99x. The two sides are unbalanced, the tasks are tiny, and the slow files hold two to ten declarations |
| B3 the file is checked more than once | confirmed | `report` and `check_all` each walk and check; `why` ran through an argument of `mark`. One walk: 1.48x |
| B4 a guard read through a pick is not a guard | confirmed | four places. `Term.subst`, `Conv.irrel`, `Conv.k_fix` and the `Ans.and` over `eq_all`. Together 5.3x on top of B3 |
| B5 raising the fuel is now safe for the stack | confirmed | `Conv.eq_all` is a tail call, so 30000 runs a 598 kB export. Time is the cap now, not the stack. Not changed; measure before you do |
| B6 the remaining timeouts are a reduction problem | open | `perf/app-lam` and the two `perf/proj-*-struct` |

B1 and B2 are the two the landing page suggests first. Both lose here, and
both are cheap to measure, so measure them before you write them.

B4 is the one worth remembering. Bend evaluates an argument before the match
picks an arm, so a helper that chooses between two values on a computed `Bool`
evaluates both. A guard only guards when something **matches** on it.

### More for the Bend kernel

| hypothesis | status | result |
|---|---|---|
| B7 a pair of identical terms need not be reduced | confirmed | most pairs are a term against itself. 2.7x to 5x per file on five of the bench files |
| B8 a spine may be compared before it is unfolded | confirmed, with care | `proj-stuck-struct` and `proj-cheap-struct` from over 400 s to 0.0 s |
| B9 a stack of routes set aside is affordable | rejected | it is a search. `refute-cheap-last` finds its refutation cheaply and then pays for every route behind it; 30000 fuel does not help. One slot, filled by the outermost offer, bounds a failure to one retry |
| B10 a depth cap on the offers serves both tests | rejected | at one, `refute-cheap-last` rejects and the struct tests time out; at three the reverse; at two neither. The one-slot design in B9 serves both |
| B11 raising the fuel buys answers | open | 11 good files still decline on budget. Measure the time cost first |

B9 is the one to remember. The cheap route is sufficient and not necessary, so
it needs a fallback, and the fallback has to be **one** route and the
outermost one. Keeping every offer turns a conversion check into a search with
no bound but the fuel.

### The Bend kernel, after the recursor

| hypothesis | status | result |
|---|---|---|
| B12 a bigger budget buys answers | confirmed | 3000 gave 179 correct and 11 declines; 30000 gives 186 and none. 100000 buys nothing more and runs one file out of memory |
| B13 a closed value can be shared rather than copied | **rejected** | `Term.lift_by` handing back a closed value instead of lifting it made `perf/shared-subterm` go from an answer in 0.1 s to a timeout at the same budget. A term DAG is not free in Bend |
| B14 the syntactic test should stop at the first difference | confirmed | `Term.same` read its halves through `Bool.and`, so it walked both terms in full whatever they were. As a worklist: 1.55x on the bench set, church-numerals 6x |
| B15 the nine timeouts are within reach of a constant factor | **rejected** | `perf/shared-subterm` answers at a budget of 3000 and needs more than seventy seconds at 30000, so it wants about a hundred times, not one and a half. They need sharing, which B13 says Bend charges for |

B13 is the second time sharing has lost here. The first was the expression
table, where one shared node took a 6 kB export from one second to two
hundred. Bend is affine: a value read in two owned positions is copied, and
the copy is lazy and repeated, so an explicit copy at a known place beats a
shared one in an unknown place. Do not try a third time without reading those
two results first.

| hypothesis | status | result |
|---|---|---|
| B16 checking declarations in parallel helps the big files | **rejected** | a divide and conquer over the declaration list with a parallel let moved none of `magma-list-deep-n21`, `magma-list-pair-n7` or `fueled-chain`, each of which has 143 to 514 declarations, and it gives up the short circuit on a rejection. Not kept |
| B17 `init-prelude` is a constant factor away | **rejected** | it does not finish in nine hundred seconds, so it is at least fifteen times away and probably more. 1824 declarations, each of them real work |
| B18 `perf/grind-ring-5` can be read at all | **rejected** | 10.2 MB, no verdict in three hundred seconds |

So the nine files that time out are not a tuning problem. Five of them are
small files built to punish a kernel with no sharing, and `init-prelude` is
large and wants throughput this representation does not have. B13 says what
the missing piece is and why Bend charges for it.

### How to look for what a limit is hiding

Five of this kernel's bugs were latent wrong answers behind something that
stopped the run early. Four were found by accident, after a change made the
kernel faster. The fifth was found on purpose, and the method is worth
writing down.

**Run the corpus at a small budget.** A declaration that gives up early costs
little, so the walk reaches far more declarations than it does at a large
budget. `init-prelude` at a fuel of 300 answers in two seconds where at 30000
it runs past sixty, and that run is what found `2 ^ 64` crashing the runtime.

It is also the broadest correctness check available: at a small budget every
declaration either passes or declines, so **any rejection is a bug**. Use it
after any change to the rules, and not only the arena's 195 files.

### Honesty has a price, and here it is measured

| hypothesis | status | result |
|---|---|---|
| B19 a stuck application is no evidence of a difference | **rejected** | `Conv.structural` answering unknown instead of no when either side is an application or projection not headed by a constructor costs eight files: seven rejections become declines (`k-rec-conv`, `nat-rec-k-lie`, `rec-missing-ih`, `100_ruleKbad`, `101_ruleKAcc`, `116_funEtaBad`, `125_accRecNoEta`) and `perf/church-numerals` stops being accepted. 186 correct -> 178 |

B19 is worth understanding rather than just dropping. Lean's kernel has no
third answer and says false when conversion fails, and it is right to, because
its reduction is complete. This kernel's no on a stuck mismatch is a bet that
its own reduction is complete enough. The corpus says the bet pays eight times
over, and `grind-ring-5` says it does not always pay.

So the fix for a stuck mismatch is to make reduction more complete, not to
weaken the verdict. That needs a blame tool for conversion, not for inference:
`bend/blame.bend` walks into a term whose **inference** is a definite no, and
nothing yet walks into a pair whose **conversion** is one.

### Where the nine timeouts spend their time, measured

`bend/count.bend` reads a file into terms and counts the nodes, which is what
separates a reader that is slow from a checker that is slow.

| file | read into terms | nodes built |
|---|---|---|
| `perf/shared-subterm` | 0.03 s | 6,292 |
| `perf/proj-stuck-struct` | 0.04 s | 1,854 |
| `perf/beta-ladder` | 0.16 s | 16,644 |
| `perf/magma-list-pair-n7` | 0.28 s | 46,830 |
| `perf/magma-list-deep-n36` | 0.62 s | 899,202 |
| `perf/fueled-chain` | 9.2 s | **206,437,819** |
| `perf/app-lam` | **more than 123 s** | — |

So two of the nine never reach the checker at all. `fueled-chain` builds 206
million nodes from an 869 kB file, and `app-lam` cannot be read: its largest
expression expands to a tree whose node count has nine hundred digits.

The cause is one line of the design. The export's expression table is a
**graph**, one expression named by many others, and this kernel reads it as a
**tree**, because Bend is affine and a value read twice is copied.

### What the export's graph looks like

| file | closed, no level parameter | closed, with one | open |
|---|---|---|---|
| `perf/app-lam` | 0.1% | 0.5% | **99.4%** |
| `perf/fueled-chain` | 0.6% | 5.1% | **94.3%** |
| `good/init-prelude` | 1.8% | 13.3% | **84.8%** |
| `perf/shared-subterm` | **88.0%** | 3.5% | 8.5% |

That table decides the design. A reference to a **closed, level-free**
expression is sound with no bookkeeping at all: a closed term is the same term
in every scope, so `Term.subst` and `Term.lift` leave it alone, and a
level-free term needs none of the per-declaration level remapping. A reference
to an **open** one needs a shift, and to a **level-carrying** one needs a
level substitution: an explicit-substitution calculus.

### B20: a reference for the closed, level-free case

| hypothesis | status | result |
|---|---|---|
| B20 a reference to a closed, level-free expression pays | **rejected as built** | the node counts fall by factors of 27,000, and the score falls by one |

What it bought, with a size threshold of 64 nodes:

| file | nodes before | nodes after |
|---|---|---|
| `perf/shared-subterm` | 6,292 | 4,282 |
| `perf/fueled-chain` | 206,437,819 | **9,775** |

What it cost: `perf/church-numerals` stops being accepted, so 186 becomes 185.
Three things were learned on the way, each measured.

**A reference may not stand where an analysis pass looks.** Every such pass
reads one as a leaf, so positivity does not see the inductive inside it, the
projection rules do not see a field, and the rule that a safe declaration may
not use an unsafe one does not see the constant. With references in types, 65
files answered wrongly.

**Resolving must not cost a reduction step.** Charging the declaration's
budget for it took `church-numerals` from accepted to out of budget on its
own. `Eval.deref` resolves in the caller instead, so the arm in `Eval.whnf`
fires once per term handed in from outside rather than once per use.

**The remaining cost is the mismatch.** A type is expanded and a value is
not, so `T.Term.same` never matches the inferred type of a value against the
declared type, and conversion loses its fast path. That is what
`church-numerals` pays. The threshold cannot fix it: at 64 the file declines,
and at 900 the parse cost comes back, because computing an entry's size by
walking an inlined child costs the threshold.

So the next step is the consistent version: references in types as well, which
needs `Term.occurs`, `Term.pars_ok`, `Term.has_bvar`, `Term.pi_count` and
`Term.pi_skip` to resolve, which needs the expression table visible from
`Term.bend`. The work is saved as a patch rather than committed, because the
half-built version is a point worse than none.


### B24: the memo does not hit, so a stored hash would not earn its refactor

| hypothesis | status | result |
|---|---|---|
| B24 the memo failed on the cost of its key, so a hash stored in every node, which makes the key free, would make it pay | **rejected** | the memo does not hit at all: given a free key it fills 64.8 GB and the process dies |

B22 left one reading open. The memo was built, it was correct, and what it
cost was the key: hashing a term and comparing two of them are both the size
of the term. A hash **stored in each node** removes that, because a node's
hash is its children's hashes mixed, which is O(1) at construction, and the
comparison on a hash match stays exact so a wrong hash can only lose a hit
and never a verdict. That is 442 sites, and it was worth measuring before
spending them.

The measurement was a probe: the deep hash, no cap on the key, and the
bucket's first entry accepted without comparison, which is what a stored hash
with an O(1) comparison would cost. On `perf/shared-subterm`:

```
185.28 real   64826261504 maximum resident set size   exit 1
```

Sixty-five gigabytes and dead. So the memo was never short of a cheaper key.
It **does not hit**: nearly every term it stores is distinct, because each of
the two repeated computations carries its own accumulated substitution, and
two terms that mean the same thing are not the same syntax. A memo keyed on
syntax cannot see that they are one computation.

### What that leaves

The sharing these files need is not sharing of answers; it is sharing of the
**work**, and that needs the shared subterm to stay one object through
substitution. That is what a closure is: a term paired with an environment,
where instantiating a binder pushes a value onto the environment rather than
copying it into the body. Then `rec t` and `rec t` are literally one object
and reduce once.

Bend is affine, so a term used twice is copied, and that is the whole
difficulty: a closure machine here means a graph reducer with a heap of its
own -- an arena of nodes, indices instead of pointers, and an explicit stack
-- written inside Bend, with the expression table as its first layer. That is
a different program from this one, not a change to it.

### B23: a lower fuel does not convert a file that runs out of time

| hypothesis | status | result |
|---|---|---|
| B23 the fuel table was measured before the reference work and structure eta, so a lower fuel may now answer where a higher one runs out of time | **rejected** | at every fuel below 30000 the nine answer `declined`, which the arena scores exactly as a timeout |

| file | fuel 300 | 1000 | 3000 | 10000 |
|---|---|---|---|---|
| `good/init-prelude` | 2 s declined | over 50 s | over 50 s | over 50 s |
| `perf/shared-subterm` | declined | declined | declined | declined |
| `perf/beta-ladder` | declined | declined | declined | over 50 s |
| `perf/magma-list-pair-n7` | declined | declined | declined | over 60 s |

`good/init-prelude` answers in two seconds at a fuel of 300, which is what
made this worth testing, and the answer is `declined`: most of its 1,824
declarations need little and a few burn whatever budget they are given, and
one unknown makes the file unknown. So 30000 stands, and the only way these
nine become correct answers is to make the work smaller rather than the
budget different.

### B22: a memo for reduction, and the identity Bend does not have

| hypothesis | status | result |
|---|---|---|
| B22 a cache from a term to its weak head normal form pays for the seven cache-punishing files | **rejected** | the key costs what the reduction costs, at every size |

Seven of the nine are the same ask. `perf/shared-subterm` states

```
ldepth (perfect n leaf) = ldepth2 (perfect n leaf)
```

by `refl`, with `n` a tower of 1,100 `succ`, so the tree has 2^1100 nodes.
The recursor's own rule builds `succ (max (rec t) (rec t))`: the field `t` is
shared, and the two `rec t` are **two computations** on it. No representation
of terms makes them one, and reducing the argument first does not either,
because what is duplicated is the computation and not the value. Four more of
the nine are the arena's `magma-*` family, which exists to punish a cache
that drops entries.

The threading is not the obstacle, and it is worth writing down how it works.
`Eval.whnf` can hand back a `Data` record of the term and the memo — a Bend
pair is a `Type` and may be used once, a `Data` record may be used twice —
and every self-call of `whnf` is in tail position, so the loop never has to
take its own result apart. Only `match` is restricted to a parameter or a
field, so a function may take the record apart at the few nested reductions.
`Conv.eq_all` is already an accumulator loop and carries the memo in it.
That was built, and all 17 regression tests passed on it.

The obstacle is the **key**. Lean keys its cache on a pointer: free to hash,
free to compare. Bend exposes no pointer, so the key is the content, and the
content costs what the reduction costs.

| key cap | result |
|---|---|
| 24 nodes | `perf/church-numerals` 0.2 s, and no hit on any of the nine |
| 200 nodes | a 292-byte export does not finish in **four hundred** seconds |
| no cap | `perf/church-numerals` goes from 0.1 s to more than sixty |

The 200-node row was re-measured after the cold-start rule below, with the
first run of the binary allowed to finish: it is the real cost and not the
artefact. What that row says is that one lookup of a 200-node key, at every
reduction step, is already more expensive than every step the file needs.

A small cap never hits, because the terms whose reduction repeats are built
by substitution and a term built by substitution is large. A large cap hits
and pays the whole cost of the reduction at every lookup, because deep
self-similar terms collide in any bounded hash and the comparison then walks
the whole of one.

So the memo needs hash consing, and hash consing needs an identity for a term
that this language does not give. The work is on the branch `memo` and is not
merged. The honest next step is not a better hash: it is either an identity
for terms, which means interning every term reduction builds and threading
the intern table through substitution, or it is accepting that these seven
files stay out of reach.

### The rig: do not use `--threads 8` on this machine

A whole stretch of measurements was poisoned by it. The same binary answers a
292-byte export in 11 ms with `--threads 1`, `--threads 4` or no flag, and
**hangs** with `--threads 8`, because this machine runs at a load average near
seven and Bend's scheduler is contention-free: every task is handed to a core
exactly once and never moved. Eight threads that cannot all run therefore
stall rather than share.

The symptom is confusing: a fresh build appears broken while an older binary
of the same source is fast, and a 292-byte file takes two hundred seconds. It
led to reverting work that was sound. The rig uses `--threads 4` now, and the
perf plan's own rule about a thread count being a collective question stands.


### B21: a reference for the open case, which is almost all of it

The four-class table above was measured by a tool that read a reference as a
leaf, and it put the weight in the wrong column. Measured again from the
export itself, with the free variables of each entry computed bottom up:

| file | entries | open | names a universe |
|---|---|---|---|
| `perf/shared-subterm` | 1,175 | 8% | 1% |
| `perf/beta-ladder` | 10,284 | **99%** | 0% |
| `perf/fueled-chain` | 16,168 | **94%** | 4% |
| `perf/app-lam` | 24,430 | **99%** | 0% |

So the level substitution is not the work. A level parameter appears in 0 to
4 percent of the entries, and the open expression is 94 to 99 percent of
them. The distribution of the free-variable count settles the design too:
almost every open entry uses one, two or three distinct variables.

**What the parse stored, before.** A tool that sums the nodes of every entry
of the table, rather than of the declarations:

| file | stored nodes | largest entry |
|---|---|---|
| `perf/shared-subterm` | 5,893 | 65 |
| `perf/beta-ladder` | 56,009,873 | 15,999 |
| `perf/fueled-chain` | **6,646,462,095** | 183,695,885 |

A reference stood only for a closed entry, so a large **open** entry was
copied into every parent, and the copies compounded. That is the 869 kB file
storing six billion nodes.

**Two designs were simulated before either was built.** The simulation
replays the export's graph and sums what each rule would store.

| rule | `beta-ladder` | `fueled-chain` | `app-lam` |
|---|---|---|---|
| closed references only, size 64 | 56,009,881 | 6,681,072,761 | 119,141,552,556,382,848 |
| lambda lifting, any size | 12,029,924 | 155,990 | 96,050,881 |
| a shift in the reference, any size | **26,946** | **52,218** | **65,427** |

Lambda lifting fails. It closes an entry by abstracting its free variables,
which needs no new machinery at all, and the use site then costs one
application per variable: the entries with two thousand and four thousand
free variables make that worse than the copy.

A shift costs one word and wins everywhere, so that is what was built.

**`TRef{i, k, m}`.** `i` names the entry, `k` shifts its free variables into
the scope the reference stands in, and `m` bounds them, so the variables a
reference uses are the ones from `k` up to `k + m`. A lift or a substitution
compares its cutoff against that range and answers in one of three ways: no
variable of the reference moves, so leave it; every one moves, so change `k`
and leave the entry alone; or the cutoff falls inside the range, and only
then is the entry read and walked.

The parser writes a shift of zero, because an expression of the export's
table is named by expressions at its own binder depth, and a de Bruijn term
is the same term wherever it is named from. That is how Lean shares its own
expressions.

Three things make it sound. A reference still may not name an expression
that mentions a level parameter, because the remapping is per declaration
and the table is shared. A declaration's own type is still stored with its
references expanded, because every pass that reads a type as syntax reads a
reference as a leaf. And the walks that may meet a reference in a value --
`Term.lift_at`, `Term.subst_at`, `Term.inst_at` -- take the table, while the
walks that may not keep the old signature and resolve against an empty
table, so a reference that ever reached them would be answered "do not know"
rather than answered wrongly.

What it bought:

| file | stored before | stored after | read into terms |
|---|---|---|---|
| `perf/shared-subterm` | 5,893 | 5,893 | 0.0 s |
| `perf/beta-ladder` | 56,009,873 | **34,280** | 0.2 s |
| `perf/fueled-chain` | 6,646,462,095 | **222,028** | 0.4 s |
| `perf/app-lam` | could not be read | **70,326** | 0.7 s |

`perf/let-ladder` answers in 1.67 s where it took 3.83 s. The score is 186
with the same nine files out of time, so the parse is no longer the wall for
any of them: every one of the nine is now the checker's own work.

### The rig: throw away the first run of a new binary

A fresh binary answered `perf/shared-subterm` in 53 seconds and the same
binary answered it in 36 milliseconds on the next run. The first execution
of a newly written file on this machine pays a fixed cost of tens of
seconds, and two binaries compared in one pass therefore hand the first one
a result that means nothing.

That is what made the earlier conclusion -- that restoring the references in
binder types was slower -- wrong: a parse-only counter showed 53 s against
0.24 s between two builds whose node counts were identical to the digit, and
both answered in 36 ms once warm. Every measurement in this file from here
on runs each binary once on a small file first and reports the second run.

### The four classes, and the order they put the work in

| file | closed, level-free | closed, with level | open, level-free | open, with level |
|---|---|---|---|---|
| `perf/app-lam` | 0.1% | 0.5% | **98.5%** | 0.9% |
| `perf/fueled-chain` | 0.6% | 5.1% | 4.3% | **90.0%** |
| `good/init-prelude` | 1.8% | 13.3% | 9.5% | **75.3%** |
| `perf/shared-subterm` | **88.0%** | 3.5% | 4.0% | 4.5% |

A reference now covers the first column, which is why `shared-subterm` builds
4,282 nodes instead of 6,292 and why the other three gain almost nothing.

What is left, in the order the measurements put it in. The first three items
of the earlier list are done, and the fourth turned out to rest on a number
that the cold-start lesson above invalidates.

1. **The checker's own work.** All nine files that run out of time now spend
   it in the checker, not the parser. Eager substitution is why: a beta step
   pushes the substitution into the body and the result is a new term, so an
   expression that was shared once is expanded once per use. A machine that
   carries an environment instead of substituting -- a closure -- is what
   fixes `perf/beta-ladder` and `perf/app-lam`, and it is a rewrite of
   `Eval.whnf`, not a tweak of it.
2. **A cache for `whnf` and for conversion.** `good/init-prelude` holds 1,824
   declarations and each is real work; it does not finish in nine hundred
   seconds. Nothing here remembers a reduction, so the same subterm is
   reduced once per occurrence.
3. **A level substitution in the reference**, which the measurement above
   puts at 0 to 4 percent of the entries. It is no longer the next thing.
4. **One table, not three.** `ETable` could hold each entry's term beside
   its size and its free-variable bound. The bound now travels in the
   shareable table, so two tables remain, and the number that made this look
   urgent was a first-run measurement.
