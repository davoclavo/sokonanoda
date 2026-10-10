# Arena harness

`arena.py` runs the [Lean Kernel Arena](https://arena.lean-lang.org) test suite
against a local build of this checker. The arena feeds a Lean export file to the
checker on standard input and reads the exit code.

| Exit code | Meaning |
|---|---|
| 0 | accept |
| 1 | reject |
| 2 | declined, the checker does not support this input |
| other | an error in the checker |

A test states the outcome it wants: `accept`, `reject`, or `either`. A declined
result scores nothing, so the harness counts it as a failure.

## Use

```
devbox run build                  # the harness needs target/release/sokonanodazo
devbox run arena-fetch            # 196 small tests, about 3.6 MB
devbox run arena                  # run every export file present
```

`devbox run arena` prints one line for each failure and for each test slower
than one second, then a summary. It exits non-zero if any test is wrong or
declined.

Give a name fragment to run a subset.

```
devbox run arena tutorial
devbox run arena "mathlib init"
```

## The large corpora

The arena publishes 223 tests. Only 196 come in the tarball. The other 27 are
built from Lean sources: 18 corner cases, 2 perf tests, and 7 real-world
corpora. Build them with the arena tooling.

```
devbox run arena-build init
devbox run arena-build "init std cedar mathlib"
```

The first build downloads a Lean toolchain with elan and builds `lean4export`.
A corner case takes seconds. `init` and `std` take about 20 seconds each. The
large projects build their own dependencies first, so `mathlib` takes much
longer and its export file is 5.8 GB.

To build every test that is still missing:

```
devbox run arena            # lists what is missing
devbox run arena-build "<the names it listed>"
```

## Where things land

Nothing is written inside this repository. The cache holds the arena clone, the
small tests, the expected outcomes, and every export file the tooling builds.

```
~/.cache/lean-kernel-arena/
  results.json    expected outcomes, downloaded from the arena
  small/          the 196 tests from the tarball
  arena/          a clone of leanprover/lean-kernel-arena
  arena/_build/   the export files the tooling builds
```

Set `ARENA_CACHE` to move the cache. Set `SOKONANODAZO` to point at a different
binary, which is how you compare two builds.

```
SOKONANODAZO=/tmp/sokonanodazo-baseline devbox run arena
```
