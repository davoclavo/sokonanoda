# Check a real Lean export.
#
# Reads the file named by SOKO_EXPORT, builds its environment, checks every
# declaration against the ones before it, and prints a verdict.
#
#   SOKO_EXPORT=<path to a .ndjson export> bend bend/check.bend
#
# The verdict covers only what this kernel implements. An inductive block is
# read and its types are checked, but nothing derives the recursor from the
# specification, so such a file answers `declined` rather than `accept`.
# Quotients, projections and literals are still skipped entirely.

import Base
import ./Bytes.bend as B
import ./Parse.bend as P
import ./Env.bend as E
import ./Kernel.bend as K
import ./Ans.bend as A

# The fuel one declaration gets.
#
# The old reason for this number was the host stack: `Conv.eq_all` kept its
# recursive call inside an argument, so the depth of the queue was the depth
# of the stack and a fuel of 100000 overflowed it. The answer travels in as a
# parameter now, so that call is a tail call and the stack no longer sets the
# cap. A fuel of 30000 runs a 598 kB export to an answer.
#
# What sets it now is time, and this number is measured. Raising the fuel buys
# answers on the files that decline and costs time on the ones that already
# answer, and the arena scores a decline and a timeout the same, so the trade
# is worth taking as long as no answer turns wrong.
#
# | fuel | correct | declined | error | wrong |
# |---|---|---|---|---|
# | 3000 | 179 | 11 | 5 | 0 |
# | 10000 | 182 | 5 | 8 | 0 |
# | 30000 | **186** | 0 | 9 | 0 |
# | 100000 | 186 | 0 | 9 | 0 |
#
# Thirty thousand is where it stops paying. A hundred thousand buys nothing
# and `perf/shared-subterm` runs the machine out of memory at it, which is a
# worse answer than not knowing.
def Check.fuel() -> Nat:
  30000n

def Check.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

def Check.trusted_word(t: Bool) -> String:
  match t:
    case True{}:
      "declined (an inductive block was taken on trust)"
    case False{}:
      "accept"

# The verdict. A file whose inductive block had to be taken on trust gets
# `declined` rather than `accept`, because this kernel does not derive the
# recursor and so is not entitled to accept it. `reject` needs no trust: a
# declaration that fails a check this kernel does make is wrong whatever the
# recursor says.
def Check.show(a: A.Ans, trusted: Bool) -> String:
  match a:
    case A.ANo{}:
      "reject"
    case A.AUnk{}:
      "declined (the budget ran out before an answer)"
    case A.AYes{}:
      Check.trusted_word(trusted)

# Did the caller ask for the per-declaration report? `SOKO_REPORT` set to
# anything turns it on.
def Check.wants_report(r: Result<&1, &1, U32 & String, String>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{v}:
      True{}

# The report and the verdict, from one walk of the declarations.
def Check.lines(p: A.Ans & String, trusted: Bool) -> String:
  (a, rep) = p
  rep ++ "verdict " ++ Check.show(a, trusted)

# What to print.
#
# The report is off unless asked for, and that is a speed decision, not a
# cosmetic one. `Kernel.report` and `Kernel.check_all` each walk the list and
# check every declaration, and `Kernel.why` runs on every declaration through
# an argument of `Kernel.mark`, so a run that printed the report checked the
# file about five times over to answer once.
#
# This was committed once and lost: a `git checkout --` during a measurement
# took the uncommitted half of it away, the Kernel half went in without it,
# and every run since has paid for the report nobody asked for. `Kernel.run`
# is the one walk that answers and reports together, and `Kernel.report` is
# gone, so the two cannot drift apart again.
def Check.out(
  want: Bool, ds: List<&2, E.Decl>, +fuel: Nat, +env: E.DTable, trusted: Bool
) -> String:
  match want:
    case True{}:
      Check.lines(K.Kernel.run(ds, fuel, env), trusted)
    case False{}:
      "verdict " ++ Check.show(K.Kernel.check_all(ds, fuel, env), trusted)

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    +st : P.PState = P.Parse.run(Check.bytes(r))
    +ds : List<&2, E.Decl> = P.Parse.decls_of(st)
    # The environment carries the export's expression table, because a term
    # may hold a reference into it and only reduction resolves one.
    +env : E.DTable = E.Env.over(P.Parse.exps_of(st))
    rv : Result<&1, &1, U32 & String, String> <- IO.get_env("SOKO_REPORT")
    IO.print("declarations " ++ Nat.show(K.Kernel.count(ds, 0n)))
    IO.print(
      Check.out(
        Check.wants_report(rv), ds, Check.fuel(), env,
        K.Kernel.trusts(ds, Check.fuel(), env)))
