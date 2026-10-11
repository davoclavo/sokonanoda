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
# What sets it now is time. Raising the fuel raises the work a declaration may
# do before it gives up, so it buys answers on the files that decline and
# costs time on the ones that already answer. Measure before you change it.
def Check.fuel() -> Nat:
  3000n

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

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    +ds : List<&2, E.Decl> = P.Parse.decls_of(P.Parse.run(Check.bytes(r)))
    IO.print("declarations " ++ Nat.show(K.Kernel.count(ds, 0n)))
    IO.print(K.Kernel.report(ds, Check.fuel(), E.Env.empty()))
    IO.print("verdict " ++ Check.show(K.Kernel.check_all(ds, Check.fuel(), E.Env.empty()), K.Kernel.trusts(ds, Check.fuel(), E.Env.empty())))
