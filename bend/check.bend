# Check a real Lean export.
#
# Reads the file named by SOKO_EXPORT, builds its environment, checks every
# declaration against the ones before it, and prints a verdict.
#
#   SOKO_EXPORT=<path to a .ndjson export> bend bend/check.bend
#
# The verdict covers only what this kernel implements. An export with
# inductive types, quotients, projections or literals is read but those
# declarations are skipped, so a verdict on such a file means nothing. The
# tutorial tests 001 to 018 are inside the fragment.

import Base
import ./Bytes.bend as B
import ./Parse.bend as P
import ./Env.bend as E
import ./Kernel.bend as K

# The fuel one declaration gets.
#
# This cannot be made large. `Conv.eq_all` works a queue of pairs and its
# recursive call sits inside an argument, not in tail position, because the
# verdict has to be read before the queue can be shortened. So its depth is
# bounded by the fuel, and Bend's host stack gives out near ten thousand
# frames. A fuel of 100000 overflows the stack on a `let` that needs real
# conversion work, which is how this number was found.
def Check.fuel() -> Nat:
  3000n

def Check.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

def Check.show(b: Bool) -> String:
  match b:
    case True{}:
      "accept"
    case False{}:
      "reject"

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    +ds : List<&2, E.Decl> = P.Parse.decls_of(P.Parse.run(Check.bytes(r)))
    IO.print("declarations " ++ Nat.show(K.Kernel.count(ds, 0n)))
    IO.print(K.Kernel.report(ds, Check.fuel(), Nil{}))
    IO.print("verdict " ++ Check.show(K.Kernel.check_all(ds, Check.fuel(), Nil{})))
