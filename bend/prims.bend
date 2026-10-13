# Which declarations carry a native rule?
#
#   SOKO_EXPORT=<an export> bend bend/prims.bend
#
# The arena enables a native `Nat`, and the parser marks eight names with the
# rule they carry. A file where the mark is missing computes them by
# unfolding, which for a bound near `UInt32.size` is a million steps.

import Base
import ./Bytes.bend as B
import ./Parse.bend as P
import ./Env.bend as E

def Pr.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

def Pr.mark(zero: Bool, +id: Nat, +op: Nat) -> String:
  match zero:
    case True{}:
      ""
    case False{}:
      "  name " ++ Nat.show(id) ++ " carries rule " ++ Nat.show(op) ++ "\n"

def Pr.one(+d: E.Decl) -> String:
  Pr.mark(
    Nat.is_eq(E.Decl.prim_op(d), 0n), E.Decl.id(d), E.Decl.prim_op(d))

def Pr.walk(ds: List<&2, E.Decl>, +acc: String) -> String:
  match ds:
    case Nil{}:
      acc
    case Con{+h, t}:
      Pr.walk(t, acc ++ Pr.one(h))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    +st : P.PState = P.Parse.run(Pr.bytes(r))
    IO.print(Pr.walk(P.Parse.decls_of(st), "native rules:\n"))
