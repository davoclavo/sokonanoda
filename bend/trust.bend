# Which recursors cannot be derived, and what shape they are.
#
#   SOKO_EXPORT=<an export> bend bend/trust.bend
#
# A file answers `declined` when one recursor's derived type does not match
# the stated one, and the verdict does not say which. This names every one
# of them with its number of motives and the size of its block, which is
# what says whether the gap is a mutual block, a nested inductive, or
# something else.

import Base
import ./Bytes.bend as B
import ./Parse.bend as P
import ./Env.bend as E
import ./Kernel.bend as K
import ./Ans.bend as A

def Tr.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

def Tr.line(bad: Bool, +d: E.Decl) -> String:
  match bad:
    case False{}:
      ""
    case True{}:
      "  id " ++ Nat.show(E.Decl.id(d)) ++
      " motives " ++ Nat.show(E.Decl.rec_nm(d)) ++
      " block " ++
        Nat.show(List.length(&2, Nat, E.Decl.rec_inds(d))) ++
      " minors " ++ Nat.show(E.Decl.rec_nmin(d)) ++ "\n"

def Tr.one(+env: E.DTable, +d: E.Decl) -> String:
  Tr.line(K.Kernel.trusted_ans(400000n, env, d), d)

def Tr.walk(
  ds: List<&2, E.Decl>, +env: E.DTable, +acc: String
) -> String:
  match ds:
    case Nil{}:
      acc
    case Con{+h, t}:
      Tr.walk(t, E.Env.add(env, h), acc ++ Tr.one(env, h))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    +st : P.PState = P.Parse.run(Tr.bytes(r))
    IO.print(
      Tr.walk(
        P.Parse.decls_of(st), E.Env.over(P.Parse.exps_of(st)),
        "recursors taken on trust:\n"))
