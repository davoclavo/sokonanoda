# The normal form of the last declaration's value.
#
#   SOKO_EXPORT=<an export> bend bend/nf1.bend
#
# A conversion that does not finish is a reduction that does not finish, and
# this says what the reduction reaches. A term the evaluator gave up on
# prints as `?`, and what stands next to it is what it is stuck on.

import Base
import ./Bytes.bend as B
import ./Parse.bend as P
import ./Env.bend as E
import ./Term.bend as T
import ./Val.bend as W
import ./Show.bend as S

def Nf1.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

def Nf1.last(
  ds: List<&2, E.Decl>, +env: E.DTable, +acc: String
) -> String:
  match ds:
    case Nil{}:
      acc
    case Con{+h, t}:
      Nf1.last(
        t, E.Env.add(env, h),
        S.Show.term(40n, W.Val.nf_in(400000n, env, E.Decl.raw_val(h))))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    +st : P.PState = P.Parse.run(Nf1.bytes(r))
    IO.print(
      Nf1.last(
        P.Parse.decls_of(st), E.Env.over(P.Parse.exps_of(st)), "none"))
