# The parsed value of the last declaration, with no reduction.
#
#   SOKO_EXPORT=<an export> bend bend/ptrm.bend
#
# This splits a fault of the reader from a fault of a rule. A literal that
# the reader missed prints as `?`, and a rule that reads numbers cannot fire
# on one.

import Base
import ./Bytes.bend as B
import ./Parse.bend as P
import ./Env.bend as E
import ./Term.bend as T
import ./Show.bend as S

def Pt.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

def Pt.last(ds: List<&2, E.Decl>, +acc: String) -> String:
  match ds:
    case Nil{}:
      acc
    case Con{+h, t}:
      Pt.last(
        t,
        "rule " ++ Nat.show(E.Decl.prim_op(h)) ++ " value "
          ++ S.Show.term(40n, E.Decl.raw_val(h)))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    +st : P.PState = P.Parse.run(Pt.bytes(r))
    IO.print(Pt.last(P.Parse.decls_of(st), "none"))
