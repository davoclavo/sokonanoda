# The types a nested block eliminates.
#
#   SOKO_EXPORT=<an export> bend bend/nest.bend
#
# A nested block states more motives than it declares types, and the ones it
# does not name have to be found. This prints what `Rec.nest_types` finds,
# for every recursor whose motives outnumber its declared types.

import Base
import ./Bytes.bend as B
import ./Parse.bend as P
import ./Env.bend as E
import ./Term.bend as T
import ./Rec.bend as R
import ./Show.bend as S

def Ns.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

def Ns.names(ts: List<&2, T.Term>, +acc: String) -> String:
  match ts:
    case Nil{}:
      acc
    case Con{+h, t}:
      Ns.names(t, acc ++ "    " ++ S.Show.term(6n, h) ++ "\n")

# The declared types of a block, as terms.
def Ns.starts(ns: List<&2, Nat>) -> List<&2, T.Term>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{+n, t}:
      Con{T.TConst{n, Nil{}}, Ns.starts(t)}

def Ns.pick(nested: Bool, +env: E.DTable, +d: E.Decl) -> String:
  match nested:
    case False{}:
      ""
    case True{}:
      "  recursor " ++ Nat.show(E.Decl.id(d)) ++
      " motives " ++ Nat.show(E.Decl.rec_nm(d)) ++
      " siblings " ++
        Nat.show(List.length(&2, Nat, E.Decl.rec_sibs(d))) ++ "\n" ++
      Ns.names(
        R.Rec.nest_types(
          E.Decl.rec_nm(d), 400000n, env,
          Ns.starts(E.Decl.rec_inds(d))),
        "")

def Ns.one(+env: E.DTable, +d: E.Decl) -> String:
  Ns.pick(
    Bool.and(
      Nat.is_eq(E.Decl.id(d), 1743n),
      Nat.is_lt(
        List.length(&2, Nat, E.Decl.rec_inds(d)), E.Decl.rec_nm(d))),
    env, d)

def Ns.walk(
  ds: List<&2, E.Decl>, +env: E.DTable, +acc: String
) -> String:
  match ds:
    case Nil{}:
      acc
    case Con{+h, t}:
      Ns.walk(t, E.Env.add(env, h), acc ++ Ns.one(env, h))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    +st : P.PState = P.Parse.run(Ns.bytes(r))
    IO.print(
      Ns.walk(
        P.Parse.decls_of(st), E.Env.over(P.Parse.exps_of(st)),
        "nested blocks:\n"))
