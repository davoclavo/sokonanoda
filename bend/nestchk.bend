# Does the derived type of a nested block's recursor match the stated one?
#
#   SOKO_EXPORT=<an export> bend bend/nestchk.bend
#
# For every recursor whose motives outnumber its declared types, this builds
# the type `Rec.nest_type` derives for each index of the block and says
# which index the statement matches, if any. The comparison is the term
# conversion, which is what `Kernel.rec_verified` uses.

import Base
import ./Bytes.bend as B
import ./Parse.bend as P
import ./Env.bend as E
import ./Term.bend as T
import ./Rec.bend as R
import ./Conv.bend as C
import ./Ans.bend as A
import ./Show.bend as S
import ./Eval.bend as V

def Nk.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

def Nk.starts(ns: List<&2, Nat>) -> List<&2, T.Term>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{+n, t}:
      Con{T.TConst{n, Nil{}}, Nk.starts(t)}

# The stated type of a recursor, with its own level parameters in place.
def Nk.stated(+d: E.Decl) -> T.Term:
  E.Decl.type_at(
    d,
    R.Rec.lvl_shift(
      List.length(&2, Nat, E.Decl.params(d)), 0n, 0n))

def Nk.tryone(
  +env: E.DTable, +d: E.Decl, +ts: List<&2, T.Term>, +i: Nat
) -> String:
  "    index " ++ Nat.show(i) ++ " " ++
  A.Ans.show(
    C.Conv.eq(
      400000n, env,
      R.Rec.nest_type(400000n, env, ts, i, R.Rec.motive_level(1n)),
      Nk.stated(d))) ++ "\n"

def Nk.tryall(
  +env: E.DTable, +d: E.Decl, +ts: List<&2, T.Term>, n: Nat, +i: Nat
) -> String:
  match n:
    case 0n:
      ""
    case 1n+k:
      Nk.tryone(env, d, ts, i) ++ Nk.tryall(env, d, ts, k, 1n+i)

# The stated rule of the `j`-th constructor of the block, by name.
def Nk.stated_rule(+d: E.Decl, +cn: Nat) -> T.Term:
  E.RecRule.rhs(
    V.Eval.rule_get(E.Decl.rule_for(E.Decl.rec_rules(d), cn)))

def Nk.rule_one(
  +env: E.DTable, +d: E.Decl, +ts: List<&2, T.Term>, +j: Nat
) -> String:
  "    rule " ++ Nat.show(j) ++ " ctor " ++
  Nat.show(
    R.Rec.nc_name(R.Rec.nth_nc(R.Rec.nest_ctors(ts, env, 0n), j))) ++
  " " ++
  A.Ans.show(
    C.Conv.eq(
      400000n, env,
      R.Rec.nest_rhs(400000n, env, d, ts, R.Rec.motive_level(1n), j),
      Nk.stated_rule(
        d,
        R.Rec.nc_name(
          R.Rec.nth_nc(R.Rec.nest_ctors(ts, env, 0n), j))))) ++ "\n" ++
  "      derived " ++
    S.Show.term(
      30n, R.Rec.nest_rhs(400000n, env, d, ts, R.Rec.motive_level(1n), j))
    ++ "\n" ++
  "      stated  " ++
    S.Show.term(
      30n,
      Nk.stated_rule(
        d,
        R.Rec.nc_name(
          R.Rec.nth_nc(R.Rec.nest_ctors(ts, env, 0n), j)))) ++ "\n"

def Nk.rules(
  +env: E.DTable, +d: E.Decl, +ts: List<&2, T.Term>, n: Nat, +j: Nat
) -> String:
  match n:
    case 0n:
      ""
    case 1n+k:
      Nk.rule_one(env, d, ts, j) ++ Nk.rules(env, d, ts, k, 1n+j)

def Nk.pick(nested: Bool, +env: E.DTable, +d: E.Decl) -> String:
  match nested:
    case False{}:
      ""
    case True{}:
      "  recursor " ++ Nat.show(E.Decl.id(d)) ++ "\n" ++
      Nk.tryall(
        env, d,
        R.Rec.nest_types(
          E.Decl.rec_nm(d), 400000n, env,
          Nk.starts(E.Decl.rec_inds(d))),
        E.Decl.rec_nm(d), 0n) ++
      Nk.rules(
        env, d,
        R.Rec.nest_types(
          E.Decl.rec_nm(d), 400000n, env,
          Nk.starts(E.Decl.rec_inds(d))),
        E.Decl.rec_nmin(d), 0n)

def Nk.one(+env: E.DTable, +d: E.Decl) -> String:
  Nk.pick(
    Nat.is_lt(
      List.length(&2, Nat, E.Decl.rec_inds(d)), E.Decl.rec_nm(d)),
    env, d)

def Nk.walk(
  ds: List<&2, E.Decl>, +env: E.DTable, +acc: String
) -> String:
  match ds:
    case Nil{}:
      acc
    case Con{+h, t}:
      Nk.walk(t, E.Env.add(env, h), acc ++ Nk.one(env, h))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    +st : P.PState = P.Parse.run(Nk.bytes(r))
    IO.print(
      Nk.walk(
        P.Parse.decls_of(st), E.Env.over(P.Parse.exps_of(st)),
        "nested recursors, derived against stated:\n"))
