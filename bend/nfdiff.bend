# Does the value evaluator agree with the reduction that substitutes?
#
#   SOKO_EXPORT=<an export> bend bend/nfdiff.bend
#
# For every declaration it takes the normal form two ways -- by `Eval.whnf`
# driven into every subterm, and by `Val.eval` with the answer read back --
# and prints the first declaration where the two are not the same term.
#
# This is the gate on the value evaluator. The branch `closure` taught that a
# reducer which agrees on hand-built terms can still be wrong on a real
# export, and that the smallest disagreement is the only useful thing to
# look at.

import Base
import ./Bytes.bend as B
import ./Parse.bend as P
import ./Env.bend as E
import ./Term.bend as T
import ./Eval.bend as V
import ./Val.bend as W
import ./Conv.bend as C
import ./Show.bend as S

def Nf.fuel() -> Nat:
  100000n

def Nf.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

# The normal form by the reduction that substitutes: reduce the head, then
# every part of what it gives back.
# Reduce the head, then every part of what it gives back.
#
# One control type and one loop, because Bend has no mutual recursion and a
# `law` cannot stand in for it: an unfilled law is a dead claim and live code
# may not use it.
type NC is Data:
  NRaw{t: T.Term}
  NRed{w: T.Term}

def Nf.go(+fuel: Nat, +env: E.DTable, c: NC) -> T.Term:
  match fuel:
    case 0n:
      T.TUnk{}
    case 1n+(+f):
      match c:
        case NRaw{+t}:
          Nf.go(f, env, NRed{V.Eval.whnf(f, env, t, Nil{})})
        case NRed{w}:
          match w:
            case T.TApp{+g, +a}:
              T.TApp{Nf.go(f, env, NRaw{g}), Nf.go(f, env, NRaw{a})}
            case T.TLam{+ty, +bd}:
              T.TLam{Nf.go(f, env, NRaw{ty}), Nf.go(f, env, NRaw{bd})}
            case T.TPi{+ty, +bd}:
              T.TPi{Nf.go(f, env, NRaw{ty}), Nf.go(f, env, NRaw{bd})}
            case T.TLet{+ty, +v, +bd}:
              T.TLet{
                Nf.go(f, env, NRaw{ty}), Nf.go(f, env, NRaw{v}),
                Nf.go(f, env, NRaw{bd})}
            case T.TProj{+tn, +idx, +st}:
              T.TProj{tn, idx, Nf.go(f, env, NRaw{st})}
            case o:
              o

def Nf.eager(+fuel: Nat, +env: E.DTable, +t: T.Term) -> T.Term:
  Nf.go(fuel, env, NRaw{t})

# The comparison gets a budget of its own, far above the kernel's. Two
# normal forms can hold millions of nodes -- `perf/repeated-subproblem` is
# one -- and `Conv.same` answers "not the same" when it runs out, which
# reported a disagreement where the two terms print the same to the last
# character.
def Nf.same_budget() -> Nat:
  400000000n

def Nf.agree(+env: E.DTable, +t: T.Term) -> Bool:
  C.Conv.same_in(
    Nf.same_budget(), env, Nf.eager(Nf.fuel(), env, t),
    W.Val.nf_in(Nf.fuel(), env, t))

def Nf.show(+env: E.DTable, +nm: String, +t: T.Term) -> String:
  "  " ++ nm ++ "\n    eager " ++
    S.Show.term(30n, Nf.eager(Nf.fuel(), env, t)) ++
  "\n    value " ++ S.Show.term(30n, W.Val.nf_in(Nf.fuel(), env, t)) ++ "\n"

def Nf.at(ok: Bool, +env: E.DTable, +d: E.Decl) -> String:
  match ok:
    case True{}:
      ""
    case False{}:
      "decl " ++ Nat.show(E.Decl.id(d)) ++ "\n" ++
      Nf.show(env, "value", E.Decl.raw_val(d))

def Nf.walk(
  ds: List<&2, E.Decl>, done: Bool, +env: E.DTable
) -> String:
  match ds done:
    case Nil{} x:
      ""
    case Con{h, t} True{}:
      ""
    case Con{+h, t} False{}:
      +ok : Bool = Nf.agree(env, E.Decl.raw_val(h))
      Nf.at(ok, env, h) ++ Nf.walk(t, Bool.not(ok), E.Env.add(env, h))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    +st : P.PState = P.Parse.run(Nf.bytes(r))
    +ds : List<&2, E.Decl> = P.Parse.decls_of(st)
    IO.print("checked " ++ Nat.show(1n))
    IO.print(Nf.walk(ds, False{}, E.Env.over(P.Parse.exps_of(st))))
