# Can the value evaluator reduce what the kernel cannot?
#
#   SOKO_EXPORT=<an export> bend bend/vprobe.bend
#
# For every declaration it evaluates the type and the value and counts the
# ones that come back unknown, which is what running out of budget looks
# like. A file whose declarations all evaluate is one the conversion built on
# this could answer.

import Base
import ./Bytes.bend as B
import ./Parse.bend as P
import ./Env.bend as E
import ./Term.bend as T
import ./Val.bend as W
import ./Ans.bend as A

def Vp.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

def Vp.bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def Vp.one(+env: E.DTable, +t: T.Term) -> Nat:
  Vp.bit(W.Val.is_unk(W.Val.eval(env, t)))

def Vp.walk(
  fuel: Nat, ds: List<&2, E.Decl>, +env: E.DTable, +bad: Nat, +n: Nat
) -> Nat & Nat:
  match fuel:
    case 0n:
      (bad, n)
    case 1n+f:
      match ds:
        case Nil{}:
          (bad, n)
        case Con{+h, t}:
          Vp.walk(
            f, t, E.Env.add(env, h),
            Nat.add(
              bad,
              Nat.add(
                Vp.one(env, E.Decl.raw_ty(h)),
                Vp.one(env, E.Decl.raw_val(h)))),
            1n+n)

def Vp.show(p: Nat & Nat) -> String:
  (bad, n) = p
  "declarations " ++ Nat.show(n) ++ "  unknown " ++ Nat.show(bad)

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    +st : P.PState = P.Parse.run(Vp.bytes(r))
    +ds : List<&2, E.Decl> = P.Parse.decls_of(st)
    IO.print(
      Vp.show(
        Vp.walk(100000n, ds, E.Env.over(P.Parse.exps_of(st)), 0n, 0n)))
