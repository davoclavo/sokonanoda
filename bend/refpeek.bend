# What does one entry of the export's table resolve to, at a shift?
#
#   SOKO_EXPORT=<an export> SOKO_REF=7124 bend bend/refpeek.bend
#
# A reference carries an entry and a shift, and `Env.expr_at` is what turns
# the pair into a term. A conversion that cannot settle a pair whose head is
# a reference wants this answer first: what the reference stands for, and
# whether the shift changed it into the unknown term.

import Base
import ./Bytes.bend as B
import ./Parse.bend as P
import ./Env.bend as E
import ./Term.bend as T
import ./Show.bend as S

def Ref.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

def Ref.digits(s: String, +acc: Nat) -> Nat:
  match s:
    case SNil{}:
      acc
    case SCon{+head, tail}:
      Ref.digits(
        tail,
        Nat.add(Nat.mul(acc, 10n), Nat.sub(U32.to_nat(Char.to_u32(head)), 48n)))

def Ref.which(r: Result<&1, &1, U32 & String, String>) -> Nat:
  match r:
    case Fail{e}:
      0n
    case Done{v}:
      Ref.digits(v, 0n)

def Ref.at(+env: E.DTable, +i: Nat, +k: Nat) -> String:
  "  shift " ++ Nat.show(k) ++ ": " ++
    S.Show.term(6n, E.Env.expr_at(env, i, k)) ++ "\n"

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    rv : Result<&1, &1, U32 & String, String> <- IO.get_env("SOKO_REF")
    +st : P.PState = P.Parse.run(Ref.bytes(r))
    +env : E.DTable = E.Env.over(P.Parse.exps_of(st))
    +i : Nat = Ref.which(rv)
    IO.print("entry " ++ Nat.show(i))
    IO.print(
      Ref.at(env, i, 0n) ++ Ref.at(env, i, 1n) ++ Ref.at(env, i, 2n))
