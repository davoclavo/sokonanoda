# Does the derived recursor match the one the file states?
#
#   SOKO_EXPORT=<an export> bend bend/derive.bend
#
# One line per recursor: `ok` when the derived type converts with the stated
# one, `NO` when it does not, `unk` when the conversion ran out of budget, and
# `shape` when the derivation does not handle the block at all. A `NO` prints
# both types, because the two are long and the difference is always small.
#
# This reports and changes nothing. The point is to measure the derivation
# against the whole corpus before the kernel's verdict depends on it.

import Base
import ./Bytes.bend as B
import ./Parse.bend as P
import ./Env.bend as E
import ./Term.bend as T
import ./Level.bend as L
import ./Conv.bend as C
import ./Rec.bend as R
import ./Ans.bend as A
import ./Show.bend as S

def Derive.fuel() -> Nat:
  3000n

def Derive.depth() -> Nat:
  120n

def Derive.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

# The declared type with its level parameters left where they are.
def Derive.stated(+d: E.Decl) -> T.Term:
  E.Decl.type_at(
    d, R.Rec.lvl_shift(List.length(&2, Nat, E.Decl.params(d)), 0n, 0n))

def Derive.word(a: A.Ans) -> String:
  match a:
    case A.AYes{}:
      "ok"
    case A.ANo{}:
      "NO"
    case A.AUnk{}:
      "unk"

def Derive.both(
  +want: T.Term, +got: T.Term, a: A.Ans
) -> String:
  match a:
    case A.AYes{}:
      ""
    case o:
      "\n    derived " ++ S.Show.term(Derive.depth(), got) ++
      "\n    stated  " ++ S.Show.term(Derive.depth(), want) ++ "\n"

def Derive.verdict(
  +a: A.Ans, +id: Nat, +got: T.Term, +want: T.Term
) -> String:
  "  rec " ++ Nat.show(id) ++ " " ++ Derive.word(a) ++
  Derive.both(want, got, a) ++ "\n"

def Derive.shape_line(
  nope: Bool, +fuel: Nat, +env: E.DTable, +id: Nat,
  +got: T.Term, +want: T.Term
) -> String:
  match nope:
    case True{}:
      "  rec " ++ Nat.show(id) ++ " shape\n"
    case False{}:
      Derive.verdict(C.Conv.eq(fuel, env, got, want), id, got, want)

def Derive.line(+fuel: Nat, +env: E.DTable, +d: E.Decl) -> String:
  +got : T.Term = R.Rec.derive(fuel, env, d)
  Derive.shape_line(
    T.Term.is_unk(got), fuel, env, E.Decl.id(d), got, Derive.stated(d))

def Derive.at(on: Bool, +fuel: Nat, +env: E.DTable, +d: E.Decl) -> String:
  match on:
    case True{}:
      Derive.line(fuel, env, d)
    case False{}:
      ""

def Derive.walk(
  ds: List<&2, E.Decl>, +fuel: Nat, +acc: E.DTable
) -> String:
  match ds:
    case Nil{}:
      ""
    case Con{+h, t}:
      Derive.at(E.Decl.is_rec(h), fuel, acc, h) ++
        Derive.walk(t, fuel, E.Env.add(acc, h))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    +ds : List<&2, E.Decl> = P.Parse.decls_of(P.Parse.run(Derive.bytes(r)))
    IO.print(Derive.walk(ds, Derive.fuel(), E.Env.empty()))
