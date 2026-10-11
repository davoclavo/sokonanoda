# Show the declared and the inferred type of every declaration that fails.
#
#   SOKO_EXPORT=<export> bend bend/dbg.bend
#
# The names are indices, as `Show.bend` explains. This exists because
# narrowing by construction stopped being able to tell two terms apart.

import Base
import ./Bytes.bend as B
import ./Parse.bend as P
import ./Env.bend as E
import ./Term.bend as T
import ./Infer.bend as I
import ./Kernel.bend as K
import ./Ans.bend as A
import ./Show.bend as S

def Dbg.fuel() -> Nat:
  3000n

def Dbg.depth() -> Nat:
  40n

def Dbg.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

# The declared type and the value of a declaration that has one.
def Dbg.ty_of(d: E.Decl) -> T.Term:
  match d:
    case E.DDef{id, ps, ty, val}:
      ty
    case E.DThm{id, ps, ty, val}:
      ty
    case o:
      T.TUnk{}

def Dbg.val_of(d: E.Decl) -> T.Term:
  match d:
    case E.DDef{id, ps, ty, val}:
      val
    case E.DThm{id, ps, ty, val}:
      val
    case o:
      T.TUnk{}

def Dbg.has_val(d: E.Decl) -> Bool:
  match d:
    case E.DDef{id, ps, ty, val}:
      True{}
    case E.DThm{id, ps, ty, val}:
      True{}
    case o:
      False{}

# One line per failing declaration, with both terms.
def Dbg.line(+fuel: Nat, +env: E.DTable, +d: E.Decl) -> String:
  "  decl " ++ Nat.show(E.Decl.id(d)) ++ "\n" ++
  "    declared " ++ S.Show.term(Dbg.depth(), Dbg.ty_of(d)) ++ "\n" ++
  "    inferred " ++
    S.Show.term(
      Dbg.depth(),
      I.Infer.res_ty(I.Infer.infer(fuel, env, Nil{}, Dbg.val_of(d)))) ++ "\n"

# Report a declaration only when it fails and has a value to compare.
def Dbg.maybe(show: Bool, +fuel: Nat, +env: E.DTable, +d: E.Decl) -> String:
  match show:
    case True{}:
      Dbg.line(fuel, env, d)
    case False{}:
      ""

def Dbg.walk(ds: List<&2, E.Decl>, +fuel: Nat, +acc: E.DTable) -> String:
  match ds:
    case Nil{}:
      ""
    case Con{+h, t}:
      Dbg.maybe(
        Bool.and(
          Dbg.has_val(h),
          Bool.not(A.Ans.is_yes(K.Kernel.check_decl(fuel, acc, h)))),
        fuel, acc, h) ++ Dbg.walk(t, fuel, E.Env.add(acc, h))

# Every declaration's own stored type, which is what the kernel reads rather
# than what the file says.
def Dbg.decls(ds: List<&2, E.Decl>) -> String:
  match ds:
    case Nil{}:
      ""
    case Con{+h, t}:
      "  " ++ K.Kernel.kind_name(h) ++ " " ++ Nat.show(E.Decl.id(h)) ++ " : " ++
        S.Show.term(Dbg.depth(), E.Decl.type_at(h, Nil{})) ++ "\n" ++
        Dbg.decls(t)

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    +ds : List<&2, E.Decl> = P.Parse.decls_of(P.Parse.run(Dbg.bytes(r)))
    IO.print(Dbg.decls(ds))
    IO.print(Dbg.walk(ds, Dbg.fuel(), E.Env.empty()))
