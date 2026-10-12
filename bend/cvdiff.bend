# Does conversion on values answer what conversion on terms answers?
#
#   SOKO_EXPORT=<an export> bend bend/cvdiff.bend
#
# For every declaration it asks both: is the type inference gives for the
# value the type the declaration states? `Conv.eq` answers it on terms and
# `Vconv.eq_in` on values, and the two must not differ. A `declined` on one
# side and a yes or a no on the other is a budget difference and is counted
# apart; a yes against a no is a bug.

import Base
import ./Bytes.bend as B
import ./Parse.bend as P
import ./Env.bend as E
import ./Term.bend as T
import ./Eval.bend as V
import ./Val.bend as W
import ./Infer.bend as I
import ./Conv.bend as C
import ./Vconv.bend as X
import ./Shape.bend as H
import ./Ans.bend as A
import ./Show.bend as S

def Cv.fuel() -> Nat:
  300000n

def Cv.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

def Cv.tag(b: Bool) -> String:
  match b:
    case True{}:
      "unknown"
    case False{}:
      "ok"

# yes against no, or no against yes: a bug. Anything with an unknown in it is
# a budget difference.
def Cv.bad(a: A.Ans, b: A.Ans) -> Bool:
  match a b:
    case A.AYes{} A.ANo{}:
      True{}
    case A.ANo{} A.AYes{}:
      True{}
    case x y:
      False{}

def Cv.soft(a: A.Ans, b: A.Ans) -> Bool:
  match a b:
    case A.AUnk{} A.AUnk{}:
      False{}
    case A.AUnk{} y:
      True{}
    case x A.AUnk{}:
      True{}
    case x y:
      False{}

def Cv.one(+fuel: Nat, +env: E.DTable, +d: E.Decl) -> A.Ans & A.Ans:
  +ity : T.Term =
    I.Infer.res_ty(I.Infer.infer(fuel, env, Nil{}, E.Decl.raw_val(d)))
  +dty : T.Term = E.Decl.raw_ty(d)
  (C.Conv.eq(fuel, env, ity, dty), X.Vconv.eq_in(fuel, env, Nil{}, ity, dty))

def Cv.yn(b: Bool) -> String:
  match b:
    case True{}:
      "yes"
    case False{}:
      "no"

# The K-like rule, probed on the declared type's own subterms: is the rule
# near, and what does the subject's type come out as?
def Cv.kprobe(+fuel: Nat, +env: E.DTable, +t: T.Term) -> String:
  +v : W.Val = W.Val.core(fuel, env, t)
  "    k near " ++ Cv.yn(X.Vconv.k_near(env, v)) ++
  "  head " ++ Nat.show(W.Val.head_name(v)) ++
  "  args " ++ Nat.show(W.Val.sp_len(W.Val.args(v), 0n)) ++ "\n"

# The two sides as the value evaluator sees them, for a declaration whose
# answers differ.
def Cv.sides(+fuel: Nat, +env: E.DTable, +d: E.Decl) -> String:
  +ity : T.Term =
    I.Infer.res_ty(I.Infer.infer(fuel, env, Nil{}, E.Decl.raw_val(d)))
  "    inferred core " ++
    Cv.tag(W.Val.is_unk(W.Val.core(fuel, env, ity))) ++
  "  declared core " ++
    Cv.tag(W.Val.is_unk(W.Val.core(fuel, env, E.Decl.raw_ty(d)))) ++
  "\n    inferred " ++
    S.Show.term(24n, W.Val.quote(env, W.Val.core(fuel, env, ity))) ++
  "\n    declared " ++
    S.Show.term(24n, W.Val.quote(env, W.Val.core(fuel, env, E.Decl.raw_ty(d)))) ++
  "\n" ++ Cv.kprobe(fuel, env, E.Decl.raw_ty(d))

def Cv.line(
  bad: Bool, soft: Bool, +id: Nat, +x: String, +y: String
) -> String:
  match bad:
    case True{}:
      "BUG  decl " ++ Nat.show(id) ++ "  terms " ++ x ++ "  values " ++ y ++ "\n"
    case False{}:
      match soft:
        case True{}:
          "soft decl " ++ Nat.show(id) ++ "  terms " ++ x ++ "  values " ++ y ++ "\n"
        case False{}:
          ""

def Cv.say(+id: Nat, p: A.Ans & A.Ans) -> String:
  (+x, +y) = p
  Cv.line(Cv.bad(x, y), Cv.soft(x, y), id, A.Ans.show(x), A.Ans.show(y))

def Cv.with_sides(
  quiet: Bool, +fuel: Nat, +env: E.DTable, +d: E.Decl, +msg: String
) -> String:
  match quiet:
    case True{}:
      ""
    case False{}:
      msg ++ Cv.sides(fuel, env, d)

def Cv.both(+fuel: Nat, +env: E.DTable, +d: E.Decl) -> String:
  +msg : String = Cv.say(E.Decl.id(d), Cv.one(fuel, env, d))
  Cv.with_sides(String.is_empty(msg), fuel, env, d, msg)

def Cv.walk(
  fuel: Nat, ds: List<&2, E.Decl>, +env: E.DTable
) -> String:
  match fuel:
    case 0n:
      ""
    case 1n+f:
      match ds:
        case Nil{}:
          ""
        case Con{+h, t}:
          Cv.both(Cv.fuel(), env, h) ++ Cv.walk(f, t, E.Env.add(env, h))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    +st : P.PState = P.Parse.run(Cv.bytes(r))
    +ds : List<&2, E.Decl> = P.Parse.decls_of(st)
    IO.print("compared")
    IO.print(Cv.walk(100000n, ds, E.Env.over(P.Parse.exps_of(st))))
