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






def Cv.kparts(
  +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>, +v: W.Val
) -> String:
  +d : E.Decl = E.Lookup.get(E.Env.find(env, W.Val.head_name(v)))
  +sj : W.Val = W.Val.sp_nth(V.Eval.major_idx(d), W.Val.args(v))
  +qs : T.Term = W.Val.quote_d(fuel, env, X.Vconv.depth(cx, 0n), sj)
  +ty : T.Term =
    V.Eval.whnf(
      fuel, env, H.Shape.ty(H.Shape.infer(fuel, env, cx, qs)), Nil{})
  "    k near yes  ctx " ++ Nat.show(X.Vconv.depth(cx, 0n)) ++
  "\n      subject " ++ S.Show.term(14n, qs) ++
  "\n      its type " ++ S.Show.term(14n, ty) ++
  "\n      type ok " ++ Cv.yn(C.Conv.k_type_ok(d, ty)) ++
  "  fits " ++ Cv.yn(C.Conv.k_fits(fuel, env, cx, d, ty)) ++
  "\n      the constructor " ++
    S.Show.term(14n, C.Conv.k_ctor(env, d, ty)) ++
  "\n      K gives " ++
    S.Show.term(
      14n,
      W.Val.quote_d(
        fuel, env, X.Vconv.depth(cx, 0n),
        X.Vconv.k_fix(fuel, env, cx, v))) ++
  "\n      terms give " ++
    S.Show.term(
      14n,
      C.Conv.k_fix(
        fuel, env, cx,
        W.Val.quote_d(fuel, env, X.Vconv.depth(cx, 0n), v))) ++ "\n"

def Cv.kshow(
  +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>, +t: T.Term, near: Bool
) -> String:
  match near:
    case False{}:
      ""
    case True{}:
      Cv.kparts(
        fuel, env, cx,
        W.Val.core_in(fuel, env, X.Vconv.depth(cx, 0n), t))

def Cv.kpick(
  +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>, +t: T.Term
) -> String:
  Cv.kshow(
    fuel, env, cx, t,
    X.Vconv.k_near(
      env,
      W.Val.core_in(fuel, env, X.Vconv.depth(cx, 0n), t)))

# Walk a term to the first application whose head is a recursor the K-like
# rule would look at, and print what the rule sees there: the subject, the
# type inference gives it, and each of the two conditions.
def Cv.kfind(
  +steps: Nat, +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>, t: T.Term
) -> String:
  match steps:
    case 0n:
      ""
    case 1n+(+k):
      match t:
        case T.TPi{+ty, +bd}:
          Cv.kfind(k, fuel, env, Con{ty, cx}, bd)
        case T.TLam{+ty, +bd}:
          Cv.kfind(k, fuel, env, Con{ty, cx}, bd)
        case T.TApp{+g, +a}:
          Cv.kpick(fuel, env, cx, T.TApp{g, a}) ++
            Cv.kfind(k, fuel, env, cx, g) ++
            Cv.kfind(k, fuel, env, cx, a)
        case o:
          ""

def Cv.kprobe(+fuel: Nat, +env: E.DTable, +t: T.Term) -> String:
  Cv.kfind(200n, fuel, env, Nil{}, t)

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
