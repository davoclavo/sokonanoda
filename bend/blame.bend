# Which subterm does the kernel reject?
#
#   SOKO_EXPORT=<export> bend bend/blame.bend
#
# A declaration that answers `reject` says so about its whole value, and the
# value of a real export is thousands of nodes. This walks down into the value
# and stops at the smallest subterm that inference calls a definite no: a node
# whose own answer is no while no child of it is. Then it prints that node,
# and for an application the type of each side, which is the pair a failed
# conversion is about.
#
# A match cannot scrutinize a computed value and Bend has no mutual recursion,
# so the walk cannot ask a helper where to go next and then recurse there.
# Instead each step computes the next node and the next context as terms and
# calls itself in tail position. A step that finds no child to blame hands
# back the node it is on, so the walk stands still and the last one prints it.

import Base
import ./Bytes.bend as B
import ./Parse.bend as P
import ./Env.bend as E
import ./Term.bend as T
import ./Eval.bend as V
import ./Infer.bend as I
import ./Kernel.bend as K
import ./Ans.bend as A
import ./Show.bend as S

def Blame.fuel() -> Nat:
  30000n

def Blame.depth() -> Nat:
  60n

def Blame.steps() -> Nat:
  40n

def Blame.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

# Does inference call this subterm a definite no?
def Blame.bad(+fuel: Nat, +env: E.DTable, ctx: List<&2, T.Term>, t: T.Term) -> Bool:
  A.Ans.is_no(I.Infer.res_ans(I.Infer.infer(fuel, env, ctx, t)))

def Blame.pick_ctx(
  b: Bool, x: List<&2, T.Term>, y: List<&2, T.Term>
) -> List<&2, T.Term>:
  match b:
    case True{}:
      x
    case False{}:
      y

# The child to blame, or the node itself when no child is to blame.
def Blame.next(
  +fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>, t: T.Term
) -> T.Term:
  match t:
    case T.TApp{+g, +a}:
      T.Term.pick(
        Blame.bad(fuel, env, ctx, g),
        g,
        T.Term.pick(Blame.bad(fuel, env, ctx, a), a, T.TApp{g, a}))
    case T.TLam{+ty, +bd}:
      T.Term.pick(
        Blame.bad(fuel, env, ctx, ty),
        ty,
        T.Term.pick(
          Blame.bad(fuel, env, Con{ty, ctx}, bd), bd, T.TLam{ty, bd}))
    case T.TPi{+ty, +bd}:
      T.Term.pick(
        Blame.bad(fuel, env, ctx, ty),
        ty,
        T.Term.pick(
          Blame.bad(fuel, env, Con{ty, ctx}, bd), bd, T.TPi{ty, bd}))
    case T.TLet{+ty, +v, +bd}:
      T.Term.pick(
        Blame.bad(fuel, env, ctx, v),
        v,
        T.Term.pick(
          Blame.bad(fuel, env, ctx, T.Term.inst(bd, v)),
          T.Term.inst(bd, v),
          T.TLet{ty, v, bd}))
    case T.TProj{+tn, +idx, +st}:
      T.Term.pick(
        Blame.bad(fuel, env, ctx, st), st, T.TProj{tn, idx, st})
    case T.TRef{+i, +k, m}:
      E.Env.expr_at(env, i, k)
    case o:
      o

# The context the child lives in. Only a binder changes it, and only when the
# walk goes into the body rather than into the binder's own type.
def Blame.next_ctx(
  +fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>, t: T.Term
) -> List<&2, T.Term>:
  match t:
    case T.TLam{+ty, +bd}:
      Blame.pick_ctx(
        Bool.and(
          Bool.not(Blame.bad(fuel, env, ctx, ty)),
          Blame.bad(fuel, env, Con{ty, ctx}, bd)),
        Con{ty, ctx},
        ctx)
    case T.TPi{+ty, +bd}:
      Blame.pick_ctx(
        Bool.and(
          Bool.not(Blame.bad(fuel, env, ctx, ty)),
          Blame.bad(fuel, env, Con{ty, ctx}, bd)),
        Con{ty, ctx},
        ctx)
    case o:
      ctx

# The two types a failed conversion at an application is about.
def Blame.sides(
  +fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>, t: T.Term
) -> String:
  match t:
    case T.TApp{+g, +a}:
      "    fn   : " ++
      S.Show.term(
        Blame.depth(),
        V.Eval.whnf(
          fuel, env, I.Infer.res_ty(I.Infer.infer(fuel, env, ctx, g)), Nil{})) ++
      "\n    arg  : " ++
      S.Show.term(
        Blame.depth(),
        V.Eval.whnf(
          fuel, env, I.Infer.res_ty(I.Infer.infer(fuel, env, ctx, a)), Nil{})) ++
      "\n"
    case o:
      ""

def Blame.here(
  +fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>, +t: T.Term
) -> String:
  "  blame: " ++ S.Show.term(Blame.depth(), t) ++ "\n" ++
  Blame.sides(fuel, env, ctx, t)

# One step down, or a stop.
def Blame.go(
  +steps: Nat, +fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>, +t: T.Term
) -> String:
  match steps:
    case 0n:
      Blame.here(fuel, env, ctx, t)
    case 1n+k:
      Blame.go(
        k, fuel, env,
        Blame.next_ctx(fuel, env, ctx, t),
        Blame.next(fuel, env, ctx, t))

def Blame.val_of(d: E.Decl) -> T.Term:
  match d:
    case E.DDef{id, ps, ty, val}:
      val
    case E.DThm{id, ps, ty, val}:
      val
    case o:
      T.TUnk{}

def Blame.has_val(d: E.Decl) -> Bool:
  match d:
    case E.DDef{id, ps, ty, val}:
      True{}
    case E.DThm{id, ps, ty, val}:
      True{}
    case o:
      False{}

def Blame.at(
  on: Bool, +steps: Nat, +fuel: Nat, +env: E.DTable, +d: E.Decl
) -> String:
  match on:
    case True{}:
      "decl " ++ Nat.show(E.Decl.id(d)) ++ "\n" ++
      Blame.go(steps, fuel, env, Nil{}, Blame.val_of(d))
    case False{}:
      ""

# Walk the declarations, build the environment as the kernel does, and report
# on the first one the kernel calls a definite no. The walk stops there,
# because every declaration after it is checked against an environment the
# first failure has already put in doubt.
def Blame.walk(
  ds: List<&2, E.Decl>, done: Bool, +fuel: Nat, +acc: E.DTable
) -> String:
  match ds done:
    case Nil{} d:
      ""
    case Con{h, t} True{}:
      ""
    case Con{+h, t} False{}:
      +hit : Bool = Bool.and(
        Blame.has_val(h),
        A.Ans.is_no(K.Kernel.check_decl(fuel, acc, h)))
      Blame.at(hit, Blame.steps(), fuel, acc, h) ++
        Blame.walk(t, hit, fuel, E.Env.add(acc, h))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    # The environment has to carry the expression table: a term may hold a
    # reference into it, and only a walk that sees the table resolves one.
    +st : P.PState = P.Parse.run(Blame.bytes(r))
    +ds : List<&2, E.Decl> = P.Parse.decls_of(st)
    IO.print(Blame.walk(ds, False{}, Blame.fuel(), E.Env.over(P.Parse.exps_of(st))))
