# Type inference.
#
# One self-recursive def, `Infer.infer`, surrounded by helpers that each match
# their own parameter. That split is what Bend's rules leave: inference has to
# look at the type it just inferred, which is a computed value, so the looking
# happens in a helper; and the helper must not call back into inference, so
# every helper here is non-recursive.
#
# A failure answers `RBad` rather than a term, so a bad subterm cannot pass for
# a good one. Each case guards its result with a Bool, and `Infer.res_if`
# turns that Bool into the answer.
#
# The local context is a list of the binders' types, innermost first. The type
# of variable `i` was written one scope per binder further out, so it is lifted
# by `i + 1` on the way out.
#
# This covers the dependently typed core: variables, sorts, constants,
# application, lambda, pi, and let. It does not cover inductive types,
# constructors, recursors, projections, or quotients, which is where most of
# the Lean kernel's bulk lives.

import Base
import ./Level.bend as L
import ./Term.bend as T
import ./Env.bend as E
import ./Eval.bend as V
import ./Conv.bend as C
import ./Ans.bend as A

type Res is Data:
  ROk{ty: T.Term}
  RBad{}
  # Inference ran out of budget, or met a term reduction had given up on. The
  # answer is neither a type nor a verdict, and it must not be read as one.
  RUnk{}

# The term a failed result stands in with.
#
# This is a loose variable on purpose. A failed inference has no type, but
# something has to come back, and whatever comes back must not look like a
# sort or like a pi. An earlier version used `Sort 0` here, and because
# `is_sort` accepted it, a failure inside a pi or a let passed for a valid
# sort and the declaration was accepted. The arena's `009_forallSortBad` is
# exactly that. Every case below also guards on `res_ok`, so this is the
# second line of defence rather than the first.
def Infer.dummy() -> T.Term:
  T.TVar{0n}

# Did inference succeed?
def Infer.res_ans(r: Res) -> A.Ans:
  match r:
    case ROk{ty}:
      A.AYes{}
    case RBad{}:
      A.ANo{}
    case RUnk{}:
      A.AUnk{}

def Infer.res_ok(r: Res) -> Bool:
  match r:
    case ROk{ty}:
      True{}
    case RBad{}:
      False{}
    case RUnk{}:
      False{}

# The inferred type, or the dummy when inference failed.
def Infer.res_ty(r: Res) -> T.Term:
  match r:
    case ROk{ty}:
      ty
    case RBad{}:
      Infer.dummy()
    case RUnk{}:
      T.TUnk{}

# A result from a Bool and a type.
def Infer.res_if(b: Bool, ty: T.Term) -> Res:
  match b:
    case True{}:
      ROk{ty}
    case False{}:
      RBad{}

# A result from a three-valued answer, so not knowing stays not knowing.
def Infer.res_of(a: A.Ans, ty: T.Term) -> Res:
  match a:
    case A.AYes{}:
      ROk{ty}
    case A.ANo{}:
      RBad{}
    case A.AUnk{}:
      RUnk{}

# Shift a result's free variables up by `d`.
def Infer.lift_res(r: Res, +d: Nat) -> Res:
  match r:
    case ROk{ty}:
      ROk{T.Term.lift(ty, d, 0n)}
    case RBad{}:
      RBad{}
    case RUnk{}:
      RUnk{}

# Is this term a pi, or did reduction give up before it could say?
def Infer.pi_ans(t: T.Term) -> A.Ans:
  match t:
    case T.TPi{ty, bd}:
      A.AYes{}
    case T.TUnk{}:
      A.AUnk{}
    case x:
      A.ANo{}

# Is this term a pi?
def Infer.is_pi(t: T.Term) -> Bool:
  match t:
    case T.TPi{ty, bd}:
      True{}
    case x:
      False{}

# A pi's domain, or the dummy. Guarded by `is_pi`.
def Infer.pi_dom(t: T.Term) -> T.Term:
  match t:
    case T.TPi{ty, bd}:
      ty
    case x:
      Infer.dummy()

# A pi's body, or the dummy. Guarded by `is_pi`.
def Infer.pi_bd(t: T.Term) -> T.Term:
  match t:
    case T.TPi{ty, bd}:
      bd
    case x:
      Infer.dummy()

# Is this term a sort, or did reduction give up before it could say?
def Infer.sort_ans(t: T.Term) -> A.Ans:
  match t:
    case T.TSort{l}:
      A.AYes{}
    case T.TUnk{}:
      A.AUnk{}
    case x:
      A.ANo{}

# Is this term a sort?
def Infer.is_sort(t: T.Term) -> Bool:
  match t:
    case T.TSort{l}:
      True{}
    case x:
      False{}

# A sort's level, or zero. Guarded by `is_sort`.
def Infer.sort_level(t: T.Term) -> L.Level:
  match t:
    case T.TSort{l}:
      l
    case x:
      L.LZero{}

# The type of the `i`-th binder, as written in its own scope.
def Infer.ctx_nth(ctx: List<&2, T.Term>, i: Nat) -> Res:
  match ctx:
    case Nil{}:
      RBad{}
    case Con{h, t}:
      match i:
        case 0n:
          ROk{h}
        case 1n+p:
          Infer.ctx_nth(t, p)

# The number of level arguments a lookup expects, and whether it was found.
def Infer.const_arity_ok(lk: E.Lookup, +ls: List<&2, L.Level>) -> Bool:
  match lk:
    case E.LFound{d}:
      Nat.is_eq(E.Decl.num_params(d), List.length(&2, L.Level, ls))
    case E.LMissing{}:
      False{}

# The type of a constant at the given levels, or the dummy.
def Infer.const_type(lk: E.Lookup, +ls: List<&2, L.Level>) -> T.Term:
  match lk:
    case E.LFound{d}:
      E.Decl.type_at(d, ls)
    case E.LMissing{}:
      Infer.dummy()

# Infer the type of `t` in the context `ctx`.
def Infer.infer(+fuel: Nat, +env: List<&2, E.Decl>, +ctx: List<&2, T.Term>, t: T.Term) -> Res:
  match fuel:
    case 0n:
      RUnk{}
    case 1n+f:
      match t:
        case T.TVar{+i}:
          Infer.lift_res(Infer.ctx_nth(ctx, i), 1n+i)
        case T.TSort{l}:
          ROk{T.TSort{L.LSucc{l}}}
        case T.TConst{+n, +ls}:
          Infer.res_if(
            Infer.const_arity_ok(E.Env.find(env, n), ls),
            Infer.const_type(E.Env.find(env, n), ls))
        case T.TApp{g, +a}:
          +gt = V.Eval.whnf(f, env, Infer.res_ty(Infer.infer(f, env, ctx, g)), Nil{})
          +at = Infer.infer(f, env, ctx, a)
          Infer.res_of(
            A.Ans.and(
              A.Ans.and(
                Infer.pi_ans(gt),
                Infer.res_ans(at)),
              C.Conv.eq_in(f, env, ctx, Infer.res_ty(at), Infer.pi_dom(gt))),
            T.Term.inst(Infer.pi_bd(gt), a))
        case T.TLam{+ty, bd}:
          +bt = Infer.infer(f, env, Con{ty, ctx}, bd)
          Infer.res_of(Infer.res_ans(bt), T.TPi{ty, Infer.res_ty(bt)})
        case T.TPi{+ty, bd}:
          +tr = Infer.infer(f, env, ctx, ty)
          +br = Infer.infer(f, env, Con{ty, ctx}, bd)
          +ts = V.Eval.whnf(f, env, Infer.res_ty(tr), Nil{})
          +bs = V.Eval.whnf(f, env, Infer.res_ty(br), Nil{})
          Infer.res_of(
            A.Ans.and(
              A.Ans.and(Infer.res_ans(tr), Infer.res_ans(br)),
              A.Ans.and(
                Infer.sort_ans(ts),
                Infer.sort_ans(bs))),
            T.TSort{L.Level.mk_imax(Infer.sort_level(ts), Infer.sort_level(bs))})
        case T.TUnk{}:
          RUnk{}
        case T.TLet{ty, +v, bd}:
          +vt = Infer.infer(f, env, ctx, v)
          +br = Infer.infer(f, env, ctx, T.Term.inst(bd, v))
          Infer.res_of(
            A.Ans.and(
              A.Ans.and(Infer.res_ans(vt), Infer.res_ans(br)),
              C.Conv.eq_in(f, env, ctx, Infer.res_ty(vt), ty)),
            Infer.res_ty(br))
