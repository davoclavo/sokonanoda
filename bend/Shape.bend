# The type of a term, without checking it.
#
# This is inference with every conversion check removed, which is what makes it
# useful: it does not depend on `Conv`, so `Conv` may depend on it. The Rust
# parent gets the same effect from one inferencer with an `InferOnly` flag, but
# Bend forbids two defs that call each other, so the two passes are two files.
#
# Proof irrelevance is why this exists. Two proofs of the same proposition are
# definitionally equal, and deciding that needs the type of each term, so
# conversion has to be able to ask for a type. Asking the checking inferencer
# would be a cycle.
#
# A term that reduction gave up on has no shape, so a guard that rests on one
# simply does not fire. That is safe: a guard only ever lets a rule apply.
#
# A shape is not a verdict. It answers the type a term would have if the term
# were well typed, and `RBad` when it cannot. Nothing here is a soundness
# claim, and `Infer` still does all of the checking.

import Base
import ./Level.bend as L
import ./Term.bend as T
import ./Env.bend as E
import ./Eval.bend as V

type Shp is Data:
  SOk{ty: T.Term}
  SBad{}

# A loose variable, so a failed shape looks like neither a sort nor a pi.
def Shape.dummy() -> T.Term:
  T.TVar{0n}

def Shape.ok(r: Shp) -> Bool:
  match r:
    case SOk{ty}:
      True{}
    case SBad{}:
      False{}

def Shape.ty(r: Shp) -> T.Term:
  match r:
    case SOk{ty}:
      ty
    case SBad{}:
      Shape.dummy()

def Shape.if_ok(b: Bool, ty: T.Term) -> Shp:
  match b:
    case True{}:
      SOk{ty}
    case False{}:
      SBad{}

def Shape.lift(r: Shp, +d: Nat) -> Shp:
  match r:
    case SOk{ty}:
      SOk{T.Term.lift(ty, d, 0n)}
    case SBad{}:
      SBad{}

def Shape.is_pi(t: T.Term) -> Bool:
  match t:
    case T.TPi{ty, bd}:
      True{}
    case x:
      False{}

def Shape.pi_dom(t: T.Term) -> T.Term:
  match t:
    case T.TPi{ty, bd}:
      ty
    case x:
      Shape.dummy()

def Shape.pi_bd(t: T.Term) -> T.Term:
  match t:
    case T.TPi{ty, bd}:
      bd
    case x:
      Shape.dummy()

def Shape.is_sort(t: T.Term) -> Bool:
  match t:
    case T.TSort{l}:
      True{}
    case x:
      False{}

def Shape.sort_level(t: T.Term) -> L.Level:
  match t:
    case T.TSort{l}:
      l
    case x:
      L.LZero{}

def Shape.ctx_nth(ctx: List<&2, T.Term>, i: Nat) -> Shp:
  match ctx:
    case Nil{}:
      SBad{}
    case Con{h, t}:
      match i:
        case 0n:
          SOk{h}
        case 1n+p:
          Shape.ctx_nth(t, p)

def Shape.const_type(lk: E.Lookup, +ls: List<&2, L.Level>) -> Shp:
  match lk:
    case E.LFound{d}:
      SOk{E.Decl.type_at(d, ls)}
    case E.LMissing{}:
      SBad{}

# Typing a projection
# -------------------
#
# The type of `s.idx` comes from the constructor's telescope. The structure's
# type gives the inductive and its parameters, the constructor's type is taken
# at those parameters, and then one binder is stepped over for each earlier
# field, with that field's own projection put in its place. The domain of the
# next binder is the answer.
#
# The structure's type is passed in rather than inferred here, because
# inferring it is the caller's job and Bend will not let these two call each
# other.

# Step over `i` binders, putting the j-th projection in place of each.
def Shape.proj_walk(
  +fuel: Nat, +env: List<&2, E.Decl>, i: Nat, +j: Nat, r: T.Term,
  +tn: Nat, +s: T.Term
) -> T.Term:
  match fuel:
    case 0n:
      T.TUnk{}
    case 1n+f:
      match i:
        case 0n:
          r
        case 1n+k:
          Shape.proj_walk(
            f, env, k, 1n+j,
            T.Term.inst(
              Shape.pi_bd(V.Eval.whnf(f, env, r, Nil{})),
              T.TProj{tn, j, s}),
            tn, s)

# Is this structure's type one this kernel can project from?
def Shape.proj_ok(+env: List<&2, E.Decl>, +sty: T.Term) -> Bool:
  Bool.and(
    E.Decl.is_ind(
      E.Lookup.get(E.Env.find(env, V.Eval.head_name(V.Eval.head(sty))))),
    E.Decl.is_one(
      E.Decl.ind_ctors(
        E.Lookup.get(E.Env.find(env, V.Eval.head_name(V.Eval.head(sty)))))))

# Put the structure's parameters into the constructor's type.
#
# This has to instantiate, one binder at a time, and not apply. A pi applied
# to an argument is not a beta-redex, so reduction leaves it exactly as it is
# and the next step looks for a binder and finds an application. A structure
# with no parameters hides the mistake completely, which is why the first
# hand-written test passed and every real one failed.
def Shape.proj_params(
  +fuel: Nat, +env: List<&2, E.Decl>, ps: List<&2, T.Term>, r: T.Term
) -> T.Term:
  match fuel:
    case 0n:
      T.TUnk{}
    case 1n+f:
      match ps:
        case Nil{}:
          r
        case Con{h, t}:
          Shape.proj_params(
            f, env, t,
            T.Term.inst(Shape.pi_bd(V.Eval.whnf(f, env, r, Nil{})), h))

# The constructor's type, at the structure's parameters.
def Shape.proj_base(+fuel: Nat, +env: List<&2, E.Decl>, +sty: T.Term) -> T.Term:
  Shape.proj_params(
    fuel, env,
    V.Eval.take(
      V.Eval.spine(sty, Nil{}),
      E.Decl.ind_np(
        E.Lookup.get(E.Env.find(env, V.Eval.head_name(V.Eval.head(sty)))))),
    E.Decl.type_at(
      E.Lookup.get(
        E.Env.find(
          env,
          E.Decl.only(
            E.Decl.ind_ctors(
              E.Lookup.get(
                E.Env.find(env, V.Eval.head_name(V.Eval.head(sty)))))))),
      V.Eval.head_levels(V.Eval.head(sty))))

# The type of `s.idx`, given the structure's own type.
def Shape.proj_from(
  +fuel: Nat, +env: List<&2, E.Decl>, +sty: T.Term, +tn: Nat, +idx: Nat, +s: T.Term
) -> Shp:
  Shape.if_ok(
    Bool.and(
      Shape.proj_ok(env, sty),
      Shape.is_pi(
        V.Eval.whnf(
          fuel, env,
          Shape.proj_walk(fuel, env, idx, 0n, Shape.proj_base(fuel, env, sty), tn, s),
          Nil{}))),
    Shape.pi_dom(
      V.Eval.whnf(
        fuel, env,
        Shape.proj_walk(fuel, env, idx, 0n, Shape.proj_base(fuel, env, sty), tn, s),
        Nil{})))

# The type `t` would have in the context `ctx`.
def Shape.infer(+fuel: Nat, +env: List<&2, E.Decl>, +ctx: List<&2, T.Term>, t: T.Term) -> Shp:
  match fuel:
    case 0n:
      SBad{}
    case 1n+f:
      match t:
        case T.TVar{+i}:
          Shape.lift(Shape.ctx_nth(ctx, i), 1n+i)
        case T.TSort{l}:
          SOk{T.TSort{L.LSucc{l}}}
        case T.TConst{n, +ls}:
          Shape.const_type(E.Env.find(env, n), ls)
        case T.TApp{g, +a}:
          +gt = V.Eval.whnf(f, env, Shape.ty(Shape.infer(f, env, ctx, g)), Nil{})
          Shape.if_ok(Shape.is_pi(gt), T.Term.inst(Shape.pi_bd(gt), a))
        case T.TLam{+ty, bd}:
          +bt = Shape.infer(f, env, Con{ty, ctx}, bd)
          Shape.if_ok(Shape.ok(bt), T.TPi{ty, Shape.ty(bt)})
        case T.TPi{+ty, bd}:
          +tr = Shape.infer(f, env, ctx, ty)
          +br = Shape.infer(f, env, Con{ty, ctx}, bd)
          +ts = V.Eval.whnf(f, env, Shape.ty(tr), Nil{})
          +bs = V.Eval.whnf(f, env, Shape.ty(br), Nil{})
          Shape.if_ok(
            Bool.and(
              Bool.and(Shape.ok(tr), Shape.ok(br)),
              Bool.and(Shape.is_sort(ts), Shape.is_sort(bs))),
            T.TSort{L.Level.mk_imax(Shape.sort_level(ts), Shape.sort_level(bs))})
        case T.TLet{ty, +v, bd}:
          Shape.infer(f, env, ctx, T.Term.inst(bd, v))
        case T.TNat{+v, +nm, +zr, +sc}:
          SOk{T.TConst{nm, Nil{}}}
        case T.TUnk{}:
          SBad{}
        case T.TProj{tn, +idx, +st}:
          Shape.proj_from(
            f, env,
            V.Eval.whnf(f, env, Shape.ty(Shape.infer(f, env, ctx, st)), Nil{}),
            tn, idx, st)

# Does the type `ty` itself have type `Sort 0`?
def Shape.prop_sort(+fuel: Nat, +env: List<&2, E.Decl>, +ctx: List<&2, T.Term>, ty: T.Term) -> Bool:
  +r = Shape.infer(fuel, env, ctx, ty)
  Bool.and(
    Shape.ok(r),
    L.Level.is_zero(
      Shape.sort_level(V.Eval.whnf(fuel, env, Shape.ty(r), Nil{}))))

# Is `t` a proof, that is, does its type live in `Prop`?
def Shape.is_proof(+fuel: Nat, +env: List<&2, E.Decl>, +ctx: List<&2, T.Term>, t: T.Term) -> Bool:
  +r = Shape.infer(fuel, env, ctx, t)
  Bool.and(
    Shape.ok(r),
    Shape.prop_sort(fuel, env, ctx, Shape.ty(r)))
