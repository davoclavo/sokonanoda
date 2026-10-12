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
import ./Vconv.bend as X
import ./Ans.bend as A
import ./Shape.bend as S

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
    case T.TUnk{}:
      T.TUnk{}
    case x:
      Infer.dummy()

# A pi's body, or the dummy. Guarded by `is_pi`.
#
# A term reduction gave up on answers with itself, not with the dummy. The
# dummy is a loose variable, and a loose variable converts with nothing, so a
# definite no comes back where the honest answer is that the budget ran out.
# That is what made the arena's `beta-ladder` reject: its type is two thousand
# lambdas deep, inference ran out, and the dummy turned a shortage into a
# rejection.
def Infer.pi_bd(t: T.Term) -> T.Term:
  match t:
    case T.TPi{ty, bd}:
      bd
    case T.TUnk{}:
      T.TUnk{}
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
def Infer.proj_walk(
  +fuel: Nat, +env: E.DTable, i: Nat, +j: Nat, r: T.Term,
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
          Infer.proj_walk(
            f, env, k, 1n+j,
            T.Term.inst(
              Infer.pi_bd(V.Eval.whnf(f, env, r, Nil{})),
              T.TProj{tn, j, s}),
            tn, s)

# Is this structure's type one this kernel can project from?
# The answer when the subject's type could not be inferred at all.
#
# `Infer.proj_ok` is a `Bool`, and a `Bool` has no way to say that the
# question was not reached. Reading its no as a rejection is a wrong answer:
# `grind-ring-5` rejects at a small budget and declines at a larger one, and
# this is one of the two places that turned the budget into a verdict.
def Infer.proj_unk(unk: Bool, ok: Bool) -> A.Ans:
  match unk:
    case True{}:
      A.AUnk{}
    case False{}:
      A.Ans.of(ok)

# Is this structure's type one this kernel can project from, and is it the
# structure the node says it is?
#
# The node carries a type name of its own and the kernel reads the field from
# the inferred type, so a name that does not match is not read at all. It is
# still wrong, and it is not harmless: the name goes into the term, where
# `Conv.proj_step` compares two projections by it and reduction reads it. The
# reference kernel rejects the mismatch and so does this.
def Infer.proj_ok(+env: E.DTable, +sty: T.Term, +tn: Nat) -> Bool:
  Bool.and(
    Nat.is_eq(tn, V.Eval.head_name(V.Eval.head(sty))),
    Bool.and(
      E.Decl.is_ind(
        E.Lookup.get(E.Env.find(env, V.Eval.head_name(V.Eval.head(sty))))),
      E.Decl.is_one(
        E.Decl.ind_ctors(
          E.Lookup.get(
            E.Env.find(env, V.Eval.head_name(V.Eval.head(sty))))))))

# Put the structure's parameters into the constructor's type.
#
# This has to instantiate, one binder at a time, and not apply. A pi applied
# to an argument is not a beta-redex, so reduction leaves it exactly as it is
# and the next step looks for a binder and finds an application. A structure
# with no parameters hides the mistake completely, which is why the first
# hand-written test passed and every real one failed.
def Infer.proj_params(
  +fuel: Nat, +env: E.DTable, ps: List<&2, T.Term>, r: T.Term
) -> T.Term:
  match fuel:
    case 0n:
      T.TUnk{}
    case 1n+f:
      match ps:
        case Nil{}:
          r
        case Con{h, t}:
          Infer.proj_params(
            f, env, t,
            T.Term.inst(Infer.pi_bd(V.Eval.whnf(f, env, r, Nil{})), h))

# The constructor's type, at the structure's parameters.
def Infer.proj_base(+fuel: Nat, +env: E.DTable, +sty: T.Term) -> T.Term:
  Infer.proj_params(
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

# A projection out of a proposition may not produce data.
#
# Lean forbids it: a structure in `Prop` has one inhabitant as far as the
# kernel can tell, so reading a field of some other sort out of one is large
# elimination, and that is unsound. The arena attacks it four times, with
# `projProp2` through `projProp6`, all on one structure in `Prop` that
# carries six fields.
#
# The test on the structure answers no when it cannot tell, so a shape this
# kernel does not recognise loses the check rather than rejecting a
# projection that is in fact allowed.

# Is this term a sort at level zero?
def Infer.sort_is_prop(t: T.Term) -> Bool:
  match t:
    case T.TSort{l}:
      L.Level.is_zero(l)
    case x:
      False{}

# Is the structure being projected from a proposition? Its own declaration
# states the sort, so no context is needed to read it.
def Infer.ind_is_prop(+env: E.DTable, +sty: T.Term) -> Bool:
  Infer.sort_is_prop(
    T.Term.pi_skip(
      Nat.add(
        E.Decl.ind_np(
          E.Lookup.get(E.Env.find(env, V.Eval.head_name(V.Eval.head(sty))))),
        E.Decl.ind_ni(
          E.Lookup.get(E.Env.find(env, V.Eval.head_name(V.Eval.head(sty)))))),
      E.Decl.ind_ty(
        E.Lookup.get(E.Env.find(env, V.Eval.head_name(V.Eval.head(sty)))))))

# The term whose sort the rule needs, or a sort when there is nothing to
# check. Inferring a sort costs nothing, and that is what every projection
# out of something that is not a proposition pays.
def Infer.prop_subject(b: Bool, +fty: T.Term) -> T.Term:
  match b:
    case True{}:
      fty
    case False{}:
      T.TSort{L.LZero{}}

# Is this term a proposition? Not known when its type cannot be found.
#
# This asks `Shape.infer` rather than `Infer.infer`, because a def may only
# call one declared above it and `Infer.infer` is below. `Shape` is the small
# inference that exists for side questions of exactly this kind.
def Infer.sort_prop_ans(w: T.Term) -> A.Ans:
  match w:
    case T.TSort{l}:
      A.Ans.of(L.Level.is_zero(l))
    case T.TUnk{}:
      A.AUnk{}
    case o:
      A.ANo{}

def Infer.prop_of(ok: Bool, w: T.Term) -> A.Ans:
  match ok:
    case False{}:
      A.AUnk{}
    case True{}:
      Infer.sort_prop_ans(w)

def Infer.is_prop_ans(
  +fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>, +t: T.Term
) -> A.Ans:
  +r : S.Shp = S.Shape.infer(fuel, env, ctx, t)
  Infer.prop_of(
    S.Shape.ok(r), V.Eval.whnf(fuel, env, S.Shape.ty(r), Nil{}))

# Given the sort of the field, is the projection allowed? Not knowing the
# sort stays not knowing.
def Infer.prop_ok(b: Bool, +ps: T.Term) -> A.Ans:
  match b:
    case True{}:
      Infer.sort_prop_ans(ps)
    case False{}:
      A.AYes{}

# Must this field be a proof, and is it one?
#
# Only when the structure is a proposition and the rest of the telescope uses
# the field, because then the walk has to form that field's own projection,
# and a projection out of a proposition may not produce data. The test is a
# match and not a disjunction, so a structure that is not a proposition pays
# for no inference at all.
def Infer.prefix_field_ans(
  check: Bool, +fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>,
  +dom: T.Term
) -> A.Ans:
  match check:
    case False{}:
      A.AYes{}
    case True{}:
      Infer.is_prop_ans(fuel, env, ctx, dom)

# Step over the earlier fields again, and ask of each whether it is allowed.
#
# This mirrors `Infer.proj_walk`, which carries the type along and cannot
# carry an answer with it. The arena's `projProp6` is the test: its field five
# is a proposition and the projection is still wrong, because field three is
# data and field four uses it.
def Infer.proj_prefix_ans(
  +fuel: Nat, +env: E.DTable, i: Nat, +j: Nat, r: T.Term,
  +tn: Nat, +s: T.Term, +isprop: Bool, +ctx: List<&2, T.Term>
) -> A.Ans:
  match fuel:
    case 0n:
      A.AUnk{}
    case 1n+f:
      match i:
        case 0n:
          A.AYes{}
        case 1n+k:
          +w : T.Term = V.Eval.whnf(f, env, r, Nil{})
          A.Ans.and(
            Infer.prefix_field_ans(
              Bool.and(isprop, T.Term.has_bvar(Infer.pi_bd(w), 0n)),
              f, env, ctx, Infer.pi_dom(w)),
            Infer.proj_prefix_ans(
              f, env, k, 1n+j,
              T.Term.inst(Infer.pi_bd(w), T.TProj{tn, j, s}),
              tn, s, isprop, ctx))

# The type of `s.idx`, given the structure's own type.
#
# A structure type that reduction gave up on answers that it is not known,
# and nothing is computed from it. Conjoining an unknown with a verdict read
# off the same unknown is how a budget becomes a rejection: `A.Ans.and` lets
# a definite no win over an unknown, which is right in general and wrong when
# the no was worked out from a term nobody could read. The arena's
# `grind-ring-5` projects the second field of an `And` whose subject is large
# enough that inference runs out, and it rejected at a small budget and
# declined at a larger one for that reason alone.
def Infer.proj_go(
  +fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>, +sty: T.Term,
  +tn: Nat, +idx: Nat, +s: T.Term
) -> Res:
  +w = V.Eval.whnf(
    fuel, env,
    Infer.proj_walk(fuel, env, idx, 0n, Infer.proj_base(fuel, env, sty), tn, s),
    Nil{})
  Infer.res_of(
    A.Ans.and(
      A.Ans.and(
        Infer.proj_unk(
          T.Term.is_unk(sty), Infer.proj_ok(env, sty, tn)),
        Infer.pi_ans(w)),
      Infer.proj_prefix_ans(
        fuel, env, idx, 0n, Infer.proj_base(fuel, env, sty), tn, s,
        Infer.ind_is_prop(env, sty), ctx)),
    Infer.pi_dom(w))

def Infer.proj_pick(
  unk: Bool, +fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>,
  +sty: T.Term, +tn: Nat, +idx: Nat, +s: T.Term
) -> Res:
  match unk:
    case True{}:
      RUnk{}
    case False{}:
      Infer.proj_go(fuel, env, ctx, sty, tn, idx, s)

def Infer.proj_from(
  +fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>, +sty: T.Term,
  +tn: Nat, +idx: Nat, +s: T.Term
) -> Res:
  Infer.proj_pick(
    T.Term.is_unk(sty), fuel, env, ctx, sty, tn, idx, s)

# Infer the type of `t` in the context `ctx`.
def Infer.infer(+fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>, t: T.Term) -> Res:
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
            X.Vconv.eq_unless_no(
              A.Ans.and(
                Infer.pi_ans(gt),
                Infer.res_ans(at)),
              f, env, ctx, Infer.res_ty(at), Infer.pi_dom(gt)),
            T.Term.inst_at(E.Env.tab(env), Infer.pi_bd(gt), a))
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
        case T.TNat{+v, +nm, +zr, +sc}:
          ROk{T.TConst{nm, Nil{}}}
        case T.TUnk{}:
          RUnk{}
        case T.TRef{+i, +k, m}:
          # A reference is resolved against the table and asked again. What
          # the table holds has references for its own children, so this costs
          # one step however large the expression it names.
          Infer.infer(f, env, ctx, E.Env.expr_at(env, i, k))
        case T.TProj{tn, +idx, +st}:
          +sty = V.Eval.whnf(
            f, env, Infer.res_ty(Infer.infer(f, env, ctx, st)), Nil{})
          +fr = Infer.proj_from(f, env, ctx, sty, tn, idx, st)
          +ps = V.Eval.whnf(
            f, env,
            Infer.res_ty(
              Infer.infer(
                f, env, ctx,
                Infer.prop_subject(
                  Infer.ind_is_prop(env, sty), Infer.res_ty(fr)))),
            Nil{})
          Infer.res_of(
            A.Ans.and(
              Infer.res_ans(fr),
              Infer.prop_ok(Infer.ind_is_prop(env, sty), ps)),
            Infer.res_ty(fr))
        case T.TLet{ty, +v, bd}:
          +vt = Infer.infer(f, env, ctx, v)
          +br = Infer.infer(f, env, ctx, T.Term.inst_at(E.Env.tab(env), bd, v))
          Infer.res_of(
            X.Vconv.eq_unless_no(
              A.Ans.and(Infer.res_ans(vt), Infer.res_ans(br)),
              f, env, ctx, Infer.res_ty(vt), ty),
            Infer.res_ty(br))
