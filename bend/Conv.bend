# Definitional equality.
#
# The shape here is forced by Bend. A conversion checker normally reduces both
# sides, inspects the two results, and recurses on their subterms. In Bend that
# is two functions calling each other, which is mutual recursion, and a match
# cannot inspect the reduced terms because they are computed values.
#
# So this is a worklist. `Conv.eq_all` holds a queue of pairs still to be shown
# equal. It takes one pair, reduces both sides, and hands the two results to
# `Conv.classify`, which matches its own parameters and answers whether the
# pair fails, succeeds, or reduces to further pairs. Those go on the front of
# the queue. The queue empties exactly when the two terms are equal.
#
# A pair carries its own local context, because a pair pushed from under a
# binder is open: its terms mention the binder. Proof irrelevance needs the
# type of each side, and a type cannot be found without that context. The
# arena's `107_proofIrrelevanceUnderBinder` is the test that says so.
#
# Proof irrelevance is tried before the two sides are taken apart. Two proofs
# of one proposition are equal whatever they look like, and once an
# application has been split into its function and its argument the chance is
# gone: `f (h a)` and `f (h b)` decompose to `a` against `b`, which no rule
# can settle.
#
# What is missing against the Lean kernel: eta for functions and structures,
# and the case split on an imax whose right side is a bare parameter.

import Base
import ./Level.bend as L
import ./Term.bend as T
import ./Env.bend as E
import ./Eval.bend as V
import ./Shape.bend as S
import ./Ans.bend as A

# A pair of terms still to be shown equal, with the context they live in.
type TPair is Data:
  MkPair{ctx: List<&2, T.Term>, a: T.Term, b: T.Term}

# What one pair reduces to.
type Step is Data:
  SNo{}
  SYes{}
  SUnk{}
  SMore{ps: List<&2, TPair>}

# Choose between two Bools on a computed Bool.
def Conv.pick_b(b: Bool, x: Bool, y: Bool) -> Bool:
  match b:
    case True{}:
      x
    case False{}:
      y

# Choose between two steps on a computed Bool.
def Conv.pick_step(b: Bool, x: Step, y: Step) -> Step:
  match b:
    case True{}:
      x
    case False{}:
      y

# What this step says on its own, before its further pairs are worked.
def Conv.step_ans(s: Step) -> A.Ans:
  match s:
    case SNo{}:
      A.ANo{}
    case SYes{}:
      A.AYes{}
    case SUnk{}:
      A.AUnk{}
    case SMore{ps}:
      A.AYes{}

# The further pairs a step asks for.
def Conv.step_more(s: Step) -> List<&2, TPair>:
  match s:
    case SNo{}:
      Nil{}
    case SYes{}:
      Nil{}
    case SUnk{}:
      Nil{}
    case SMore{ps}:
      ps

# A yes or no step from a Bool.
def Conv.step_of(b: Bool) -> Step:
  match b:
    case True{}:
      SYes{}
    case False{}:
      SNo{}

# Compare two lists of levels pairwise.
def Conv.levels_eq(+fuel: Nat, xs: List<&2, L.Level>, ys: List<&2, L.Level>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xr} Con{y, yr}:
      Bool.and(L.Level.eq(fuel, x, y), Conv.levels_eq(fuel, xr, yr))
    case x y:
      False{}

# Take the two sides apart. Both are already in weak head normal form. A pair
# pushed from under a binder carries the extended context.
#
# The two mixed lambda cases are eta for functions: `f` and `fun x => f x` are
# the same function, so a lambda against anything else goes under the binder
# and compares the body with the other side applied to the new variable. The
# other side is lifted, because it was written one scope out.
def Conv.structural(
  +fuel: Nat, +ctx: List<&2, T.Term>, a: T.Term, b: T.Term
) -> Step:
  match a b:
    case T.TVar{i} T.TVar{j}:
      Conv.step_of(Nat.is_eq(i, j))
    case T.TSort{x} T.TSort{y}:
      Conv.step_of(L.Level.eq(fuel, x, y))
    case T.TConst{n1, l1} T.TConst{n2, l2}:
      Conv.step_of(Bool.and(Nat.is_eq(n1, n2), Conv.levels_eq(fuel, l1, l2)))
    case T.TApp{f1, a1} T.TApp{f2, a2}:
      SMore{[MkPair{ctx, f1, f2}, MkPair{ctx, a1, a2}]}
    case T.TLam{+t1, b1} T.TLam{t2, b2}:
      SMore{[MkPair{ctx, t1, t2}, MkPair{Con{t1, ctx}, b1, b2}]}
    case T.TPi{+t1, b1} T.TPi{t2, b2}:
      SMore{[MkPair{ctx, t1, t2}, MkPair{Con{t1, ctx}, b1, b2}]}
    case T.TLam{+t1, b1} y:
      SMore{[MkPair{Con{t1, ctx}, b1, T.TApp{T.Term.lift(y, 1n, 0n), T.TVar{0n}}}]}
    case x T.TLam{+t2, b2}:
      SMore{[MkPair{Con{t2, ctx}, T.TApp{T.Term.lift(x, 1n, 0n), T.TVar{0n}}, b2}]}
    case T.TUnk{} y:
      SUnk{}
    case x T.TUnk{}:
      SUnk{}
    case x y:
      SNo{}

# Could this term be a proof? A sort and a pi are types, and the type of a
# type is never `Prop`, so neither can ever be a proof. The test is syntactic
# and costs nothing, which matters: without it every pair on the queue pays
# for an inference pass, and the recursion-heavy tests do not finish.
def Conv.maybe_proof(t: T.Term) -> Bool:
  match t:
    case T.TSort{l}:
      False{}
    case T.TPi{ty, bd}:
      False{}
    case x:
      True{}

# The head of an application.
def Conv.head(t: T.Term) -> T.Term:
  match t:
    case T.TApp{f, a}:
      Conv.head(f)
    case x:
      x

# The name a head names, or zero.
def Conv.head_name(t: T.Term) -> Nat:
  match t:
    case T.TConst{n, ls}:
      n
    case x:
      0n

# Does this declaration describe a unit type?
def Conv.unit_of(+env: List<&2, E.Decl>, +d: E.Decl) -> Bool:
  Bool.and(
    Bool.and(E.Decl.is_ind(d), Nat.is_eq(E.Decl.ind_ni(d), 0n)),
    Bool.and(
      E.Decl.is_one(E.Decl.ind_ctors(d)),
      Nat.is_eq(
        E.Decl.ctor_nf(
          E.Lookup.get(E.Env.find(env, E.Decl.only(E.Decl.ind_ctors(d))))),
        0n)))

# Is this type a unit: an inductive with no indices and exactly one
# constructor that takes no fields?
#
# Every element of such a type is that constructor, so any two of them are
# equal. This is eta for a structure with no fields, and it is what settles
# the arena's `unitEta` tests. The general structure rule, where an element
# equals its constructor applied to its own projections, needs projections and
# is not here.
def Conv.is_unit(+env: List<&2, E.Decl>, +t: T.Term) -> Bool:
  Conv.unit_of(env, E.Lookup.get(E.Env.find(env, Conv.head_name(Conv.head(t)))))

# Try proof irrelevance in earnest, now that it is worth the inference.
def Conv.irrel_go(
  +fuel: Nat, +env: List<&2, E.Decl>, +ctx: List<&2, T.Term>, +a: T.Term, +b: T.Term
) -> Step:
  +ra = S.Shape.infer(fuel, env, ctx, a)
  +rb = S.Shape.infer(fuel, env, ctx, b)
  Conv.pick_step(
    Bool.and(
      Bool.and(S.Shape.ok(ra), S.Shape.ok(rb)),
      Bool.or(
        S.Shape.prop_sort(fuel, env, ctx, S.Shape.ty(ra)),
        Conv.is_unit(
          env,
          V.Eval.whnf(fuel, env, S.Shape.ty(ra), Nil{})))),
    SMore{[MkPair{ctx, S.Shape.ty(ra), S.Shape.ty(rb)}]},
    Conv.structural(fuel, ctx, a, b))

# Two terms are equal when their types are, in two cases: the type is a
# proposition, which is proof irrelevance, or the type is a unit, which is eta
# for a structure with no fields. Both put the two types on the queue instead
# of the two terms.
#
# The two types are inferred once and bound, not inferred again for each use.
def Conv.irrel(
  +fuel: Nat, +env: List<&2, E.Decl>, +ctx: List<&2, T.Term>, +a: T.Term, +b: T.Term
) -> Step:
  Conv.pick_step(
    Bool.and(Conv.maybe_proof(a), Conv.maybe_proof(b)),
    Conv.irrel_go(fuel, env, ctx, a, b),
    Conv.structural(fuel, ctx, a, b))

# Choose between two terms on a computed Bool.
def Conv.pick_t(b: Bool, x: T.Term, y: T.Term) -> T.Term:
  match b:
    case True{}:
      x
    case False{}:
      y

# K-like reduction
# ----------------
#
# A recursor whose inductive has one constructor that takes no fields may fire
# even when the major premise is not written as that constructor, because that
# is the only thing it could be. The Lean kernel reaches this two ways, as the
# K rule for something like `Eq` and as eta for a structure for something like
# a one-element type, and both land in the same place here.
#
# The flag the export carries is not the condition. The arena's
# `075_typeSingletonRecReduction` has `k` unset and still reduces, because its
# inductive is a structure; its `101_ruleKAcc` has one constructor that does
# carry data, so it must not reduce. What decides it is the shape of the
# constructor and the type check below.
#
# It may not fire unguarded. The Lean kernel infers the major premise's type
# first and requires it to be an application of the recursor's own inductive;
# without that, the rule fires on a premise of the wrong type and the arena's
# `100_ruleKbad` passes. Reduction cannot infer a type, because that would
# make reduction and inference call each other, which Bend forbids.
#
# So the rule lives here instead. Conversion already depends on `Shape`, so it
# can ask for a type, and it already depends on `Eval`, so it can reduce the
# result. The premise is replaced by the constructor applied to the type's
# parameters, and ordinary iota does the rest.

# The arguments of an application, in order.
def Conv.args(t: T.Term) -> List<&2, T.Term>:
  V.Eval.spine(t, Nil{})

# The level arguments of a head constant, or none.
def Conv.head_levels(t: T.Term) -> List<&2, L.Level>:
  match t:
    case T.TConst{n, ls}:
      ls
    case x:
      Nil{}

# Replace the `i`-th argument of a list.
def Conv.put(+xs: List<&2, T.Term>, +i: Nat, +v: T.Term) -> List<&2, T.Term>:
  List.append(&2, T.Term,
    V.Eval.take(xs, i),
    Con{v, V.Eval.drop(xs, 1n+i)})

# Does this type head the recursor's own inductive?
def Conv.k_type_ok(+d: E.Decl, +ty: T.Term) -> Bool:
  Nat.is_eq(Conv.head_name(Conv.head(ty)), E.Decl.only(E.Decl.rec_inds(d)))

# The constructor, applied to the parameters the major premise's type carries.
def Conv.k_ctor(+env: List<&2, E.Decl>, +d: E.Decl, +ty: T.Term) -> T.Term:
  V.Eval.rebuild(
    V.Eval.take(Conv.args(ty), E.Decl.rec_np(d)),
    T.TConst{
      E.Decl.only(
        E.Decl.ind_ctors(
          E.Lookup.get(E.Env.find(env, E.Decl.only(E.Decl.rec_inds(d)))))),
      Conv.head_levels(Conv.head(ty))})

# Is putting the constructor in place of the major premise type correct?
#
# This is the guard. The arena states the rule as "the recursor reduces even
# if the major argument is not a constructor, as long as replacing the major
# argument with a constructor is type correct", and the two tests are the two
# sides of it. With `h : true = true` the premise's type is `Eq Bool true
# true` and the constructor's is the same, so the rule fires. With `h : true =
# false` the premise's type is `Eq Bool true false` while the constructor's is
# still `Eq Bool true true`, so it must not. The comparison is syntactic,
# which tells those two apart and can only ever be too strict.
def Conv.k_fits(
  +fuel: Nat, +env: List<&2, E.Decl>, +ctx: List<&2, T.Term>,
  +d: E.Decl, +ty: T.Term
) -> Bool:
  T.Term.same(
    V.Eval.whnf(
      fuel, env,
      S.Shape.ty(S.Shape.infer(fuel, env, ctx, Conv.k_ctor(env, d, ty))),
      Nil{}),
    ty)

# Does this recursor's inductive have exactly one constructor, and does that
# constructor take no fields?
#
# No fields is what lets the constructor be written without projections. A
# constructor that carries data needs them, so `Acc`, whose one constructor
# does carry data, is left alone. That is the arena's `101_ruleKAcc`.
def Conv.k_single(+env: List<&2, E.Decl>, +d: E.Decl) -> Bool:
  Bool.and(
    E.Decl.is_one(
      E.Decl.ind_ctors(
        E.Lookup.get(E.Env.find(env, E.Decl.only(E.Decl.rec_inds(d)))))),
    Nat.is_eq(
      E.Decl.ctor_nf(
        E.Lookup.get(
          E.Env.find(
            env,
            E.Decl.only(
              E.Decl.ind_ctors(
                E.Lookup.get(
                  E.Env.find(env, E.Decl.only(E.Decl.rec_inds(d))))))))),
      0n))

# Is the K rule allowed on this application? The declaration must be a
# recursor with the flag set and enough arguments, its inductive must have one
# constructor, and the major premise's type must head that inductive.
def Conv.k_ok(
  +fuel: Nat, +env: List<&2, E.Decl>, +ctx: List<&2, T.Term>,
  +d: E.Decl, +args: List<&2, T.Term>, +ty: T.Term
) -> Bool:
  Bool.and(
    Bool.and(
      E.Decl.is_rec(d),
      Nat.is_lt(V.Eval.major_idx(d), V.Eval.len(args, 0n))),
    Bool.and(
      Bool.and(Conv.k_single(env, d), Conv.k_type_ok(d, ty)),
      Conv.k_fits(fuel, env, ctx, d, ty)))

# The application with its major premise replaced by the constructor.
def Conv.k_rebuilt(
  +env: List<&2, E.Decl>, +d: E.Decl, +t: T.Term, +args: List<&2, T.Term>, +ty: T.Term
) -> T.Term:
  V.Eval.rebuild(
    Conv.put(args, V.Eval.major_idx(d), Conv.k_ctor(env, d, ty)),
    Conv.head(t))

# Fire it, or leave the term alone.
def Conv.k_go(
  +fuel: Nat, +env: List<&2, E.Decl>, +ctx: List<&2, T.Term>, +t: T.Term,
  +d: E.Decl, +args: List<&2, T.Term>, +ty: T.Term
) -> T.Term:
  Conv.pick_t(
    Conv.k_ok(fuel, env, ctx, d, args, ty),
    V.Eval.whnf(fuel, env, Conv.k_rebuilt(env, d, t, args, ty), Nil{}),
    t)

# Apply the K rule to a term already in weak head normal form, if it applies.
def Conv.k_fix(
  +fuel: Nat, +env: List<&2, E.Decl>, +ctx: List<&2, T.Term>, +t: T.Term
) -> T.Term:
  Conv.k_go(
    fuel, env, ctx, t,
    E.Lookup.get(E.Env.find(env, Conv.head_name(Conv.head(t)))),
    Conv.args(t),
    V.Eval.whnf(
      fuel, env,
      S.Shape.ty(
        S.Shape.infer(
          fuel, env, ctx,
          V.Eval.nth(
            Conv.args(t),
            V.Eval.major_idx(
              E.Lookup.get(E.Env.find(env, Conv.head_name(Conv.head(t)))))))),
      Nil{}))

# Reduce the two sides of a pair, then try proof irrelevance before taking
# them apart.
def Conv.classify_pair(+fuel: Nat, +env: List<&2, E.Decl>, p: TPair) -> Step:
  match p:
    case MkPair{+ctx, a, b}:
      Conv.irrel(
        fuel,
        env,
        ctx,
        Conv.k_fix(fuel, env, ctx, V.Eval.whnf(fuel, env, a, Nil{})),
        Conv.k_fix(fuel, env, ctx, V.Eval.whnf(fuel, env, b, Nil{})))

# Work the queue. It empties exactly when every pair in it is equal.
#
# A pair that settles the question does not stop the walk, because Bend
# forbids the two defs that would take. `Ans.and` does the work instead: a
# definite no anywhere is a rejection whatever the rest says, and not knowing
# one pair leaves the whole answer unknown unless some other pair is a
# definite no.
def Conv.eq_all(+fuel: Nat, +env: List<&2, E.Decl>, work: List<&2, TPair>) -> A.Ans:
  match fuel:
    case 0n:
      A.AUnk{}
    case 1n+f:
      match work:
        case Nil{}:
          A.AYes{}
        case Con{p, rest}:
          +st = Conv.classify_pair(f, env, p)
          A.Ans.and(
            Conv.step_ans(st),
            Conv.eq_all(f, env, List.append(&2, TPair, Conv.step_more(st), rest)))

# Are these two terms definitionally equal in the given context?
def Conv.eq_in(
  +fuel: Nat, +env: List<&2, E.Decl>, ctx: List<&2, T.Term>, a: T.Term, b: T.Term
) -> A.Ans:
  Conv.eq_all(fuel, env, [MkPair{ctx, a, b}])

# Are these two closed terms definitionally equal?
def Conv.eq(+fuel: Nat, +env: List<&2, E.Decl>, a: T.Term, b: T.Term) -> A.Ans:
  Conv.eq_in(fuel, env, Nil{}, a, b)
