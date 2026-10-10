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

# A pair of terms still to be shown equal, with the context they live in.
type TPair is Data:
  MkPair{ctx: List<&2, T.Term>, a: T.Term, b: T.Term}

# What one pair reduces to.
type Step is Data:
  SNo{}
  SYes{}
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

# True unless the step says no.
def Conv.step_ok(s: Step) -> Bool:
  match s:
    case SNo{}:
      False{}
    case SYes{}:
      True{}
    case SMore{ps}:
      True{}

# The further pairs a step asks for.
def Conv.step_more(s: Step) -> List<&2, TPair>:
  match s:
    case SNo{}:
      Nil{}
    case SYes{}:
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
    case x y:
      SNo{}

# Proof irrelevance: if the left side is a proof, the two sides are equal
# exactly when their types are, so the types go on the queue instead.
def Conv.irrel(
  +fuel: Nat, +env: List<&2, E.Decl>, +ctx: List<&2, T.Term>, +a: T.Term, +b: T.Term
) -> Step:
  Conv.pick_step(
    Bool.and(
      S.Shape.is_proof(fuel, env, ctx, a),
      S.Shape.ok(S.Shape.infer(fuel, env, ctx, b))),
    SMore{[MkPair{
      ctx,
      S.Shape.ty(S.Shape.infer(fuel, env, ctx, a)),
      S.Shape.ty(S.Shape.infer(fuel, env, ctx, b))}]},
    Conv.structural(fuel, ctx, a, b))

# Reduce the two sides of a pair, then try proof irrelevance before taking
# them apart.
def Conv.classify_pair(+fuel: Nat, +env: List<&2, E.Decl>, p: TPair) -> Step:
  match p:
    case MkPair{+ctx, a, b}:
      Conv.irrel(
        fuel,
        env,
        ctx,
        V.Eval.whnf(fuel, env, a, Nil{}),
        V.Eval.whnf(fuel, env, b, Nil{}))

# Work the queue. It empties exactly when every pair in it is equal.
def Conv.eq_all(+fuel: Nat, +env: List<&2, E.Decl>, work: List<&2, TPair>) -> Bool:
  match fuel:
    case 0n:
      False{}
    case 1n+f:
      match work:
        case Nil{}:
          True{}
        case Con{p, rest}:
          +st = Conv.classify_pair(f, env, p)
          Conv.pick_b(
            Conv.step_ok(st),
            Conv.eq_all(f, env, List.append(&2, TPair, Conv.step_more(st), rest)),
            False{})

# Are these two terms definitionally equal in the given context?
def Conv.eq_in(
  +fuel: Nat, +env: List<&2, E.Decl>, ctx: List<&2, T.Term>, a: T.Term, b: T.Term
) -> Bool:
  Conv.eq_all(fuel, env, [MkPair{ctx, a, b}])

# Are these two closed terms definitionally equal?
def Conv.eq(+fuel: Nat, +env: List<&2, E.Decl>, a: T.Term, b: T.Term) -> Bool:
  Conv.eq_in(fuel, env, Nil{}, a, b)
