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
