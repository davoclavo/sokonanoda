# Definitional equality.
#
# The shape here is forced by Bend. A conversion checker normally reduces both
# sides, inspects the two results, and recurses on their subterms. In Bend that
# is two functions calling each other, which is mutual recursion, and a match
# cannot inspect the reduced terms because they are computed values.
#
# So this is a worklist. `Conv.eq` holds a queue of pairs still to be shown
# equal. It takes one pair, reduces both sides, and hands the two results to
# `Conv.classify`, which matches its own parameters and answers whether the
# pair fails, succeeds, or reduces to further pairs. Those go on the front of
# the queue. The queue empties exactly when the two terms are equal.
#
# This is also close to how a real conversion checker works, since a queue of
# constraints is what the recursion was standing in for.
#
# What is missing against the Lean kernel: eta for functions and structures,
# proof irrelevance, and the case split on imax in the level order. Proof
# irrelevance is the interesting omission, because it needs the type of a
# term, and that would make conversion and inference mutually recursive.

import Base
import ./Level.bend as L
import ./Term.bend as T
import ./Env.bend as E
import ./Eval.bend as V

# A pair of terms still to be shown equal.
type TPair is Data:
  MkPair{a: T.Term, b: T.Term}

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
      Bool.and(
        L.Level.eq(fuel, L.Level.norm(x), L.Level.norm(y)),
        Conv.levels_eq(fuel, xr, yr))
    case x y:
      False{}

# Classify one pair of terms, both already in weak head normal form. This
# matches its own parameters, which is what lets the recursion stay in one def.
def Conv.classify(+fuel: Nat, a: T.Term, b: T.Term) -> Step:
  match a b:
    case T.TVar{i} T.TVar{j}:
      Conv.step_of(Nat.is_eq(i, j))
    case T.TSort{x} T.TSort{y}:
      Conv.step_of(L.Level.eq(fuel, L.Level.norm(x), L.Level.norm(y)))
    case T.TConst{n1, l1} T.TConst{n2, l2}:
      Conv.step_of(Bool.and(Nat.is_eq(n1, n2), Conv.levels_eq(fuel, l1, l2)))
    case T.TApp{f1, a1} T.TApp{f2, a2}:
      SMore{[MkPair{f1, f2}, MkPair{a1, a2}]}
    case T.TLam{t1, b1} T.TLam{t2, b2}:
      SMore{[MkPair{t1, t2}, MkPair{b1, b2}]}
    case T.TPi{t1, b1} T.TPi{t2, b2}:
      SMore{[MkPair{t1, t2}, MkPair{b1, b2}]}
    case x y:
      SNo{}

# Reduce the two sides of a pair and classify them.
def Conv.classify_pair(+fuel: Nat, +env: List<&2, E.Decl>, p: TPair) -> Step:
  match p:
    case MkPair{a, b}:
      Conv.classify(
        fuel,
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

# Are these two terms definitionally equal?
def Conv.eq(+fuel: Nat, +env: List<&2, E.Decl>, a: T.Term, b: T.Term) -> Bool:
  Conv.eq_all(fuel, env, [MkPair{a, b}])
