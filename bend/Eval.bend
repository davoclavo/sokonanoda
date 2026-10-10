# Weak head normal form: beta, delta and zeta reduction.
#
# This is one self-recursive def with an explicit argument spine, because Bend
# forbids mutual recursion. The usual shape, where `whnf` reduces the head and
# a second function inspects the result, would be two functions calling each
# other. Carrying the arguments in `sp` instead keeps everything in one def.
#
# `fuel` strictly decreases on every recursive call, which is how this passes
# Bend's termination check. A kernel's whnf genuinely does not terminate on
# every input, so the fuel is not a formality: it is the honest statement that
# this function answers within a budget. When the budget runs out it rebuilds
# the term unreduced, which is sound for a checker that then rejects.
#
# Every test on a computed value goes through a helper that matches its own
# parameter, since a Bend match may not scrutinize a computed value.

import Base
import ./Level.bend as L
import ./Term.bend as T
import ./Env.bend as E

# Choose between two terms on a computed Bool.
def Eval.pick_t(b: Bool, x: T.Term, y: T.Term) -> T.Term:
  match b:
    case True{}:
      x
    case False{}:
      y

# Apply a term to a spine of arguments, in application order. The spine comes
# first because Bend needs the shrinking parameter in that position.
def Eval.rebuild(sp: List<&2, T.Term>, t: T.Term) -> T.Term:
  match sp:
    case Nil{}:
      t
    case Con{h, r}:
      Eval.rebuild(r, T.TApp{t, h})

# Unwrap a value, or answer the default.
def Eval.val_or(m: Maybe<&2, T.Term>, dflt: T.Term) -> T.Term:
  match m:
    case Some{v}:
      v
    case None{}:
      dflt

# True when a lookup found a declaration that has a value.
def Eval.is_def(lk: E.Lookup) -> Bool:
  match lk:
    case E.LFound{d}:
      E.Decl.is_def(d)
    case E.LMissing{}:
      False{}

# The value a lookup unfolds to, with its level parameters replaced, or the
# default when there is nothing to unfold.
def Eval.unfold_of(lk: E.Lookup, +ls: List<&2, L.Level>, dflt: T.Term) -> T.Term:
  match lk:
    case E.LFound{d}:
      Eval.val_or(E.Decl.value_at(d, ls), dflt)
    case E.LMissing{}:
      dflt

# Reduce `t` applied to `sp` to weak head normal form.
def Eval.whnf(+fuel: Nat, +env: List<&2, E.Decl>, t: T.Term, +sp: List<&2, T.Term>) -> T.Term:
  match fuel:
    case 0n:
      Eval.rebuild(sp, t)
    case 1n+f:
      match t:
        case T.TVar{i}:
          Eval.rebuild(sp, T.TVar{i})
        case T.TSort{l}:
          Eval.rebuild(sp, T.TSort{l})
        case T.TConst{+n, +ls}:
          Eval.pick_t(
            Eval.is_def(E.Env.find(env, n)),
            Eval.whnf(f, env, Eval.unfold_of(E.Env.find(env, n), ls, T.TConst{n, ls}), sp),
            Eval.rebuild(sp, T.TConst{n, ls}))
        case T.TApp{g, a}:
          Eval.whnf(f, env, g, Con{a, sp})
        case T.TLam{ty, bd}:
          match sp:
            case Nil{}:
              T.TLam{ty, bd}
            case Con{a, rest}:
              Eval.whnf(f, env, T.Term.inst(bd, a), rest)
        case T.TPi{ty, bd}:
          Eval.rebuild(sp, T.TPi{ty, bd})
        case T.TLet{ty, v, bd}:
          Eval.whnf(f, env, T.Term.inst(bd, v), sp)
