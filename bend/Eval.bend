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
# this function answers within a budget.
#
# When the budget runs out it hands back `TUnk` rather than the term
# unreduced. The difference matters. An unreduced term looks like an answer,
# and conversion then compares it with something and says they differ, so the
# declaration is rejected for want of budget. `TUnk` says what happened, and
# everything that meets it answers that it does not know.
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

# Iota reduction
# --------------
#
# A recursor applied to a constructor computes. Its arguments come in the
# order the declaration states: parameters, motives, minor premises, indices,
# then the major premise. When the major premise reduces to a constructor,
# the rule for that constructor replaces the whole application.
#
# The right-hand side of a rule expects the recursor's parameters, motives and
# minor premises, then the constructor's fields, which are its arguments past
# its parameters. Whatever followed the major premise is applied after that.

# The position of the major premise among a recursor's arguments.
def Eval.major_idx(+d: E.Decl) -> Nat:
  Nat.add(
    Nat.add(E.Decl.rec_np(d), E.Decl.rec_nm(d)),
    Nat.add(E.Decl.rec_nmin(d), E.Decl.rec_ni(d)))

# How long is this list?
def Eval.len(xs: List<&2, T.Term>, +acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      Eval.len(t, 1n+acc)

# The i-th term, or a sort when the list is too short.
def Eval.nth(xs: List<&2, T.Term>, i: Nat) -> T.Term:
  match xs:
    case Nil{}:
      T.TSort{L.LZero{}}
    case Con{h, t}:
      match i:
        case 0n:
          h
        case 1n+p:
          Eval.nth(t, p)

# The first `n` terms.
def Eval.take(xs: List<&2, T.Term>, n: Nat) -> List<&2, T.Term>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match n:
        case 0n:
          Nil{}
        case 1n+p:
          Con{h, Eval.take(t, p)}

# Everything past the first `n` terms.
def Eval.drop(xs: List<&2, T.Term>, n: Nat) -> List<&2, T.Term>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match n:
        case 0n:
          Con{h, t}
        case 1n+p:
          Eval.drop(t, p)

# Peel an application into its head and its arguments, in order.
def Eval.spine(t: T.Term, +acc: List<&2, T.Term>) -> List<&2, T.Term>:
  match t:
    case T.TApp{f, a}:
      Eval.spine(f, Con{a, acc})
    case x:
      acc

# The head of an application.
def Eval.head(t: T.Term) -> T.Term:
  match t:
    case T.TApp{f, a}:
      Eval.head(f)
    case x:
      x

# The name a head names, or zero. Guard with `Eval.head_is_const`.
def Eval.head_name(t: T.Term) -> Nat:
  match t:
    case T.TConst{n, ls}:
      n
    case x:
      0n

# Is the head of this application a constant?
def Eval.head_is_const(t: T.Term) -> Bool:
  match t:
    case T.TConst{n, ls}:
      True{}
    case x:
      False{}

# Unwrap a rule, or none.
def Eval.rule_ok(m: Maybe<&2, E.RecRule>) -> Bool:
  match m:
    case Some{r}:
      True{}
    case None{}:
      False{}

def Eval.rule_get(m: Maybe<&2, E.RecRule>) -> E.RecRule:
  match m:
    case Some{r}:
      r
    case None{}:
      E.MkRule{0n, 0n, T.TSort{L.LZero{}}}

# A branch of `Eval.pick_t` is evaluated whether or not it is chosen, so a
# branch that is about to be thrown away must still be cheap. These two
# functions make that so: each hands back a term that reduces at once unless
# the branch is the one that matters.
#
# This is not a detail. Without it, the branch that unfolds a definition runs
# on a constant that has no value, where it rebuilds the same constant and
# calls itself again, and every such constant costs the whole remaining fuel.
# That alone was enough to stop the recursion-heavy tests from finishing.

# Is this a recursor with enough arguments to reach its major premise? This is
# the cheap test, and it guards the expensive one. Reducing the major premise
# for every constant, rather than only for a recursor, is what made the
# recursion-heavy tests fail to finish.
def Eval.rec_ready(+d: E.Decl, +sp: List<&2, T.Term>) -> Bool:
  Bool.and(
    E.Decl.is_rec(d),
    Nat.is_lt(Eval.major_idx(d), Eval.len(sp, 0n)))

# The value a declaration unfolds to, or a sort when it has none. The sort is
# never used: the branch that reads it is only chosen for a definition.
def Eval.unfold_decl(+d: E.Decl, +ls: List<&2, L.Level>) -> T.Term:
  Eval.pick_t(
    E.Decl.is_def(d),
    Eval.val_or(E.Decl.value_at(d, ls), T.TSort{L.LZero{}}),
    T.TSort{L.LZero{}})

# The major premise of a recursor, or a sort when this is not a recursor with
# enough arguments. The sort is never used, for the same reason.
def Eval.major_or_sort(+d: E.Decl, +sp: List<&2, T.Term>) -> T.Term:
  Eval.pick_t(
    Eval.rec_ready(d, sp),
    Eval.nth(sp, Eval.major_idx(d)),
    T.TSort{L.LZero{}})

# Can iota fire here? The declaration must be a recursor, the spine must reach
# the major premise, and the reduced major premise must be a constructor this
# recursor has a rule for.
def Eval.can_iota(+d: E.Decl, +sp: List<&2, T.Term>, +mw: T.Term) -> Bool:
  Bool.and(
    Eval.rec_ready(d, sp),
    Bool.and(
      Eval.head_is_const(Eval.head(mw)),
      Eval.rule_ok(
        E.Decl.rule_for(E.Decl.rec_rules(d), Eval.head_name(Eval.head(mw))))))

# The term a fired rule reduces to. Guard with `Eval.can_iota`.
def Eval.iota_term(
  +d: E.Decl, +ls: List<&2, L.Level>, +sp: List<&2, T.Term>, +mw: T.Term
) -> T.Term:
  +rule = Eval.rule_get(
    E.Decl.rule_for(E.Decl.rec_rules(d), Eval.head_name(Eval.head(mw))))
  Eval.rebuild(
    List.append(&2, T.Term,
      Eval.take(
        Eval.drop(Eval.spine(mw, Nil{}), E.Decl.rec_np(d)),
        E.RecRule.nfields(rule)),
      Eval.drop(sp, 1n+Eval.major_idx(d))),
    Eval.rebuild(
      Eval.take(
        sp,
        Nat.add(
          Nat.add(E.Decl.rec_np(d), E.Decl.rec_nm(d)),
          E.Decl.rec_nmin(d))),
      T.Term.subst_levels(E.RecRule.rhs(rule), ls)))

# Reduce `t` applied to `sp` to weak head normal form.
def Eval.whnf(+fuel: Nat, +env: List<&2, E.Decl>, t: T.Term, +sp: List<&2, T.Term>) -> T.Term:
  match fuel:
    case 0n:
      T.TUnk{}
    case 1n+f:
      match t:
        case T.TVar{i}:
          Eval.rebuild(sp, T.TVar{i})
        case T.TSort{l}:
          Eval.rebuild(sp, T.TSort{l})
        case T.TConst{+n, +ls}:
          +d = E.Lookup.get(E.Env.find(env, n))
          +mw = Eval.whnf(f, env, Eval.major_or_sort(d, sp), Nil{})
          Eval.pick_t(
            E.Decl.is_def(d),
            Eval.whnf(f, env, Eval.unfold_decl(d, ls), sp),
            Eval.pick_t(
              Eval.can_iota(d, sp, mw),
              Eval.whnf(f, env, Eval.iota_term(d, ls, sp, mw), Nil{}),
              Eval.rebuild(sp, T.TConst{n, ls})))
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
        case T.TUnk{}:
          T.TUnk{}
