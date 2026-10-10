# Lean terms, with de Bruijn indices.
#
# A constant is a Nat id rather than a name, for the same reason levels use an
# index: a Bend string is a linked list of characters.
#
# `TLam` and `TPi` carry the binder's type and the body. The binder's name is
# not kept, because nothing here prints a term back to the user.

import Base
import ./Level.bend as L

type Term is Data:
  TVar{i: Nat}
  TSort{l: L.Level}
  TConst{n: Nat, ls: List<&2, L.Level>}
  TApp{f: Term, a: Term}
  TLam{ty: Term, bd: Term}
  TPi{ty: Term, bd: Term}
  TLet{ty: Term, v: Term, bd: Term}

# Choose between two terms on a computed Bool.
def Term.pick(b: Bool, x: Term, y: Term) -> Term:
  match b:
    case True{}:
      x
    case False{}:
      y

# Add `d` to every free variable whose index is at least `cut`.
def Term.lift(t: Term, +d: Nat, +cut: Nat) -> Term:
  match t:
    case TVar{+i}:
      Term.pick(Nat.is_lt(i, cut), TVar{i}, TVar{Nat.add(i, d)})
    case TSort{l}:
      TSort{l}
    case TConst{n, ls}:
      TConst{n, ls}
    case TApp{f, a}:
      TApp{Term.lift(f, d, cut), Term.lift(a, d, cut)}
    case TLam{ty, bd}:
      TLam{Term.lift(ty, d, cut), Term.lift(bd, d, 1n+cut)}
    case TPi{ty, bd}:
      TPi{Term.lift(ty, d, cut), Term.lift(bd, d, 1n+cut)}
    case TLet{ty, v, bd}:
      TLet{Term.lift(ty, d, cut), Term.lift(v, d, cut), Term.lift(bd, d, 1n+cut)}

# Replace the variable at depth `cut` with `v`, and shift the ones above it
# down by one. This is the de Bruijn instantiation a beta step needs.
def Term.subst(t: Term, +v: Term, +cut: Nat) -> Term:
  match t:
    case TVar{+i}:
      Term.pick(
        Nat.is_eq(i, cut),
        Term.lift(v, cut, 0n),
        Term.pick(Nat.is_lt(i, cut), TVar{i}, TVar{Nat.sub(i, 1n)}))
    case TSort{l}:
      TSort{l}
    case TConst{n, ls}:
      TConst{n, ls}
    case TApp{f, a}:
      TApp{Term.subst(f, v, cut), Term.subst(a, v, cut)}
    case TLam{ty, bd}:
      TLam{Term.subst(ty, v, cut), Term.subst(bd, v, 1n+cut)}
    case TPi{ty, bd}:
      TPi{Term.subst(ty, v, cut), Term.subst(bd, v, 1n+cut)}
    case TLet{ty, vl, bd}:
      TLet{Term.subst(ty, v, cut), Term.subst(vl, v, cut), Term.subst(bd, v, 1n+cut)}

# Instantiate the body of a binder with `v`, which is the common case of
# `Term.subst` at depth zero.
def Term.inst(bd: Term, +v: Term) -> Term:
  Term.subst(bd, v, 0n)

# Substitute the level parameters through a list of levels. This is written
# out rather than passed to `List.map`, because a Bend template argument must
# be closed and the mapped function mentions `vs`.
def Term.subst_level_list(ls: List<&2, L.Level>, +vs: List<&2, L.Level>) -> List<&2, L.Level>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{L.Level.subst(h, vs), Term.subst_level_list(t, vs)}

# Substitute a declaration's level parameters throughout a term.
def Term.subst_levels(t: Term, +vs: List<&2, L.Level>) -> Term:
  match t:
    case TVar{i}:
      TVar{i}
    case TSort{l}:
      TSort{L.Level.subst(l, vs)}
    case TConst{n, ls}:
      TConst{n, Term.subst_level_list(ls, vs)}
    case TApp{f, a}:
      TApp{Term.subst_levels(f, vs), Term.subst_levels(a, vs)}
    case TLam{ty, bd}:
      TLam{Term.subst_levels(ty, vs), Term.subst_levels(bd, vs)}
    case TPi{ty, bd}:
      TPi{Term.subst_levels(ty, vs), Term.subst_levels(bd, vs)}
    case TLet{ty, v, bd}:
      TLet{Term.subst_levels(ty, vs), Term.subst_levels(v, vs), Term.subst_levels(bd, vs)}
