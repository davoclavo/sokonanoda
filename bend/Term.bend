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

# Structural equality of two level lists.
def Term.same_levels(xs: List<&2, L.Level>, ys: List<&2, L.Level>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xr} Con{y, yr}:
      Bool.and(L.Level.same(x, y), Term.same_levels(xr, yr))
    case x y:
      False{}

# Structural equality of two terms, without fuel. The recursion is on both
# sides at once, so it is bounded by the smaller one. This is equality of
# syntax, not of meaning, and that is what it is for: a guard that must never
# say yes to two terms that differ.
def Term.same(a: Term, b: Term) -> Bool:
  match a b:
    case TVar{i} TVar{j}:
      Nat.is_eq(i, j)
    case TSort{x} TSort{y}:
      L.Level.same(x, y)
    case TConst{n1, l1} TConst{n2, l2}:
      Bool.and(Nat.is_eq(n1, n2), Term.same_levels(l1, l2))
    case TApp{f1, a1} TApp{f2, a2}:
      Bool.and(Term.same(f1, f2), Term.same(a1, a2))
    case TLam{t1, b1} TLam{t2, b2}:
      Bool.and(Term.same(t1, t2), Term.same(b1, b2))
    case TPi{t1, b1} TPi{t2, b2}:
      Bool.and(Term.same(t1, t2), Term.same(b1, b2))
    case TLet{t1, v1, b1} TLet{t2, v2, b2}:
      Bool.and(
        Term.same(t1, t2),
        Bool.and(Term.same(v1, v2), Term.same(b1, b2)))
    case x y:
      False{}

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

# Renumber the level parameters in a list of levels.
def Term.remap_level_list(ls: List<&2, L.Level>, +ps: List<&2, Nat>) -> List<&2, L.Level>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{L.Level.remap(h, ps), Term.remap_level_list(t, ps)}

# Renumber every level parameter in a term from name index to position.
def Term.remap_levels(t: Term, +ps: List<&2, Nat>) -> Term:
  match t:
    case TVar{i}:
      TVar{i}
    case TSort{l}:
      TSort{L.Level.remap(l, ps)}
    case TConst{n, ls}:
      TConst{n, Term.remap_level_list(ls, ps)}
    case TApp{f, a}:
      TApp{Term.remap_levels(f, ps), Term.remap_levels(a, ps)}
    case TLam{ty, bd}:
      TLam{Term.remap_levels(ty, ps), Term.remap_levels(bd, ps)}
    case TPi{ty, bd}:
      TPi{Term.remap_levels(ty, ps), Term.remap_levels(bd, ps)}
    case TLet{ty, v, bd}:
      TLet{Term.remap_levels(ty, ps), Term.remap_levels(v, ps), Term.remap_levels(bd, ps)}

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
