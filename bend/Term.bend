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
  # The `idx`-th field of a structure. `tn` is the inductive's name, which the
  # export carries and which the type of the field is read from.
  TProj{tn: Nat, idx: Nat, s: Term}
  # A `Nat` literal, with the name the export gives the type `Nat`.
  #
  # The arena enables a native `Nat`, where a literal is one term rather than
  # a tower of `Nat.succ`, and arithmetic on two of them is a rule of the
  # kernel. A tower cannot hold the arena's own numbers: `1000000` is one of
  # them. The name travels in the term because inference has to answer with
  # it and has no other way to learn it. `zr` and `sc` are the names of
  # `Nat.zero` and `Nat.succ`, which let a literal be written as a
  # constructor application when a recursor or a comparison needs one.
  TNat{v: Nat, nm: Nat, zr: Nat, sc: Nat}
  # The term reduction gives back when it runs out of budget.
  #
  # Running out is not an answer. A kernel that treats it as one reports
  # falsely: it rejects a declaration it merely failed to reduce far enough.
  # So reduction hands back this instead, and everything that meets it answers
  # "I do not know" rather than yes or no.
  TUnk{}

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

# Is this the term reduction gives back when it runs out of budget?
def Term.is_unk(t: Term) -> Bool:
  match t:
    case TUnk{}:
      True{}
    case x:
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
    case TProj{n1, i1, s1} TProj{n2, i2, s2}:
      Bool.and(
        Bool.and(Nat.is_eq(n1, n2), Nat.is_eq(i1, i2)),
        Term.same(s1, s2))
    case TNat{v1, m1, z1, s1} TNat{v2, m2, z2, s2}:
      Nat.is_eq(v1, v2)
    case TLet{t1, v1, b1} TLet{t2, v2, b2}:
      Bool.and(
        Term.same(t1, t2),
        Bool.and(Term.same(v1, v2), Term.same(b1, b2)))
    case x y:
      False{}

# How many binders a telescope opens with. The result type of a constructor
# is an application of its inductive and never a pi, so this counts exactly
# the parameters and the fields.
def Term.pi_count(t: Term, +acc: Nat) -> Nat:
  match t:
    case TPi{ty, bd}:
      Term.pi_count(bd, 1n+acc)
    case x:
      acc

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
    case TNat{v, m, z, c}:
      TNat{v, m, z, c}
    case TUnk{}:
      TUnk{}
    case TProj{tn, idx, st}:
      TProj{tn, idx, Term.lift(st, d, cut)}

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
    case TNat{v, m, z, c}:
      TNat{v, m, z, c}
    case TUnk{}:
      TUnk{}
    case TProj{tn, idx, st}:
      TProj{tn, idx, Term.subst(st, v, cut)}

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
    case TNat{v, m, z, c}:
      TNat{v, m, z, c}
    case TUnk{}:
      TUnk{}
    case TProj{tn, idx, st}:
      TProj{tn, idx, Term.remap_levels(st, ps)}

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
    case TNat{v, m, z, c}:
      TNat{v, m, z, c}
    case TUnk{}:
      TUnk{}
    case TProj{tn, idx, st}:
      TProj{tn, idx, Term.subst_levels(st, vs)}
