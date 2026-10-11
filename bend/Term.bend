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
  # A reference to an expression of the export's own table.
  #
  # The table holds each expression once, and the export's expressions form a
  # graph: one expression is named by many others. This kernel read that graph
  # as a tree, which copies a subterm once per reference, because Bend is
  # affine and a value read twice is copied. An 869 kB export built 206
  # million nodes that way, and a 1.3 MB one could not be read at all.
  #
  # A reference is one word. `Eval.whnf` resolves it against the table, and
  # what it finds has references for its own children, so every step is
  # shallow.
  #
  # The parser emits one only for an expression with no free variable in it. A
  # closed term is the same term in every scope, so `Term.subst` and
  # `Term.lift` leave a reference alone and cost nothing, which is what makes
  # this sound as well as cheap.
  TRef{i: Nat}

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

# How many binders a telescope opens with. The result type of a constructor
# is an application of its inductive and never a pi, so this counts exactly
# the parameters and the fields.
def Term.pi_count(t: Term, +acc: Nat) -> Nat:
  match t:
    case TPi{ty, bd}:
      Term.pi_count(bd, 1n+acc)
    case x:
      acc

# What a telescope reaches after `n` binders, read as syntax and with no
# reduction. The binders are left open: the callers of this ask only whether
# what they reach is a sort, and a sort is closed.
def Term.pi_skip(n: Nat, t: Term) -> Term:
  match n:
    case 0n:
      t
    case 1n+m:
      match t:
        case TPi{ty, bd}:
          Term.pi_skip(m, bd)
        case x:
          x

# Does the constant `n` appear anywhere in this term?
def Term.occurs(t: Term, +n: Nat) -> Bool:
  match t:
    case TConst{m, ls}:
      Nat.is_eq(m, n)
    case TApp{f, a}:
      Bool.or(Term.occurs(f, n), Term.occurs(a, n))
    case TLam{ty, bd}:
      Bool.or(Term.occurs(ty, n), Term.occurs(bd, n))
    case TPi{ty, bd}:
      Bool.or(Term.occurs(ty, n), Term.occurs(bd, n))
    case TLet{ty, v, bd}:
      Bool.or(
        Term.occurs(ty, n),
        Bool.or(Term.occurs(v, n), Term.occurs(bd, n)))
    case TProj{tn, idx, st}:
      Term.occurs(st, n)
    case x:
      False{}

# Does the constant `n` appear in any of these terms?
    case TRef{i}:
      False{}

def Term.occurs_any(ts: List<&2, Term>, +n: Nat) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Term.occurs(h, n), Term.occurs_any(t, n))

# Is every level parameter in this list one of the first `n`?
def Term.pars_ok_levels(ls: List<&2, L.Level>, +n: Nat) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(L.Level.pars_ok(h, n), Term.pars_ok_levels(t, n))

# Is every level parameter in this term one of the first `n`?
#
# A declaration that names a universe it did not declare is rejected by the
# Lean kernel, and `Level.param_pos` leaves a marker for one, so this is where
# the marker is caught.
def Term.pars_ok(t: Term, +n: Nat) -> Bool:
  match t:
    case TVar{i}:
      True{}
    case TSort{l}:
      L.Level.pars_ok(l, n)
    case TConst{m, ls}:
      Term.pars_ok_levels(ls, n)
    case TApp{f, a}:
      Bool.and(Term.pars_ok(f, n), Term.pars_ok(a, n))
    case TLam{ty, bd}:
      Bool.and(Term.pars_ok(ty, n), Term.pars_ok(bd, n))
    case TPi{ty, bd}:
      Bool.and(Term.pars_ok(ty, n), Term.pars_ok(bd, n))
    case TLet{ty, v, bd}:
      Bool.and(
        Bool.and(Term.pars_ok(ty, n), Term.pars_ok(v, n)),
        Term.pars_ok(bd, n))
    case TNat{v, m, z, c}:
      True{}
    case TUnk{}:
      True{}
    case TProj{tn, idx, st}:
      Term.pars_ok(st, n)
    case TRef{i}:
      True{}

# Does this term hold a variable bound `d` binders out or further?
#
# With `d` at zero that asks whether the term is closed. The parser asks it of
# every expression it stores, because a closed and level-free expression is
# one a reference may stand for. A reference answers no, which is sound and is
# what makes the test cost nothing: an entry whose children are references is
# a shallow node.
def Term.has_free(t: Term, +d: Nat) -> Bool:
  match t:
    case TVar{+i}:
      Nat.is_le(d, i)
    case TSort{l}:
      False{}
    case TConst{n, ls}:
      False{}
    case TApp{f, a}:
      Bool.or(Term.has_free(f, d), Term.has_free(a, d))
    case TLam{ty, bd}:
      Bool.or(Term.has_free(ty, d), Term.has_free(bd, 1n+d))
    case TPi{ty, bd}:
      Bool.or(Term.has_free(ty, d), Term.has_free(bd, 1n+d))
    case TLet{ty, v, bd}:
      Bool.or(
        Bool.or(Term.has_free(ty, d), Term.has_free(v, d)),
        Term.has_free(bd, 1n+d))
    case TNat{v, m, z, c}:
      False{}
    case TUnk{}:
      False{}
    case TProj{tn, idx, st}:
      Term.has_free(st, d)
    case TRef{i}:
      False{}

# Does this term use the variable bound `d` binders out?
#
# The Lean kernel calls this a loose bound variable. A projection out of a
# proposition needs it: a field before the one projected has to be a proof
# only when the rest of the constructor's telescope uses it.
    case TRef{i}:
      True{}

def Term.has_bvar(t: Term, +d: Nat) -> Bool:
  match t:
    case TVar{+i}:
      Nat.is_eq(i, d)
    case TSort{l}:
      False{}
    case TConst{n, ls}:
      False{}
    case TApp{f, a}:
      Bool.or(Term.has_bvar(f, d), Term.has_bvar(a, d))
    case TLam{ty, bd}:
      Bool.or(Term.has_bvar(ty, d), Term.has_bvar(bd, 1n+d))
    case TPi{ty, bd}:
      Bool.or(Term.has_bvar(ty, d), Term.has_bvar(bd, 1n+d))
    case TLet{ty, v, bd}:
      Bool.or(
        Bool.or(Term.has_bvar(ty, d), Term.has_bvar(v, d)),
        Term.has_bvar(bd, 1n+d))
    case TNat{v, m, z, c}:
      False{}
    case TUnk{}:
      False{}
    case TProj{tn, idx, st}:
      Term.has_bvar(st, d)

# Add `d` to every free variable whose index is at least `cut`.
    case TRef{i}:
      False{}

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

# Lift a value into the scope it lands in, unless it lands in the scope it
# was written in. A lift by zero is the value itself, and `Term.lift` would
# walk and rebuild the whole of it to find that out.
    case TRef{i}:
      TRef{i}

def Term.lift_by(at_top: Bool, v: Term, +cut: Nat) -> Term:
  match at_top:
    case True{}:
      v
    case False{}:
      Term.lift(v, cut, 0n)

# What one variable of the body becomes.
#
# This exists so that the value is walked only at the variable that is being
# replaced. `Term.pick` evaluates both of its branches, because an argument
# evaluates before the match picks an arm, so a lift written there copied the
# whole value at every variable in the body, matching or not. A body with a
# thousand variables copied a thousand values to use one.
def Term.subst_var(hit: Bool, +i: Nat, +v: Term, +cut: Nat) -> Term:
  match hit:
    case True{}:
      Term.lift_by(Nat.is_eq(cut, 0n), v, cut)
    case False{}:
      Term.pick(Nat.is_lt(i, cut), TVar{i}, TVar{Nat.sub(i, 1n)})

# Replace the variable at depth `cut` with `v`, and shift the ones above it
# down by one. This is the de Bruijn instantiation a beta step needs.
def Term.subst(t: Term, +v: Term, +cut: Nat) -> Term:
  match t:
    case TVar{+i}:
      Term.subst_var(Nat.is_eq(i, cut), i, v, cut)
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
    case TRef{i}:
      TRef{i}

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
    case TRef{i}:
      TRef{i}

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
    case TRef{i}:
      TRef{i}
