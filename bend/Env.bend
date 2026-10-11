# The environment: the declarations a term may name.
#
# A declaration is an axiom, which has a type and no value, or a definition,
# which has both. `nps` is how many level parameters it takes.
#
# The environment is a plain list searched by id. The Rust parent interns
# names and resolves a constant in one load, but that design needs 64-bit
# packed pointers, which Bend does not have, so this is a list.
#
# Bend forbids mutual recursion, so the search cannot split into a loop and a
# per-entry step that call each other. It is one self-recursive def, and the
# comparison goes through `Env.pick` because a match cannot scrutinize a
# computed value.

import Base
import ./Level.bend as L
import ./Term.bend as T

# One computation rule of a recursor: for this constructor, with this many
# fields, reduce to this right-hand side.
type RecRule is Data:
  MkRule{ctor: Nat, nfields: Nat, rhs: T.Term}

type Decl is Data:
  DAxiom{id: Nat, ps: List<&2, Nat>, ty: T.Term}
  DDef{id: Nat, ps: List<&2, Nat>, ty: T.Term, val: T.Term}
  DThm{id: Nat, ps: List<&2, Nat>, ty: T.Term, val: T.Term}
  # An inductive type. `np` parameters and `ni` indices, with the names of its
  # constructors.
  DInd{id: Nat, ps: List<&2, Nat>, ty: T.Term, np: Nat, ni: Nat, ctors: List<&2, Nat>}
  # A constructor of `ind`, the `cidx`-th, with `np` parameters and `nf` fields.
  DCtor{id: Nat, ps: List<&2, Nat>, ty: T.Term, ind: Nat, cidx: Nat, np: Nat, nf: Nat}
  # A recursor. Its arguments come in the order: `np` parameters, `nm`
  # motives, `nmin` minor premises, `ni` indices, then the major premise.
  DRec{
    id: Nat, ps: List<&2, Nat>, ty: T.Term,
    np: Nat, ni: Nat, nm: Nat, nmin: Nat,
    k: Bool, rules: List<&2, RecRule>, inds: List<&2, Nat>}
  # One of the four quotient declarations. `kind` is 0 for `Quot` itself, 1
  # for `Quot.mk`, 2 for `Quot.lift` and 3 for `Quot.ind`. The export states
  # their types; the Lean kernel has them built in, so taking the file's word
  # for the type is a thing this kernel trusts.
  DQuot{id: Nat, ps: List<&2, Nat>, ty: T.Term, kind: Nat}

type Lookup is Data:
  LFound{d: Decl}
  LMissing{}

# Choose between two lookup results on a computed Bool.
def Env.pick(b: Bool, x: Lookup, y: Lookup) -> Lookup:
  match b:
    case True{}:
      x
    case False{}:
      y

# The id of a declaration.
def Decl.id(d: Decl) -> Nat:
  match d:
    case DAxiom{id, ps, ty}:
      id
    case DDef{id, ps, ty, val}:
      id
    case DThm{id, ps, ty, val}:
      id
    case DInd{id, ps, ty, np, ni, ctors}:
      id
    case DCtor{id, ps, ty, ind, cidx, np, nf}:
      id
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds}:
      id
    case DQuot{id, ps, ty, kind}:
      id

# True when this declaration is a theorem, whose type must be a Prop.
def Decl.is_thm(d: Decl) -> Bool:
  match d:
    case DAxiom{id, ps, ty}:
      False{}
    case DDef{id, ps, ty, val}:
      False{}
    case DThm{id, ps, ty, val}:
      True{}
    case DInd{id, ps, ty, np, ni, ctors}:
      False{}
    case DCtor{id, ps, ty, ind, cidx, np, nf}:
      False{}
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds}:
      False{}
    case DQuot{id, ps, ty, kind}:
      False{}

# True when this declaration has a value, so delta reduction can unfold it.
def Decl.is_def(d: Decl) -> Bool:
  match d:
    case DAxiom{id, ps, ty}:
      False{}
    case DDef{id, ps, ty, val}:
      True{}
    case DThm{id, ps, ty, val}:
      True{}
    case DInd{id, ps, ty, np, ni, ctors}:
      False{}
    case DCtor{id, ps, ty, ind, cidx, np, nf}:
      False{}
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds}:
      False{}
    case DQuot{id, ps, ty, kind}:
      False{}

# How many numbers a list holds. A level parameter list is a handful long.
def Decl.len(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+Decl.len(t)

# Does this list hold `j`?
def Decl.elem(xs: List<&2, Nat>, +j: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Nat.is_eq(h, j), Decl.elem(t, j))

# Is every entry of this list different? The Lean kernel refuses a declaration
# with a repeated universe parameter, in `check_duplicated_univ_params`.
def Decl.no_dupes(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      Bool.and(Bool.not(Decl.elem(t, h)), Decl.no_dupes(t))

# How many level parameters a declaration takes.
def Decl.num_params(d: Decl) -> Nat:
  match d:
    case DAxiom{id, ps, ty}:
      Decl.len(ps)
    case DDef{id, ps, ty, val}:
      Decl.len(ps)
    case DThm{id, ps, ty, val}:
      Decl.len(ps)
    case DInd{id, ps, ty, np, ni, ctors}:
      Decl.len(ps)
    case DCtor{id, ps, ty, ind, cidx, np, nf}:
      Decl.len(ps)
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds}:
      Decl.len(ps)
    case DQuot{id, ps, ty, kind}:
      Decl.len(ps)

# The level parameters a declaration takes.
def Decl.params(d: Decl) -> List<&2, Nat>:
  match d:
    case DAxiom{id, ps, ty}:
      ps
    case DDef{id, ps, ty, val}:
      ps
    case DThm{id, ps, ty, val}:
      ps
    case DInd{id, ps, ty, np, ni, ctors}:
      ps
    case DCtor{id, ps, ty, ind, cidx, np, nf}:
      ps
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds}:
      ps
    case DQuot{id, ps, ty, kind}:
      ps

# The declared type of a declaration, with its level parameters replaced.
def Decl.type_at(d: Decl, +ls: List<&2, L.Level>) -> T.Term:
  match d:
    case DAxiom{id, ps, ty}:
      T.Term.subst_levels(ty, ls)
    case DDef{id, ps, ty, val}:
      T.Term.subst_levels(ty, ls)
    case DThm{id, ps, ty, val}:
      T.Term.subst_levels(ty, ls)
    case DInd{id, ps, ty, np, ni, ctors}:
      T.Term.subst_levels(ty, ls)
    case DCtor{id, ps, ty, ind, cidx, np, nf}:
      T.Term.subst_levels(ty, ls)
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds}:
      T.Term.subst_levels(ty, ls)
    case DQuot{id, ps, ty, kind}:
      T.Term.subst_levels(ty, ls)

# The value of a definition, with its level parameters replaced. An axiom has
# no value, so it answers `None`.
def Decl.value_at(d: Decl, +ls: List<&2, L.Level>) -> Maybe<&2, T.Term>:
  match d:
    case DAxiom{id, ps, ty}:
      None{}
    case DDef{id, ps, ty, val}:
      Some{T.Term.subst_levels(val, ls)}
    case DThm{id, ps, ty, val}:
      Some{T.Term.subst_levels(val, ls)}
    case DInd{id, ps, ty, np, ni, ctors}:
      None{}
    case DCtor{id, ps, ty, ind, cidx, np, nf}:
      None{}
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds}:
      None{}
    case DQuot{id, ps, ty, kind}:
      None{}

# A recursor's argument layout, and its rules. A declaration that is not a
# recursor answers zero, so guard these with `Decl.is_rec`.
def Decl.is_rec(d: Decl) -> Bool:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds}:
      True{}
    case o:
      False{}

def Decl.rec_np(d: Decl) -> Nat:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds}:
      np
    case o:
      0n

def Decl.rec_ni(d: Decl) -> Nat:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds}:
      ni
    case o:
      0n

def Decl.rec_nm(d: Decl) -> Nat:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds}:
      nm
    case o:
      0n

def Decl.rec_nmin(d: Decl) -> Nat:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds}:
      nmin
    case o:
      0n

# Does this recursor reduce by the K rule? That is set for an inductive with
# one constructor that takes no fields, where the major premise need not be a
# literal constructor for the rule to fire.
#
# The flag is read from the export and kept, but nothing fires on it yet. An
# unguarded K rule is unsound: the Lean kernel infers the major premise's type
# before it fires, and without that check the rule fires on a major premise of
# the wrong type. Measured here, firing it unguarded turned the arena's
# `100_ruleKbad`, which is the attack on exactly that, from a correct
# rejection into a pass. Inferring a type inside reduction would make
# reduction and inference call each other, which Bend forbids, so this waits
# for those two to be fused into one def.
def Decl.rec_k(d: Decl) -> Bool:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds}:
      k
    case o:
      False{}

def Decl.rec_inds(d: Decl) -> List<&2, Nat>:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds}:
      inds
    case o:
      Nil{}

def Decl.rec_rules(d: Decl) -> List<&2, RecRule>:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds}:
      rules
    case o:
      Nil{}

# An inductive's shape. Guard with `Decl.is_ind`.
def Decl.is_ind(d: Decl) -> Bool:
  match d:
    case DInd{id, ps, ty, np, ni, ctors}:
      True{}
    case o:
      False{}

def Decl.ind_np(d: Decl) -> Nat:
  match d:
    case DInd{id, ps, ty, np, ni, ctors}:
      np
    case o:
      0n

def Decl.ind_ni(d: Decl) -> Nat:
  match d:
    case DInd{id, ps, ty, np, ni, ctors}:
      ni
    case o:
      1n

def Decl.ind_ctors(d: Decl) -> List<&2, Nat>:
  match d:
    case DInd{id, ps, ty, np, ni, ctors}:
      ctors
    case o:
      Nil{}

# A constructor's layout. Guard with `Decl.is_ctor`.
def Decl.is_ctor(d: Decl) -> Bool:
  match d:
    case DCtor{id, ps, ty, ind, cidx, np, nf}:
      True{}
    case o:
      False{}

def Decl.ctor_np(d: Decl) -> Nat:
  match d:
    case DCtor{id, ps, ty, ind, cidx, np, nf}:
      np
    case o:
      0n

# The inductive a constructor builds, or zero.
def Decl.ctor_ind(d: Decl) -> Nat:
  match d:
    case DCtor{id, ps, ty, ind, cidx, np, nf}:
      ind
    case o:
      0n

def Decl.ctor_nf(d: Decl) -> Nat:
  match d:
    case DCtor{id, ps, ty, ind, cidx, np, nf}:
      nf
    case o:
      1n

# The only entry of a one-entry list, or zero.
def Decl.only(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      h



def Decl.is_nil(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

# Does this list hold exactly one entry?
def Decl.is_one(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Decl.is_nil(t)

# One rule's parts.
def RecRule.ctor(r: RecRule) -> Nat:
  match r:
    case MkRule{c, n, rhs}:
      c

def RecRule.nfields(r: RecRule) -> Nat:
  match r:
    case MkRule{c, n, rhs}:
      n

def RecRule.rhs(r: RecRule) -> T.Term:
  match r:
    case MkRule{c, n, rhs}:
      rhs

# Choose between a rule and the rest of the search.
def Decl.pick_rule(b: Bool, h: RecRule, rest: Maybe<&2, RecRule>) -> Maybe<&2, RecRule>:
  match b:
    case True{}:
      Some{h}
    case False{}:
      rest

# The rule for this constructor, or none.
def Decl.rule_for(rs: List<&2, RecRule>, +c: Nat) -> Maybe<&2, RecRule>:
  match rs:
    case Nil{}:
      None{}
    case Con{+h, t}:
      Decl.pick_rule(Nat.is_eq(RecRule.ctor(h), c), h, Decl.rule_for(t, c))

# Which of the four quotient declarations is this, if any? A declaration that
# is not one answers 9, which matches nothing.
def Decl.quot_kind(d: Decl) -> Nat:
  match d:
    case DQuot{id, ps, ty, kind}:
      kind
    case o:
      9n

# A declaration to stand in with when a lookup found nothing. Guard with
# `Env.found`.
def Decl.none() -> Decl:
  DAxiom{0n, Nil{}, T.TSort{L.LZero{}}}

# The declaration a lookup found, or the stand-in.
def Lookup.get(lk: Lookup) -> Decl:
  match lk:
    case LFound{d}:
      d
    case LMissing{}:
      Decl.none()

# Find a declaration by id.
def Env.find(env: List<&2, Decl>, +i: Nat) -> Lookup:
  match env:
    case Nil{}:
      LMissing{}
    case Con{+h, t}:
      Env.pick(Nat.is_eq(Decl.id(h), i), LFound{h}, Env.find(t, i))
