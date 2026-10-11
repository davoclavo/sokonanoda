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
import ./Table.bend as Tb

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
    k: Bool, rules: List<&2, RecRule>, inds: List<&2, Nat>,
    # Is this declaration's own name the one a recursor must have? Lean names
    # the eliminator of `I` as `I.rec`, and the reader is the only part that
    # sees a name's characters, so it reads this and the kernel checks it.
    named: Bool}
  # One of the four quotient declarations. `kind` is 0 for `Quot` itself, 1
  # for `Quot.mk`, 2 for `Quot.lift` and 3 for `Quot.ind`. The export states
  # their types; the Lean kernel has them built in, so taking the file's word
  # for the type is a thing this kernel trusts.
  DQuot{id: Nat, ps: List<&2, Nat>, ty: T.Term, kind: Nat}
  # A definition the kernel also knows how to compute directly. `op` names
  # which rule: 1 add, 2 sub, 3 mul, 4 div, 5 mod, 6 beq, 7 ble, 8 pow.
  # `yes` and `no` are the names of `Bool.true` and `Bool.false`, which the
  # two rules that compare need to answer with and have no other way to learn.
  #
  # The arena enables a native `Nat`, where the kernel computes on two
  # literals instead of unfolding the Lean definition. The definition is still
  # here, so a call the rule cannot answer, because an argument is not a
  # literal, unfolds as it always did.
  DPrim{id: Nat, ps: List<&2, Nat>, ty: T.Term, val: T.Term, op: Nat, yes: Nat, no: Nat}

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
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named}:
      id
    case DQuot{id, ps, ty, kind}:
      id
    case DPrim{id, ps, ty, val, op, yes, no}:
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
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named}:
      False{}
    case DQuot{id, ps, ty, kind}:
      False{}
    case DPrim{id, ps, ty, val, op, yes, no}:
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
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named}:
      False{}
    case DQuot{id, ps, ty, kind}:
      False{}
    case DPrim{id, ps, ty, val, op, yes, no}:
      True{}

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
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named}:
      Decl.len(ps)
    case DQuot{id, ps, ty, kind}:
      Decl.len(ps)
    case DPrim{id, ps, ty, val, op, yes, no}:
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
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named}:
      ps
    case DQuot{id, ps, ty, kind}:
      ps
    case DPrim{id, ps, ty, val, op, yes, no}:
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
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named}:
      T.Term.subst_levels(ty, ls)
    case DQuot{id, ps, ty, kind}:
      T.Term.subst_levels(ty, ls)
    case DPrim{id, ps, ty, val, op, yes, no}:
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
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named}:
      None{}
    case DQuot{id, ps, ty, kind}:
      None{}
    case DPrim{id, ps, ty, val, op, yes, no}:
      Some{T.Term.subst_levels(val, ls)}

# A recursor's argument layout, and its rules. A declaration that is not a
# recursor answers zero, so guard these with `Decl.is_rec`.
def Decl.is_rec(d: Decl) -> Bool:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named}:
      True{}
    case o:
      False{}

def Decl.rec_np(d: Decl) -> Nat:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named}:
      np
    case o:
      0n

def Decl.rec_ni(d: Decl) -> Nat:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named}:
      ni
    case o:
      0n

def Decl.rec_nm(d: Decl) -> Nat:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named}:
      nm
    case o:
      0n

def Decl.rec_nmin(d: Decl) -> Nat:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named}:
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
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named}:
      k
    case o:
      False{}

def Decl.rec_inds(d: Decl) -> List<&2, Nat>:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named}:
      inds
    case o:
      Nil{}

def Decl.rec_rules(d: Decl) -> List<&2, RecRule>:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named}:
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

# An inductive's type as written, with its level parameters still in place.
def Decl.ind_ty(d: Decl) -> T.Term:
  match d:
    case DInd{id, ps, ty, np, ni, ctors}:
      ty
    case o:
      T.TUnk{}

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

# A constructor's type as written, with its level parameters still in place.
def Decl.ctor_ty(d: Decl) -> T.Term:
  match d:
    case DCtor{id, ps, ty, ind, cidx, np, nf}:
      ty
    case o:
      T.TUnk{}

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

# How many rules a recursor states.
def Decl.rules_len(rs: List<&2, RecRule>, +acc: Nat) -> Nat:
  match rs:
    case Nil{}:
      acc
    case Con{h, t}:
      Decl.rules_len(t, 1n+acc)

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

# Which native rule a declaration carries, or zero for none.
def Decl.prim_op(d: Decl) -> Nat:
  match d:
    case DPrim{id, ps, ty, val, op, yes, no}:
      op
    case o:
      0n

# The name a comparing rule answers with: `Bool.true` or `Bool.false`.
def Decl.prim_yes(d: Decl) -> Nat:
  match d:
    case DPrim{id, ps, ty, val, op, yes, no}:
      yes
    case o:
      0n

def Decl.prim_no(d: Decl) -> Nat:
  match d:
    case DPrim{id, ps, ty, val, op, yes, no}:
      no
    case o:
      0n

# Does this recursor carry the name a recursor must have?
def Decl.rec_named(d: Decl) -> Bool:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named}:
      named
    case o:
      True{}

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
# The environment as a trie on the bits of a name.
#
# It was a list, searched from the head, and a constant is looked up on every
# step of reduction and inference. So checking a file cost the square of the
# number of declarations in it, and the arena's `init-prelude` spent minutes
# there after reading in two seconds.
#
# A found declaration is checked against the name asked for. The path already
# determines the slot, so this cannot fail, and it is free: the declaration
# carries its own name. It is the difference between a table that loses an
# entry and one that answers under the wrong name.
type DTable is Data:
  DTip{}
  DNode{v: Maybe<&2, Decl>, lo: DTable, hi: DTable}

def Env.empty() -> DTable:
  DTip{}

def Env.found(m: Maybe<&2, Decl>, +i: Nat) -> Lookup:
  match m:
    case None{}:
      LMissing{}
    case Some{+d}:
      Env.pick(Nat.is_eq(Decl.id(d), i), LFound{d}, LMissing{})

def Env.at(t: DTable, +i: Nat) -> Lookup:
  match t:
    case DTip{}:
      LMissing{}
    case DNode{v, lo, hi}:
      Env.found(v, i)

# The declaration named `i`, or nothing. `stop` says the path ends at this
# node and `b` says which half it takes otherwise.
def Env.get(
  n: Nat, stop: Bool, b: Bool, t: DTable, +i: Nat, +name: Nat
) -> Lookup:
  match n:
    case 0n:
      LMissing{}
    case 1n+m:
      match stop:
        case True{}:
          Env.at(t, name)
        case False{}:
          match b:
            case True{}:
              match t:
                case DTip{}:
                  LMissing{}
                case DNode{v, lo, hi}:
                  Env.get(
                    m,
                    Tb.Table.here(Tb.Table.rest(i)),
                    Tb.Table.low(Tb.Table.rest(i)),
                    lo,
                    Tb.Table.rest(i),
                    name)
            case False{}:
              match t:
                case DTip{}:
                  LMissing{}
                case DNode{v, lo, hi}:
                  Env.get(
                    m,
                    Tb.Table.here(Tb.Table.rest(i)),
                    Tb.Table.low(Tb.Table.rest(i)),
                    hi,
                    Tb.Table.rest(i),
                    name)

def Env.put(
  n: Nat, stop: Bool, b: Bool, t: DTable, +i: Nat, +d: Decl
) -> DTable:
  match n:
    case 0n:
      t
    case 1n+m:
      match stop:
        case True{}:
          match t:
            case DTip{}:
              DNode{Some{d}, DTip{}, DTip{}}
            case DNode{o, lo, hi}:
              DNode{Some{d}, lo, hi}
        case False{}:
          match b:
            case True{}:
              match t:
                case DTip{}:
                  DNode{
                    None{},
                    Env.put(
                      m,
                      Tb.Table.here(Tb.Table.rest(i)),
                      Tb.Table.low(Tb.Table.rest(i)),
                      DTip{},
                      Tb.Table.rest(i),
                      d),
                    DTip{}}
                case DNode{o, lo, hi}:
                  DNode{
                    o,
                    Env.put(
                      m,
                      Tb.Table.here(Tb.Table.rest(i)),
                      Tb.Table.low(Tb.Table.rest(i)),
                      lo,
                      Tb.Table.rest(i),
                      d),
                    hi}
            case False{}:
              match t:
                case DTip{}:
                  DNode{
                    None{},
                    DTip{},
                    Env.put(
                      m,
                      Tb.Table.here(Tb.Table.rest(i)),
                      Tb.Table.low(Tb.Table.rest(i)),
                      DTip{},
                      Tb.Table.rest(i),
                      d)}
                case DNode{o, lo, hi}:
                  DNode{
                    o,
                    lo,
                    Env.put(
                      m,
                      Tb.Table.here(Tb.Table.rest(i)),
                      Tb.Table.low(Tb.Table.rest(i)),
                      hi,
                      Tb.Table.rest(i),
                      d)}

# Look up a name.
def Env.find(+env: DTable, +i: Nat) -> Lookup:
  Env.get(
    Tb.Table.bits(),
    Tb.Table.here(Tb.Table.path(i)),
    Tb.Table.low(Tb.Table.path(i)),
    env,
    Tb.Table.path(i),
    i)

# Add a declaration under its own name.
def Env.add(+env: DTable, +d: Decl) -> DTable:
  Env.put(
    Tb.Table.bits(),
    Tb.Table.here(Tb.Table.path(Decl.id(d))),
    Tb.Table.low(Tb.Table.path(Decl.id(d))),
    env,
    Tb.Table.path(Decl.id(d)),
    d)


# Every declaration of a list, under its own name. For a hand-built
# environment, where the list is written out in the test itself.
def Env.of_list(ds: List<&2, Decl>, +acc: DTable) -> DTable:
  match ds:
    case Nil{}:
      acc
    case Con{h, t}:
      Env.of_list(t, Env.add(acc, h))
