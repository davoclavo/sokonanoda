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
    # The names of every recursor of this declaration's own block, in the
    # order the export lists them.
    #
    # A nested block has one recursor per type it eliminates and more of
    # them than it has declared types: `Lean.Syntax` declares one type and
    # states three recursors, for `Syntax`, `Array Syntax` and
    # `List Syntax`. The rule of one names another -- the minor premise for
    # `Syntax.node` calls the recursor of `Array Syntax` on its field --
    # so deriving a rule needs the names of the siblings, and this is where
    # they come from.
    sibs: List<&2, Nat>,
    # Is this declaration's own name the one a recursor must have? Lean names
    # the eliminator of `I` as `I.rec`, and the reader is the only part that
    # sees a name's characters, so it reads this and the kernel checks it.
    named: Bool}
  # One of the four quotient declarations. `kind` is 0 for `Quot` itself, 1
  # for `Quot.mk`, 2 for `Quot.lift` and 3 for `Quot.ind`. The export states
  # their types; the Lean kernel has them built in, so taking the file's word
  # for the type is a thing this kernel trusts.
  DQuot{id: Nat, ps: List<&2, Nat>, ty: T.Term, kind: Nat, eq: Nat}
  # A declaration the exporter marks `unsafe` or `partial`. Lean's kernel
  # never looks at one, so neither does this: only its type is kept, and
  # nothing is checked. A safe declaration that mentions one is rejected,
  # which is the rule that makes the omission sound. See `Kernel.safe_uses`.
  DUnsafe{id: Nat, ps: List<&2, Nat>, ty: T.Term}
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
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, sibs, named}:
      id
    case DQuot{id, ps, ty, kind, eq}:
      id
    case DUnsafe{id, ps, ty}:
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
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, sibs, named}:
      False{}
    case DQuot{id, ps, ty, kind, eq}:
      False{}
    case DUnsafe{id, ps, ty}:
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
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, sibs, named}:
      False{}
    case DQuot{id, ps, ty, kind, eq}:
      False{}
    case DUnsafe{id, ps, ty}:
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
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, sibs, named}:
      Decl.len(ps)
    case DQuot{id, ps, ty, kind, eq}:
      Decl.len(ps)
    case DUnsafe{id, ps, ty}:
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
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, sibs, named}:
      ps
    case DQuot{id, ps, ty, kind, eq}:
      ps
    case DUnsafe{id, ps, ty}:
      ps
    case DPrim{id, ps, ty, val, op, yes, no}:
      ps

# The declared type as it is stored, with its level parameters at the
# positions the reader gave them. `Decl.type_at` rebuilds the term to
# substitute; this reads it.
def Decl.raw_ty(d: Decl) -> T.Term:
  match d:
    case DAxiom{id, ps, ty}:
      ty
    case DDef{id, ps, ty, val}:
      ty
    case DThm{id, ps, ty, val}:
      ty
    case DInd{id, ps, ty, np, ni, ctors}:
      ty
    case DCtor{id, ps, ty, ind, cidx, np, nf}:
      ty
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, sibs, named}:
      ty
    case DQuot{id, ps, ty, kind, eq}:
      ty
    case DUnsafe{id, ps, ty}:
      ty
    case DPrim{id, ps, ty, val, op, yes, no}:
      ty

# The stored value, or the unknown term for a declaration with none.
def Decl.raw_val(d: Decl) -> T.Term:
  match d:
    case DDef{id, ps, ty, val}:
      val
    case DThm{id, ps, ty, val}:
      val
    case DPrim{id, ps, ty, val, op, yes, no}:
      val
    case o:
      T.TUnk{}

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
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, sibs, named}:
      T.Term.subst_levels(ty, ls)
    case DQuot{id, ps, ty, kind, eq}:
      T.Term.subst_levels(ty, ls)
    case DUnsafe{id, ps, ty}:
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
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, sibs, named}:
      None{}
    case DQuot{id, ps, ty, kind, eq}:
      None{}
    case DUnsafe{id, ps, ty}:
      None{}
    case DPrim{id, ps, ty, val, op, yes, no}:
      Some{T.Term.subst_levels(val, ls)}

# A recursor's argument layout, and its rules. A declaration that is not a
# recursor answers zero, so guard these with `Decl.is_rec`.
def Decl.is_rec(d: Decl) -> Bool:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, sibs, named}:
      True{}
    case o:
      False{}

def Decl.rec_np(d: Decl) -> Nat:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, sibs, named}:
      np
    case o:
      0n

def Decl.rec_ni(d: Decl) -> Nat:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, sibs, named}:
      ni
    case o:
      0n

def Decl.rec_nm(d: Decl) -> Nat:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, sibs, named}:
      nm
    case o:
      0n

def Decl.rec_nmin(d: Decl) -> Nat:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, sibs, named}:
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
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, sibs, named}:
      k
    case o:
      False{}

def Decl.rec_inds(d: Decl) -> List<&2, Nat>:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, sibs, named}:
      inds
    case o:
      Nil{}

def Decl.rec_rules(d: Decl) -> List<&2, RecRule>:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, sibs, named}:
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
# The name index of `Eq`, which only a quotient declaration carries. The type
# of `Quot.lift` states that a function respects the relation, and it says so
# with `Eq`, so a kernel that checks that type needs the name. The reader
# finds it by its spelling, as it finds `Nat`.
# Is this a declaration Lean's kernel never looks at?
def Decl.is_unsafe(d: Decl) -> Bool:
  match d:
    case DUnsafe{id, ps, ty}:
      True{}
    case o:
      False{}

def Decl.quot_eq(d: Decl) -> Nat:
  match d:
    case DQuot{id, ps, ty, kind, eq}:
      eq
    case o:
      0n

def Decl.quot_kind(d: Decl) -> Nat:
  match d:
    case DQuot{id, ps, ty, kind, eq}:
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
# The names of every recursor of this declaration's own block.
def Decl.rec_sibs(d: Decl) -> List<&2, Nat>:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, +sibs, named}:
      sibs
    case o:
      Nil{}

def Decl.rec_named(d: Decl) -> Bool:
  match d:
    case DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, sibs, named}:
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
# The declarations, four ways at a time. Every constant of a reduction is
# looked up here, so the depth is the hottest read in the kernel; four ways
# halves it. `Idx.bend` has the measurement that chose four.
type DTree is Data:
  DTip{}
  DNode{
    v: Maybe<&2, Decl>, k0: DTree, k1: DTree, k2: DTree, k3: DTree}

# What the kernel carries everywhere: the declarations, and the export's own
# expression table.
#
# The table is here rather than in a parameter of its own because `Eval.whnf`
# is the only thing that reads it and every path to `Eval.whnf` already
# carries the environment. Keeping the name `DTable` is deliberate: a hundred
# and forty signatures name it and none of them had to change.
type DTable is Data:
  MkDT{ds: DTree, ex: T.ETable}

def Env.empty() -> DTable:
  MkDT{DTip{}, T.ETable.new()}

# An environment over an export's expression table.
def Env.over(+ex: T.ETable) -> DTable:
  MkDT{DTip{}, ex}

# The expression the table holds under this index.
def Env.expr(+env: DTable, +i: Nat) -> T.Term:
  match env:
    case MkDT{ds, +ex}:
      T.Term.read_ex(ex, i)

# What a reference stands for: the entry, with its free variables shifted to
# the scope the reference stands in. A closed entry needs no shift, and that
# is the case the walk answers in one step.
def Env.expr_at(+env: DTable, +i: Nat, +k: Nat) -> T.Term:
  match env:
    case MkDT{ds, +ex}:
      T.Term.lift_if(Nat.is_eq(k, 0n), ex, T.Term.read_ex(ex, i), k, 0n)

# The expression table itself, for the walks that must resolve a reference.
def Env.tab(+env: DTable) -> T.ETable:
  match env:
    case MkDT{ds, +ex}:
      ex

def Env.found(m: Maybe<&2, Decl>, +i: Nat) -> Lookup:
  match m:
    case None{}:
      LMissing{}
    case Some{+d}:
      Env.pick(Nat.is_eq(Decl.id(d), i), LFound{d}, LMissing{})

def Env.at(t: DTree, +i: Nat) -> Lookup:
  match t:
    case DTip{}:
      LMissing{}
    case DNode{v, k0, k1, k2, k3}:
      Env.found(v, i)

# The declaration named `i`, or nothing. `w` says which of the four
# children the path takes, and zero says it ends at this node.
def Env.get(n: Nat, w: Nat, t: DTree, +i: Nat, +name: Nat) -> Lookup:
  match n:
    case 0n:
      LMissing{}
    case 1n+m:
      match w:
        case 0n:
          Env.at(t, name)
        case 1n+j0:
          match j0:
            case 0n:
              match t:
                case DTip{}:
                  LMissing{}
                case DNode{v, k0, k1, k2, k3}:
                  Env.get(
                    m, Tb.Table.way(Tb.Table.rest4(i)), k0,
                    Tb.Table.rest4(i), name)
            case 1n+j1:
              match j1:
                case 0n:
                  match t:
                    case DTip{}:
                      LMissing{}
                    case DNode{v, k0, k1, k2, k3}:
                      Env.get(
                        m, Tb.Table.way(Tb.Table.rest4(i)), k1,
                        Tb.Table.rest4(i), name)
                case 1n+j2:
                  match j2:
                    case 0n:
                      match t:
                        case DTip{}:
                          LMissing{}
                        case DNode{v, k0, k1, k2, k3}:
                          Env.get(
                            m, Tb.Table.way(Tb.Table.rest4(i)), k2,
                            Tb.Table.rest4(i), name)
                    case 1n+j3:
                      match t:
                        case DTip{}:
                          LMissing{}
                        case DNode{v, k0, k1, k2, k3}:
                          Env.get(
                            m, Tb.Table.way(Tb.Table.rest4(i)), k3,
                            Tb.Table.rest4(i), name)

def Env.put(n: Nat, w: Nat, t: DTree, +i: Nat, +d: Decl) -> DTree:
  match n:
    case 0n:
      t
    case 1n+m:
      match w:
        case 0n:
          match t:
            case DTip{}:
              DNode{Some{d}, DTip{}, DTip{}, DTip{}, DTip{}}
            case DNode{o, k0, k1, k2, k3}:
              DNode{Some{d}, k0, k1, k2, k3}
        case 1n+j0:
          match j0:
            case 0n:
              match t:
                case DTip{}:
                  DNode{
                    None{},
                    Env.put(
                      m, Tb.Table.way(Tb.Table.rest4(i)), DTip{},
                      Tb.Table.rest4(i), d),
                    DTip{}, DTip{}, DTip{}}
                case DNode{o, k0, k1, k2, k3}:
                  DNode{
                    o,
                    Env.put(
                      m, Tb.Table.way(Tb.Table.rest4(i)), k0,
                      Tb.Table.rest4(i), d),
                    k1, k2, k3}
            case 1n+j1:
              match j1:
                case 0n:
                  match t:
                    case DTip{}:
                      DNode{
                        None{}, DTip{},
                        Env.put(
                          m, Tb.Table.way(Tb.Table.rest4(i)), DTip{},
                          Tb.Table.rest4(i), d),
                        DTip{}, DTip{}}
                    case DNode{o, k0, k1, k2, k3}:
                      DNode{
                        o, k0,
                        Env.put(
                          m, Tb.Table.way(Tb.Table.rest4(i)), k1,
                          Tb.Table.rest4(i), d),
                        k2, k3}
                case 1n+j2:
                  match j2:
                    case 0n:
                      match t:
                        case DTip{}:
                          DNode{
                            None{}, DTip{}, DTip{},
                            Env.put(
                              m, Tb.Table.way(Tb.Table.rest4(i)),
                              DTip{}, Tb.Table.rest4(i), d),
                            DTip{}}
                        case DNode{o, k0, k1, k2, k3}:
                          DNode{
                            o, k0, k1,
                            Env.put(
                              m, Tb.Table.way(Tb.Table.rest4(i)), k2,
                              Tb.Table.rest4(i), d),
                            k3}
                    case 1n+j3:
                      match t:
                        case DTip{}:
                          DNode{
                            None{}, DTip{}, DTip{}, DTip{},
                            Env.put(
                              m, Tb.Table.way(Tb.Table.rest4(i)),
                              DTip{}, Tb.Table.rest4(i), d)}
                        case DNode{o, k0, k1, k2, k3}:
                          DNode{
                            o, k0, k1, k2,
                            Env.put(
                              m, Tb.Table.way(Tb.Table.rest4(i)), k3,
                              Tb.Table.rest4(i), d)}

def Env.find(+env: DTable, +i: Nat) -> Lookup:
  match env:
    case MkDT{+ds, ex}:
      Env.get(
        Tb.Table.bits(),
        Tb.Table.way(Tb.Table.path(i)),
        ds,
        Tb.Table.path(i),
        i)

# Add a declaration under its own name. The expression table moves into the
# new environment rather than being copied, which an affine language gives
# for nothing.
def Env.add(+env: DTable, +d: Decl) -> DTable:
  match env:
    case MkDT{+ds, ex}:
      MkDT{
        Env.put(
          Tb.Table.bits(),
          Tb.Table.way(Tb.Table.path(Decl.id(d))),
          ds,
          Tb.Table.path(Decl.id(d)),
          d),
        ex}


# Every declaration of a list, under its own name. For a hand-built
# environment, where the list is written out in the test itself.
def Env.of_list(ds: List<&2, Decl>, +acc: DTable) -> DTable:
  match ds:
    case Nil{}:
      acc
    case Con{h, t}:
      Env.of_list(t, Env.add(acc, h))
