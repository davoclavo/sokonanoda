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

type Decl is Data:
  DAxiom{id: Nat, ps: List<&2, Nat>, ty: T.Term}
  DDef{id: Nat, ps: List<&2, Nat>, ty: T.Term, val: T.Term}
  DThm{id: Nat, ps: List<&2, Nat>, ty: T.Term, val: T.Term}

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

# True when this declaration is a theorem, whose type must be a Prop.
def Decl.is_thm(d: Decl) -> Bool:
  match d:
    case DAxiom{id, ps, ty}:
      False{}
    case DDef{id, ps, ty, val}:
      False{}
    case DThm{id, ps, ty, val}:
      True{}

# True when this declaration has a value, so delta reduction can unfold it.
def Decl.is_def(d: Decl) -> Bool:
  match d:
    case DAxiom{id, ps, ty}:
      False{}
    case DDef{id, ps, ty, val}:
      True{}
    case DThm{id, ps, ty, val}:
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

# The level parameters a declaration takes.
def Decl.params(d: Decl) -> List<&2, Nat>:
  match d:
    case DAxiom{id, ps, ty}:
      ps
    case DDef{id, ps, ty, val}:
      ps
    case DThm{id, ps, ty, val}:
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

# Find a declaration by id.
def Env.find(env: List<&2, Decl>, +i: Nat) -> Lookup:
  match env:
    case Nil{}:
      LMissing{}
    case Con{+h, t}:
      Env.pick(Nat.is_eq(Decl.id(h), i), LFound{h}, Env.find(t, i))
