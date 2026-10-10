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
  DAxiom{id: Nat, nps: Nat, ty: T.Term}
  DDef{id: Nat, nps: Nat, ty: T.Term, val: T.Term}

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
    case DAxiom{id, nps, ty}:
      id
    case DDef{id, nps, ty, val}:
      id

# True when this declaration has a value, so delta reduction can unfold it.
def Decl.is_def(d: Decl) -> Bool:
  match d:
    case DAxiom{id, nps, ty}:
      False{}
    case DDef{id, nps, ty, val}:
      True{}

# How many level parameters a declaration takes.
def Decl.num_params(d: Decl) -> Nat:
  match d:
    case DAxiom{id, nps, ty}:
      nps
    case DDef{id, nps, ty, val}:
      nps

# The declared type of a declaration, with its level parameters replaced.
def Decl.type_at(d: Decl, +ls: List<&2, L.Level>) -> T.Term:
  match d:
    case DAxiom{id, nps, ty}:
      T.Term.subst_levels(ty, ls)
    case DDef{id, nps, ty, val}:
      T.Term.subst_levels(ty, ls)

# The value of a definition, with its level parameters replaced. An axiom has
# no value, so it answers `None`.
def Decl.value_at(d: Decl, +ls: List<&2, L.Level>) -> Maybe<&2, T.Term>:
  match d:
    case DAxiom{id, nps, ty}:
      None{}
    case DDef{id, nps, ty, val}:
      Some{T.Term.subst_levels(val, ls)}

# Find a declaration by id.
def Env.find(env: List<&2, Decl>, +i: Nat) -> Lookup:
  match env:
    case Nil{}:
      LMissing{}
    case Con{+h, t}:
      Env.pick(Nat.is_eq(Decl.id(h), i), LFound{h}, Env.find(t, i))
