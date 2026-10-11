# The types of the four quotient declarations.
#
# A quotient is not derived from anything: Lean's kernel adds `Quot`,
# `Quot.mk`, `Quot.lift` and `Quot.ind` with types it writes itself. A file
# states them, so a kernel that takes the statement on trust will accept a
# proof the quotient should not allow, which is why a file with a quotient
# used to answer `declined`.
#
# These are those four types. With `u` the first level parameter and `v` the
# second:
#
#   Quot      : Pi a : Sort u, Pi r : (a -> a -> Prop), Sort u
#   Quot.mk   : Pi a : Sort u, Pi r : .., Pi x : a, Quot a r
#   Quot.lift : Pi a : Sort u, Pi r : .., Pi b : Sort v,
#               Pi f : (a -> b),
#               Pi h : (Pi x y : a, Pi _ : r x y, Eq b (f x) (f y)),
#               Pi q : Quot a r, b
#   Quot.ind  : Pi a : Sort u, Pi r : .., Pi b : (Quot a r -> Prop),
#               Pi h : (Pi x : a, b (Quot.mk a r x)),
#               Pi q : Quot a r, b q
#
# The names of `Quot` and `Quot.mk` come from the file, by the kind each
# quotient line states. The name of `Eq` comes from the reader, which finds it
# by its spelling as it finds `Nat`.
#
# A kind this does not know gives `T.TUnk`, which converts with nothing.

import Base
import ./Term.bend as T
import ./Level.bend as L
import ./Env.bend as E
import ./Eval.bend as V

# The names a quotient's type needs, gathered from the file.
type QN is Data:
  MkQN{ty: Nat, mk: Nat}

def Quo.ty_of(q: QN) -> Nat:
  match q:
    case MkQN{t, m}:
      t

def Quo.mk_of(q: QN) -> Nat:
  match q:
    case MkQN{t, m}:
      m

# Record a name if the declaration is the quotient type or its constructor.
# Any other kind, and the number nine a declaration that is not a quotient
# answers with, leaves the pair alone.
def Quo.put(kind: Nat, +id: Nat, +q: QN) -> QN:
  match kind:
    case 0n:
      MkQN{id, Quo.mk_of(q)}
    case 1n+k:
      match k:
        case 0n:
          MkQN{Quo.ty_of(q), id}
        case 1n+j:
          q

def Quo.scan(ds: List<&2, E.Decl>, q: QN) -> QN:
  match ds:
    case Nil{}:
      q
    case Con{+h, t}:
      Quo.scan(t, Quo.put(E.Decl.quot_kind(h), E.Decl.id(h), q))

# `a -> a -> Prop`, where `a` is the binder just outside.
def Quo.rel() -> T.Term:
  T.TPi{T.TVar{0n}, T.TPi{T.TVar{1n}, T.TSort{L.LZero{}}}}

# `Quot a r`, where `a` is `da` binders in and `r` is `dr`.
def Quo.quot_at(+qt: Nat, +da: Nat, +dr: Nat) -> T.Term:
  V.Eval.rebuild(
    [T.TVar{da}, T.TVar{dr}], T.TConst{qt, [L.LPar{0n}]})

def Quo.want_type() -> T.Term:
  T.TPi{
    T.TSort{L.LPar{0n}},
    T.TPi{Quo.rel(), T.TSort{L.LPar{0n}}}}

def Quo.want_mk(+qt: Nat) -> T.Term:
  T.TPi{
    T.TSort{L.LPar{0n}},
    T.TPi{
      Quo.rel(),
      T.TPi{T.TVar{1n}, Quo.quot_at(qt, 2n, 1n)}}}

def Quo.want_lift(+qt: Nat, +eqn: Nat) -> T.Term:
  T.TPi{
    T.TSort{L.LPar{0n}},
    T.TPi{
      Quo.rel(),
      T.TPi{
        T.TSort{L.LPar{1n}},
        T.TPi{
          T.TPi{T.TVar{2n}, T.TVar{1n}},
          T.TPi{
            T.TPi{
              T.TVar{3n},
              T.TPi{
                T.TVar{4n},
                T.TPi{
                  V.Eval.rebuild([T.TVar{1n}, T.TVar{0n}], T.TVar{4n}),
                  V.Eval.rebuild(
                    [T.TVar{4n},
                     T.TApp{T.TVar{3n}, T.TVar{2n}},
                     T.TApp{T.TVar{3n}, T.TVar{1n}}],
                    T.TConst{eqn, [L.LPar{1n}]})}}},
            T.TPi{Quo.quot_at(qt, 4n, 3n), T.TVar{3n}}}}}}}

def Quo.want_ind(+qt: Nat, +qmk: Nat) -> T.Term:
  T.TPi{
    T.TSort{L.LPar{0n}},
    T.TPi{
      Quo.rel(),
      T.TPi{
        T.TPi{Quo.quot_at(qt, 1n, 0n), T.TSort{L.LZero{}}},
        T.TPi{
          T.TPi{
            T.TVar{2n},
            T.TApp{
              T.TVar{1n},
              V.Eval.rebuild(
                [T.TVar{3n}, T.TVar{2n}, T.TVar{0n}],
                T.TConst{qmk, [L.LPar{0n}]})}},
          T.TPi{
            Quo.quot_at(qt, 3n, 2n),
            T.TApp{T.TVar{2n}, T.TVar{0n}}}}}}}

# The type the file should state for the quotient of this kind.
def Quo.want(kind: Nat, +qt: Nat, +qmk: Nat, +eqn: Nat) -> T.Term:
  match kind:
    case 0n:
      Quo.want_type()
    case 1n+k:
      match k:
        case 0n:
          Quo.want_mk(qt)
        case 1n+j:
          match j:
            case 0n:
              Quo.want_lift(qt, eqn)
            case 1n+i:
              match i:
                case 0n:
                  Quo.want_ind(qt, qmk)
                case 1n+z:
                  T.TUnk{}
