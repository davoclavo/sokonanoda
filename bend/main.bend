# The driver: check a small environment and print the verdict.
#
# These environments are written in Bend rather than read from a file, so this
# driver exercises the kernel without the reader. For a real export, use
# `check.bend`.
#
# Declarations are checked in order, and each one sees only the declarations
# before it, as the Lean kernel does. The checking itself lives in
# `Kernel.bend`, which `check.bend` uses as well.

import Base
import ./Level.bend as L
import ./Term.bend as T
import ./Env.bend as E
import ./Eval.bend as V
import ./Conv.bend as C
import ./Kernel.bend as K
import ./Ans.bend as A

# An environment that must be accepted.
#
#   axiom Ty  : Sort 1
#   axiom el  : Ty
#   def   idf : Ty -> Ty  := fun x => x
#   def   got : Ty        := idf el
#
# `got` exercises delta on `idf`, beta on its body, and conversion against the
# declared type.
def Main.env_good() -> List<&2, E.Decl>:
  [ E.DAxiom{0n, [], T.TSort{L.LSucc{L.LZero{}}}}
  , E.DAxiom{1n, [], T.TConst{0n, []}}
  , E.DDef{2n, [],
      T.TPi{T.TConst{0n, []}, T.TConst{0n, []}},
      T.TLam{T.TConst{0n, []}, T.TVar{0n}}}
  , E.DDef{3n, [],
      T.TConst{0n, []},
      T.TApp{T.TConst{2n, []}, T.TConst{1n, []}}}
  ]

# An environment that must be rejected. `bad` claims to be an element of `Ty`
# but its value is the function `idf`.
def Main.env_bad() -> List<&2, E.Decl>:
  [ E.DAxiom{0n, [], T.TSort{L.LSucc{L.LZero{}}}}
  , E.DAxiom{1n, [], T.TConst{0n, []}}
  , E.DDef{2n, [],
      T.TPi{T.TConst{0n, []}, T.TConst{0n, []}},
      T.TLam{T.TConst{0n, []}, T.TVar{0n}}}
  , E.DDef{3n, [],
      T.TConst{0n, []},
      T.TConst{2n, []}}
  ]

# An environment that must be rejected for a different reason: `fwd` names a
# declaration that comes after it, which the ordered check must not allow.
def Main.env_forward() -> List<&2, E.Decl>:
  [ E.DAxiom{0n, [], T.TSort{L.LSucc{L.LZero{}}}}
  , E.DDef{1n, [], T.TConst{0n, []}, T.TConst{2n, []}}
  , E.DAxiom{2n, [], T.TConst{0n, []}}
  ]

# An environment that must be accepted, and that cannot be checked without
# iota reduction.
#
#   inductive Bool : Type where tt | ff
#   Bool.rec : Pi (m : Bool -> Type), m tt -> m ff -> Pi (t : Bool), m t
#   axiom P  : Bool -> Type
#   axiom p  : P tt
#   def   q  : P (Bool.rec (fun _ => Bool) tt ff tt) := p
#
# `q` is well typed exactly when the recursor applied to `tt` reduces to its
# first minor premise. Nothing else in this file needs iota, so this is the
# regression test for it.

# `Pi (m : Bool -> Type), m tt -> m ff -> Pi (t : Bool), m t`
#
# Mind the indices. Inside the innermost body the context holds, innermost
# first, the major premise, the second minor premise, the first minor premise
# and the motive, so the motive is three binders out and not two.
def Main.rec_type() -> T.Term:
  T.TPi{
    T.TPi{T.TConst{0n, []}, T.TSort{L.LSucc{L.LZero{}}}},
    T.TPi{
      T.TApp{T.TVar{0n}, T.TConst{1n, []}},
      T.TPi{
        T.TApp{T.TVar{1n}, T.TConst{2n, []}},
        T.TPi{
          T.TConst{0n, []},
          T.TApp{T.TVar{3n}, T.TVar{0n}}}}}}

# `fun m a b => a`, the right-hand side for the first constructor.
def Main.rhs_first() -> T.Term:
  T.TLam{
    T.TPi{T.TConst{0n, []}, T.TSort{L.LSucc{L.LZero{}}}},
    T.TLam{
      T.TApp{T.TVar{0n}, T.TConst{1n, []}},
      T.TLam{T.TApp{T.TVar{1n}, T.TConst{2n, []}}, T.TVar{1n}}}}

# `fun m a b => b`, for the second constructor.
def Main.rhs_second() -> T.Term:
  T.TLam{
    T.TPi{T.TConst{0n, []}, T.TSort{L.LSucc{L.LZero{}}}},
    T.TLam{
      T.TApp{T.TVar{0n}, T.TConst{1n, []}},
      T.TLam{T.TApp{T.TVar{1n}, T.TConst{2n, []}}, T.TVar{0n}}}}

# `Bool.rec` applied to a motive, both minor premises, and the given major.
def Main.rec_app(major: T.Term) -> T.Term:
  T.TApp{
    T.TApp{
      T.TApp{
        T.TApp{T.TConst{3n, []}, T.TLam{T.TConst{0n, []}, T.TConst{0n, []}}},
        T.TConst{1n, []}},
      T.TConst{2n, []}},
    major}

# The environment, with the major premise given.
def Main.env_iota_at(major: T.Term) -> List<&2, E.Decl>:
  [ E.DInd{0n, [], T.TSort{L.LSucc{L.LZero{}}}, 0n, 0n, [1n, 2n]}
  , E.DCtor{1n, [], T.TConst{0n, []}, 0n, 0n, 0n, 0n}
  , E.DCtor{2n, [], T.TConst{0n, []}, 0n, 1n, 0n, 0n}
  , E.DRec{3n, [], Main.rec_type(), 0n, 0n, 1n, 2n, False{},
      [ E.MkRule{1n, 0n, Main.rhs_first()}
      , E.MkRule{2n, 0n, Main.rhs_second()}],
      [0n]}
  , E.DAxiom{4n, [], T.TPi{T.TConst{0n, []}, T.TSort{L.LSucc{L.LZero{}}}}}
  , E.DAxiom{5n, [], T.TApp{T.TConst{4n, []}, T.TConst{1n, []}}}
  , E.DDef{6n, [],
      T.TApp{T.TConst{4n, []}, Main.rec_app(major)},
      T.TConst{5n, []}}
  ]

# An environment that cannot be checked without projections.
#
#   inductive Bool : Type where tt | ff
#   inductive P    : Type where mk : Bool -> Bool -> P
#   axiom Q : Bool -> Type
#   axiom q : Q ff
#   def   r : Q (P.mk tt ff).1 := q
#
# `r` is well typed exactly when the second field of that constructor
# application is `ff`, which needs both the type of a projection and its
# reduction.
def Main.env_proj(field: Nat) -> List<&2, E.Decl>:
  [ E.DInd{0n, [], T.TSort{L.LSucc{L.LZero{}}}, 0n, 0n, [1n, 2n]}
  , E.DCtor{1n, [], T.TConst{0n, []}, 0n, 0n, 0n, 0n}
  , E.DCtor{2n, [], T.TConst{0n, []}, 0n, 1n, 0n, 0n}
  , E.DInd{7n, [], T.TSort{L.LSucc{L.LZero{}}}, 0n, 0n, [8n]}
  , E.DCtor{8n, [],
      T.TPi{T.TConst{0n, []}, T.TPi{T.TConst{0n, []}, T.TConst{7n, []}}},
      7n, 0n, 0n, 2n}
  , E.DAxiom{9n, [], T.TPi{T.TConst{0n, []}, T.TSort{L.LSucc{L.LZero{}}}}}
  , E.DAxiom{10n, [], T.TApp{T.TConst{9n, []}, T.TConst{2n, []}}}
  , E.DDef{11n, [],
      T.TApp{
        T.TConst{9n, []},
        T.TProj{
          7n, field,
          T.TApp{
            T.TApp{T.TConst{8n, []}, T.TConst{1n, []}},
            T.TConst{2n, []}}}},
      T.TConst{10n, []}}
  ]

# `Pi (x y f1 f2 : Bool), A x y`. Inside the last binder the context holds
# f2, f1, y, x innermost first, so x is three out and y is two.
def Main.mk_type() -> T.Term:
  T.TPi{T.TConst{0n, []},
    T.TPi{T.TConst{0n, []},
      T.TPi{T.TConst{0n, []},
        T.TPi{T.TConst{0n, []},
          T.TApp{T.TApp{T.TConst{7n, []}, T.TVar{3n}}, T.TVar{2n}}}}}}

# `A.mk tt ff tt ff`
def Main.mk_app() -> T.Term:
  T.TApp{
    T.TApp{
      T.TApp{T.TApp{T.TConst{8n, []}, T.TConst{1n, []}}, T.TConst{2n, []}},
      T.TConst{1n, []}},
    T.TConst{2n, []}}

# The same, but the structure has two parameters, which is what every
# projection in the arena has and what the simple test above lacks.
#
#   inductive A (x y : Bool) : Type where mk : Bool -> Bool -> A x y
#   def r : Q (A.mk tt ff tt ff).field := q
def Main.env_proj2(field: Nat) -> List<&2, E.Decl>:
  [ E.DInd{0n, [], T.TSort{L.LSucc{L.LZero{}}}, 0n, 0n, [1n, 2n]}
  , E.DCtor{1n, [], T.TConst{0n, []}, 0n, 0n, 0n, 0n}
  , E.DCtor{2n, [], T.TConst{0n, []}, 0n, 1n, 0n, 0n}
  , E.DInd{7n, [],
      T.TPi{T.TConst{0n, []}, T.TPi{T.TConst{0n, []}, T.TSort{L.LSucc{L.LZero{}}}}},
      2n, 0n, [8n]}
  , E.DCtor{8n, [], Main.mk_type(), 7n, 0n, 2n, 2n}
  , E.DAxiom{9n, [], T.TPi{T.TConst{0n, []}, T.TSort{L.LSucc{L.LZero{}}}}}
  , E.DAxiom{10n, [], T.TApp{T.TConst{9n, []}, T.TConst{2n, []}}}
  , E.DDef{11n, [],
      T.TApp{T.TConst{9n, []}, T.TProj{7n, field, Main.mk_app()}},
      T.TConst{10n, []}}
  ]

# A projection from a variable, which is stuck because the variable is not a
# constructor application. This is the shape every projection in the arena has
# and the shape none of the tests above had.
#
#   inductive S : Type where mk : Bool -> Bool -> S
#   def r : Pi (x : S), Bool := fun x => x.0
def Main.env_projvar(field: Nat) -> List<&2, E.Decl>:
  [ E.DInd{0n, [], T.TSort{L.LSucc{L.LZero{}}}, 0n, 0n, [1n, 2n]}
  , E.DCtor{1n, [], T.TConst{0n, []}, 0n, 0n, 0n, 0n}
  , E.DCtor{2n, [], T.TConst{0n, []}, 0n, 1n, 0n, 0n}
  , E.DInd{7n, [], T.TSort{L.LSucc{L.LZero{}}}, 0n, 0n, [8n]}
  , E.DCtor{8n, [],
      T.TPi{T.TConst{0n, []}, T.TPi{T.TConst{0n, []}, T.TConst{7n, []}}},
      7n, 0n, 0n, 2n}
  , E.DDef{11n, [],
      T.TPi{T.TConst{7n, []}, T.TConst{0n, []}},
      T.TLam{T.TConst{7n, []}, T.TProj{7n, field, T.TVar{0n}}}}
  ]

# A projection from a structure that takes a level parameter, which is the one
# thing the tests above do not have and every arena projection does.
#
#   inductive S.{u} : Sort (u+1) where mk : Sort u -> S.{u}
#   def r : Pi (x : S.{0}), Sort 0 := fun x => x.0
#
# Declarations here are written as the parser stores them, so a level
# parameter is already a position: `LPar{0}` is the first one.
def Main.env_projlv() -> List<&2, E.Decl>:
  [ E.DInd{7n, [5n], T.TSort{L.LSucc{L.LPar{0n}}}, 0n, 0n, [8n]}
  , E.DCtor{8n, [5n],
      T.TPi{T.TSort{L.LPar{0n}}, T.TConst{7n, [L.LPar{0n}]}},
      7n, 0n, 0n, 1n}
  , E.DDef{11n, [],
      T.TPi{T.TConst{7n, [L.LZero{}]}, T.TSort{L.LZero{}}},
      T.TLam{T.TConst{7n, [L.LZero{}]}, T.TProj{7n, 0n, T.TVar{0n}}}}
  ]

# "accept" or "reject".
def Main.show(a: A.Ans) -> String:
  A.Ans.show(a)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("good    expect accept  got " ++ Main.show(K.Kernel.check_all(Main.env_good(), 400n, Nil{})))
    IO.print("bad     expect reject  got " ++ Main.show(K.Kernel.check_all(Main.env_bad(), 400n, Nil{})))
    IO.print("forward expect reject  got " ++ Main.show(K.Kernel.check_all(Main.env_forward(), 400n, Nil{})))
    IO.print("iota    expect accept  got " ++ Main.show(K.Kernel.check_all(Main.env_iota_at(T.TConst{1n, []}), 4000n, Nil{})))
    IO.print("iotabad expect reject  got " ++ Main.show(K.Kernel.check_all(Main.env_iota_at(T.TConst{2n, []}), 4000n, Nil{})))
    IO.print("proj 1  expect accept  got " ++ Main.show(K.Kernel.check_all(Main.env_proj(1n), 4000n, Nil{})))
    IO.print("proj 0  expect reject  got " ++ Main.show(K.Kernel.check_all(Main.env_proj(0n), 4000n, Nil{})))
    IO.print("proj2 1 expect accept  got " ++ Main.show(K.Kernel.check_all(Main.env_proj2(1n), 4000n, Nil{})))
    IO.print("proj2 0 expect reject  got " ++ Main.show(K.Kernel.check_all(Main.env_proj2(0n), 4000n, Nil{})))
    IO.print("proj2 field1 == ff  expect accept  got " ++ A.Ans.show(C.Conv.eq(4000n, Main.env_proj2(1n), T.TProj{7n, 1n, Main.mk_app()}, T.TConst{2n, []})))
    IO.print("proj2 field0 == tt  expect accept  got " ++ A.Ans.show(C.Conv.eq(4000n, Main.env_proj2(1n), T.TProj{7n, 0n, Main.mk_app()}, T.TConst{1n, []})))
    IO.print("projvar 0 expect accept  got " ++ Main.show(K.Kernel.check_all(Main.env_projvar(0n), 4000n, Nil{})))
    IO.print("projvar 1 expect accept  got " ++ Main.show(K.Kernel.check_all(Main.env_projvar(1n), 4000n, Nil{})))
    IO.print("projlv  expect accept  got " ++ Main.show(K.Kernel.check_all(Main.env_projlv(), 4000n, Nil{})))
    IO.print("rec tt == tt   expect accept  got " ++ Main.show(C.Conv.eq(4000n, Main.env_iota_at(T.TConst{1n, []}), Main.rec_app(T.TConst{1n, []}), T.TConst{1n, []})))
    IO.print("rec ff == ff   expect accept  got " ++ Main.show(C.Conv.eq(4000n, Main.env_iota_at(T.TConst{1n, []}), Main.rec_app(T.TConst{2n, []}), T.TConst{2n, []})))
    IO.print("rec tt == ff   expect reject  got " ++ Main.show(C.Conv.eq(4000n, Main.env_iota_at(T.TConst{1n, []}), Main.rec_app(T.TConst{1n, []}), T.TConst{2n, []})))
