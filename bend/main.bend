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
    IO.print("rec tt == tt   expect accept  got " ++ Main.show(C.Conv.eq(4000n, Main.env_iota_at(T.TConst{1n, []}), Main.rec_app(T.TConst{1n, []}), T.TConst{1n, []})))
    IO.print("rec ff == ff   expect accept  got " ++ Main.show(C.Conv.eq(4000n, Main.env_iota_at(T.TConst{1n, []}), Main.rec_app(T.TConst{2n, []}), T.TConst{2n, []})))
    IO.print("rec tt == ff   expect reject  got " ++ Main.show(C.Conv.eq(4000n, Main.env_iota_at(T.TConst{1n, []}), Main.rec_app(T.TConst{1n, []}), T.TConst{2n, []})))
