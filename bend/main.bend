# The driver: check a small environment and print the verdict.
#
# There is no parser. The Rust parent reads a Lean export in NDJSON, but a
# Bend string is a linked list of characters, so reading the arena's 6 GB
# mathlib export is out of reach. The environments here are built in Bend.
#
# Declarations are checked in order, and each one sees only the declarations
# before it, as the Lean kernel does.

import Base
import ./Level.bend as L
import ./Term.bend as T
import ./Env.bend as E
import ./Eval.bend as V
import ./Conv.bend as C
import ./Infer.bend as I

# Is this term a type, that is, does its own type reduce to a sort?
def Main.is_type(+fuel: Nat, +env: List<&2, E.Decl>, ty: T.Term) -> Bool:
  I.Infer.is_sort(
    V.Eval.whnf(fuel, env, I.Infer.res_ty(I.Infer.infer(fuel, env, Nil{}, ty)), Nil{}))

# Does `v` have type `ty`?
def Main.has_type(+fuel: Nat, +env: List<&2, E.Decl>, v: T.Term, ty: T.Term) -> Bool:
  +r = I.Infer.infer(fuel, env, Nil{}, v)
  Bool.and(
    I.Infer.res_ok(r),
    C.Conv.eq(fuel, env, I.Infer.res_ty(r), ty))

# Check one declaration against the declarations before it.
def Main.check_decl(+fuel: Nat, +env: List<&2, E.Decl>, d: E.Decl) -> Bool:
  match d:
    case E.DAxiom{id, nps, ty}:
      Main.is_type(fuel, env, ty)
    case E.DDef{id, nps, +ty, val}:
      Bool.and(
        Main.is_type(fuel, env, ty),
        Main.has_type(fuel, env, val, ty))

# Check every declaration, each against the ones before it.
def Main.check_all(ds: List<&2, E.Decl>, +fuel: Nat, +acc: List<&2, E.Decl>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{+h, t}:
      Bool.and(
        Main.check_decl(fuel, acc, h),
        Main.check_all(t, fuel, Con{h, acc}))

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
  [ E.DAxiom{0n, 0n, T.TSort{L.LSucc{L.LZero{}}}}
  , E.DAxiom{1n, 0n, T.TConst{0n, []}}
  , E.DDef{2n, 0n,
      T.TPi{T.TConst{0n, []}, T.TConst{0n, []}},
      T.TLam{T.TConst{0n, []}, T.TVar{0n}}}
  , E.DDef{3n, 0n,
      T.TConst{0n, []},
      T.TApp{T.TConst{2n, []}, T.TConst{1n, []}}}
  ]

# An environment that must be rejected. `bad` claims to be an element of `Ty`
# but its value is the function `idf`.
def Main.env_bad() -> List<&2, E.Decl>:
  [ E.DAxiom{0n, 0n, T.TSort{L.LSucc{L.LZero{}}}}
  , E.DAxiom{1n, 0n, T.TConst{0n, []}}
  , E.DDef{2n, 0n,
      T.TPi{T.TConst{0n, []}, T.TConst{0n, []}},
      T.TLam{T.TConst{0n, []}, T.TVar{0n}}}
  , E.DDef{3n, 0n,
      T.TConst{0n, []},
      T.TConst{2n, []}}
  ]

# An environment that must be rejected for a different reason: `fwd` names a
# declaration that comes after it, which the ordered check must not allow.
def Main.env_forward() -> List<&2, E.Decl>:
  [ E.DAxiom{0n, 0n, T.TSort{L.LSucc{L.LZero{}}}}
  , E.DDef{1n, 0n, T.TConst{0n, []}, T.TConst{2n, []}}
  , E.DAxiom{2n, 0n, T.TConst{0n, []}}
  ]

# "accept" or "reject".
def Main.show(b: Bool) -> String:
  match b:
    case True{}:
      "accept"
    case False{}:
      "reject"

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("good    expect accept  got " ++ Main.show(Main.check_all(Main.env_good(), 400n, Nil{})))
    IO.print("bad     expect reject  got " ++ Main.show(Main.check_all(Main.env_bad(), 400n, Nil{})))
    IO.print("forward expect reject  got " ++ Main.show(Main.check_all(Main.env_forward(), 400n, Nil{})))
