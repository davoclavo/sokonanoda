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
    IO.print("good    expect accept  got " ++ Main.show(K.Kernel.check_all(Main.env_good(), 400n, Nil{})))
    IO.print("bad     expect reject  got " ++ Main.show(K.Kernel.check_all(Main.env_bad(), 400n, Nil{})))
    IO.print("forward expect reject  got " ++ Main.show(K.Kernel.check_all(Main.env_forward(), 400n, Nil{})))
