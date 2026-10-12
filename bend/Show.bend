# Printing a term.
#
# Every diagnosis up to now came from narrowing by construction: build the
# smallest input that could show a fault, and if it passes, change one thing.
# That method ran out on projections, where six hand-built shapes all pass and
# every real export still differs. What was missing is the ability to look at
# the two terms.
#
# The names are indices, because that is what this kernel stores: `c19` is the
# constant whose name index is 19, and `#0` is the innermost bound variable.
# `fuel` bounds the depth, and `..` marks where it ran out.

import Base
import ./Level.bend as L
import ./Term.bend as T

def Show.level(+fuel: Nat, l: L.Level) -> String:
  match fuel:
    case 0n:
      ".."
    case 1n+f:
      match l:
        case L.LZero{}:
          "0"
        case L.LSucc{x}:
          "(s " ++ Show.level(f, x) ++ ")"
        case L.LMax{a, b}:
          "(max " ++ Show.level(f, a) ++ " " ++ Show.level(f, b) ++ ")"
        case L.LIMax{a, b}:
          "(imax " ++ Show.level(f, a) ++ " " ++ Show.level(f, b) ++ ")"
        case L.LPar{i}:
          "p" ++ Nat.show(i)

def Show.levels_rest(+fuel: Nat, ls: List<&2, L.Level>) -> String:
  match fuel:
    case 0n:
      ".."
    case 1n+f:
      match ls:
        case Nil{}:
          ""
        case Con{h, t}:
          " " ++ Show.level(f, h) ++ Show.levels_rest(f, t)

def Show.levels(+fuel: Nat, ls: List<&2, L.Level>) -> String:
  match fuel:
    case 0n:
      ".."
    case 1n+f:
      match ls:
        case Nil{}:
          ""
        case Con{h, t}:
          Show.level(f, h) ++ Show.levels_rest(f, t)

def Show.term(+fuel: Nat, t: T.Term) -> String:
  match fuel:
    case 0n:
      ".."
    case 1n+f:
      match t:
        case T.TVar{i}:
          "#" ++ Nat.show(i)
        case T.TSort{l}:
          "Sort " ++ Show.level(f, l)
        case T.TConst{n, ls}:
          "c" ++ Nat.show(n) ++ "{" ++ Show.levels(f, ls) ++ "}"
        case T.TApp{g, a}:
          "(" ++ Show.term(f, g) ++ " " ++ Show.term(f, a) ++ ")"
        case T.TLam{ty, bd}:
          "(fun :" ++ Show.term(f, ty) ++ " => " ++ Show.term(f, bd) ++ ")"
        case T.TPi{ty, bd}:
          "(Pi :" ++ Show.term(f, ty) ++ " -> " ++ Show.term(f, bd) ++ ")"
        case T.TLet{ty, v, bd}:
          "(let :" ++ Show.term(f, ty) ++ " := " ++ Show.term(f, v) ++ " in "
            ++ Show.term(f, bd) ++ ")"
        case T.TProj{tn, idx, s}:
          "(" ++ Show.term(f, s) ++ "." ++ Nat.show(idx) ++ "@" ++ Nat.show(tn) ++ ")"
        case T.TNat{v, nm, zr, sc}:
          Nat.show(v)
        case T.TUnk{}:
          "?"
        case T.TRef{+i, +k, m}:
          "@" ++ Nat.show(i) ++ "+" ++ Nat.show(k)
