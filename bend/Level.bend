# Universe levels, as the Lean kernel has them.
#
# A level is zero, a successor, a max, an imax, or a parameter. A parameter is
# a Nat index into the declaration's parameter list, not a name: a Bend string
# is a linked list of characters, so an index compares in constant time where
# a name would not.
#
# imax is the awkward one. `imax a b` is zero when b is zero and `max a b`
# otherwise, so it cannot be decided while b is a bare parameter. Every
# function here keeps that case rather than guessing.
#
# Two of Bend's rules shape this file. A `match` may only scrutinize a
# parameter or a field, never a computed value, so every test on a computed
# Bool goes through `Level.pick`. A def may only call a def declared above it,
# so the order here is bottom up.
#
# Constructor names are global in Bend, so these carry an `L` prefix to stay
# clear of Base, where `Succ` already belongs to Nat.

import Base

type Level is Data:
  LZero{}
  LSucc{l: Level}
  LMax{a: Level, b: Level}
  LIMax{a: Level, b: Level}
  LPar{i: Nat}

# Choose between two levels on a computed Bool. A match needs a parameter.
def Level.pick(b: Bool, x: Level, y: Level) -> Level:
  match b:
    case True{}:
      x
    case False{}:
      y

# Add `n` successors to `l`.
def Level.bump(n: Nat, l: Level) -> Level:
  match n:
    case 0n:
      l
    case 1n+p:
      LSucc{Level.bump(p, l)}

# True when this level is zero under every assignment of its parameters.
def Level.is_zero(l: Level) -> Bool:
  match l:
    case LZero{}:
      True{}
    case LSucc{x}:
      False{}
    case LMax{a, b}:
      Bool.and(Level.is_zero(a), Level.is_zero(b))
    case LIMax{a, b}:
      Level.is_zero(b)
    case LPar{i}:
      False{}

# True when this level is a successor under every assignment, so never zero.
def Level.is_succ(l: Level) -> Bool:
  match l:
    case LZero{}:
      False{}
    case LSucc{x}:
      True{}
    case LMax{a, b}:
      Bool.or(Level.is_succ(a), Level.is_succ(b))
    case LIMax{a, b}:
      Level.is_succ(b)
    case LPar{i}:
      False{}

# The smart constructor for max. A zero side vanishes.
def Level.mk_max(+a: Level, +b: Level) -> Level:
  Level.pick(
    Level.is_zero(a),
    b,
    Level.pick(Level.is_zero(b), a, LMax{a, b}))

# The smart constructor for imax. It collapses to zero when the right side is
# zero, to max when the right side is a successor, and otherwise stays an imax
# because the answer depends on an assignment this kernel does not have.
def Level.mk_imax(+a: Level, +b: Level) -> Level:
  Level.pick(
    Level.is_zero(b),
    LZero{},
    Level.pick(Level.is_succ(b), Level.mk_max(a, b), LIMax{a, b}))

# Normalize bottom up, with the smart constructors.
def Level.norm(l: Level) -> Level:
  match l:
    case LZero{}:
      LZero{}
    case LSucc{x}:
      LSucc{Level.norm(x)}
    case LMax{a, b}:
      Level.mk_max(Level.norm(a), Level.norm(b))
    case LIMax{a, b}:
      Level.mk_imax(Level.norm(a), Level.norm(b))
    case LPar{i}:
      LPar{i}

# Equality of two levels as syntax. Run `Level.norm` on both sides first.
# This is not equality under every assignment of the parameters: deciding that
# needs the case split on imax that the Lean kernel performs, which this
# kernel does not yet do.
def Level.eq(+fuel: Nat, a: Level, b: Level) -> Bool:
  match fuel:
    case 0n:
      False{}
    case 1n+f:
      match a b:
        case LZero{} LZero{}:
          True{}
        case LSucc{x} LSucc{y}:
          Level.eq(f, x, y)
        case LMax{x1, y1} LMax{x2, y2}:
          Bool.and(Level.eq(f, x1, x2), Level.eq(f, y1, y2))
        case LIMax{x1, y1} LIMax{x2, y2}:
          Bool.and(Level.eq(f, x1, x2), Level.eq(f, y1, y2))
        case LPar{i} LPar{j}:
          Nat.is_eq(i, j)
        case x y:
          False{}

# The i-th level of a list, or `LPar{i}` when the list is too short. The list
# comes first because Bend matches scrutinees in binder order and the list is
# what shrinks.
def Level.nth(vs: List<&2, Level>, i: Nat) -> Level:
  match vs:
    case Nil{}:
      LPar{i}
    case Con{h, t}:
      match i:
        case 0n:
          h
        case 1n+p:
          Level.nth(t, p)

# Substitute the parameters of a level. `LPar{i}` becomes the i-th entry of
# `vs`, and an index past the end of `vs` stays as it was.
def Level.subst(l: Level, +vs: List<&2, Level>) -> Level:
  match l:
    case LZero{}:
      LZero{}
    case LSucc{x}:
      LSucc{Level.subst(x, vs)}
    case LMax{a, b}:
      LMax{Level.subst(a, vs), Level.subst(b, vs)}
    case LIMax{a, b}:
      LIMax{Level.subst(a, vs), Level.subst(b, vs)}
    case LPar{i}:
      Level.nth(vs, i)
