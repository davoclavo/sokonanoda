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

# Structural equality of two levels, without fuel. The recursion is on both
# sides at once, so it is bounded by the smaller one.
def Level.same(a: Level, b: Level) -> Bool:
  match a b:
    case LZero{} LZero{}:
      True{}
    case LSucc{x} LSucc{y}:
      Level.same(x, y)
    case LMax{x1, y1} LMax{x2, y2}:
      Bool.and(Level.same(x1, x2), Level.same(y1, y2))
    case LIMax{x1, y1} LIMax{x2, y2}:
      Bool.and(Level.same(x1, x2), Level.same(y1, y2))
    case LPar{i} LPar{j}:
      Nat.is_eq(i, j)
    case x y:
      False{}

# The smart constructor for max. A zero side vanishes, and `max l l` is `l`.
#
# The idempotent case is not decoration. Without it the type of `Prop -> Prop`
# comes out as `Sort (max 1 1)` where the export declares `Sort 1`, and the
# conversion check compares the two as syntax and rejects a correct
# declaration. The arena's `003_arrowType` is exactly that.
def Level.mk_max(+a: Level, +b: Level) -> Level:
  Level.pick(
    Level.is_zero(a),
    b,
    Level.pick(
      Level.is_zero(b),
      a,
      Level.pick(Level.same(a, b), a, LMax{a, b})))

# The smart constructor for imax. It collapses to zero when the right side is
# zero, to max when the right side is a successor, and to the side itself when
# both sides agree, since `imax u u` is zero when `u` is zero and `max u u` as
# `u` otherwise, which is `u` either way. Only then does it stay an imax,
# because the answer depends on an assignment this kernel does not have.
#
# The idempotent case is what types a Church numeral. `Pi (_: a), a` at
# `a : Sort u` has type `Sort (imax u u)`, and without the collapse that never
# matches the `Sort u` the export declares. The arena's `030_peano1` and its
# two siblings are exactly that.
def Level.mk_imax(+a: Level, +b: Level) -> Level:
  Level.pick(
    Level.is_zero(b),
    LZero{},
    Level.pick(
      Level.is_succ(b),
      Level.mk_max(a, b),
      Level.pick(Level.same(a, b), a, LIMax{a, b})))

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

# The position of name index `j` among `ps`, as a level, or `LPar{j}` when `j`
# is not one of them. The search is over the declaration's level parameters,
# which number a handful, so it needs no table and no fuel.
def Level.param_pos(ps: List<&2, Nat>, +j: Nat, +k: Nat) -> Level:
  match ps:
    case Nil{}:
      LPar{j}
    case Con{+h, t}:
      Level.pick(Nat.is_eq(h, j), LPar{k}, Level.param_pos(t, j, 1n+k))

# Renumber a level's parameters from name index to position.
#
# A level line writes `LPar{j}` with `j` the export's name index, because that
# is what the line carries. A stored declaration has to name its parameters by
# position instead, since that is what a use site supplies. This is the
# translation.
def Level.remap(l: Level, +ps: List<&2, Nat>) -> Level:
  match l:
    case LZero{}:
      LZero{}
    case LSucc{x}:
      LSucc{Level.remap(x, ps)}
    case LMax{a, b}:
      LMax{Level.remap(a, ps), Level.remap(b, ps)}
    case LIMax{a, b}:
      LIMax{Level.remap(a, ps), Level.remap(b, ps)}
    case LPar{i}:
      Level.param_pos(ps, i, 0n)

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
