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

# Normal form
# -----------
#
# Two levels are equal when they are equal under every assignment of their
# parameters. Comparing syntax does not decide that: `max u v` and `max v u`
# are the same level, and so are `max 2 1` and `2`.
#
# So a level is put in a normal form first. Every level is a max of atoms,
# where an atom is a base with a count of successors on it, and the base is
# zero, a parameter, or an imax that cannot be decided. Flattening gives the
# atoms, sorting puts them in one order, and two atoms on the same base
# collapse to the one with the larger count. A zero atom disappears when
# another atom already reaches as high.
#
# That makes max commutative, associative, idempotent and absorbing, and it
# makes two closed numerals compare by value. Those are the arena's
# `levelMaxComm`, `levelMaxAssoc`, `levelMaxIdem`, `levelMaxAbsorb` and
# `levelComp3`.

type Atom is Data:
  MkAtom{base: Level, off: Nat}

def Level.base(a: Atom) -> Level:
  match a:
    case MkAtom{b, o}:
      b

def Level.off(a: Atom) -> Nat:
  match a:
    case MkAtom{b, o}:
      o

# The larger of two counts.
def Level.max_nat(b: Bool, x: Nat, y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

# An order on constructors, so unlike bases still compare.
def Level.tag(l: Level) -> Nat:
  match l:
    case LZero{}:
      0n
    case LPar{i}:
      1n
    case LIMax{a, b}:
      2n
    case LSucc{x}:
      3n
    case LMax{a, b}:
      4n

# Take the first comparison unless it is equal.
def Level.pick_cmp(c1: Cmp, c2: Cmp) -> Cmp:
  match c1:
    case EQ{}:
      c2
    case o:
      c1

# A total order on levels, for sorting atoms. Any order will do, as long as it
# is the same every time.
def Level.cmp(a: Level, b: Level) -> Cmp:
  match a b:
    case LZero{} LZero{}:
      EQ{}
    case LPar{i} LPar{j}:
      Nat.cmp(i, j)
    case LIMax{x1, y1} LIMax{x2, y2}:
      Level.pick_cmp(Level.cmp(x1, x2), Level.cmp(y1, y2))
    case LSucc{x} LSucc{y}:
      Level.cmp(x, y)
    case LMax{x1, y1} LMax{x2, y2}:
      Level.pick_cmp(Level.cmp(x1, x2), Level.cmp(y1, y2))
    case x y:
      Nat.cmp(Level.tag(x), Level.tag(y))

# Flatten a level into atoms, adding `off` successors to each.
def Level.atoms(+fuel: Nat, l: Level, +off: Nat, +acc: List<&2, Atom>) -> List<&2, Atom>:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      match l:
        case LZero{}:
          Con{MkAtom{LZero{}, off}, acc}
        case LSucc{x}:
          Level.atoms(f, x, 1n+off, acc)
        case LMax{a, b}:
          Level.atoms(f, a, off, Level.atoms(f, b, off, acc))
        case LIMax{a, b}:
          Con{MkAtom{LIMax{a, b}, off}, acc}
        case LPar{i}:
          Con{MkAtom{LPar{i}, off}, acc}

# Where an atom belongs, given how it compares with the head.
def Level.ins_pick(
  c: Cmp, +a: Atom, +h: Atom, +t: List<&2, Atom>, rest: List<&2, Atom>
) -> List<&2, Atom>:
  match c:
    case LT{}:
      Con{a, Con{h, t}}
    case EQ{}:
      Con{
        MkAtom{
          Level.base(h),
          Level.max_nat(Nat.is_lt(Level.off(h), Level.off(a)), Level.off(a), Level.off(h))},
        t}
    case GT{}:
      Con{h, rest}

# Insert an atom into a sorted list, collapsing two atoms on the same base.
def Level.ins(xs: List<&2, Atom>, +a: Atom) -> List<&2, Atom>:
  match xs:
    case Nil{}:
      Con{a, Nil{}}
    case Con{+h, +t}:
      Level.ins_pick(
        Level.cmp(Level.base(a), Level.base(h)),
        a, h, t,
        Level.ins(t, a))

# Sort atoms by insertion. An atom list is short, so this is enough.
def Level.sort_atoms(xs: List<&2, Atom>, +acc: List<&2, Atom>) -> List<&2, Atom>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      Level.sort_atoms(t, Level.ins(acc, h))

# Does any atom reach at least `j`?
def Level.any_ge(xs: List<&2, Atom>, +j: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Nat.is_ge(Level.off(h), j), Level.any_ge(t, j))

# Choose between two atom lists on a computed Bool.
def Level.pick_atoms(b: Bool, x: List<&2, Atom>, y: List<&2, Atom>) -> List<&2, Atom>:
  match b:
    case True{}:
      x
    case False{}:
      y

# Drop a leading zero atom when another atom already reaches as high. Sorting
# puts the zero atom first, so only the head can be dropped.
def Level.drop_zero(xs: List<&2, Atom>) -> List<&2, Atom>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, +t}:
      Level.pick_atoms(
        Bool.and(Level.is_zero(Level.base(h)), Level.any_ge(t, Level.off(h))),
        t,
        Con{h, t})

# The normal form of a level: its atoms, sorted and collapsed.
def Level.nf(+fuel: Nat, l: Level) -> List<&2, Atom>:
  Level.drop_zero(
    Level.sort_atoms(Level.atoms(fuel, Level.norm(l), 0n, Nil{}), Nil{}))

# Are two atoms the same?
def Level.atom_eq(+a: Atom, +b: Atom) -> Bool:
  Bool.and(
    Level.same(Level.base(a), Level.base(b)),
    Nat.is_eq(Level.off(a), Level.off(b)))

# Are two normal forms the same?
def Level.atoms_eq(xs: List<&2, Atom>, ys: List<&2, Atom>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xr} Con{y, yr}:
      Bool.and(Level.atom_eq(x, y), Level.atoms_eq(xr, yr))
    case x y:
      False{}

# Are these two levels equal under every assignment of their parameters?
#
# This decides the question for everything except an imax whose right side is
# a bare parameter. Two such imax atoms are compared as syntax, so the case
# split the Lean kernel performs on them is still missing.
def Level.eq(+fuel: Nat, a: Level, b: Level) -> Bool:
  Level.atoms_eq(Level.nf(fuel, a), Level.nf(fuel, b))

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
