# Indexed tables for the reader and the environment.
#
# A line names an expression by index, and a large export names tens of
# thousands. A list makes each of those a walk, so reading a file costs the
# square of its size: the arena's 3.7 MB `init-prelude` took 29 seconds that
# way and takes two this way.
#
# A table here is a binary trie on the bits of the index, holding a value at
# every node rather than only at the leaves. So the path to an index is as
# long as that index has bits, a small index costs few steps, and no two
# indices ever share a slot. A fixed depth would be wrong: two indices that
# agree on the low bits of the depth would collide, and the table would hand
# back a declaration under the wrong name.
#
# Base has `Array`, which is the shape of a full table, and it cannot be used.
# `Array` is declared `is Type`, so it is linear: a read consumes it and hands
# it back as half of a pair, and every caller has to thread it onward. The
# kernel passes its tables to reduction, to conversion and to inference, often
# twice in one expression, so threading would turn the whole kernel inside
# out. These types are `Data`, which can be used many times, and that is the
# whole reason they exist.
#
# Two things this file learned the hard way.
#
# A table built from `TNode{t, t}`, sharing one subtree in both halves, is
# cheap to build and ruinous to read: every read descends through as many
# duplications as there are levels, and each one copies. A 6 kB export went
# from one second to over two hundred. Nothing here shares.
#
# Which half to take is a computed value, and a match cannot scrutinize one.
# Choosing with a helper and then descending would make the helper and the
# descent call each other, which Bend forbids. So the choice travels in as a
# parameter, and the caller computes the first one.

import Base
import ./Level.bend as L
import ./Term.bend as T
import ./Idx.bend as Ix

# The five lines of the descent live in `Idx.bend`, because `Term.bend` holds
# the table of expressions and may not import this file.
def Table.bits() -> Nat:
  Ix.Idx.bits()

def Table.here(+i: Nat) -> Bool:
  Ix.Idx.here(i)

def Table.low(+i: Nat) -> Bool:
  Ix.Idx.low(i)

def Table.rest(+i: Nat) -> Nat:
  Ix.Idx.rest(i)

def Table.path(+i: Nat) -> Nat:
  Ix.Idx.path(i)

# Levels
# ------

type LTable is Data:
  LvTip{}
  LvNode{v: Maybe<&2, L.Level>, lo: LTable, hi: LTable}

def LTable.new() -> LTable:
  LvTip{}

def LTable.or_zero(m: Maybe<&2, L.Level>) -> L.Level:
  match m:
    case None{}:
      L.LZero{}
    case Some{v}:
      v

def LTable.at(t: LTable) -> L.Level:
  match t:
    case LvTip{}:
      L.LZero{}
    case LvNode{v, lo, hi}:
      LTable.or_zero(v)

# The level at `i`, or zero where nothing was written. `stop` says the path
# ends at this node and `b` says which half it takes otherwise. Start both
# from `Table.path(i)`.
def LTable.get(
  n: Nat, stop: Bool, b: Bool, t: LTable, +i: Nat
) -> L.Level:
  match n:
    case 0n:
      L.LZero{}
    case 1n+m:
      match stop:
        case True{}:
          LTable.at(t)
        case False{}:
          match b:
            case True{}:
              match t:
                case LvTip{}:
                  L.LZero{}
                case LvNode{v, lo, hi}:
                  LTable.get(
                    m,
                    Table.here(Table.rest(i)),
                    Table.low(Table.rest(i)),
                    lo,
                    Table.rest(i))
            case False{}:
              match t:
                case LvTip{}:
                  L.LZero{}
                case LvNode{v, lo, hi}:
                  LTable.get(
                    m,
                    Table.here(Table.rest(i)),
                    Table.low(Table.rest(i)),
                    hi,
                    Table.rest(i))

def LTable.set(
  n: Nat, stop: Bool, b: Bool, t: LTable, +i: Nat, +v: L.Level
) -> LTable:
  match n:
    case 0n:
      t
    case 1n+m:
      match stop:
        case True{}:
          match t:
            case LvTip{}:
              LvNode{Some{v}, LvTip{}, LvTip{}}
            case LvNode{o, lo, hi}:
              LvNode{Some{v}, lo, hi}
        case False{}:
          match b:
            case True{}:
              match t:
                case LvTip{}:
                  LvNode{
                    None{},
                    LTable.set(
                      m,
                      Table.here(Table.rest(i)),
                      Table.low(Table.rest(i)),
                      LvTip{},
                      Table.rest(i),
                      v),
                    LvTip{}}
                case LvNode{o, lo, hi}:
                  LvNode{
                    o,
                    LTable.set(
                      m,
                      Table.here(Table.rest(i)),
                      Table.low(Table.rest(i)),
                      lo,
                      Table.rest(i),
                      v),
                    hi}
            case False{}:
              match t:
                case LvTip{}:
                  LvNode{
                    None{},
                    LvTip{},
                    LTable.set(
                      m,
                      Table.here(Table.rest(i)),
                      Table.low(Table.rest(i)),
                      LvTip{},
                      Table.rest(i),
                      v)}
                case LvNode{o, lo, hi}:
                  LvNode{
                    o,
                    lo,
                    LTable.set(
                      m,
                      Table.here(Table.rest(i)),
                      Table.low(Table.rest(i)),
                      hi,
                      Table.rest(i),
                      v)}

# Terms
# -----
#
# The table of expressions is in `Term.bend`, because `Term.subst` must
# resolve a reference and `Term.bend` may not import this file. These two
# stand here so that the name the rest of the kernel calls does not change.

def ETable.new() -> T.ETable:
  T.ETable.new()

# Numbers
# -------
#
# A table of numbers keyed by a name, for a fact about a name that the reader
# learns from its name line and the kernel needs much later.

type NTable is Data:
  NmTip{}
  NmNode{v: Maybe<&2, Nat>, lo: NTable, hi: NTable}

def NTable.new() -> NTable:
  NmTip{}

def NTable.or_zero(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{v}:
      v

def NTable.at(t: NTable) -> Nat:
  match t:
    case NmTip{}:
      0n
    case NmNode{v, lo, hi}:
      NTable.or_zero(v)

def NTable.get(n: Nat, stop: Bool, b: Bool, t: NTable, +i: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+m:
      match stop:
        case True{}:
          NTable.at(t)
        case False{}:
          match b:
            case True{}:
              match t:
                case NmTip{}:
                  0n
                case NmNode{v, lo, hi}:
                  NTable.get(
                    m,
                    Table.here(Table.rest(i)),
                    Table.low(Table.rest(i)),
                    lo,
                    Table.rest(i))
            case False{}:
              match t:
                case NmTip{}:
                  0n
                case NmNode{v, lo, hi}:
                  NTable.get(
                    m,
                    Table.here(Table.rest(i)),
                    Table.low(Table.rest(i)),
                    hi,
                    Table.rest(i))

def NTable.set(
  n: Nat, stop: Bool, b: Bool, t: NTable, +i: Nat, +v: Nat
) -> NTable:
  match n:
    case 0n:
      t
    case 1n+m:
      match stop:
        case True{}:
          match t:
            case NmTip{}:
              NmNode{Some{v}, NmTip{}, NmTip{}}
            case NmNode{o, lo, hi}:
              NmNode{Some{v}, lo, hi}
        case False{}:
          match b:
            case True{}:
              match t:
                case NmTip{}:
                  NmNode{
                    None{},
                    NTable.set(
                      m,
                      Table.here(Table.rest(i)),
                      Table.low(Table.rest(i)),
                      NmTip{},
                      Table.rest(i),
                      v),
                    NmTip{}}
                case NmNode{o, lo, hi}:
                  NmNode{
                    o,
                    NTable.set(
                      m,
                      Table.here(Table.rest(i)),
                      Table.low(Table.rest(i)),
                      lo,
                      Table.rest(i),
                      v),
                    hi}
            case False{}:
              match t:
                case NmTip{}:
                  NmNode{
                    None{},
                    NmTip{},
                    NTable.set(
                      m,
                      Table.here(Table.rest(i)),
                      Table.low(Table.rest(i)),
                      NmTip{},
                      Table.rest(i),
                      v)}
                case NmNode{o, lo, hi}:
                  NmNode{
                    o,
                    lo,
                    NTable.set(
                      m,
                      Table.here(Table.rest(i)),
                      Table.low(Table.rest(i)),
                      hi,
                      Table.rest(i),
                      v)}

def Table.read_nat(+t: NTable, +i: Nat) -> Nat:
  NTable.get(
    Table.bits(),
    Table.here(Table.path(i)),
    Table.low(Table.path(i)),
    t,
    Table.path(i))

def Table.write_nat(+t: NTable, +i: Nat, +v: Nat) -> NTable:
  NTable.set(
    Table.bits(),
    Table.here(Table.path(i)),
    Table.low(Table.path(i)),
    t,
    Table.path(i),
    v)

def Table.read(+t: T.ETable, +i: Nat) -> T.Term:
  T.Term.read_ex(t, i)

def Table.write(+t: T.ETable, +i: Nat, +v: T.Term) -> T.ETable:
  T.Term.write_ex(t, i, v)

def Table.read_lv(+t: LTable, +i: Nat) -> L.Level:
  LTable.get(
    Table.bits(),
    Table.here(Table.path(i)),
    Table.low(Table.path(i)),
    t,
    Table.path(i))

def Table.write_lv(+t: LTable, +i: Nat, +v: L.Level) -> LTable:
  LTable.set(
    Table.bits(),
    Table.here(Table.path(i)),
    Table.low(Table.path(i)),
    t,
    Table.path(i),
    v)

# A name for each kind of term, so the test below can show that a read gives
# back what a write put there.
def Table.kind(t: T.Term) -> String:
  match t:
    case T.TVar{i}:
      "var"
    case T.TSort{l}:
      "sort"
    case T.TUnk{}:
      "unset"
    case x:
      "other"

# The indices here are chosen to catch the two mistakes this file has made:
# 0 against 1 is the shortest pair of paths, and 7 against 262151, which is
# 7 plus two to the eighteenth, is the pair a table of fixed depth 18 would
# have put in one slot.
def main() -> String:
  +e = Table.write(
    Table.write(
      Table.write(
        Table.write(ETable.new(), 0n, T.TVar{1n}),
        1n, T.TSort{L.LZero{}}),
      7n, T.TVar{7n}),
    262151n, T.TSort{L.LZero{}})
  "0 " ++ Table.kind(Table.read(e, 0n))
    ++ ", 1 " ++ Table.kind(Table.read(e, 1n))
    ++ ", 7 " ++ Table.kind(Table.read(e, 7n))
    ++ ", 262151 " ++ Table.kind(Table.read(e, 262151n))
    ++ ", 9 " ++ Table.kind(Table.read(e, 9n))
    ++ ", 262144 " ++ Table.kind(Table.read(e, 262144n))
