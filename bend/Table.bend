# Indexed tables for the reader.
#
# The level table and the expression table are read far more often than they
# are written: a line names an expression by index, and a large export names
# tens of thousands. A list makes each of those a walk, so reading a file
# costs the square of its size. Reading the arena's 3.7 MB `init-prelude`
# took 29 seconds that way and takes one second this way.
#
# A table here is a binary trie on the bits of the index. It starts empty and
# a write creates only the nodes on its own path, so a read and a write both
# cost the number of bits and not the size of the table.
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

# How many bits of the index the tables use. Two to the eighteenth is 262144
# slots, which is more than any export the arena ships.
def Table.depth() -> Nat:
  18n

# Does this index take the low half at this level?
def Table.low(+i: Nat) -> Bool:
  Nat.is_eq(Nat.mod(i, 2n), 0n)

# The index with the bit this level used taken off.
def Table.rest(+i: Nat) -> Nat:
  Nat.div(i, 2n)

# Levels
# ------

type LTable is Data:
  LvTip{}
  LvLeaf{v: L.Level}
  LvNode{lo: LTable, hi: LTable}

def LTable.new() -> LTable:
  LvTip{}

def LTable.val(t: LTable) -> L.Level:
  match t:
    case LvTip{}:
      L.LZero{}
    case LvLeaf{v}:
      v
    case LvNode{lo, hi}:
      L.LZero{}

# The level at `i`, or zero where nothing was written. `b` says which half
# this level takes; start it with `Table.low(i)`.
def LTable.get(d: Nat, b: Bool, t: LTable, +i: Nat) -> L.Level:
  match d:
    case 0n:
      LTable.val(t)
    case 1n+p:
      match b:
        case True{}:
          match t:
            case LvTip{}:
              L.LZero{}
            case LvLeaf{v}:
              v
            case LvNode{lo, hi}:
              LTable.get(
                p, Table.low(Table.rest(i)), lo, Table.rest(i))
        case False{}:
          match t:
            case LvTip{}:
              L.LZero{}
            case LvLeaf{v}:
              v
            case LvNode{lo, hi}:
              LTable.get(
                p, Table.low(Table.rest(i)), hi, Table.rest(i))

def LTable.set(d: Nat, b: Bool, t: LTable, +i: Nat, +v: L.Level) -> LTable:
  match d:
    case 0n:
      LvLeaf{v}
    case 1n+p:
      match b:
        case True{}:
          match t:
            case LvTip{}:
              LvNode{
                LTable.set(
                  p, Table.low(Table.rest(i)), LvTip{}, Table.rest(i), v),
                LvTip{}}
            case LvLeaf{o}:
              LvLeaf{v}
            case LvNode{lo, hi}:
              LvNode{
                LTable.set(
                  p, Table.low(Table.rest(i)), lo, Table.rest(i), v),
                hi}
        case False{}:
          match t:
            case LvTip{}:
              LvNode{
                LvTip{},
                LTable.set(
                  p, Table.low(Table.rest(i)), LvTip{}, Table.rest(i), v)}
            case LvLeaf{o}:
              LvLeaf{v}
            case LvNode{lo, hi}:
              LvNode{
                lo,
                LTable.set(
                  p, Table.low(Table.rest(i)), hi, Table.rest(i), v)}

# Terms
# -----

type ETable is Data:
  ExTip{}
  ExLeaf{v: T.Term}
  ExNode{lo: ETable, hi: ETable}

def ETable.new() -> ETable:
  ExTip{}

def ETable.val(t: ETable) -> T.Term:
  match t:
    case ExTip{}:
      T.TUnk{}
    case ExLeaf{v}:
      v
    case ExNode{lo, hi}:
      T.TUnk{}

# The expression at `i`. A slot nothing was written to answers the unknown
# term, so a line that names an expression the export never wrote is not
# mistaken for a real one.
def ETable.get(d: Nat, b: Bool, t: ETable, +i: Nat) -> T.Term:
  match d:
    case 0n:
      ETable.val(t)
    case 1n+p:
      match b:
        case True{}:
          match t:
            case ExTip{}:
              T.TUnk{}
            case ExLeaf{v}:
              v
            case ExNode{lo, hi}:
              ETable.get(
                p, Table.low(Table.rest(i)), lo, Table.rest(i))
        case False{}:
          match t:
            case ExTip{}:
              T.TUnk{}
            case ExLeaf{v}:
              v
            case ExNode{lo, hi}:
              ETable.get(
                p, Table.low(Table.rest(i)), hi, Table.rest(i))

def ETable.set(d: Nat, b: Bool, t: ETable, +i: Nat, +v: T.Term) -> ETable:
  match d:
    case 0n:
      ExLeaf{v}
    case 1n+p:
      match b:
        case True{}:
          match t:
            case ExTip{}:
              ExNode{
                ETable.set(
                  p, Table.low(Table.rest(i)), ExTip{}, Table.rest(i), v),
                ExTip{}}
            case ExLeaf{o}:
              ExLeaf{v}
            case ExNode{lo, hi}:
              ExNode{
                ETable.set(
                  p, Table.low(Table.rest(i)), lo, Table.rest(i), v),
                hi}
        case False{}:
          match t:
            case ExTip{}:
              ExNode{
                ExTip{},
                ETable.set(
                  p, Table.low(Table.rest(i)), ExTip{}, Table.rest(i), v)}
            case ExLeaf{o}:
              ExLeaf{v}
            case ExNode{lo, hi}:
              ExNode{
                lo,
                ETable.set(
                  p, Table.low(Table.rest(i)), hi, Table.rest(i), v)}

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

def Table.read(+t: ETable, +i: Nat) -> T.Term:
  ETable.get(Table.depth(), Table.low(i), t, i)

def Table.write(+t: ETable, +i: Nat, +v: T.Term) -> ETable:
  ETable.set(Table.depth(), Table.low(i), t, i, v)

def main() -> String:
  +e = Table.write(
    Table.write(ETable.new(), 7n, T.TVar{5n}),
    40000n, T.TSort{L.LZero{}})
  "at 7 " ++ Table.kind(Table.read(e, 7n))
    ++ ", at 40000 " ++ Table.kind(Table.read(e, 40000n))
    ++ ", at 9 " ++ Table.kind(Table.read(e, 9n))
