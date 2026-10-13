# The path an index takes through a binary trie.
#
# `Table.bend` holds the tables of levels and of numbers, and `Term.bend`
# holds the table of expressions, because `Term.subst` must resolve a
# reference and `Term.bend` may not import `Table.bend`. Both need these five
# lines, so the lines live here, below each of them.

import Base

# A bound on the number of bits an index has. A Bend `Nat` holds less than
# 2^48, so no index reaches this. The descent stops when the index runs out,
# not here; this is only what makes the recursion terminate.
def Idx.bits() -> Nat:
  48n

# Is this index the one stored at the node the descent has reached?
def Idx.here(+i: Nat) -> Bool:
  Nat.is_eq(i, 0n)

# Does the rest of this index take the low half?
def Idx.low(+i: Nat) -> Bool:
  Nat.is_eq(Nat.mod(i, 2n), 0n)

# The index with the bit this level used taken off.
def Idx.rest(+i: Nat) -> Nat:
  Nat.div(i, 2n)

# The path an index takes. One more than the index, so that the index itself
# is reached when the path runs out.
def Idx.path(+i: Nat) -> Nat:
  1n+i

# The same path, read four ways at a time.
#
# A write to a trie rebuilds the path, so the depth is what it costs. Two
# million writes take 2.22 s through a two-way trie and 1.52 s through a
# four-way one, where the depth is halved and a node holds four children
# instead of two. Eight ways is 1.48 s and sixteen is 1.71, so four is
# where it settles.
#
# Zero says the descent has arrived. Any other answer is one more than the
# child to take, and `Idx.rest4` is the rest of the path. The digits of the
# path in base four are unique, so no two indices share a path.
def Idx.ways() -> Nat:
  4n

def Idx.way_pick(stop: Bool, +i: Nat) -> Nat:
  match stop:
    case True{}:
      0n
    case False{}:
      1n+Nat.mod(i, Idx.ways())

def Idx.way(+i: Nat) -> Nat:
  Idx.way_pick(Nat.is_eq(i, 0n), i)

def Idx.rest4(+i: Nat) -> Nat:
  Nat.div(i, Idx.ways())
