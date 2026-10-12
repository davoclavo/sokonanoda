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
