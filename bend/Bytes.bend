# A byte scanner, as the foundation of a reader for Lean exports.
#
# Why bytes and not String: a Bend String is a linked list of characters, and
# Base's `String.lines`, `String.length` and `String.split` recurse once per
# character without the call in tail position. They overflow the host stack at
# about ten thousand characters, which is upstream bendlang/bend#798 and #802.
# Measured here, `String.lines` dies on a 50 KB export while the smallest arena
# test is 3.7 MB.
#
# `File.read_bytes` gives `List<&2, U32>`, and a tail call compiles to a loop,
# so a tail-recursive walk over those bytes has no such limit. Measured here, a
# tail accumulator counts all 3741967 bytes of `init-prelude.ndjson` in 0.14 s.
#
# Keeping the recursive call in tail position is what costs the effort, because
# Bend will not let a `match` look at a computed value and will not let two defs
# call each other. The idiom throughout this file:
#
#   1. peek at the head with a small non-recursive helper,
#   2. pass the answer as a parameter of the next call,
#   3. make that call the whole body, so it is a tail call.
#
# `fuel` comes first in every signature because Bend needs the shrinking
# parameter there, and the carried flag cannot be it.

import Base

# A number and the bytes after it.
type Scan is Data:
  SOk{val: Nat, rest: List<&2, U32>}
  SBad{}

# A position in the byte stream.
type Pos is Data:
  POk{rest: List<&2, U32>}
  PBad{}

# ASCII codes this file needs.
def Bytes.zero() -> U32:
  48

def Bytes.nine() -> U32:
  57

def Bytes.newline() -> U32:
  10

def Bytes.quote() -> U32:
  34

# Is this byte a decimal digit?
def Bytes.is_digit(+c: U32) -> Bool:
  Bool.and(U32.is_ge(c, Bytes.zero()), U32.is_le(c, Bytes.nine()))

# The value of a digit byte. A non-digit answers zero, so guard it.
def Bytes.digit_val(c: U32) -> Nat:
  U32.to_nat(U32.sub(c, Bytes.zero()))

# Peek: does the stream start with a digit? Non-recursive, so it may look.
def Bytes.starts_digit(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{c, r}:
      Bytes.is_digit(c)

# Peek: does the stream start with this byte?
def Bytes.starts_with(xs: List<&2, U32>, +b: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{c, r}:
      U32.is_eq(c, b)

# Peek: is the stream empty?
def Bytes.is_empty(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{c, r}:
      False{}

# One for true, zero for false. Base has no `Bool.to_nat`.
def Bytes.bool_nat(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# The code of a character. Base has no `Char.code`.
def Bytes.char_code(c: Char) -> U32:
  match c:
    case Chr{x}:
      x

# One if the two bytes are equal, zero if not. Used to count without a branch.
def Bytes.eq_one(a: U32, b: U32) -> Nat:
  Bytes.bool_nat(U32.is_eq(a, b))

# Choose between two numbers on a computed Bool.
def Bytes.pick_nat(b: Bool, x: Nat, y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

# The largest number this reader will read. A Bend `Nat` holds up to 2^48-1,
# and Lean's own prelude writes `18446744073709551616` for the size of a
# `UInt64`, which is past that. Reading it crashed the kernel, and a crash is
# the one answer worse than not knowing. So the reader stops here instead, and
# a literal that reaches this cap is read as unknown.
#
# The cap is 2^40, written as a product because Bend reads a number up to
# 2^32-1 in source. Ten times this one and nine more is 1.1e13, well inside
# the 2.8e14 an immediate holds, so the accumulator never overflows.
#
# A cap of 2^31 was the first number here, and it was too low to read
# `4294967296`, the size of a `UInt32`. The prelude decides
# `1114112 < UInt32.size` to show that every `Char` fits a `UInt32`, and an
# unknown literal there made the whole file decline. That number and
# `18446744073709551616` are the only literals in the corpus above 2^31, and
# the second one is past what an immediate holds whatever this cap says.
def Bytes.nat_cap() -> Nat:
  Nat.mul(1073741824n, 1024n)

# One more digit, or the cap. The cap is below 2^48 by enough that ten times
# it and nine more is still an immediate, so this never overflows.
def Bytes.digit_acc(+acc: Nat, +d: Nat) -> Nat:
  Bytes.pick_nat(
    Nat.is_lt(Nat.add(Nat.mul(acc, 10n), d), Bytes.nat_cap()),
    Nat.add(Nat.mul(acc, 10n), d),
    Bytes.nat_cap())

# Read a decimal number. `go` says the head is a digit, which the caller
# establishes with `Bytes.starts_digit`. The recursive call is the whole body.
def Bytes.digits(fuel: Nat, go: Bool, +acc: Nat, xs: List<&2, U32>) -> Scan:
  match fuel:
    case 0n:
      SBad{}
    case 1n+f:
      match go:
        case False{}:
          SOk{acc, xs}
        case True{}:
          match xs:
            case Nil{}:
              SOk{acc, Nil{}}
            case Con{c, +r}:
              Bytes.digits(
                f,
                Bytes.starts_digit(r),
                Bytes.digit_acc(acc, Bytes.digit_val(c)),
                r)

# Read a decimal number from the head of the stream.
def Bytes.number(fuel: Nat, +xs: List<&2, U32>) -> Scan:
  Bytes.digits(fuel, Bytes.starts_digit(xs), 0n, xs)

# Match a literal byte prefix. `ok` carries the previous byte's comparison, so
# the recursive call stays in tail position. Start it with `True`. The pattern
# comes before the stream because Bend matches scrutinees in binder order.
def Bytes.lit(fuel: Nat, ok: Bool, pat: List<&2, U32>, xs: List<&2, U32>) -> Pos:
  match fuel:
    case 0n:
      PBad{}
    case 1n+f:
      match ok:
        case False{}:
          PBad{}
        case True{}:
          match pat:
            case Nil{}:
              POk{xs}
            case Con{b, pr}:
              match xs:
                case Nil{}:
                  PBad{}
                case Con{c, xr}:
                  Bytes.lit(f, U32.is_eq(c, b), pr, xr)

# Did a literal match?
def Bytes.pos_ok(p: Pos) -> Bool:
  match p:
    case POk{r}:
      True{}
    case PBad{}:
      False{}

# Fuel for matching one key. A key is short, so this is generous.
def Bytes.key_fuel() -> Nat:
  1024n

# Does the stream start with the whole key? `Bytes.lit` recurses once per key
# byte rather than per file byte, so its depth is bounded by the key.
def Bytes.is_hit(+key: List<&2, U32>, +xs: List<&2, U32>) -> Bool:
  Bytes.pos_ok(Bytes.lit(Bytes.key_fuel(), True{}, key, xs))

# Find the first occurrence of `key` and answer the position after it.
#
# `hit` says the key matches right here, which the caller establishes with
# `Bytes.is_hit`. On a miss the stream advances one byte and the next call
# carries the test for the new position, so the outer walk is a tail call.
# Matching to the key's first byte alone is not enough: the first `"` in an
# export belongs to the metadata line, and a search that stops there never
# reaches the key.
def Bytes.find(fuel: Nat, hit: Bool, +key: List<&2, U32>, xs: List<&2, U32>) -> Pos:
  match fuel:
    case 0n:
      PBad{}
    case 1n+f:
      match hit:
        case True{}:
          Bytes.lit(Bytes.key_fuel(), True{}, key, xs)
        case False{}:
          match xs:
            case Nil{}:
              PBad{}
            case Con{c, +r}:
              Bytes.find(f, Bytes.is_hit(key, r), key, r)

# Skip bytes until the stream starts with `b`, which is left unconsumed.
# `go` says the head is not `b` yet.
def Bytes.skip_to(fuel: Nat, go: Bool, +b: U32, xs: List<&2, U32>) -> Pos:
  match fuel:
    case 0n:
      PBad{}
    case 1n+f:
      match go:
        case False{}:
          POk{xs}
        case True{}:
          match xs:
            case Nil{}:
              PBad{}
            case Con{c, +r}:
              Bytes.skip_to(f, Bool.not(Bytes.starts_with(r, b)), b, r)

# Count how many times `b` occurs. No branch per byte, so no flag to carry.
def Bytes.count(fuel: Nat, +acc: Nat, +b: U32, xs: List<&2, U32>) -> Nat:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      match xs:
        case Nil{}:
          acc
        case Con{c, r}:
          Bytes.count(f, Nat.add(acc, Bytes.eq_one(c, b)), b, r)

# How many bytes are there? A tail accumulator, where `List.length` is not one.
def Bytes.length(fuel: Nat, +acc: Nat, xs: List<&2, U32>) -> Nat:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      match xs:
        case Nil{}:
          acc
        case Con{c, r}:
          Bytes.length(f, 1n+acc, r)

# The bytes of a short String. Only for literals written in the source, never
# for file contents, so the depth stays small.
def Bytes.of_chars(cs: List<&2, Char>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{c, r}:
      Con{Bytes.char_code(c), Bytes.of_chars(r)}

def Bytes.of_string(s: String) -> List<&2, U32>:
  Bytes.of_chars(String.to_list(s))
