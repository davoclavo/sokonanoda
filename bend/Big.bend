# Numbers that a machine word does not hold.
#
# A Bend `Nat` is an immediate of 48 bits, and the prelude of Lean writes
# `18446744073709551616` for the size of a `UInt64`. `good/init-prelude`
# turns on exactly that number: `UInt64.ofNatLT` states its bound as
# `n < UInt64.size` and `BitVec.ofNatLT` wants `n < 2 ^ 64`, so the kernel
# has to decide that the literal and the power are the same number. With
# every oversized number of that file made small, the whole of it checks in
# 2.9 s, so this is the one thing between it and an answer.
#
# A number here is a list of digits in base 2^24, least significant first,
# with no zero at the most significant end. Two digits multiply to less than
# 2^48, so a product of digits is still an immediate.
#
# `BBad` is what an operation answers when its result is longer than the
# cap. Nothing may be concluded from one, and every caller turns it into the
# unknown term.

import Base

def Big.base() -> Nat:
  16777216n

# The most digits a number may have. Six digits is 144 bits, which is more
# than twice what the corpus asks for, and the cost of a product is
# quadratic in this.
def Big.cap() -> Nat:
  6n

# How long a row of a product may grow before it is measured.
def Big.room() -> Nat:
  13n

type Big is Data:
  BOk{ds: List<&2, Nat>}
  BBad{}

def Big.pick_ds(
  b: Bool, x: List<&2, Nat>, y: List<&2, Nat>
) -> List<&2, Nat>:
  match b:
    case True{}:
      x
    case False{}:
      y

def Big.pick_b(b: Bool, x: Bool, y: Bool) -> Bool:
  match b:
    case True{}:
      x
    case False{}:
      y

def Big.ds_of(b: Big) -> List<&2, Nat>:
  match b:
    case BOk{+ds}:
      ds
    case BBad{}:
      Nil{}

def Big.is_bad(b: Big) -> Bool:
  match b:
    case BOk{ds}:
      False{}
    case BBad{}:
      True{}

# This digit is the last one that matters unless the rest is empty and it is
# zero.
def Big.trim_pick(rest: List<&2, Nat>, +d: Nat) -> List<&2, Nat>:
  match rest:
    case Nil{}:
      Big.pick_ds(Nat.is_eq(d, 0n), Nil{}, [d])
    case o:
      Con{d, o}

# Drop the zeros at the most significant end, which are at the tail.
def Big.trim(fuel: Nat, ds: List<&2, Nat>) -> List<&2, Nat>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+(+f):
      match ds:
        case Nil{}:
          Nil{}
        case Con{+d, r}:
          Big.trim_pick(Big.trim(f, r), d)

def Big.len(ds: List<&2, Nat>, +acc: Nat) -> Nat:
  match ds:
    case Nil{}:
      acc
    case Con{d, r}:
      Big.len(r, 1n+acc)

# A number, from a machine word.
def Big.of_nat(fuel: Nat, n: Nat) -> List<&2, Nat>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+(+f):
      match n:
        case 0n:
          Nil{}
        case +o:
          Con{Nat.mod(o, Big.base()), Big.of_nat(f, Nat.div(o, Big.base()))}

# A machine word, from a number of at most two digits.
#
# The shape is Horner's and not a running shift, and that is not a style
# choice: Bend refuses a `Nat` past 2^48-1 rather than wrapping it, and a
# running shift computes the next power of the base even on the step that
# does not use it. Two digits are 48 bits, so a longer number must not come
# here at all, and `Big.small` is what every caller asks first.
def Big.to_nat(ds: List<&2, Nat>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{+d, r}:
      Nat.add(d, Nat.mul(Big.base(), Big.to_nat(r)))

# Does this number fit a machine word? Two digits are 48 bits, which is
# what an immediate holds.
def Big.small(+ds: List<&2, Nat>) -> Bool:
  Nat.is_le(Big.len(ds, 0n), 2n)

def Big.word(ds: List<&2, Nat>) -> Nat:
  Big.to_nat(ds)

# Does this number fit a machine word below the given cap?
#
# The two tests cannot be an `and`: both sides of one are computed, and
# `Big.word` of a number wider than two digits multiplies past what an
# immediate holds, which stops the whole run. So the length decides first,
# in a `match`, and the value is read only inside the arm that may read it.
def Big.fits_pick(ok: Bool, +ds: List<&2, Nat>, +cap: Nat) -> Bool:
  match ok:
    case True{}:
      Nat.is_lt(Big.word(ds), cap)
    case False{}:
      False{}

def Big.fits_word(+ds: List<&2, Nat>, +cap: Nat) -> Bool:
  Big.fits_pick(Big.small(ds), ds, cap)

# The word of a number that may be too wide: zero where it is, so the
# branch of a `pick` that is thrown away cannot stop the run.
def Big.word_pick(ok: Bool, +ds: List<&2, Nat>) -> Nat:
  match ok:
    case True{}:
      Big.word(ds)
    case False{}:
      0n

def Big.small_word(+ds: List<&2, Nat>) -> Nat:
  Big.word_pick(Big.small(ds), ds)

# An exponent past this cannot fit the cap of digits whatever the base is,
# and the power loop would run that many times to find out.
def Big.exp_cap() -> Nat:
  200n

def Big.is_zero(ds: List<&2, Nat>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case o:
      False{}

# Are these two numbers the same? Both are trimmed, so the digits match one
# for one.
def Big.eq(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{+x, xr} Con{+y, yr}:
      Bool.and(Nat.is_eq(x, y), Big.eq(xr, yr))
    case x y:
      False{}

# Is the first at most the second, for two numbers of the same length? The
# digits are compared from the most significant end, which is the tail: the
# answer of the rest decides unless the rest is equal.
def Big.le_go(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{+x, +xr} Con{+y, +yr}:
      Big.pick_b(Big.eq(xr, yr), Nat.is_le(x, y), Big.le_go(xr, yr))
    case x y:
      False{}

def Big.le_pick(
  same: Bool, shorter: Bool, xs: List<&2, Nat>, ys: List<&2, Nat>
) -> Bool:
  match same:
    case True{}:
      Big.le_go(xs, ys)
    case False{}:
      shorter

def Big.le(+xs: List<&2, Nat>, +ys: List<&2, Nat>) -> Bool:
  Big.le_pick(
    Nat.is_eq(Big.len(xs, 0n), Big.len(ys, 0n)),
    Nat.is_lt(Big.len(xs, 0n), Big.len(ys, 0n)),
    xs, ys)

def Big.carry_end(+c: Nat) -> List<&2, Nat>:
  Big.pick_ds(Nat.is_eq(c, 0n), Nil{}, [c])

# The sum, digit by digit with a carry.
def Big.add_go(
  fuel: Nat, +c: Nat, xs: List<&2, Nat>, ys: List<&2, Nat>
) -> List<&2, Nat>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+(+f):
      match xs ys:
        case Nil{} Nil{}:
          Big.carry_end(c)
        case Con{+x, xr} Nil{}:
          Con{
            Nat.mod(Nat.add(x, c), Big.base()),
            Big.add_go(
              f, Nat.div(Nat.add(x, c), Big.base()), xr, Nil{})}
        case Nil{} Con{+y, yr}:
          Con{
            Nat.mod(Nat.add(y, c), Big.base()),
            Big.add_go(
              f, Nat.div(Nat.add(y, c), Big.base()), Nil{}, yr)}
        case Con{+x, xr} Con{+y, yr}:
          Con{
            Nat.mod(Nat.add(Nat.add(x, y), c), Big.base()),
            Big.add_go(
              f, Nat.div(Nat.add(Nat.add(x, y), c), Big.base()), xr, yr)}

def Big.of_pick(ok: Bool, ds: List<&2, Nat>) -> Big:
  match ok:
    case True{}:
      BOk{ds}
    case False{}:
      BBad{}

def Big.of_keep(+ds: List<&2, Nat>) -> Big:
  Big.of_pick(Nat.is_le(Big.len(ds, 0n), Big.cap()), ds)

# A list of digits, trimmed and measured against the cap. A number longer
# than the cap is not read as a number at all.
def Big.of_ds(ds: List<&2, Nat>) -> Big:
  Big.of_keep(Big.trim(Big.room(), ds))

def Big.add(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Big:
  Big.of_ds(Big.add_go(Big.room(), 0n, xs, ys))

# One digit times a number, with a carry.
def Big.mul1(
  fuel: Nat, +d: Nat, +c: Nat, xs: List<&2, Nat>
) -> List<&2, Nat>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+(+f):
      match xs:
        case Nil{}:
          Big.carry_end(c)
        case Con{+x, +xr}:
          Con{
            Nat.mod(Nat.add(Nat.mul(x, d), c), Big.base()),
            Big.mul1(
              f, d, Nat.div(Nat.add(Nat.mul(x, d), c), Big.base()), xr)}

# A number with `n` zero digits put below it.
def Big.zeros(n: Nat, ds: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      ds
    case 1n+k:
      Con{0n, Big.zeros(k, ds)}

# The product, as the sum of one row per digit of the second number, each
# row moved up by the place of its digit.
def Big.mul_rows(
  fuel: Nat, +xs: List<&2, Nat>, ys: List<&2, Nat>, +sh: Nat
) -> List<&2, Nat>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+(+f):
      match ys:
        case Nil{}:
          Nil{}
        case Con{+y, yr}:
          Big.add_go(
            Big.room(), 0n,
            Big.zeros(sh, Big.mul1(Big.room(), y, 0n, xs)),
            Big.mul_rows(f, xs, yr, 1n+sh))

def Big.mul(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Big:
  Big.of_ds(Big.mul_rows(Big.room(), xs, ys, 0n))

# The accumulator of a power, times the base.
def Big.mul_big(acc: Big, +xs: List<&2, Nat>) -> Big:
  match acc:
    case BBad{}:
      BBad{}
    case BOk{ds}:
      Big.mul(ds, xs)

# A power, by repeated multiplication. The exponent is a machine word.
def Big.pow(fuel: Nat, +xs: List<&2, Nat>, n: Nat, acc: Big) -> Big:
  match fuel:
    case 0n:
      BBad{}
    case 1n+(+f):
      match n:
        case 0n:
          acc
        case 1n+k:
          Big.pow(f, xs, k, Big.mul_big(acc, xs))

# Read a decimal digit into a number: ten times this one, and the digit.
def Big.digit10(ds: List<&2, Nat>, d: Nat) -> Big:
  Big.add(
    Big.mul_rows(Big.room(), ds, [10n], 0n), Big.of_nat(Big.room(), d))
