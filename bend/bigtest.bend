# Does the wide-number arithmetic hold?
#
#   bend bend/bigtest.bend
#
# Every line prints `ok` or `BAD`. The one that matters is the last: the
# decimal `18446744073709551616` read digit by digit, against two to the
# sixty-fourth by repeated multiplication. `good/init-prelude` turns on that
# one equality.

import Base
import ./Big.bend as G

def BT.show(name: String, ok: Bool) -> String:
  match ok:
    case True{}:
      name ++ " ok\n"
    case False{}:
      name ++ " BAD\n"

# A decimal string, read into a number.
def BT.read(fuel: Nat, acc: G.Big, s: String) -> G.Big:
  match fuel:
    case 0n:
      G.BBad{}
    case 1n+(+f):
      match s:
        case SNil{}:
          acc
        case SCon{+head, tail}:
          BT.read(
            f,
            G.Big.digit10(
              G.Big.ds_of(acc),
              Nat.sub(U32.to_nat(Char.to_u32(head)), 48n)),
            tail)

def BT.of(n: Nat) -> List<&2, Nat>:
  G.Big.of_nat(G.Big.room(), n)

def BT.pow(b: Nat, e: Nat) -> G.Big:
  G.Big.pow(100n, BT.of(b), e, G.BOk{[1n]})

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(
      BT.show("a word there and back", Nat.is_eq(G.Big.word(BT.of(123456789n)), 123456789n)) ++
      BT.show(
        "a word above the base",
        Nat.is_eq(
          G.Big.word(BT.of(Nat.mul(1073741824n, 1024n))),
          Nat.mul(1073741824n, 1024n))) ++
      BT.show("zero is empty", G.Big.is_zero(BT.of(0n))) ++
      BT.show("two is small", G.Big.small(BT.of(2n))) ++
      BT.show(
        "a sum",
        G.Big.eq(
          G.Big.ds_of(G.Big.add(BT.of(16777215n), BT.of(1n))),
          BT.of(16777216n))) ++
      BT.show(
        "a product",
        G.Big.eq(
          G.Big.ds_of(G.Big.mul(BT.of(16777216n), BT.of(8388608n))),
          BT.of(Nat.mul(16777216n, 8388608n)))) ++
      BT.show(
        "two to the ten",
        G.Big.eq(G.Big.ds_of(BT.pow(2n, 10n)), BT.of(1024n))) ++
      BT.show(
        "two to the forty",
        G.Big.eq(
          G.Big.ds_of(BT.pow(2n, 40n)),
          BT.of(Nat.mul(1073741824n, 1024n)))) ++
      BT.show(
        "a number is at most itself",
        G.Big.le(G.Big.ds_of(BT.pow(2n, 64n)), G.Big.ds_of(BT.pow(2n, 64n)))) ++
      BT.show(
        "and less than the next one",
        Bool.not(
          G.Big.le(
            G.Big.ds_of(BT.pow(2n, 65n)), G.Big.ds_of(BT.pow(2n, 64n))))) ++
      BT.show(
        "a word is less than a wide number",
        G.Big.le(BT.of(1114112n), G.Big.ds_of(BT.pow(2n, 64n)))) ++
      BT.show(
        "the decimal of two to the sixty-fourth",
        G.Big.eq(
          G.Big.ds_of(BT.read(40n, G.BOk{Nil{}}, "18446744073709551616")),
          G.Big.ds_of(BT.pow(2n, 64n)))) ++
      BT.show(
        "a number past the cap is refused",
        G.Big.is_bad(BT.pow(2n, 200n))))
