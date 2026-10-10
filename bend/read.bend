# Walk a real export and tally its line kinds.
#
# This is the evidence that line splitting and classification work on a whole
# file. The loop keeps its recursive call in tail position, because an export
# has tens of thousands of lines and a non-tail loop overflows the host stack
# well before that.
#
#   SOKO_EXPORT=~/.cache/lean-kernel-arena/small/good/init-prelude.ndjson \
#     bend bend/read.bend

import Base
import ./Bytes.bend as B
import ./Reader.bend as R

type Tally is Data:
  MkTally{
    meta: Nat, name: Nat, level: Nat, expr: Nat, ax: Nat,
    dfn: Nat, thm: Nat, ind: Nat, quot: Nat, opq: Nat, other: Nat}

def Read.fuel() -> Nat:
  4000000n

def Read.empty() -> Tally:
  MkTally{0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}

# Add one to the counter this kind names. The tally comes first because Bend
# matches scrutinees in binder order.
def Tally.bump(t: Tally, k: R.LineKind) -> Tally:
  match t:
    case MkTally{m, n, l, e, a, d, h, i, q, p, o}:
      match k:
        case R.KMeta{}:
          MkTally{1n+m, n, l, e, a, d, h, i, q, p, o}
        case R.KName{}:
          MkTally{m, 1n+n, l, e, a, d, h, i, q, p, o}
        case R.KLevel{}:
          MkTally{m, n, 1n+l, e, a, d, h, i, q, p, o}
        case R.KExpr{}:
          MkTally{m, n, l, 1n+e, a, d, h, i, q, p, o}
        case R.KAxiom{}:
          MkTally{m, n, l, e, 1n+a, d, h, i, q, p, o}
        case R.KDef{}:
          MkTally{m, n, l, e, a, 1n+d, h, i, q, p, o}
        case R.KThm{}:
          MkTally{m, n, l, e, a, d, 1n+h, i, q, p, o}
        case R.KInductive{}:
          MkTally{m, n, l, e, a, d, h, 1n+i, q, p, o}
        case R.KQuot{}:
          MkTally{m, n, l, e, a, d, h, i, 1n+q, p, o}
        case R.KOpaque{}:
          MkTally{m, n, l, e, a, d, h, i, q, 1n+p, o}
        case R.KOther{}:
          MkTally{m, n, l, e, a, d, h, i, q, 1n+p, 1n+o}

# The loop. `done` carries whether the stream is spent, so the recursive call
# stays the whole body.
def Read.go(fuel: Nat, done: Bool, +t: Tally, xs: List<&2, U32>) -> Tally:
  match fuel:
    case 0n:
      t
    case 1n+f:
      match done:
        case True{}:
          t
        case False{}:
          +ln = R.Reader.line(R.Reader.line_fuel(), xs)
          Read.go(
            f,
            B.Bytes.is_empty(R.Reader.line_rest(ln)),
            Tally.bump(t, R.Reader.line_kind(R.Reader.line_bytes(ln))),
            R.Reader.line_rest(ln))

def Read.show(t: Tally) -> String:
  match t:
    case MkTally{m, n, l, e, a, d, h, i, q, p, o}:
      "meta "       ++ Nat.show(m) ++
      "\nname "     ++ Nat.show(n) ++
      "\nlevel "    ++ Nat.show(l) ++
      "\nexpr "     ++ Nat.show(e) ++
      "\naxiom "    ++ Nat.show(a) ++
      "\ndef "      ++ Nat.show(d) ++
      "\nthm "      ++ Nat.show(h) ++
      "\ninductive " ++ Nat.show(i) ++
      "\nquot "     ++ Nat.show(q) ++
      "\nopaque "   ++ Nat.show(p) ++
      "\nother "    ++ Nat.show(o)

def Read.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    +bs : List<&2, U32> = Read.bytes(r)
    IO.print(Read.show(Read.go(Read.fuel(), B.Bytes.is_empty(bs), Read.empty(), bs)))
