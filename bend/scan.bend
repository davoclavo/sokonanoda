# Read a real Lean export and report what the scanner found.
#
# This is the evidence that the byte path works at the sizes the arena uses.
# It reads the file named by SOKO_EXPORT, counts its bytes and its lines with
# tail accumulators, and reads the first number after the first `"ie":`.
#
#   SOKO_EXPORT=~/.cache/lean-kernel-arena/small/good/init-prelude.ndjson \
#     bend bend/scan.bend
#
# Base's `String.lines` overflows the host stack on the same file. These
# counts come from `Bytes`, where every recursive call is a tail call.

import Base
import ./Bytes.bend as B

# The fuel every scan gets. One unit per byte is enough for a single pass.
def Scan.fuel() -> Nat:
  64000000n

# Unwrap the bytes a read answered.
def Scan.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

# The number a scan found, or zero.
def Scan.val(s: B.Scan) -> Nat:
  match s:
    case B.SOk{v, rest}:
      v
    case B.SBad{}:
      0n

# The stream a position left, or empty.
def Scan.rest(p: B.Pos) -> List<&2, U32>:
  match p:
    case B.POk{rest}:
      rest
    case B.PBad{}:
      Nil{}

# The first number after the first occurrence of `key`.
def Scan.after(+key: List<&2, U32>, +xs: List<&2, U32>) -> Nat:
  Scan.val(
    B.Bytes.number(
      Scan.fuel(),
      Scan.rest(
        B.Bytes.find(Scan.fuel(), B.Bytes.is_hit(key, xs), key, xs))))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    +bs : List<&2, U32> = Scan.bytes(r)
    IO.print("bytes " ++ Nat.show(B.Bytes.length(Scan.fuel(), 0n, bs)))
    IO.print("lines " ++ Nat.show(B.Bytes.count(Scan.fuel(), 0n, B.Bytes.newline(), bs)))
    IO.print("first ie " ++ Nat.show(Scan.after(B.Bytes.of_string("\"ie\":"), bs)))
    IO.print("first in " ++ Nat.show(Scan.after(B.Bytes.of_string("\"in\":"), bs)))
    IO.print("first sort " ++ Nat.show(Scan.after(B.Bytes.of_string("\"sort\":"), bs)))
