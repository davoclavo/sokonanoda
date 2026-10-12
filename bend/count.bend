# How long does it take only to read a file into terms?
#
#   SOKO_EXPORT=<an export> bend bend/count.bend
#
# `read.bend` scans bytes and builds no terms. `check.bend` builds terms and
# then checks them. This builds the terms and counts them, which is what
# separates a reader that is slow from a checker that is slow.
#
# It counts nodes as well as declarations, because the export's expression
# table is a graph and this kernel reads it as a tree: an expression named by
# ten others is built ten times. A node count far above the file's own line
# count is that, and nothing else.

import Base
import ./Bytes.bend as B
import ./Parse.bend as P
import ./Env.bend as E
import ./Term.bend as T
import ./Kernel.bend as K

def Count.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

# How many nodes in this term?
def Count.nodes(t: T.Term, +acc: Nat) -> Nat:
  match t:
    case T.TVar{i}:
      1n+acc
    case T.TSort{l}:
      1n+acc
    case T.TConst{n, ls}:
      1n+acc
    case T.TApp{f, a}:
      Count.nodes(f, Count.nodes(a, 1n+acc))
    case T.TLam{ty, bd}:
      Count.nodes(ty, Count.nodes(bd, 1n+acc))
    case T.TPi{ty, bd}:
      Count.nodes(ty, Count.nodes(bd, 1n+acc))
    case T.TLet{ty, v, bd}:
      Count.nodes(ty, Count.nodes(v, Count.nodes(bd, 1n+acc)))
    case T.TNat{v, m, z, c}:
      1n+acc
    case T.TUnk{}:
      1n+acc
    case T.TProj{tn, idx, st}:
      Count.nodes(st, 1n+acc)
    case T.TRef{i, k, m}:
      1n+acc

def Count.decl(+d: E.Decl, +acc: Nat) -> Nat:
  Count.nodes(
    E.Decl.raw_ty(d), Count.nodes(E.Decl.raw_val(d), acc))

def Count.all(ds: List<&2, E.Decl>, +acc: Nat) -> Nat:
  match ds:
    case Nil{}:
      acc
    case Con{+h, t}:
      Count.all(t, Count.decl(h, acc))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    +ds : List<&2, E.Decl> = P.Parse.decls_of(P.Parse.run(Count.bytes(r)))
    IO.print("declarations " ++ Nat.show(K.Kernel.count(ds, 0n)))
    IO.print("nodes " ++ Nat.show(Count.all(ds, 0n)))
