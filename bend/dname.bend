# The name id of the declaration at a given place in the flattened list.
#
#   SOKO_EXPORT=<an export> SOKO_LIMIT=<k> bend bend/dname.bend
#
# An inductive line of the export becomes several declarations here -- its
# type, its constructors and its recursors -- so the place a measurement
# stops at is not a line of the file. This prints the id, and the export's
# name table says what the id is called.

import Base
import ./Bytes.bend as B
import ./Parse.bend as P
import ./Env.bend as E

def Dn.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

def Dn.digits(s: String, +acc: Nat) -> Nat:
  match s:
    case SNil{}:
      acc
    case SCon{+head, tail}:
      Dn.digits(
        tail,
        Nat.add(Nat.mul(acc, 10n), Nat.sub(U32.to_nat(Char.to_u32(head)), 48n)))

def Dn.limit(r: Result<&1, &1, U32 & String, String>) -> Nat:
  match r:
    case Fail{e}:
      0n
    case Done{v}:
      Dn.digits(v, 0n)

def Dn.at(ds: List<&2, E.Decl>, +k: Nat, +acc: String) -> String:
  match ds:
    case Nil{}:
      acc
    case Con{+h, t}:
      match k:
        case 0n:
          "id " ++ Nat.show(E.Decl.id(h))
        case 1n+(+j):
          Dn.at(t, j, acc)

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    lv : Result<&1, &1, U32 & String, String> <- IO.get_env("SOKO_LIMIT")
    +st : P.PState = P.Parse.run(Dn.bytes(r))
    IO.print(Dn.at(P.Parse.decls_of(st), Dn.limit(lv), "past the end"))
