# Dump the first inductive block of an export, to show the reader handles its
# nested arrays of objects.
#
#   SOKO_EXPORT=<export> bend bend/ind.bend

import Base
import ./Bytes.bend as B
import ./Reader.bend as R

def Ind.fuel() -> Nat:
  4000000n

def Ind.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

# Is this line an inductive block?
def Ind.is_ind(k: R.LineKind) -> Bool:
  match k:
    case R.KInductive{}:
      True{}
    case o:
      False{}

# Find the first inductive line. `hit` says the line already in hand is the
# one wanted, and `done` says the stream is spent. Both are carried so the
# recursive call stays the whole body, which Bend needs for a loop.
def Ind.find(
  fuel: Nat, hit: Bool, +line: List<&2, U32>, done: Bool, xs: List<&2, U32>
) -> List<&2, U32>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+f:
      match hit:
        case True{}:
          line
        case False{}:
          match done:
            case True{}:
              Nil{}
            case False{}:
              +ln = R.Reader.line(R.Reader.line_fuel(), xs)
              Ind.find(
                f,
                Ind.is_ind(R.Reader.line_kind(R.Reader.line_bytes(ln))),
                R.Reader.line_bytes(ln),
                B.Bytes.is_empty(R.Reader.line_rest(ln)),
                R.Reader.line_rest(ln))

# The named fields of one object.
def Ind.show_keys(ks: List<&2, String>, +o: List<&2, U32>) -> String:
  match ks:
    case Nil{}:
      ""
    case Con{+k, t}:
      " " ++ k ++ "=" ++ Nat.show(R.Reader.field(k, o)) ++ Ind.show_keys(t, o)

# One line per object, showing the fields this kernel needs.
def Ind.show_objs(
  os: List<&2, List<&2, U32>>, +tag: String, +keys: List<&2, String>
) -> String:
  match os:
    case Nil{}:
      ""
    case Con{o, t}:
      "  " ++ tag ++ Ind.show_keys(keys, o) ++ "\n" ++ Ind.show_objs(t, tag, keys)

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    +line : List<&2, U32> = Ind.find(Ind.fuel(), False{}, Nil{}, False{}, Ind.bytes(r))
    IO.print(Ind.show_objs(
      R.Reader.obj_list("types", line), "type", ["name", "numParams", "numIndices", "type"]))
    IO.print(Ind.show_objs(
      R.Reader.obj_list("ctors", line), "ctor", ["name", "cidx", "induct", "numParams", "numFields", "type"]))
    IO.print(Ind.show_objs(
      R.Reader.obj_list("recs", line), "rec ", ["name", "numParams", "numIndices", "numMotives", "numMinors", "type"]))
