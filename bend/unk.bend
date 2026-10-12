# Which declaration holds the term reduction gives back when it runs out,
# and where does it come from?
#
#   SOKO_EXPORT=<an export> bend bend/unk.bend
#
# A declaration whose check answers "do not know" has either run out of
# budget or met `TUnk` in its own term, and the two want different fixes. A
# node the reader does not read is one `TUnk`, and so is a reference that
# does not resolve. This names the declarations that hold one, in their own
# type and in their own value, before any check is asked.

import Base
import ./Bytes.bend as B
import ./Parse.bend as P
import ./Env.bend as E
import ./Term.bend as T

def Unk.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

def Unk.mark(b: Bool, +s: String) -> String:
  match b:
    case True{}:
      s
    case False{}:
      ""

# The walk goes through a reference, because a reference is where an
# unreadable node hides.
def Unk.deep(+fuel: Nat, +env: E.DTable, t: T.Term) -> Bool:
  match fuel:
    case 0n:
      False{}
    case 1n+(+f):
      match t:
        case T.TUnk{}:
          True{}
        case T.TRef{+i, +k, m}:
          Unk.deep(f, env, E.Env.expr_at(env, i, k))
        case T.TApp{+g, +a}:
          Bool.or(Unk.deep(f, env, g), Unk.deep(f, env, a))
        case T.TLam{+ty, +bd}:
          Bool.or(Unk.deep(f, env, ty), Unk.deep(f, env, bd))
        case T.TPi{+ty, +bd}:
          Bool.or(Unk.deep(f, env, ty), Unk.deep(f, env, bd))
        case T.TLet{+ty, +v, +bd}:
          Bool.or(
            Unk.deep(f, env, ty),
            Bool.or(Unk.deep(f, env, v), Unk.deep(f, env, bd)))
        case T.TProj{tn, idx, +st}:
          Unk.deep(f, env, st)
        case o:
          False{}

# A declaration with no value of its own has the unknown term for one, so
# the type and the value are reported apart.
def Unk.one(+env: E.DTable, +d: E.Decl) -> String:
  "  " ++ Nat.show(E.Decl.id(d)) ++
  Unk.mark(Unk.deep(200000n, env, E.Decl.raw_ty(d)), " type=unknown") ++
  Unk.mark(Unk.deep(200000n, env, E.Decl.raw_val(d)), " value=unknown") ++
  "\n"

def Unk.walk(
  ds: List<&2, E.Decl>, +env: E.DTable, +acc: String
) -> String:
  match ds:
    case Nil{}:
      acc
    case Con{+h, t}:
      Unk.walk(t, E.Env.add(env, h), acc ++ Unk.one(env, h))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    +st : P.PState = P.Parse.run(Unk.bytes(r))
    IO.print(
      Unk.walk(
        P.Parse.decls_of(st), E.Env.over(P.Parse.exps_of(st)), "done\n"))
