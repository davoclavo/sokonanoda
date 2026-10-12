# Print the raw value of the last declaration, shallowly.
#
#   SOKO_EXPORT=<an export> bend bend/peek.bend

import Base
import ./Bytes.bend as B
import ./Parse.bend as P
import ./Env.bend as E
import ./Term.bend as T
import ./Show.bend as S
import ./Infer.bend as I
import ./Kernel.bend as K
import ./Ans.bend as A

def Peek.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

# Resolve a reference, so the print can go through it.
def Peek.deref(+env: E.DTable, t: T.Term) -> T.Term:
  match t:
    case T.TRef{+i, +k, m}:
      E.Env.expr_at(env, i, k)
    case o:
      o

def Peek.fn(t: T.Term) -> T.Term:
  match t:
    case T.TApp{+g, a}:
      g
    case o:
      o

def Peek.arg(t: T.Term) -> T.Term:
  match t:
    case T.TApp{g, +a}:
      a
    case T.TLam{ty, +bd}:
      bd
    case o:
      o

# Inference on its own, with nothing else of the kernel.
def Peek.inf(+env: E.DTable, +d: E.Decl) -> String:
  A.Ans.show(K.Kernel.check_decl(400000n, env, d))

def Peek.show(+env: E.DTable, +t: T.Term) -> String:
  +root : T.Term = Peek.deref(env, Peek.deref(env, t))
  "root " ++ S.Show.term(3n, root) ++
  "\n  its function " ++
    S.Show.term(3n, Peek.deref(env, Peek.fn(root))) ++
  "\n  its argument " ++
    S.Show.term(4n, Peek.deref(env, Peek.arg(root))) ++
  "\n  that argument one level in " ++
    S.Show.term(4n,
      Peek.deref(env, Peek.arg(Peek.deref(env, Peek.arg(root)))))

# Every declaration goes in the environment, and the last one's value is
# the one inference is asked about.
def Peek.last(
  ds: List<&2, E.Decl>, +env: E.DTable, +acc: String
) -> String:
  match ds:
    case Nil{}:
      acc
    case Con{+h, t}:
      Peek.last(
        t, E.Env.add(env, h), Peek.inf(env, h))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    +st : P.PState = P.Parse.run(Peek.bytes(r))
    +env : E.DTable = E.Env.over(P.Parse.exps_of(st))
    IO.print(Peek.last(P.Parse.decls_of(st), env, "none"))
