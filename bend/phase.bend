# Which phase of the kernel spends the time, on the first `k` declarations.
#
#   SOKO_EXPORT=<an export> bend bend/phase.bend
#   SOKO_LIMIT=400 ...    the first 400 declarations only
#   SOKO_TRUST=1   ...    the walk that asks whether a block is trusted
#
# A file that does not answer says nothing about where its time goes. This
# checks a prefix of the declarations, so the time against `k` says which
# ones carry it, and it parses once rather than once per cut.
#
# It is what found the wall in `good/init-prelude`: the whole file's
# per-declaration checks cost 11.6 s, and the walk that asks whether an
# inductive block was taken on trust did not finish in two hundred. The
# declarations between 350 and 355 were where that walk turned expensive,
# which is `String.rec`.
#
# `Peek.inf` is the phase. Point it at `Kernel.check_decl`, at
# `Infer.infer`, at `Rec.derive`, or at whatever is in question.

import Base
import ./Bytes.bend as B
import ./Parse.bend as P
import ./Env.bend as E
import ./Term.bend as T
import ./Show.bend as S
import ./Infer.bend as I
import ./Kernel.bend as K
import ./Rec.bend as R
import ./Vconv.bend as X
import ./Ans.bend as A

def Peek.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

# Only the derivation, forced as far as its head.
def Peek.derived(b: Bool) -> Bool:
  match b:
    case True{}:
      True{}
    case False{}:
      False{}

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
# The limit, read from the environment. No limit means every declaration.
def Peek.digits(s: String, +acc: Nat) -> Nat:
  match s:
    case SNil{}:
      acc
    case SCon{+head, tail}:
      Peek.digits(
        tail,
        Nat.add(Nat.mul(acc, 10n), Nat.sub(U32.to_nat(Char.to_u32(head)), 48n)))

def Peek.limit(r: Result<&1, &1, U32 & String, String>) -> Nat:
  match r:
    case Fail{e}:
      1000000n
    case Done{v}:
      Peek.digits(v, 0n)

# The trust walk over the first `k` declarations, which is what
# `Kernel.trusts_from` does. The answer travels in so the cost is the cost
# of the prefix and nothing more.
def Peek.trust_pre(
  ds: List<&2, E.Decl>, +k: Nat, +env: E.DTable, +acc: Bool
) -> Bool:
  match ds:
    case Nil{}:
      acc
    case Con{+h, t}:
      match k:
        case 0n:
          acc
        case 1n+j:
          Peek.trust_pre(
            t, j, E.Env.add(env, h),
            Bool.or(
              acc,
              K.Kernel.trusted_ans(400000n, env, h)))

def Peek.wants(r: Result<&1, &1, U32 & String, String>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{v}:
      True{}

def Peek.pick(b: Bool, x: String, y: String) -> String:
  match b:
    case True{}:
      x
    case False{}:
      y

def Peek.inf(+env: E.DTable, +d: E.Decl) -> A.Ans:
  A.Ans.and(
    A.Ans.of(K.Kernel.safe_uses(d, env)),
    K.Kernel.check_decl(400000n, env, d))

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
# Check the first `k` declarations, each against the ones before it. The
# limit is what makes a 3.7 MB file bisectable: the time for a prefix says
# where the cost is, and one process parses once.
# The answers are combined, not replaced. An answer that is replaced is
# never read, and nothing is evaluated that nothing reads, so a walk that
# kept only the last one measured only the last declaration.
def Peek.last(
  ds: List<&2, E.Decl>, +k: Nat, +env: E.DTable, +acc: A.Ans
) -> A.Ans:
  match ds:
    case Nil{}:
      acc
    case Con{+h, t}:
      match k:
        case 0n:
          acc
        case 1n+j:
          Peek.last(
            t, j, E.Env.add(env, h),
            A.Ans.and(acc, Peek.inf(env, h)))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    +st : P.PState = P.Parse.run(Peek.bytes(r))
    +env : E.DTable = E.Env.over(P.Parse.exps_of(st))
    kv0 : Result<&1, &1, U32 & String, String> <- IO.get_env("SOKO_LIMIT")
    +kv : Nat = Peek.limit(kv0)
    tv : Result<&1, &1, U32 & String, String> <- IO.get_env("SOKO_TRUST")
    IO.print(
      Peek.pick(
        Peek.wants(tv),
        Bool.show(
          Peek.trust_pre(
            P.Parse.decls_of(st), kv,
            E.Env.over(P.Parse.exps_of(st)), False{})),
        A.Ans.show(
          Peek.last(P.Parse.decls_of(st), kv, env, A.AYes{}))))
