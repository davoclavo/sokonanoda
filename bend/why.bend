# Which pair does conversion refuse?
#
#   SOKO_EXPORT=<an export> bend bend/why.bend
#
# `bend/blame.bend` walks into a term whose inference is a definite no. This
# walks into a *pair* whose conversion is one. The two questions are different
# and the second is the one a stuck reduction raises: conversion answers no
# when the two sides reduce to different heads, and that is right only if the
# reduction was complete. To find out which reduction is missing, you need the
# pair it gave up on and both of its reduced forms.
#
# The walk takes the first declaration whose value does not have its declared
# type, puts the inferred type against the declared one, and descends into the
# first sub-pair that conversion also refuses. A pair with no refusing child
# is the one to look at, and it prints both sides as written and as reduced.
#
# A match needs a parameter and Bend has no mutual recursion, so the search
# for a refusing child carries its answer as a parameter, and the descent
# computes the next pair and calls itself in tail position.

import Base
import ./Bytes.bend as B
import ./Parse.bend as P
import ./Env.bend as E
import ./Term.bend as T
import ./Eval.bend as V
import ./Conv.bend as C
import ./Infer.bend as I
import ./Kernel.bend as K
import ./Ans.bend as A
import ./Show.bend as S

def Why.fuel() -> Nat:
  30000n

def Why.depth() -> Nat:
  40n

def Why.steps() -> Nat:
  40n

def Why.bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  Result.default(&1, &1, U32 & String, List<&2, U32>,
    Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, r), Nil{})

# Does conversion refuse this pair?
def Why.bad(+fuel: Nat, +env: E.DTable, p: C.TPair) -> Bool:
  match p:
    case C.MkPair{+ctx, a, b}:
      A.Ans.is_no(C.Conv.eq_in(fuel, env, ctx, a, b))
    case C.MkDeep{+ctx, a, b}:
      A.Ans.is_no(C.Conv.eq_in(fuel, env, ctx, a, b))

# The pairs this one reduces to.
#
# An `SEither` offers two routes and the queue takes the cheap one, keeping
# the dear one on a stack. A cheap route that a definite no comes back from
# is recovered there, so a pair refused on the cheap route is not the reason
# the parent failed. This walk therefore takes the **dear** route: the two
# sides reduced. Taking the cheap one printed a bound variable against a pi
# type, which is refused and means nothing.
def Why.dear(s: C.Step) -> List<&2, C.TPair>:
  match s:
    case C.SEither{cheap, dear}:
      dear
    case o:
      C.Conv.step_more(o)

def Why.kids(+fuel: Nat, +env: E.DTable, p: C.TPair) -> List<&2, C.TPair>:
  Why.dear(C.Conv.classify_pair(fuel, env, p))

def Why.keep(ok: Bool, h: C.TPair, acc: C.TPair) -> C.TPair:
  match ok:
    case True{}:
      h
    case False{}:
      acc

# The first child conversion refuses, or the pair itself when none is
# refused, which is what marks it as the one to look at.
def Why.scan(
  ps: List<&2, C.TPair>, found: Bool, +fuel: Nat, +env: E.DTable,
  +acc: C.TPair
) -> C.TPair:
  match ps found:
    case Nil{} f:
      acc
    case Con{h, t} True{}:
      acc
    case Con{+h, t} False{}:
      +hit : Bool = Why.bad(fuel, env, h)
      Why.scan(t, hit, fuel, env, Why.keep(hit, h, acc))

def Why.show_two(
  +fuel: Nat, +env: E.DTable, +a: T.Term, +b: T.Term
) -> String:
  "  left    " ++ S.Show.term(Why.depth(), a) ++ "\n" ++
  "  right   " ++ S.Show.term(Why.depth(), b) ++ "\n" ++
  "  left'   " ++
    S.Show.term(Why.depth(), V.Eval.whnf(fuel, env, a, Nil{})) ++ "\n" ++
  "  right'  " ++
    S.Show.term(Why.depth(), V.Eval.whnf(fuel, env, b, Nil{})) ++ "\n"

def Why.here(+fuel: Nat, +env: E.DTable, p: C.TPair) -> String:
  match p:
    case C.MkPair{ctx, +a, +b}:
      Why.show_two(fuel, env, a, b)
    case C.MkDeep{ctx, +a, +b}:
      Why.show_two(fuel, env, a, b)

def Why.go(
  +steps: Nat, +fuel: Nat, +env: E.DTable, +p: C.TPair
) -> String:
  match steps:
    case 0n:
      Why.here(fuel, env, p)
    case 1n+k:
      Why.go(
        k, fuel, env,
        Why.scan(Why.kids(fuel, env, p), False{}, fuel, env, p))

# The inferred type of a declaration's value against its declared type.
def Why.decl_pair(+fuel: Nat, +env: E.DTable, +d: E.Decl) -> C.TPair:
  C.MkPair{
    Nil{},
    I.Infer.res_ty(
      I.Infer.infer(fuel, env, Nil{}, E.Decl.raw_val(d))),
    E.Decl.raw_ty(d)}

def Why.has_val(d: E.Decl) -> Bool:
  match d:
    case E.DDef{id, ps, ty, val}:
      True{}
    case E.DThm{id, ps, ty, val}:
      True{}
    case o:
      False{}

def Why.at(on: Bool, +fuel: Nat, +env: E.DTable, +d: E.Decl) -> String:
  match on:
    case True{}:
      "decl " ++ Nat.show(E.Decl.id(d)) ++ "\n" ++
      Why.go(Why.steps(), fuel, env, Why.decl_pair(fuel, env, d))
    case False{}:
      ""

# Walk the declarations and report on the first whose value does not have the
# type it declares. The walk stops there.
def Why.walk(
  ds: List<&2, E.Decl>, done: Bool, +fuel: Nat, +acc: E.DTable
) -> String:
  match ds done:
    case Nil{} d:
      ""
    case Con{h, t} True{}:
      ""
    case Con{+h, t} False{}:
      +hit : Bool = Bool.and(
        Why.has_val(h),
        A.Ans.is_no(K.Kernel.check_decl(fuel, acc, h)))
      Why.at(hit, fuel, acc, h) ++
        Why.walk(t, hit, fuel, E.Env.add(acc, h))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("SOKO_EXPORT"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64000000)
    # The environment has to carry the expression table: a term may hold a
    # reference into it, and only a walk that sees the table resolves one.
    +st : P.PState = P.Parse.run(Why.bytes(r))
    +ds : List<&2, E.Decl> = P.Parse.decls_of(st)
    IO.print(Why.walk(ds, False{}, Why.fuel(), E.Env.over(P.Parse.exps_of(st))))
