# Checking an environment.
#
# A declaration is checked against the declarations before it, as the Lean
# kernel does, so a forward reference cannot resolve.
#
# An inductive type, a constructor and a recursor are checked only for a well
# formed type. Their contents are taken on trust: nothing here derives the
# recursor from the inductive specification and compares the two, and nothing
# checks positivity. So a file whose recursor is a lie is accepted. That is
# not a verdict this kernel is entitled to give, and `Kernel.trusts` reports
# which declarations were taken on trust so a caller can decline instead.

import Base
import ./Level.bend as L
import ./Term.bend as T
import ./Env.bend as E
import ./Eval.bend as V
import ./Conv.bend as C
import ./Infer.bend as I
import ./Ans.bend as A

# Is this term a type, that is, does its own type reduce to a sort?
def Kernel.is_type(+fuel: Nat, +env: List<&2, E.Decl>, ty: T.Term) -> A.Ans:
  +r = I.Infer.infer(fuel, env, Nil{}, ty)
  A.Ans.and(
    I.Infer.res_ans(r),
    I.Infer.sort_ans(V.Eval.whnf(fuel, env, I.Infer.res_ty(r), Nil{})))

# Does `v` have type `ty`?
def Kernel.has_type(+fuel: Nat, +env: List<&2, E.Decl>, v: T.Term, ty: T.Term) -> A.Ans:
  +r = I.Infer.infer(fuel, env, Nil{}, v)
  A.Ans.and(
    I.Infer.res_ans(r),
    C.Conv.eq(fuel, env, I.Infer.res_ty(r), ty))

# Is this term a Prop, that is, does its own type reduce to `Sort 0`?
# A theorem's type must be one.
def Kernel.is_prop(+fuel: Nat, +env: List<&2, E.Decl>, ty: T.Term) -> A.Ans:
  +w = V.Eval.whnf(fuel, env, I.Infer.res_ty(I.Infer.infer(fuel, env, Nil{}, ty)), Nil{})
  A.Ans.and(
    I.Infer.sort_ans(w),
    A.Ans.of(L.Level.is_zero(I.Infer.sort_level(w))))

# Check one declaration against the declarations before it.
def Kernel.check_decl(+fuel: Nat, +env: List<&2, E.Decl>, d: E.Decl) -> A.Ans:
  match d:
    case E.DAxiom{id, ps, ty}:
      A.Ans.and(
        A.Ans.of(E.Decl.no_dupes(ps)),
        Kernel.is_type(fuel, env, ty))
    case E.DDef{id, ps, +ty, val}:
      A.Ans.and(
        A.Ans.of(E.Decl.no_dupes(ps)),
        A.Ans.and(
          Kernel.is_type(fuel, env, ty),
          Kernel.has_type(fuel, env, val, ty)))
    case E.DThm{id, ps, +ty, val}:
      A.Ans.and(
        A.Ans.of(E.Decl.no_dupes(ps)),
        A.Ans.and(
          A.Ans.and(
            Kernel.is_type(fuel, env, ty),
            Kernel.is_prop(fuel, env, ty)),
          Kernel.has_type(fuel, env, val, ty)))
    case E.DInd{id, ps, ty, np, ni, ctors}:
      A.Ans.and(
        A.Ans.of(E.Decl.no_dupes(ps)),
        Kernel.is_type(fuel, env, ty))
    case E.DCtor{id, ps, ty, ind, cidx, np, nf}:
      A.Ans.and(
        A.Ans.of(E.Decl.no_dupes(ps)),
        Kernel.is_type(fuel, env, ty))
    case E.DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds}:
      A.Ans.and(
        A.Ans.of(E.Decl.no_dupes(ps)),
        Kernel.is_type(fuel, env, ty))
    case E.DQuot{id, ps, ty, kind}:
      A.Ans.and(
        A.Ans.of(E.Decl.no_dupes(ps)),
        Kernel.is_type(fuel, env, ty))

# True when a lookup found nothing.
def Kernel.missing(lk: E.Lookup) -> Bool:
  match lk:
    case E.LFound{d}:
      False{}
    case E.LMissing{}:
      True{}

# Is this name free in the environment? A declaration may not be made twice.
def Kernel.is_fresh(+env: List<&2, E.Decl>, +i: Nat) -> Bool:
  Kernel.missing(E.Env.find(env, i))

# Check every declaration, each against the ones before it. A name that is
# already taken is rejected, which is what stops a second declaration of the
# same constant from quietly replacing the first.
def Kernel.check_all(ds: List<&2, E.Decl>, +fuel: Nat, +acc: List<&2, E.Decl>) -> A.Ans:
  match ds:
    case Nil{}:
      A.AYes{}
    case Con{+h, t}:
      A.Ans.and(
        A.Ans.and(
          A.Ans.of(Kernel.is_fresh(acc, E.Decl.id(h))),
          Kernel.check_decl(fuel, acc, h)),
        Kernel.check_all(t, fuel, Con{h, acc}))

# The kind of a declaration, for the report.
def Kernel.kind_name(d: E.Decl) -> String:
  match d:
    case E.DAxiom{id, ps, ty}:
      "axiom"
    case E.DDef{id, ps, ty, val}:
      "def  "
    case E.DThm{id, ps, ty, val}:
      "thm  "
    case E.DInd{id, ps, ty, np, ni, ctors}:
      "ind  "
    case E.DCtor{id, ps, ty, ind, cidx, np, nf}:
      "ctor "
    case E.DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds}:
      "rec  "
    case E.DQuot{id, ps, ty, kind}:
      "quot "

# One check, named, with a tick or a cross.
def Kernel.flag(+name: String, a: A.Ans) -> String:
  match a:
    case A.AYes{}:
      " " ++ name ++ "=ok"
    case A.ANo{}:
      " " ++ name ++ "=BAD"
    case A.AUnk{}:
      " " ++ name ++ "=unknown"

# Which of the checks on a declaration passed? A rejection says little on its
# own, and the three parts fail for very different reasons.
def Kernel.why(+fuel: Nat, +env: List<&2, E.Decl>, d: E.Decl) -> String:
  match d:
    case E.DAxiom{id, ps, ty}:
      Kernel.flag("params", A.Ans.of(E.Decl.no_dupes(ps))) ++
      Kernel.flag("type", Kernel.is_type(fuel, env, ty))
    case E.DDef{id, ps, +ty, +val}:
      Kernel.flag("params", A.Ans.of(E.Decl.no_dupes(ps))) ++
      Kernel.flag("type", Kernel.is_type(fuel, env, ty)) ++
      Kernel.flag("infer", I.Infer.res_ans(I.Infer.infer(fuel, env, Nil{}, val))) ++
      Kernel.flag("conv", C.Conv.eq(fuel, env,
        I.Infer.res_ty(I.Infer.infer(fuel, env, Nil{}, val)), ty)) ++
      Kernel.flag("same", A.Ans.of(T.Term.same(
        I.Infer.res_ty(I.Infer.infer(fuel, env, Nil{}, val)), ty)))
    case E.DThm{id, ps, +ty, +val}:
      Kernel.flag("params", A.Ans.of(E.Decl.no_dupes(ps))) ++
      Kernel.flag("type", Kernel.is_type(fuel, env, ty)) ++
      Kernel.flag("prop", Kernel.is_prop(fuel, env, ty)) ++
      Kernel.flag("value", Kernel.has_type(fuel, env, val, ty))
    case o:
      ""

# One line of the report.
def Kernel.mark(a: A.Ans, +id: Nat, +kind: String, +why: String) -> String:
  match a:
    case A.AYes{}:
      "  ok     " ++ kind ++ " " ++ Nat.show(id) ++ "\n"
    case A.ANo{}:
      "  REJECT " ++ kind ++ " " ++ Nat.show(id) ++ why ++ "\n"
    case A.AUnk{}:
      "  unknown " ++ kind ++ " " ++ Nat.show(id) ++ why ++ "\n"

# Which declaration failed? Reports one line per declaration, in order, so a
# rejection can be traced to the declaration that caused it rather than
# guessed at. The id is the export's own name index.
def Kernel.report(ds: List<&2, E.Decl>, +fuel: Nat, +acc: List<&2, E.Decl>) -> String:
  match ds:
    case Nil{}:
      ""
    case Con{+h, t}:
      Kernel.mark(
        A.Ans.and(
          A.Ans.of(Kernel.is_fresh(acc, E.Decl.id(h))),
          Kernel.check_decl(fuel, acc, h)),
        E.Decl.id(h),
        Kernel.kind_name(h),
        Kernel.why(fuel, acc, h)) ++ Kernel.report(t, fuel, Con{h, acc})

# Is this declaration one whose contents are not checked?
def Kernel.is_trusted(d: E.Decl) -> Bool:
  match d:
    case E.DInd{id, ps, ty, np, ni, ctors}:
      True{}
    case E.DCtor{id, ps, ty, ind, cidx, np, nf}:
      True{}
    case E.DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds}:
      True{}
    case E.DQuot{id, ps, ty, kind}:
      True{}
    case o:
      False{}

# Did any declaration have to be taken on trust? A caller that cares about
# soundness should decline rather than accept when this is true.
def Kernel.trusts(ds: List<&2, E.Decl>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{+h, t}:
      Bool.or(Kernel.is_trusted(h), Kernel.trusts(t))

# How many declarations are there?
def Kernel.count(ds: List<&2, E.Decl>, +acc: Nat) -> Nat:
  match ds:
    case Nil{}:
      acc
    case Con{h, t}:
      Kernel.count(t, 1n+acc)
