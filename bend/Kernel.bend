# Checking an environment.
#
# A declaration is checked against the declarations before it, as the Lean
# kernel does, so a forward reference cannot resolve.

import Base
import ./Level.bend as L
import ./Term.bend as T
import ./Env.bend as E
import ./Eval.bend as V
import ./Conv.bend as C
import ./Infer.bend as I

# Is this term a type, that is, does its own type reduce to a sort?
def Kernel.is_type(+fuel: Nat, +env: List<&2, E.Decl>, ty: T.Term) -> Bool:
  I.Infer.is_sort(
    V.Eval.whnf(fuel, env, I.Infer.res_ty(I.Infer.infer(fuel, env, Nil{}, ty)), Nil{}))

# Does `v` have type `ty`?
def Kernel.has_type(+fuel: Nat, +env: List<&2, E.Decl>, v: T.Term, ty: T.Term) -> Bool:
  +r = I.Infer.infer(fuel, env, Nil{}, v)
  Bool.and(
    I.Infer.res_ok(r),
    C.Conv.eq(fuel, env, I.Infer.res_ty(r), ty))

# Is this term a Prop, that is, does its own type reduce to `Sort 0`?
# A theorem's type must be one.
def Kernel.is_prop(+fuel: Nat, +env: List<&2, E.Decl>, ty: T.Term) -> Bool:
  L.Level.is_zero(
    I.Infer.sort_level(
      V.Eval.whnf(fuel, env, I.Infer.res_ty(I.Infer.infer(fuel, env, Nil{}, ty)), Nil{})))

# Check one declaration against the declarations before it.
def Kernel.check_decl(+fuel: Nat, +env: List<&2, E.Decl>, d: E.Decl) -> Bool:
  match d:
    case E.DAxiom{id, ps, ty}:
      Bool.and(
        E.Decl.no_dupes(ps),
        Kernel.is_type(fuel, env, ty))
    case E.DDef{id, ps, +ty, val}:
      Bool.and(
        E.Decl.no_dupes(ps),
        Bool.and(
          Kernel.is_type(fuel, env, ty),
          Kernel.has_type(fuel, env, val, ty)))
    case E.DThm{id, ps, +ty, val}:
      Bool.and(
        E.Decl.no_dupes(ps),
        Bool.and(
          Bool.and(
            Kernel.is_type(fuel, env, ty),
            Kernel.is_prop(fuel, env, ty)),
          Kernel.has_type(fuel, env, val, ty)))

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
def Kernel.check_all(ds: List<&2, E.Decl>, +fuel: Nat, +acc: List<&2, E.Decl>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{+h, t}:
      Bool.and(
        Bool.and(
          Kernel.is_fresh(acc, E.Decl.id(h)),
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

# One line of the report.
def Kernel.mark(ok: Bool, +id: Nat, +kind: String) -> String:
  match ok:
    case True{}:
      "  ok     " ++ kind ++ " " ++ Nat.show(id) ++ "\n"
    case False{}:
      "  REJECT " ++ kind ++ " " ++ Nat.show(id) ++ "\n"

# Which declaration failed? Reports one line per declaration, in order, so a
# rejection can be traced to the declaration that caused it rather than
# guessed at. The id is the export's own name index.
def Kernel.report(ds: List<&2, E.Decl>, +fuel: Nat, +acc: List<&2, E.Decl>) -> String:
  match ds:
    case Nil{}:
      ""
    case Con{+h, t}:
      Kernel.mark(
        Bool.and(
          Kernel.is_fresh(acc, E.Decl.id(h)),
          Kernel.check_decl(fuel, acc, h)),
        E.Decl.id(h),
        Kernel.kind_name(h)) ++ Kernel.report(t, fuel, Con{h, acc})

# How many declarations are there?
def Kernel.count(ds: List<&2, E.Decl>, +acc: Nat) -> Nat:
  match ds:
    case Nil{}:
      acc
    case Con{h, t}:
      Kernel.count(t, 1n+acc)
