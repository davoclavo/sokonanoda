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
def Kernel.is_type(+fuel: Nat, +env: E.DTable, ty: T.Term) -> A.Ans:
  +r = I.Infer.infer(fuel, env, Nil{}, ty)
  A.Ans.and(
    I.Infer.res_ans(r),
    I.Infer.sort_ans(V.Eval.whnf(fuel, env, I.Infer.res_ty(r), Nil{})))

# Does `v` have type `ty`?
def Kernel.has_type(+fuel: Nat, +env: E.DTable, v: T.Term, ty: T.Term) -> A.Ans:
  +r = I.Infer.infer(fuel, env, Nil{}, v)
  A.Ans.and(
    I.Infer.res_ans(r),
    C.Conv.eq(fuel, env, I.Infer.res_ty(r), ty))

# Is this term a Prop, that is, does its own type reduce to `Sort 0`?
# A theorem's type must be one.
def Kernel.is_prop(+fuel: Nat, +env: E.DTable, ty: T.Term) -> A.Ans:
  +w = V.Eval.whnf(fuel, env, I.Infer.res_ty(I.Infer.infer(fuel, env, Nil{}, ty)), Nil{})
  A.Ans.and(
    I.Infer.sort_ans(w),
    A.Ans.of(L.Level.is_zero(I.Infer.sort_level(w))))

# The checks on an inductive block that need no derivation
# -------------------------------------------------------
#
# A block states more than it proves. These three are the parts a kernel can
# settle by reading, without deriving the recursor, and each one is an attack
# the arena makes.

# Is this name an inductive in the environment?
def Kernel.is_ind_name(+env: E.DTable, +i: Nat) -> Bool:
  E.Decl.is_ind(E.Lookup.get(E.Env.find(env, i)))

# A constructor must build an inductive that exists. The arena's
# `orphan-ctor` names one that does not.
def Kernel.ctor_ind_ok(+env: E.DTable, +d: E.Decl) -> Bool:
  Kernel.is_ind_name(env, E.Decl.ctor_ind(d))

# A constructor's type opens with one binder for each parameter and one for
# each field, and nothing else: its result is an application of its own
# inductive, which is not a binder. The arena's `ctor-num-fields` states a
# count that the type does not have.
def Kernel.ctor_arity_ok(+d: E.Decl) -> Bool:
  Nat.is_eq(
    T.Term.pi_count(E.Decl.ctor_ty(d), 0n),
    Nat.add(E.Decl.ctor_np(d), E.Decl.ctor_nf(d)))

# A constructor's result is its own inductive, applied to its parameters in
# the order they were bound and at its own level parameters in that order.
#
# The arena attacks all three parts. `inductWrongCtorParams` applies the
# inductive to a constant where a parameter belongs,
# `inductWrongCtorResParams` passes the two parameters the other way round,
# and `inductWrongCtorResLevel` passes the two levels the other way round.
#
# Reading the result is syntactic, and that is safe only because
# `Kernel.ctor_arity_ok` has already settled that the telescope has exactly
# the binders it claims. Without that, a binder hidden behind a definition
# would make this read the wrong term and reject a constructor that is right.

# Is this level the `k`-th parameter?
def Kernel.level_is_par(l: L.Level, +k: Nat) -> Bool:
  match l:
    case L.LPar{i}:
      Nat.is_eq(i, k)
    case x:
      False{}

# Are these the level parameters of the declaration, in order?
def Kernel.levels_in_order(ls: List<&2, L.Level>, +k: Nat, +n: Nat) -> Bool:
  match ls:
    case Nil{}:
      Nat.is_eq(k, n)
    case Con{h, t}:
      Bool.and(
        Kernel.level_is_par(h, k),
        Kernel.levels_in_order(t, 1n+k, n))

# Are these arguments the parameters, in the order they were bound? Inside a
# telescope of `1n+base` binders the first one bound is the furthest away, so
# parameter `k` is the variable `base - k`.
def Kernel.params_in_order(args: List<&2, T.Term>, +k: Nat, +base: Nat) -> Bool:
  match args:
    case Nil{}:
      True{}
    case Con{h, t}:
      match h:
        case T.TVar{i}:
          Bool.and(
            Nat.is_eq(i, Nat.sub(base, k)),
            Kernel.params_in_order(t, 1n+k, base))
        case x:
          False{}

# Is the head of the result the inductive, at its own levels, applied to its
# own parameters?
def Kernel.result_head(
  h: T.Term, +ind: Nat, +nl: Nat, +np: Nat, +base: Nat,
  +args: List<&2, T.Term>
) -> Bool:
  match h:
    case T.TConst{n, ls}:
      Bool.and(
        Bool.and(Nat.is_eq(n, ind), Kernel.levels_in_order(ls, 0n, nl)),
        Bool.and(
          Nat.is_le(np, V.Eval.len(args, 0n)),
          Kernel.params_in_order(V.Eval.take(args, np), 0n, base)))
    case x:
      False{}

def Kernel.ctor_result_ok(+d: E.Decl) -> Bool:
  Kernel.result_head(
    V.Eval.head(
      T.Term.pi_skip(
        Nat.add(E.Decl.ctor_np(d), E.Decl.ctor_nf(d)),
        E.Decl.ctor_ty(d))),
    E.Decl.ctor_ind(d),
    E.Decl.len(E.Decl.params(d)),
    E.Decl.ctor_np(d),
    Nat.sub(Nat.add(E.Decl.ctor_np(d), E.Decl.ctor_nf(d)), 1n),
    V.Eval.spine(
      T.Term.pi_skip(
        Nat.add(E.Decl.ctor_np(d), E.Decl.ctor_nf(d)),
        E.Decl.ctor_ty(d)),
      Nil{}))

# Every field of a constructor is strictly positive in the inductive.
#
# The inductive may not occur in the domain of an arrow inside a field. A
# field of type `I -> I` makes the type its own negation, which is unsound,
# and the arena's `indNeg` declares exactly that. `indNegReducible` hides the
# occurrence behind an application in the domain, and the rule catches it just
# the same, because it reads every occurrence and not only a head.
#
# Only the domains are refused. An occurrence to the right of an arrow, as in
# `Nat -> I`, is what an ordinary recursive field looks like, and an
# occurrence under another inductive, as in `List I`, is the nested case that
# Lean accepts. Refusing those would reject types that are in fact sound,
# which is the one mistake worth more than a missed attack.

# No occurrence of the inductive in any domain of this field's type.
def Kernel.positive(t: T.Term, +ind: Nat) -> Bool:
  match t:
    case T.TPi{ty, bd}:
      Bool.and(
        Bool.not(T.Term.occurs(ty, ind)),
        Kernel.positive(bd, ind))
    case x:
      True{}

# Walk the constructor's telescope. The first `n` binders are its parameters
# and are not fields; every binder after them is one.
def Kernel.ctor_pos(t: T.Term, +n: Nat, +ind: Nat) -> Bool:
  match t:
    case T.TPi{ty, bd}:
      match n:
        case 0n:
          Bool.and(
            Kernel.positive(ty, ind),
            Kernel.ctor_pos(bd, 0n, ind))
        case 1n+m:
          Kernel.ctor_pos(bd, m, ind)
    case x:
      True{}

def Kernel.ctor_pos_ok(+d: E.Decl) -> Bool:
  Kernel.ctor_pos(E.Decl.ctor_ty(d), E.Decl.ctor_np(d), E.Decl.ctor_ind(d))

# The inductive being declared may not occur in its own indices.
#
# Lean refuses it outright, and so does this. The arena's `inductInIndex`
# declares `inductInIndex : Prop -> Prop` with the one constructor
# `mk : inductInIndex (inductInIndex aProp)`, where the index names the very
# type being defined.
#
# Only the indices are read, never the fields. A recursive occurrence in a
# field is what makes `Nat.succ` work and is allowed.
def Kernel.ctor_index_ok(+d: E.Decl) -> Bool:
  Bool.not(
    T.Term.occurs_any(
      V.Eval.drop(
        V.Eval.spine(
          T.Term.pi_skip(
            Nat.add(E.Decl.ctor_np(d), E.Decl.ctor_nf(d)),
            E.Decl.ctor_ty(d)),
          Nil{}),
        E.Decl.ctor_np(d)),
      E.Decl.ctor_ind(d)))

# A recursor eliminates at least one inductive, and every one it names must
# exist. The arena's `orphan-rec` names none at all.
def Kernel.rec_inds_ok(+env: E.DTable, +ns: List<&2, Nat>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(Kernel.is_ind_name(env, h), Kernel.rec_inds_ok(env, t))

# A recursor must also carry the name a recursor has. Lean names the
# eliminator of `I` as `I.rec`, and the arena ships three attacks on that:
# `extra-rec` adds a second eliminator called `False.rogue`, and
# `misnamed_rec_user` and `dup_rec_def2` each name theirs `not_rec`.
def Kernel.rec_ok(+env: E.DTable, +d: E.Decl) -> Bool:
  Bool.and(
    E.Decl.rec_named(d),
    Bool.and(
      Bool.not(E.Decl.is_nil(E.Decl.rec_inds(d))),
      Kernel.rec_inds_ok(env, E.Decl.rec_inds(d))))

# An inductive's type is a telescope of one binder for each parameter and
# each index, and it ends in a sort. The arena attacks both halves:
# `inductTooFewParams` states two parameters for a type with one binder, and
# `inductBadNonSort2` ends in `aType`, an axiom whose own type is a sort,
# which makes it a term of a sort and never a sort itself.
#
# Reduction runs before each binder, because a binder can be hidden behind a
# definition. Running out of binders answers with a loose variable, which is
# neither a sort nor a pi, so the check reports a definite no: a term already
# in weak head normal form that is not a pi will never become one. Running out
# of budget answers with the unknown term, and that reports not knowing.
def Kernel.strip(fuel: Nat, +env: E.DTable, n: Nat, w: T.Term) -> T.Term:
  match fuel:
    case 0n:
      T.TUnk{}
    case 1n+(+f):
      match n:
        case 0n:
          w
        case 1n+m:
          match w:
            case T.TPi{ty, bd}:
              Kernel.strip(f, env, m, V.Eval.whnf(f, env, bd, Nil{}))
            case T.TUnk{}:
              T.TUnk{}
            case x:
              T.TVar{0n}

def Kernel.ind_shape(+fuel: Nat, +env: E.DTable, +d: E.Decl) -> A.Ans:
  I.Infer.sort_ans(
    Kernel.strip(
      fuel,
      env,
      Nat.add(E.Decl.ind_np(d), E.Decl.ind_ni(d)),
      V.Eval.whnf(fuel, env, E.Decl.ind_ty(d), Nil{})))

# A constructor's fields must fit in the inductive's own universe.
#
# Only the fields. The parameters are binders of the constructor's type too,
# and their sorts are higher than the inductive's by design: `Prod` lives in
# `Type (max u v)` while its two parameters live in `Type (u+1)` and
# `Type (v+1)`. Taking the sort of the whole type rejected seventeen correct
# files before this was split out.
#
# A field's sort is read in a context holding the binders before it, because
# a later field may be typed by an earlier one.
#
# An inductive in `Prop` is exempt. Proof irrelevance makes every proof of
# one proposition equal, so a field of any sort is sound there, and Lean
# allows it. `Exists`, `Acc` and the arena's own `Prop` structures all carry
# fields above `Prop`, and eight correct files were rejected before this was
# written down. What such a type may not do is let a field back out, and that
# is the separate rule in `Infer.proj_from`.
def Kernel.field_fits(+w: T.Term, +s: L.Level, +fuel: Nat) -> A.Ans:
  A.Ans.and(
    I.Infer.sort_ans(w),
    A.Ans.of(L.Level.leq(fuel, I.Infer.sort_level(w), s)))

def Kernel.field_univ(
  +fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>,
  +ty: T.Term, +s: L.Level
) -> A.Ans:
  Kernel.field_fits(
    V.Eval.whnf(
      fuel, env,
      I.Infer.res_ty(I.Infer.infer(fuel, env, ctx, ty)),
      Nil{}),
    s,
    fuel)

# Walk the constructor's telescope. The first `n` binders are parameters and
# only join the context; every binder after one is a field and is checked.
def Kernel.fields_univ(
  fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>, t: T.Term,
  +n: Nat, +s: L.Level
) -> A.Ans:
  match fuel:
    case 0n:
      A.AUnk{}
    case 1n+(+f):
      match t:
        case T.TPi{+ty, bd}:
          match n:
            case 0n:
              A.Ans.and(
                Kernel.field_univ(f, env, ctx, ty, s),
                Kernel.fields_univ(f, env, Con{ty, ctx}, bd, 0n, s))
            case 1n+m:
              Kernel.fields_univ(f, env, Con{ty, ctx}, bd, m, s)
        case x:
          A.AYes{}

def Kernel.univ_skip(
  b: Bool, +fuel: Nat, +env: E.DTable, +d: E.Decl, +s: L.Level
) -> A.Ans:
  match b:
    case True{}:
      A.AYes{}
    case False{}:
      Kernel.fields_univ(
        fuel, env, Nil{}, E.Decl.ctor_ty(d), E.Decl.ctor_np(d), s)

def Kernel.ctor_univ_at(
  +fuel: Nat, +env: E.DTable, +d: E.Decl, +ds: T.Term
) -> A.Ans:
  A.Ans.and(
    I.Infer.sort_ans(ds),
    Kernel.univ_skip(
      L.Level.is_zero(I.Infer.sort_level(ds)),
      fuel, env, d, I.Infer.sort_level(ds)))

def Kernel.ctor_univ(+fuel: Nat, +env: E.DTable, +d: E.Decl) -> A.Ans:
  Kernel.ctor_univ_at(
    fuel,
    env,
    d,
    Kernel.strip(
      fuel,
      env,
      Nat.add(
        E.Decl.ind_np(
          E.Lookup.get(E.Env.find(env, E.Decl.ctor_ind(d)))),
        E.Decl.ind_ni(
          E.Lookup.get(E.Env.find(env, E.Decl.ctor_ind(d))))),
      V.Eval.whnf(
        fuel, env,
        E.Decl.ind_ty(E.Lookup.get(E.Env.find(env, E.Decl.ctor_ind(d)))),
        Nil{})))

# A recursor's counts must match the block it eliminates.
#
# These are the numbers the recursor states about itself, and the block it
# names says what each one has to be: one motive for each inductive, one minor
# premise for each constructor of all of them, one rule for each minor
# premise, and the same parameters and indices as the inductive.
#
# Nothing here derives anything. It is the cheap half of the check that a
# derivation would make, and it is enough for the arena's `BogusRecursor`,
# which declares a recursor for a one-constructor type with no motive, no
# minor premise and no rule at all.
def Kernel.ctors_total(ns: List<&2, Nat>, +env: E.DTable, +acc: Nat) -> Nat:
  match ns:
    case Nil{}:
      acc
    case Con{h, t}:
      Kernel.ctors_total(
        t,
        env,
        Nat.add(
          acc,
          E.Decl.len(
            E.Decl.ind_ctors(E.Lookup.get(E.Env.find(env, h))))))

def Kernel.rec_counts_ok(+env: E.DTable, +d: E.Decl) -> Bool:
  Bool.and(
    Bool.and(
      Nat.is_eq(E.Decl.rec_nm(d), E.Decl.len(E.Decl.rec_inds(d))),
      Nat.is_eq(
        E.Decl.rec_nmin(d),
        Kernel.ctors_total(E.Decl.rec_inds(d), env, 0n))),
    Bool.and(
      Nat.is_eq(
        E.Decl.rules_len(E.Decl.rec_rules(d), 0n),
        E.Decl.rec_nmin(d)),
      Bool.and(
        Nat.is_eq(
          E.Decl.rec_np(d),
          E.Decl.ind_np(
            E.Lookup.get(
              E.Env.find(env, E.Decl.only(E.Decl.rec_inds(d)))))),
        Nat.is_eq(
          E.Decl.rec_ni(d),
          E.Decl.ind_ni(
            E.Lookup.get(
              E.Env.find(env, E.Decl.only(E.Decl.rec_inds(d)))))))))

# A recursor on a proposition with more than one constructor may eliminate
# only into a proposition.
#
# An inductive in `Prop` with two or more constructors has no large
# elimination: reading which constructor built a proof would recover data
# from a proof, and proof irrelevance has already made the two proofs equal.
# So its recursor takes no universe of its own, and the arena's
# `large-elim-prop-bool` gives one a universe anyway.
#
# One constructor is the subsingleton case and is left alone. `Eq`, `And` and
# `Acc` all eliminate into any sort and all have one constructor, so the rule
# must not fire on them. A proposition with no constructors, such as `False`,
# is the same: there is nothing to read.
def Kernel.large_ok(
  b: Bool, +nl: Nat, +ns: Nat
) -> A.Ans:
  match b:
    case True{}:
      A.Ans.of(Nat.is_eq(nl, ns))
    case False{}:
      A.AYes{}

def Kernel.rec_elim_at(
  +fuel: Nat, +d: E.Decl, +ind: E.Decl, +ds: T.Term
) -> A.Ans:
  A.Ans.and(
    I.Infer.sort_ans(ds),
    Kernel.large_ok(
      Bool.and(
        L.Level.is_zero(I.Infer.sort_level(ds)),
        Nat.is_lt(1n, E.Decl.rec_nmin(d))),
      E.Decl.len(E.Decl.params(d)),
      E.Decl.len(E.Decl.params(ind))))

def Kernel.rec_elim(+fuel: Nat, +env: E.DTable, +d: E.Decl) -> A.Ans:
  Kernel.rec_elim_at(
    fuel,
    d,
    E.Lookup.get(E.Env.find(env, E.Decl.only(E.Decl.rec_inds(d)))),
    Kernel.strip(
      fuel,
      env,
      Nat.add(
        E.Decl.ind_np(
          E.Lookup.get(
            E.Env.find(env, E.Decl.only(E.Decl.rec_inds(d))))),
        E.Decl.ind_ni(
          E.Lookup.get(
            E.Env.find(env, E.Decl.only(E.Decl.rec_inds(d)))))),
      V.Eval.whnf(
        fuel, env,
        E.Decl.ind_ty(
          E.Lookup.get(
            E.Env.find(env, E.Decl.only(E.Decl.rec_inds(d))))),
        Nil{})))

# Check one declaration against the declarations before it.
def Kernel.check_decl(+fuel: Nat, +env: E.DTable, d: E.Decl) -> A.Ans:
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
    case E.DInd{+id, +ps, +ty, +np, +ni, +ctors}:
      A.Ans.and(
        A.Ans.and(
          A.Ans.of(E.Decl.no_dupes(ps)),
          Kernel.ind_shape(
            fuel, env, E.DInd{id, ps, ty, np, ni, ctors})),
        Kernel.is_type(fuel, env, ty))
    case E.DCtor{+id, +ps, +ty, +ind, +cidx, +np, +nf}:
      A.Ans.and(
        Kernel.ctor_univ(
          fuel, env, E.DCtor{id, ps, ty, ind, cidx, np, nf}),
      A.Ans.and(
        A.Ans.of(
          Bool.and(
            E.Decl.no_dupes(ps),
            Bool.and(
              Kernel.ctor_ind_ok(env, E.DCtor{id, ps, ty, ind, cidx, np, nf}),
              Bool.and(
                Kernel.ctor_arity_ok(E.DCtor{id, ps, ty, ind, cidx, np, nf}),
                Bool.and(
                  Kernel.ctor_result_ok(
                    E.DCtor{id, ps, ty, ind, cidx, np, nf}),
                  Bool.and(
                    Kernel.ctor_index_ok(
                      E.DCtor{id, ps, ty, ind, cidx, np, nf}),
                    Kernel.ctor_pos_ok(
                      E.DCtor{id, ps, ty, ind, cidx, np, nf}))))))),
        Kernel.is_type(fuel, env, ty)))
    case E.DRec{+id, +ps, +ty, +np, +ni, +nm, +nmin, +k, +rules, +inds, +named}:
      A.Ans.and(
        A.Ans.and(
          A.Ans.of(
            Bool.and(
              E.Decl.no_dupes(ps),
              Bool.and(
                Kernel.rec_ok(
                  env,
                  E.DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named}),
                Kernel.rec_counts_ok(
                  env,
                  E.DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named})))),
          Kernel.rec_elim(
            fuel, env,
            E.DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named})),
        Kernel.is_type(fuel, env, ty))
    case E.DQuot{id, ps, ty, kind}:
      A.Ans.and(
        A.Ans.of(E.Decl.no_dupes(ps)),
        Kernel.is_type(fuel, env, ty))
    case E.DPrim{id, ps, +ty, val, op, yes, no}:
      A.Ans.and(
        A.Ans.of(E.Decl.no_dupes(ps)),
        A.Ans.and(
          Kernel.is_type(fuel, env, ty),
          Kernel.has_type(fuel, env, val, ty)))

# True when a lookup found nothing.
def Kernel.missing(lk: E.Lookup) -> Bool:
  match lk:
    case E.LFound{d}:
      False{}
    case E.LMissing{}:
      True{}

# Is this name free in the environment? A declaration may not be made twice.
def Kernel.is_fresh(+env: E.DTable, +i: Nat) -> Bool:
  Kernel.missing(E.Env.find(env, i))

# Check every declaration, each against the ones before it. A name that is
# already taken is rejected, which is what stops a second declaration of the
# same constant from quietly replacing the first.
def Kernel.check_all(ds: List<&2, E.Decl>, +fuel: Nat, +acc: E.DTable) -> A.Ans:
  match ds:
    case Nil{}:
      A.AYes{}
    case Con{+h, t}:
      A.Ans.and(
        A.Ans.and(
          A.Ans.of(Kernel.is_fresh(acc, E.Decl.id(h))),
          Kernel.check_decl(fuel, acc, h)),
        Kernel.check_all(t, fuel, E.Env.add(acc, h)))

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
    case E.DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named}:
      "rec  "
    case E.DQuot{id, ps, ty, kind}:
      "quot "
    case E.DPrim{id, ps, ty, val, op, yes, no}:
      "prim "

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
def Kernel.why(+fuel: Nat, +env: E.DTable, d: E.Decl) -> String:
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
def Kernel.report(ds: List<&2, E.Decl>, +fuel: Nat, +acc: E.DTable) -> String:
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
        Kernel.why(fuel, acc, h)) ++ Kernel.report(t, fuel, E.Env.add(acc, h))

# Is this declaration one whose contents are not checked?
def Kernel.is_trusted(d: E.Decl) -> Bool:
  match d:
    case E.DInd{id, ps, ty, np, ni, ctors}:
      True{}
    case E.DCtor{id, ps, ty, ind, cidx, np, nf}:
      True{}
    case E.DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named}:
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
