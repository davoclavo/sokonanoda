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
import ./Vconv.bend as X
import ./Infer.bend as I
import ./Ans.bend as A
import ./Rec.bend as R
import ./Quo.bend as Q
import ./Table.bend as Tb

# Is this term a type, that is, does its own type reduce to a sort?
def Kernel.is_type(+fuel: Nat, +env: E.DTable, ty: T.Term) -> A.Ans:
  +r = I.Infer.infer(fuel, env, Nil{}, ty)
  A.Ans.and(
    I.Infer.res_ans(r),
    I.Infer.sort_ans(V.Eval.whnf(fuel, env, I.Infer.res_ty(r), Nil{})))

# Does `v` have type `ty`?
#
# The conversion is skipped when inference has already answered no. That is
# not only the cost of a pass nobody needs: `I.Infer.res_ty` of a definite no
# is the dummy, a loose variable, and comparing it against the declared type
# reports a second failure that is an artefact of the first. `bend/why.bend`
# on a 10 MB export spent its whole walk on that artefact before this.
def Kernel.has_type(+fuel: Nat, +env: E.DTable, v: T.Term, ty: T.Term) -> A.Ans:
  +r = I.Infer.infer(fuel, env, Nil{}, v)
  X.Vconv.eq_unless_no(
    I.Infer.res_ans(r), fuel, env, Nil{}, I.Infer.res_ty(r), ty)

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
    A.Ans.of(L.Level.leq(I.Infer.sort_level(w), s)))

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

# Does this recursor eliminate a nested block?
#
# A nested inductive gets auxiliary types that the export does not list among
# the recursor's inductives, so its motive count is larger than that list.
# Nothing here can count the constructors of a type it cannot name, so the
# counts cannot be checked and must not be claimed wrong.
#
# The test is one-sided, and that matters. A nested block states **more**
# motives than it lists inductives, because the auxiliary types need one
# each. The arena's `073_BogusRecursor` states fewer, zero against one, so a
# two-sided test let it through to the trust path and it answered declined
# where it had answered reject.
#
# A file could still state an inflated motive count to escape the counts
# below. It cannot buy anything with that: the derivation in `Rec.bend` wants
# one motive, so the block stays trusted and the file declines rather than
# accepts.
def Kernel.rec_nested(+d: E.Decl) -> Bool:
  Nat.is_lt(E.Decl.len(E.Decl.rec_inds(d)), E.Decl.rec_nm(d))

def Kernel.rec_counts_strict(+env: E.DTable, +d: E.Decl) -> Bool:
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
def Kernel.rec_counts_ok(+env: E.DTable, +d: E.Decl) -> Bool:
  Bool.or(
    Kernel.rec_nested(d),
    Kernel.rec_counts_strict(env, d))

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
    case E.DQuot{id, ps, ty, kind, eq}:
      A.Ans.and(
        A.Ans.of(E.Decl.no_dupes(ps)),
        Kernel.is_type(fuel, env, ty))
    case E.DPrim{id, ps, +ty, val, op, yes, no}:
      A.Ans.and(
        A.Ans.of(E.Decl.no_dupes(ps)),
        A.Ans.and(
          Kernel.is_type(fuel, env, ty),
          Kernel.has_type(fuel, env, val, ty)))
    case E.DUnsafe{id, ps, ty}:
      A.AYes{}

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

# Does this declaration name only the universes it declares?
#
# The Lean kernel rejects one that does, and this kernel has to, because
# `Level.param_pos` numbers a declaration's parameters by position: a name
# index that is smaller than the number of declared parameters would be read
# as one of them, so a file could use a universe it never declared and have
# it taken for a universe it did. The marker `Level.param_pos` leaves is out
# of range, and so is any index past the last declared parameter.
def Kernel.pars_ok(+d: E.Decl) -> Bool:
  Bool.or(
    E.Decl.is_unsafe(d),
    Bool.and(
      T.Term.pars_ok(
        E.Decl.raw_ty(d), List.length(&2, Nat, E.Decl.params(d))),
      T.Term.pars_ok(
        E.Decl.raw_val(d), List.length(&2, Nat, E.Decl.params(d)))))

# Does this term mention a declaration Lean's kernel never looked at?
#
# A constant that is not in the environment yet answers no, because the
# ordered check rejects a forward reference on its own.
#
# A reference is resolved rather than read as a leaf. Without that the rule is
# blind and `140_falseFromUnsafe` is accepted. Resolving is not a structural
# step, so the walk carries a budget, and running out answers no, which is the
# permissive side and cannot turn an unknown into a rejection.
#
# Each entry of the table is resolved **once**. A term may name one entry
# twice, and `perf/app-lam` names every one of its four thousand levels
# twice, so a walk that resolved a reference wherever it met one did the
# work of the whole expansion: `2^n`. A generated family of that shape
# measured this walk at a factor of two per level, and the file could not be
# read at all. What the entry holds is the same term wherever it is named
# from, and the shift does not change which constants it mentions, so the
# number of the entry is the whole of the key.
def Kernel.uses_stop(
  bad: Bool, +rest: List<&2, T.Term>
) -> List<&2, T.Term>:
  match bad:
    case True{}:
      Nil{}
    case False{}:
      rest

def Kernel.uses_push(
  seen: Bool, +env: E.DTable, +i: Nat, +k: Nat,
  +rest: List<&2, T.Term>
) -> List<&2, T.Term>:
  match seen:
    case True{}:
      rest
    case False{}:
      Con{E.Env.expr_at(env, i, k), rest}

def Kernel.uses_mark(
  seen: Bool, +tb: Tb.NTable, +i: Nat
) -> Tb.NTable:
  match seen:
    case True{}:
      tb
    case False{}:
      Tb.Table.write_nat(tb, i, 1n)

def Kernel.uses_go(
  +fuel: Nat, +env: E.DTable, +tb: Tb.NTable, work: List<&2, T.Term>
) -> Bool:
  match fuel:
    case 0n:
      False{}
    case 1n+f:
      match work:
        case Nil{}:
          False{}
        case Con{t, +rest}:
          match t:
            case T.TRef{+i, +k, m}:
              +sn : Bool = Nat.is_lt(0n, Tb.Table.read_nat(tb, i))
              Kernel.uses_go(
                f, env, Kernel.uses_mark(sn, tb, i),
                Kernel.uses_push(sn, env, i, k, rest))
            case T.TConst{+n, ls}:
              +bad : Bool =
                E.Decl.is_unsafe(E.Lookup.get(E.Env.find(env, n)))
              Bool.or(
                bad,
                Kernel.uses_go(
                  f, env, tb, Kernel.uses_stop(bad, rest)))
            case T.TApp{+g, +a}:
              Kernel.uses_go(f, env, tb, Con{g, Con{a, rest}})
            case T.TLam{+ty, +bd}:
              Kernel.uses_go(f, env, tb, Con{ty, Con{bd, rest}})
            case T.TPi{+ty, +bd}:
              Kernel.uses_go(f, env, tb, Con{ty, Con{bd, rest}})
            case T.TLet{+ty, +v, +bd}:
              Kernel.uses_go(
                f, env, tb, Con{ty, Con{v, Con{bd, rest}}})
            case T.TProj{tn, idx, +st}:
              Kernel.uses_go(f, env, tb, Con{st, rest})
            case o:
              Kernel.uses_go(f, env, tb, rest)

def Kernel.uses_unsafe(+fuel: Nat, t: T.Term, +env: E.DTable) -> Bool:
  Kernel.uses_go(fuel, env, Tb.NTable.new(), [t])

# How far the walk for an unsafe use may go. It is not the declaration's
# budget: this is a walk of a term and not a reduction, and giving up answers
# the permissive side, so the bound has to be one a real export never reaches.
def Kernel.deep_budget() -> Nat:
  1000000n

def Kernel.safe_pick(un: Bool, +d: E.Decl, +env: E.DTable) -> Bool:
  match un:
    case True{}:
      True{}
    case False{}:
      Bool.not(
        Bool.or(
          Kernel.uses_unsafe(
            Kernel.deep_budget(), E.Decl.raw_ty(d), env),
          Kernel.uses_unsafe(
            Kernel.deep_budget(), E.Decl.raw_val(d), env)))

# May this declaration use what it uses?
#
# An unsafe declaration may use anything, because nothing is concluded from
# it. A safe one may not mention an unsafe one, and that is the rule that
# lets the kernel leave an unsafe body unread: the arena's
# `140_falseFromUnsafe` proves `False` from `unsafe def loop : False := loop`
# and this is what refuses it.
def Kernel.safe_uses(+d: E.Decl, +env: E.DTable) -> Bool:
  Kernel.safe_pick(E.Decl.is_unsafe(d), d, env)

# Check every declaration, each against the ones before it, with the answer
# so far as a parameter.
#
# The answer travels in rather than out for the same two reasons it does in
# `Conv.eq_all`. A definite no stops the walk, which a conjunction over the
# recursive call cannot do, because an argument evaluates before the match
# picks an arm. And the call is in tail position, so a file with tens of
# thousands of declarations does not need a host frame for each one.
def Kernel.check_from(
  ds: List<&2, E.Decl>, a: A.Ans, +fuel: Nat, +acc: E.DTable
) -> A.Ans:
  match ds a:
    case Nil{} o:
      o
    case Con{h, t} A.ANo{}:
      A.ANo{}
    case Con{+h, t} o:
      Kernel.check_from(
        t,
        A.Ans.and(
          o,
          A.Ans.and(
            A.Ans.and(
              A.Ans.of(Kernel.is_fresh(acc, E.Decl.id(h))),
              A.Ans.and(
                A.Ans.of(Kernel.pars_ok(h)),
                A.Ans.of(Kernel.safe_uses(h, acc)))),
            Kernel.check_decl(fuel, acc, h))),
        fuel,
        E.Env.add(acc, h))

# Check every declaration, each against the ones before it. A name that is
# already taken is rejected, which is what stops a second declaration of the
# same constant from quietly replacing the first.
def Kernel.check_all(ds: List<&2, E.Decl>, +fuel: Nat, +acc: E.DTable) -> A.Ans:
  Kernel.check_from(ds, A.AYes{}, fuel, acc)

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
    case E.DQuot{id, ps, ty, kind, eq}:
      "quot "
    case E.DPrim{id, ps, ty, val, op, yes, no}:
      "prim "
    case E.DUnsafe{id, ps, ty}:
      "unsf "

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
def Kernel.why_kind(+fuel: Nat, +env: E.DTable, d: E.Decl) -> String:
  match d:
    case E.DAxiom{id, ps, ty}:
      Kernel.flag("params", A.Ans.of(E.Decl.no_dupes(ps))) ++
      Kernel.flag("type", Kernel.is_type(fuel, env, ty))
    case E.DDef{id, ps, +ty, +val}:
      Kernel.flag("params", A.Ans.of(E.Decl.no_dupes(ps))) ++
      Kernel.flag("type", Kernel.is_type(fuel, env, ty)) ++
      Kernel.flag("infer", I.Infer.res_ans(I.Infer.infer(fuel, env, Nil{}, val))) ++
      Kernel.flag("conv", X.Vconv.eq(fuel, env,
        I.Infer.res_ty(I.Infer.infer(fuel, env, Nil{}, val)), ty)) ++
      Kernel.flag("same", A.Ans.of(C.Conv.same(env, 
        I.Infer.res_ty(I.Infer.infer(fuel, env, Nil{}, val)), ty)))
    case E.DThm{id, ps, +ty, +val}:
      Kernel.flag("params", A.Ans.of(E.Decl.no_dupes(ps))) ++
      Kernel.flag("type", Kernel.is_type(fuel, env, ty)) ++
      Kernel.flag("prop", Kernel.is_prop(fuel, env, ty)) ++
      Kernel.flag(
        "infer", I.Infer.res_ans(I.Infer.infer(fuel, env, Nil{}, val))) ++
      Kernel.flag(
        "conv",
        X.Vconv.eq(
          fuel, env,
          I.Infer.res_ty(I.Infer.infer(fuel, env, Nil{}, val)), ty))
    case E.DCtor{+id, +ps, +ty, +ind, +cidx, +np, +nf}:
      Kernel.flag("params", A.Ans.of(E.Decl.no_dupes(ps))) ++
      Kernel.flag(
        "univ",
        Kernel.ctor_univ(
          fuel, env, E.DCtor{id, ps, ty, ind, cidx, np, nf})) ++
      Kernel.flag(
        "ind",
        A.Ans.of(
          Kernel.ctor_ind_ok(
            env, E.DCtor{id, ps, ty, ind, cidx, np, nf}))) ++
      Kernel.flag(
        "arity",
        A.Ans.of(
          Kernel.ctor_arity_ok(E.DCtor{id, ps, ty, ind, cidx, np, nf}))) ++
      Kernel.flag(
        "result",
        A.Ans.of(
          Kernel.ctor_result_ok(E.DCtor{id, ps, ty, ind, cidx, np, nf}))) ++
      Kernel.flag(
        "index",
        A.Ans.of(
          Kernel.ctor_index_ok(E.DCtor{id, ps, ty, ind, cidx, np, nf}))) ++
      Kernel.flag(
        "positive",
        A.Ans.of(
          Kernel.ctor_pos_ok(E.DCtor{id, ps, ty, ind, cidx, np, nf}))) ++
      Kernel.flag("type", Kernel.is_type(fuel, env, ty))
    case E.DRec{+id, +ps, +ty, +np, +ni, +nm, +nmin, +k, +rules, +inds, +named}:
      Kernel.flag("params", A.Ans.of(E.Decl.no_dupes(ps))) ++
      Kernel.flag(
        "block",
        A.Ans.of(
          Kernel.rec_ok(
            env,
            E.DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named}))) ++
      Kernel.flag(
        "counts",
        A.Ans.of(
          Kernel.rec_counts_ok(
            env,
            E.DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named}))) ++
      Kernel.flag(
        "elim",
        Kernel.rec_elim(
          fuel, env,
          E.DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named})) ++
      Kernel.flag("type", Kernel.is_type(fuel, env, ty))
    case o:
      ""

# One line of the report.
#
# The reason takes the declaration, not a string. An argument evaluates before
# the match picks an arm, so a `why` passed in as a string ran on every
# declaration, and `why` for a definition infers the body three more times.
# Taking the declaration keeps that cost on the two arms that print a reason.
def Kernel.why(+fuel: Nat, +env: E.DTable, +d: E.Decl) -> String:
  Kernel.flag("universes", A.Ans.of(Kernel.pars_ok(d))) ++
  Kernel.flag("safe", A.Ans.of(Kernel.safe_uses(d, env))) ++
  Kernel.why_kind(fuel, env, d)

def Kernel.mark(a: A.Ans, +id: Nat, +kind: String, +fuel: Nat, +env: E.DTable, d: E.Decl) -> String:
  match a:
    case A.AYes{}:
      "  ok     " ++ kind ++ " " ++ Nat.show(id) ++ "\n"
    case A.ANo{}:
      "  REJECT " ++ kind ++ " " ++ Nat.show(id) ++ Kernel.why(fuel, env, d) ++ "\n"
    case A.AUnk{}:
      "  unknown " ++ kind ++ " " ++ Nat.show(id) ++ Kernel.why(fuel, env, d) ++ "\n"

# The right side of every rule, against the one the file states.
def Kernel.rules_match(
  +fuel: Nat, +env: E.DTable, +r: E.Decl, n: Nat, +j: Nat
) -> A.Ans:
  match n:
    case 0n:
      A.AYes{}
    case 1n+k:
      A.Ans.and(
        X.Vconv.eq(
          fuel, env,
          R.Rec.rhs_at(fuel, env, r, j),
          R.Rec.stated_rhs(env, r, j)),
        Kernel.rules_match(fuel, env, r, k, 1n+j))

# Is this recursor the one its inductive implies?
#
# The type and every rule are derived from the specification and compared by
# conversion, not by syntax, because the exporter writes a telescope in
# whatever form it reduced to. A shape the derivation does not handle gives
# `T.TUnk`, which converts with nothing, so the answer is no and the block
# stays trusted.
def Kernel.rec_verified(+fuel: Nat, +env: E.DTable, +r: E.Decl) -> A.Ans:
  A.Ans.and(
    A.Ans.and(
      X.Vconv.eq(
        fuel, env,
        R.Rec.derive(fuel, env, r),
        E.Decl.type_at(
          r,
          R.Rec.lvl_shift(
            List.length(&2, Nat, E.Decl.params(r)), 0n, 0n))),
      A.Ans.of(
        R.Rec.rule_fields_ok(
          E.Decl.ind_ctors(
            E.Lookup.get(
              E.Env.find(env, E.Decl.only(E.Decl.rec_inds(r))))),
          env,
          E.Decl.rec_rules(r)))),
    Kernel.rules_match(fuel, env, r, E.Decl.rec_nmin(r), 0n))

# Does this declaration still have to be taken on trust?
#
# An inductive and its constructors are checked by the ten rules on a block.
# What was left was the recursor, which the file states and the kernel now
# derives, so a block whose recursor matches needs no trust. A quotient is
# still taken on trust, because nothing here derives one.
def Kernel.trusted_ans(+fuel: Nat, +env: E.DTable, d: E.Decl) -> Bool:
  match d:
    case E.DRec{+id, +ps, +ty, +np, +ni, +nm, +nmin, +k, +rules, +inds, +named}:
      Bool.not(
        A.Ans.is_yes(
          Kernel.rec_verified(
            fuel, env,
            E.DRec{id, ps, ty, np, ni, nm, nmin, k, rules, inds, named})))
    case o:
      False{}

# Does this quotient state the type Lean gives it?
#
# A quotient is checked against a fixed type, not derived from anything, so
# the only question is whether the file wrote it. A declaration that is not a
# quotient answers yes and costs one comparison of a number.
def Kernel.quot_one(
  is_q: Bool, +fuel: Nat, +env: E.DTable, +d: E.Decl, +q: Q.QN
) -> A.Ans:
  match is_q:
    case False{}:
      A.AYes{}
    case True{}:
      X.Vconv.eq(
        fuel, env,
        Q.Quo.want(
          E.Decl.quot_kind(d),
          Q.Quo.ty_of(q), Q.Quo.mk_of(q), E.Decl.quot_eq(d)),
        E.Decl.type_at(
          d,
          R.Rec.lvl_shift(
            List.length(&2, Nat, E.Decl.params(d)), 0n, 0n)))

# Every quotient in the file, against its fixed type.
#
# The environment is the one the whole file builds, because a quotient's type
# names `Quot` and `Eq` and the order they arrive in is the exporter's
# business. That is sound: this is a comparison of types and the check that a
# name is not used before it is declared is a separate one.
def Kernel.quots_ans(
  ds: List<&2, E.Decl>, +fuel: Nat, +env: E.DTable, +q: Q.QN
) -> A.Ans:
  match ds:
    case Nil{}:
      A.AYes{}
    case Con{+h, t}:
      A.Ans.and(
        Kernel.quot_one(
          Nat.is_lt(E.Decl.quot_kind(h), 4n), fuel, env, h, q),
        Kernel.quots_ans(t, fuel, env, q))

# The environment the whole file builds.
def Kernel.env_all(ds: List<&2, E.Decl>, +acc: E.DTable) -> E.DTable:
  match ds:
    case Nil{}:
      acc
    case Con{+h, t}:
      Kernel.env_all(t, E.Env.add(acc, h))

# Did any declaration have to be taken on trust? A caller that cares about
# soundness should decline rather than accept when this is true.
#
# The walk builds the environment as the kernel does, because a recursor can
# only be derived against the inductive and the constructors before it.
def Kernel.trusts_from(
  ds: List<&2, E.Decl>, +fuel: Nat, +acc: E.DTable
) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{+h, t}:
      Bool.or(
        Kernel.trusted_ans(fuel, acc, h),
        Kernel.trusts_from(t, fuel, E.Env.add(acc, h)))

def Kernel.trusts(+ds: List<&2, E.Decl>, +fuel: Nat, +acc: E.DTable) -> Bool:
  Bool.or(
    Kernel.trusts_from(ds, fuel, acc),
    Bool.not(
      A.Ans.is_yes(
        Kernel.quots_ans(
          ds, fuel,
          Kernel.env_all(ds, acc),
          Q.Quo.scan(ds, Q.MkQN{0n, 0n})))))

# How many declarations are there?
def Kernel.count(ds: List<&2, E.Decl>, +acc: Nat) -> Nat:
  match ds:
    case Nil{}:
      acc
    case Con{h, t}:
      Kernel.count(t, 1n+acc)

# Put one declaration's line in front of the rest of the walk. A match needs
# a parameter, so the pair the walk returns arrives as one.
def Kernel.run_join(line: String, p: A.Ans & String) -> A.Ans & String:
  (ra, rs) = p
  (ra, line ++ rs)

# Check every declaration once, and build the report from the same walk.
#
# `Kernel.report` and `Kernel.check_all` each walk the list and check every
# declaration, so a run that wants both answers checks the file twice. This
# walks it once and returns the verdict beside the report. It stops at the
# first rejection, as `Kernel.check_from` does, which is also what makes the
# report usable: `Kernel.why` runs on the declaration that failed and on no
# other.
def Kernel.run_from(
  ds: List<&2, E.Decl>, a: A.Ans, +fuel: Nat, +acc: E.DTable
) -> A.Ans & String:
  match ds a:
    case Nil{} o:
      (o, "")
    case Con{h, t} A.ANo{}:
      (A.ANo{}, "")
    case Con{+h, t} o:
      +b : A.Ans = A.Ans.and(
        A.Ans.and(
          A.Ans.of(Kernel.is_fresh(acc, E.Decl.id(h))),
          A.Ans.and(
            A.Ans.of(Kernel.pars_ok(h)),
            A.Ans.of(Kernel.safe_uses(h, acc)))),
        Kernel.check_decl(fuel, acc, h))
      line : String = Kernel.mark(b, E.Decl.id(h), Kernel.kind_name(h), fuel, acc, h)
      Kernel.run_join(line, Kernel.run_from(t, A.Ans.and(o, b), fuel, E.Env.add(acc, h)))

def Kernel.run(ds: List<&2, E.Decl>, +fuel: Nat, +acc: E.DTable) -> A.Ans & String:
  Kernel.run_from(ds, A.AYes{}, fuel, acc)
