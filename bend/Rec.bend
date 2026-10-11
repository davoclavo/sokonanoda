# Deriving a recursor from the inductive it eliminates.
#
# A file states a recursor: its type, and one rule per constructor. Nothing
# obliges the file to tell the truth, and a kernel that takes the statement on
# trust will accept a proof the recursor should not allow. So the kernel has to
# build the recursor itself from the inductive specification and compare.
#
# The type it builds for an inductive `I` with `np` parameters, `ni` indices
# and constructors `C_0 .. C_{m-1}` is
#
#   Pi p_0 .. p_{np-1},
#   Pi motive : (Pi i_0 .. i_{ni-1}, Pi t : I p.. i.., Sort v),
#   Pi minor_0 .. minor_{m-1},
#   Pi i_0 .. i_{ni-1},
#   Pi t : I p.. i..,
#   motive i.. t
#
# and the minor premise for `C_j : Pi p.., Pi f_0 .. f_{k-1}, I p.. a..` is
#
#   Pi f_0 .. f_{k-1},
#   Pi (one hypothesis per recursive field, in field order),
#   motive a.. (C_j p.. f..)
#
# where the hypothesis for a field `f_i : Pi x.., I p.. b..` is
#
#   Pi x.., motive b.. (f_i x..)
#
# Nothing here answers no. A derivation this cannot do hands back `T.TUnk`,
# and the caller compares that with the stated type and finds it does not
# convert, which leaves the block trusted and the file declined. So a gap here
# costs an acceptance and can never cost a false rejection.
#
# What it does not do yet: a mutual block, a nested inductive, and a recursor
# whose level parameters are not the inductive's with at most one in front.

import Base
import ./Term.bend as T
import ./Level.bend as L
import ./Env.bend as E
import ./Eval.bend as V

# The variables `TVar{first}`, `TVar{first-1}`, down to `first-n+1`.
def Rec.vars(n: Nat, +first: Nat) -> List<&2, T.Term>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{T.TVar{first}, Rec.vars(m, Nat.sub(first, 1n))}

# The level parameters at positions `at .. at+n-1`, each moved up by `by`.
# Substituting these through a term moves every level parameter in it, which
# is what a recursor with its own level in front of the inductive's needs.
def Rec.lvl_shift(n: Nat, +by: Nat, +at: Nat) -> List<&2, L.Level>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{L.LPar{Nat.add(at, by)}, Rec.lvl_shift(m, by, 1n+at)}

# The binder types of the first `n` binders of a telescope, outermost first.
def Rec.tele(n: Nat, t: T.Term) -> List<&2, T.Term>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      match t:
        case T.TPi{ty, bd}:
          Con{ty, Rec.tele(m, bd)}
        case o:
          Nil{}

# A pi telescope over a body, from binder types given outermost first.
def Rec.pis(tys: List<&2, T.Term>, body: T.Term) -> T.Term:
  match tys:
    case Nil{}:
      body
    case Con{h, t}:
      T.TPi{h, Rec.pis(t, body)}

# Lift every binder type of a telescope by `by`, each at its own depth.
def Rec.lift_tele(
  tys: List<&2, T.Term>, +by: Nat, +at: Nat
) -> List<&2, T.Term>:
  match tys:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{T.Term.lift(h, by, at), Rec.lift_tele(t, by, 1n+at)}

# Lift every term of a list by `by`. These are arguments side by side, all in
# one scope, not a telescope, so they all move by the same amount.
def Rec.lift_all(ts: List<&2, T.Term>, +by: Nat) -> List<&2, T.Term>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{T.Term.lift(h, by, 0n), Rec.lift_all(t, by)}

# The inductive applied to its parameters and indices.
#
# The innermost index is at zero and the innermost parameter at `ni + gap`,
# where `gap` counts the binders that stand between the two blocks. Inside the
# motive's own type there are none; in the recursor's telescope there are the
# motive and the minor premises.
def Rec.ind_app(
  +i0: Nat, +lvls: List<&2, L.Level>, +np: Nat, +ni: Nat, +gap: Nat
) -> T.Term:
  V.Eval.rebuild(
    List.append(&2, T.Term,
      Rec.vars(np, Nat.sub(Nat.add(Nat.add(ni, gap), np), 1n)),
      Rec.vars(ni, Nat.sub(ni, 1n))),
    T.TConst{i0, lvls})

# One field of a constructor: its type, whether it recurses, and where it
# stands among the fields.
type Field is Data:
  MkField{ty: T.Term, rec: Bool, at: Nat}

# What a field's telescope reaches, reduced.
#
# Reduced, because the arena's `reduceCtorParam` writes a recursive field as
# `constType (I a) (I a)`, where `constType` is a definition that hands back
# its first argument. Read as syntax that field is headed by `constType` and
# the inductive only occurs inside it, which looks like a nested occurrence
# and is not one.
def Rec.fres(+fuel: Nat, +env: E.DTable, +fty: T.Term) -> T.Term:
  V.Eval.whnf(
    fuel, env, T.Term.pi_skip(T.Term.pi_count(fty, 0n), fty), Nil{})

# Does this field recurse on the inductive, and does it do so plainly?
#
# Plainly means the inductive heads what the field's telescope reaches and
# appears nowhere else in the field: not in the field's own binders, and not
# in the arguments of its result. A field that mentions the inductive anywhere
# else is a nested occurrence, which this does not derive.
def Rec.field_rec(+fuel: Nat, +env: E.DTable, +i0: Nat, +fty: T.Term) -> Bool:
  Bool.and(
    V.Eval.head_is_const(V.Eval.head(Rec.fres(fuel, env, fty))),
    Nat.is_eq(
      V.Eval.head_name(V.Eval.head(Rec.fres(fuel, env, fty))),
      i0))

# Does the inductive occur where this derivation cannot put a hypothesis?
def Rec.field_nested(
  +fuel: Nat, +env: E.DTable, +i0: Nat, +fty: T.Term
) -> Bool:
  Bool.and(
    Bool.not(Rec.field_rec(fuel, env, i0, fty)),
    T.Term.occurs(fty, i0))

def Rec.field_args_clean(
  +fuel: Nat, +env: E.DTable, +i0: Nat, +fty: T.Term
) -> Bool:
  Bool.and(
    Bool.not(
      T.Term.occurs_any(
        Rec.tele(T.Term.pi_count(fty, 0n), fty), i0)),
    Bool.not(
      T.Term.occurs_any(
        V.Eval.spine(Rec.fres(fuel, env, fty), Nil{}), i0)))

# The fields of a constructor, tagged.
def Rec.fields(
  tys: List<&2, T.Term>, +fuel: Nat, +env: E.DTable, +i0: Nat, +at: Nat
) -> List<&2, Field>:
  match tys:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Con{
        MkField{h, Rec.field_rec(fuel, env, i0, h), at},
        Rec.fields(t, fuel, env, i0, 1n+at)}

# Can every field be handled? A nested occurrence cannot, and neither can a
# recursive field that mentions the inductive in its own binders or in the
# arguments of its result.
def Rec.fields_ok(
  fs: List<&2, Field>, +fuel: Nat, +env: E.DTable, +i0: Nat
) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{MkField{+fty, r, at}, t}:
      Bool.and(
        Bool.and(
          Bool.not(Rec.field_nested(fuel, env, i0, fty)),
          Rec.field_args_clean(fuel, env, i0, fty)),
        Rec.fields_ok(t, fuel, env, i0))

# How many fields recurse?
def Rec.count_rec(fs: List<&2, Field>, +acc: Nat) -> Nat:
  match fs:
    case Nil{}:
      acc
    case Con{MkField{fty, True{}, at}, t}:
      Rec.count_rec(t, 1n+acc)
    case Con{MkField{fty, False{}, at}, t}:
      Rec.count_rec(t, acc)

# The hypothesis for one recursive field.
#
#   Pi x.., motive b.. (f_i x..)
#
# written where `nf` fields and `k` hypotheses already stand, inside the minor
# premise of the `j`-th constructor.
#
# Two offsets, and they are not the same. The field's type was written before
# its own binder was bound, so the binders between there and here are the
# fields from this one on and the hypotheses already placed: `nf - i + k`.
# The field's own variable is bound, so it stands at `nf - 1 - i + k`. The two
# differ by one, and nothing that has no indices shows it: a field type with
# no parameter in it does not care how far it is lifted.
def Rec.ih(
  +fuel: Nat, +env: E.DTable, +fty: T.Term, +i: Nat, +nf: Nat, +k: Nat,
  +j: Nat, +np: Nat
) -> T.Term:
  +up : Nat = Nat.add(Nat.sub(nf, i), k)
  +var : Nat = Nat.add(Nat.sub(Nat.sub(nf, 1n), i), k)
  +lf : T.Term = T.Term.lift(fty, up, 0n)
  +nx : Nat = T.Term.pi_count(lf, 0n)
  Rec.pis(
    Rec.tele(nx, lf),
    V.Eval.rebuild(
      List.append(&2, T.Term,
        V.Eval.drop(
          V.Eval.spine(Rec.fres(fuel, env, lf), Nil{}), np),
        [V.Eval.rebuild(
          Rec.vars(nx, Nat.sub(nx, 1n)),
          T.TVar{Nat.add(nx, var)})]),
      T.TVar{Nat.add(Nat.add(Nat.add(nx, nf), k), j)}))

# The hypotheses of one minor premise, in field order.
def Rec.ihs(
  fs: List<&2, Field>, +fuel: Nat, +env: E.DTable, +nf: Nat, +k: Nat,
  +j: Nat, +np: Nat
) -> List<&2, T.Term>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{MkField{+fty, True{}, +at}, t}:
      Con{
        Rec.ih(fuel, env, fty, at, nf, k, j, np),
        Rec.ihs(t, fuel, env, nf, 1n+k, j, np)}
    case Con{MkField{fty, False{}, at}, t}:
      Rec.ihs(t, fuel, env, nf, k, j, np)

# The minor premise for the `j`-th constructor.
def Rec.minor(
  +fuel: Nat, +env: E.DTable, +cn: Nat, +i0: Nat,
  +lvls: List<&2, L.Level>, +nl: Nat, +by: Nat, +np: Nat, +j: Nat
) -> T.Term:
  +c : E.Decl = E.Lookup.get(E.Env.find(env, cn))
  +nf : Nat = E.Decl.ctor_nf(c)
  +body : T.Term = T.Term.lift(
    T.Term.pi_skip(
      np,
      T.Term.subst_levels(
        E.Decl.ctor_ty(c), Rec.lvl_shift(nl, by, 0n))),
    1n+j, 0n)
  +ftys : List<&2, T.Term> = Rec.tele(nf, body)
  +fs : List<&2, Field> = Rec.fields(Rec.tele(nf, body), fuel, env, i0, 0n)
  +nih : Nat = Rec.count_rec(
    Rec.fields(Rec.tele(nf, body), fuel, env, i0, 0n), 0n)
  Rec.pis(
    ftys,
    Rec.pis(
      Rec.ihs(fs, fuel, env, nf, 0n, j, np),
      V.Eval.rebuild(
        List.append(&2, T.Term,
          Rec.lift_all(
            V.Eval.drop(
              V.Eval.spine(T.Term.pi_skip(nf, body), Nil{}), np),
            nih),
          [V.Eval.rebuild(
            List.append(&2, T.Term,
              Rec.vars(
                np,
                Nat.add(Nat.add(Nat.add(nf, nih), j), np)),
              Rec.vars(nf, Nat.sub(Nat.add(nf, nih), 1n))),
            T.TConst{cn, lvls})]),
        T.TVar{Nat.add(Nat.add(nf, nih), j)})))

# Every minor premise, in constructor order.
def Rec.minors(
  cs: List<&2, Nat>, +fuel: Nat, +env: E.DTable, +i0: Nat,
  +lvls: List<&2, L.Level>, +nl: Nat, +by: Nat, +np: Nat, +j: Nat
) -> List<&2, T.Term>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Con{
        Rec.minor(fuel, env, h, i0, lvls, nl, by, np, j),
        Rec.minors(t, fuel, env, i0, lvls, nl, by, np, 1n+j)}

# Can every constructor of this block be handled?
def Rec.ctors_ok(
  cs: List<&2, Nat>, +fuel: Nat, +env: E.DTable, +i0: Nat, +np: Nat
) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+h, t}:
      Bool.and(
        Rec.fields_ok(
          Rec.fields(
            Rec.tele(
              E.Decl.ctor_nf(E.Lookup.get(E.Env.find(env, h))),
              T.Term.pi_skip(
                np,
                E.Decl.ctor_ty(E.Lookup.get(E.Env.find(env, h))))),
            fuel, env, i0, 0n),
          fuel, env, i0),
        Rec.ctors_ok(t, fuel, env, i0, np))

# The recursor type, given that the shape is one this can derive.
def Rec.build(
  +fuel: Nat, +env: E.DTable, +ind: E.Decl, +i0: Nat,
  +nl: Nat, +by: Nat, +mv: L.Level
) -> T.Term:
  +lvls : List<&2, L.Level> = Rec.lvl_shift(nl, by, 0n)
  +np : Nat = E.Decl.ind_np(ind)
  +ni : Nat = E.Decl.ind_ni(ind)
  +nm : Nat = V.Eval.len(
    Rec.minors(
      E.Decl.ind_ctors(ind), fuel, env, i0, lvls, nl, by, np, 0n),
    0n)
  +ity : T.Term = T.Term.subst_levels(
    E.Decl.ind_ty(ind), Rec.lvl_shift(nl, by, 0n))
  Rec.pis(
    Rec.tele(np, ity),
    T.TPi{
      Rec.pis(
        Rec.tele(ni, T.Term.pi_skip(np, ity)),
        T.TPi{Rec.ind_app(i0, lvls, np, ni, 0n), T.TSort{mv}}),
      Rec.pis(
        Rec.minors(
          E.Decl.ind_ctors(ind), fuel, env, i0, lvls, nl, by, np, 0n),
        Rec.pis(
          Rec.lift_tele(
            Rec.tele(ni, T.Term.pi_skip(np, ity)), 1n+nm, 0n),
          T.TPi{
            Rec.ind_app(i0, lvls, np, ni, 1n+nm),
            V.Eval.rebuild(
              List.append(&2, T.Term,
                Rec.vars(ni, ni),
                [T.TVar{0n}]),
              T.TVar{Nat.add(Nat.add(ni, nm), 1n)})}))})

# Is this a block the derivation can handle?
def Rec.shape_ok(
  +fuel: Nat, +env: E.DTable, +r: E.Decl, +ind: E.Decl, +i0: Nat, +by: Nat
) -> Bool:
  Bool.and(
    Bool.and(
      Bool.and(
        E.Decl.is_ind(ind),
        E.Decl.is_one(E.Decl.rec_inds(r))),
      Bool.and(
        Nat.is_eq(E.Decl.rec_nm(r), 1n),
        Nat.is_lt(by, 2n))),
    Bool.and(
      Bool.and(
        Nat.is_eq(E.Decl.rec_np(r), E.Decl.ind_np(ind)),
        Nat.is_eq(E.Decl.rec_ni(r), E.Decl.ind_ni(ind))),
      Rec.ctors_ok(
        E.Decl.ind_ctors(ind), fuel, env, i0, E.Decl.ind_np(ind))))

# The motive's sort. A recursor with one level parameter more than its
# inductive has it in front, and the motive is at that level. One with the
# same number eliminates into `Prop` only.
def Rec.motive_level(+by: Nat) -> L.Level:
  match by:
    case 0n:
      L.LZero{}
    case 1n+k:
      L.LPar{0n}

def Rec.pick(ok: Bool, t: T.Term) -> T.Term:
  match ok:
    case True{}:
      t
    case False{}:
      T.TUnk{}

# The type this recursor would have if the file told the truth about it, or
# `T.TUnk` when the shape is not one this derives.
def Rec.derive(+fuel: Nat, +env: E.DTable, +r: E.Decl) -> T.Term:
  +i0 : Nat = E.Decl.only(E.Decl.rec_inds(r))
  +ind : E.Decl = E.Lookup.get(E.Env.find(env, i0))
  +nl : Nat = List.length(&2, Nat, E.Decl.params(ind))
  +by : Nat = Nat.sub(
    List.length(&2, Nat, E.Decl.params(r)),
    List.length(&2, Nat, E.Decl.params(ind)))
  Rec.pick(
    Rec.shape_ok(fuel, env, r, ind, i0, by),
    Rec.build(fuel, env, ind, i0, nl, by, Rec.motive_level(by)))

# The rules
# ---------
#
# A recursor's type says what it proves and its rules say what it computes, so
# a file that states an honest type and a dishonest rule is as dangerous as
# one that states neither. The rule for `C_j` is
#
#   Lam p.., Lam motive, Lam minor_0..minor_{m-1}, Lam f_0..f_{nf-1},
#     minor_j f.. (one recursive call per recursive field)
#
# and the call for a recursive field `f_i : Pi x.., I p.. b..` is
#
#   Lam x.., I.rec p.. motive minors.. b.. (f_i x..)
#
# The binder types matter, because conversion compares them, so they are the
# same telescope the type is built from.

# A lambda telescope over a body, from binder types given outermost first.
def Rec.lams(tys: List<&2, T.Term>, body: T.Term) -> T.Term:
  match tys:
    case Nil{}:
      body
    case Con{h, t}:
      T.TLam{h, Rec.lams(t, body)}

# The `j`-th constructor's name.
def Rec.ctor_at(cs: List<&2, Nat>, +j: Nat) -> Nat:
  match cs:
    case Nil{}:
      0n
    case Con{+h, t}:
      match j:
        case 0n:
          h
        case 1n+k:
          Rec.ctor_at(t, k)

# The recursive call the rule hands to the minor premise for one field. The
# rule binds no hypotheses, so the only lift is over the fields from this one
# on.
def Rec.call(
  +fuel: Nat, +env: E.DTable, +fty: T.Term, +i: Nat, +nf: Nat, +np: Nat,
  +m: Nat, +rid: Nat, +rlvls: List<&2, L.Level>
) -> T.Term:
  +up : Nat = Nat.sub(nf, i)
  +var : Nat = Nat.sub(Nat.sub(nf, 1n), i)
  +lf : T.Term = T.Term.lift(fty, up, 0n)
  +nx : Nat = T.Term.pi_count(lf, 0n)
  +base : Nat = Nat.add(Nat.add(nx, nf), m)
  Rec.lams(
    Rec.tele(nx, lf),
    V.Eval.rebuild(
      List.append(&2, T.Term,
        List.append(&2, T.Term,
          List.append(&2, T.Term,
            Rec.vars(np, Nat.add(base, np)),
            [T.TVar{base}]),
          Rec.vars(m, Nat.sub(base, 1n))),
        List.append(&2, T.Term,
          V.Eval.drop(
            V.Eval.spine(Rec.fres(fuel, env, lf), Nil{}), np),
          [V.Eval.rebuild(
            Rec.vars(nx, Nat.sub(nx, 1n)),
            T.TVar{Nat.add(nx, var)})])),
      T.TConst{rid, rlvls}))

# One call per recursive field, in field order.
def Rec.calls(
  fs: List<&2, Field>, +fuel: Nat, +env: E.DTable, +nf: Nat, +np: Nat,
  +m: Nat, +rid: Nat, +rlvls: List<&2, L.Level>
) -> List<&2, T.Term>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{MkField{+fty, True{}, +at}, t}:
      Con{
        Rec.call(fuel, env, fty, at, nf, np, m, rid, rlvls),
        Rec.calls(t, fuel, env, nf, np, m, rid, rlvls)}
    case Con{MkField{fty, False{}, at}, t}:
      Rec.calls(t, fuel, env, nf, np, m, rid, rlvls)

# The right side of the rule for the `j`-th constructor, given a shape this
# derives.
def Rec.rhs_build(
  +fuel: Nat, +env: E.DTable, +ind: E.Decl, +i0: Nat, +rid: Nat,
  +nl: Nat, +by: Nat, +mv: L.Level, +j: Nat
) -> T.Term:
  +lvls : List<&2, L.Level> = Rec.lvl_shift(nl, by, 0n)
  +rlvls : List<&2, L.Level> = Rec.lvl_shift(Nat.add(nl, by), 0n, 0n)
  +np : Nat = E.Decl.ind_np(ind)
  +ni : Nat = E.Decl.ind_ni(ind)
  +m : Nat = List.length(&2, Nat, E.Decl.ind_ctors(ind))
  +cn : Nat = Rec.ctor_at(E.Decl.ind_ctors(ind), j)
  +nf : Nat = E.Decl.ctor_nf(E.Lookup.get(E.Env.find(env, cn)))
  +ity : T.Term = T.Term.subst_levels(
    E.Decl.ind_ty(ind), Rec.lvl_shift(nl, by, 0n))
  +body : T.Term = T.Term.lift(
    T.Term.pi_skip(
      np,
      T.Term.subst_levels(
        E.Decl.ctor_ty(E.Lookup.get(E.Env.find(env, cn))),
        Rec.lvl_shift(nl, by, 0n))),
    1n+m, 0n)
  +fs : List<&2, Field> = Rec.fields(
    Rec.tele(nf, body), fuel, env, i0, 0n)
  Rec.lams(
    Rec.tele(np, ity),
    T.TLam{
      Rec.pis(
        Rec.tele(ni, T.Term.pi_skip(np, ity)),
        T.TPi{Rec.ind_app(i0, lvls, np, ni, 0n), T.TSort{mv}}),
      Rec.lams(
        Rec.minors(
          E.Decl.ind_ctors(ind), fuel, env, i0, lvls, nl, by, np, 0n),
        Rec.lams(
          Rec.tele(nf, body),
          V.Eval.rebuild(
            List.append(&2, T.Term,
              Rec.vars(nf, Nat.sub(nf, 1n)),
              Rec.calls(fs, fuel, env, nf, np, m, rid, rlvls)),
            T.TVar{Nat.add(nf, Nat.sub(Nat.sub(m, 1n), j))})))})

# The right side the `j`-th rule would have if the file told the truth about
# it, or `T.TUnk` when the shape is not one this derives.
def Rec.rhs_at(+fuel: Nat, +env: E.DTable, +r: E.Decl, +j: Nat) -> T.Term:
  +i0 : Nat = E.Decl.only(E.Decl.rec_inds(r))
  +ind : E.Decl = E.Lookup.get(E.Env.find(env, i0))
  +nl : Nat = List.length(&2, Nat, E.Decl.params(ind))
  +by : Nat = Nat.sub(
    List.length(&2, Nat, E.Decl.params(r)),
    List.length(&2, Nat, E.Decl.params(ind)))
  Rec.pick(
    Rec.shape_ok(fuel, env, r, ind, i0, by),
    Rec.rhs_build(
      fuel, env, ind, i0, E.Decl.id(r), nl, by, Rec.motive_level(by), j))

# How many rules should there be, and how many fields should each name?
def Rec.rule_fields_ok(
  cs: List<&2, Nat>, +env: E.DTable, +rules: List<&2, E.RecRule>
) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+h, t}:
      Bool.and(
        Nat.is_eq(
          E.RecRule.nfields(
            V.Eval.rule_get(E.Decl.rule_for(rules, h))),
          E.Decl.ctor_nf(E.Lookup.get(E.Env.find(env, h)))),
        Rec.rule_fields_ok(t, env, rules))

# The right side the file states for the `j`-th constructor.
def Rec.stated_rhs(+env: E.DTable, +r: E.Decl, +j: Nat) -> T.Term:
  E.RecRule.rhs(
    V.Eval.rule_get(
      E.Decl.rule_for(
        E.Decl.rec_rules(r),
        Rec.ctor_at(
          E.Decl.ind_ctors(
            E.Lookup.get(
              E.Env.find(env, E.Decl.only(E.Decl.rec_inds(r))))),
          j))))
