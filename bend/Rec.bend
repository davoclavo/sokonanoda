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

# A nested block
# --------------
#
# `Lean.Syntax` declares one type and states three recursors, each with
# three motives and seven minor premises. `Syntax.node` holds an
# `Array Syntax`, and `Array` holds a `List`, so Lean eliminates `Syntax`,
# `Array Syntax` and `List Syntax` together: three motives, and the minors
# of all three types' constructors in that order.
#
# Nothing of that is in the export beyond the count. The types after the
# first are found here, by walking the fields of the constructors already
# in the list and taking every inductive application that mentions one of
# them. The order is the order of the walk, and it is Lean's: the field of
# `Syntax.node` gives `Array Syntax`, and the field of `Array.mk` at that
# instance gives `List Syntax`.
#
# A derivation that cannot see the shape hands back the unknown term, as
# everything here does, so a gap costs an acceptance and never an answer.

# What a field's telescope reaches, with the pis stripped.
def Rec.fld_res(+fty: T.Term) -> T.Term:
  T.Term.pi_skip(T.Term.pi_count(fty, 0n), fty)

# Is this term an inductive applied to arguments?
def Rec.is_ind_app(+env: E.DTable, +t: T.Term) -> Bool:
  Bool.and(
    V.Eval.head_is_const(V.Eval.head(t)),
    E.Decl.is_ind(
      E.Lookup.get(
        E.Env.find(env, V.Eval.head_name(V.Eval.head(t))))))

# Does this term mention the head of any type of the list?
def Rec.mentions_any(ts: List<&2, T.Term>, +t: T.Term) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case Con{+h, r}:
      Bool.or(
        T.Term.occurs(t, V.Eval.head_name(V.Eval.head(h))),
        Rec.mentions_any(r, t))

# Are these two types the same inductive applied to the same arguments?
# They are built here and in the export from the same declarations, so
# syntax is enough.
def Rec.ty_fuel() -> Nat:
  400n

def Rec.same_ty(+a: T.Term, +b: T.Term) -> Bool:
  T.Term.eq(Rec.ty_fuel(), a, b)

def Rec.has_ty(ts: List<&2, T.Term>, +t: T.Term) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case Con{+h, r}:
      Bool.or(Rec.same_ty(h, t), Rec.has_ty(r, t))

# Which type of the list is this, counted from the front, or the length of
# the list when it is none of them.
#
# The whole list is walked whichever way the test goes, because a pick runs
# both of its branches. The list has as many entries as the block has
# motives, which is three for the one nested block of the corpus, so the
# walk costs nothing and the shape stays a fold.
def Rec.pick_nat(b: Bool, +x: Nat, +y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

def Rec.which_go(ts: List<&2, T.Term>, +t: T.Term, +at: Nat) -> Nat:
  match ts:
    case Nil{}:
      at
    case Con{+h, r}:
      Rec.pick_nat(
        Rec.same_ty(h, t), at, Rec.which_go(r, t, 1n+at))

def Rec.which_ty(ts: List<&2, T.Term>, +t: T.Term) -> Nat:
  Rec.which_go(ts, t, 0n)

# A constructor's type with the inductive's parameters given, which for a
# type of the list means the arguments that type is applied to.
def Rec.inst_args(
  args: List<&2, T.Term>, +ex: T.ETable, ty: T.Term
) -> T.Term:
  match args:
    case Nil{}:
      ty
    case Con{+a, r}:
      Rec.inst_args(r, ex, T.Term.inst_at(ex, T.Term.pi_body(ty), a))

# The field types of one constructor at those arguments.
#
# The levels of the type travel in as well. `Array.mk` is stated with
# `Array`'s own level parameter, and the occurrence the walk found is
# `Array Syntax` at a level the file wrote, so the parameter has to be
# replaced or the type the walk builds is not the type the file states.
def Rec.ctor_fields(
  +fuel: Nat, +env: E.DTable, +cn: Nat, +args: List<&2, T.Term>,
  +lvls: List<&2, L.Level>
) -> List<&2, T.Term>:
  Rec.tele(
    E.Decl.ctor_nf(E.Lookup.get(E.Env.find(env, cn))),
    Rec.inst_args(
      args, E.Env.tab(env),
      T.Term.subst_levels(
        E.Decl.ctor_ty(E.Lookup.get(E.Env.find(env, cn))), lvls)))

# Every field type of every constructor of this type.
def Rec.ty_fields(
  cs: List<&2, Nat>, +fuel: Nat, +env: E.DTable, +args: List<&2, T.Term>,
  +lvls: List<&2, L.Level>
) -> List<&2, T.Term>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      List.append(&2, T.Term,
        Rec.ctor_fields(fuel, env, h, args, lvls),
        Rec.ty_fields(t, fuel, env, args, lvls))

def Rec.ty_all_fields(
  +fuel: Nat, +env: E.DTable, +t: T.Term
) -> List<&2, T.Term>:
  Rec.ty_fields(
    E.Decl.ind_ctors(
      E.Lookup.get(
        E.Env.find(env, V.Eval.head_name(V.Eval.head(t))))),
    fuel, env, V.Eval.spine(t, Nil{}),
    V.Eval.head_levels(V.Eval.head(t)))

# Is this field's result a type the block must eliminate as well? It must be
# an inductive applied to arguments, it must mention a type of the list, and
# it must not be one of them already.
def Rec.is_new_ty(
  +fuel: Nat, +env: E.DTable, +ts: List<&2, T.Term>, +t: T.Term
) -> Bool:
  Bool.and(
    Bool.and(
      Rec.is_ind_app(env, t), Bool.not(Rec.has_ty(ts, t))),
    Rec.mentions_any(ts, t))

def Rec.keep_ty(
  ok: Bool, +t: T.Term, rest: List<&2, T.Term>
) -> List<&2, T.Term>:
  match ok:
    case True{}:
      Con{t, rest}
    case False{}:
      rest

# The new types among a list of field types.
def Rec.new_tys(
  fs: List<&2, T.Term>, +fuel: Nat, +env: E.DTable, +ts: List<&2, T.Term>
) -> List<&2, T.Term>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{+h, r}:
      Rec.keep_ty(
        Rec.is_new_ty(fuel, env, ts, Rec.fld_res(h)),
        Rec.fld_res(h),
        Rec.new_tys(r, fuel, env, ts))

# One pass: every type of the list, scanned for new ones.
def Rec.grow_go(
  todo: List<&2, T.Term>, +fuel: Nat, +env: E.DTable,
  +ts: List<&2, T.Term>
) -> List<&2, T.Term>:
  match todo:
    case Nil{}:
      Nil{}
    case Con{+h, r}:
      List.append(&2, T.Term,
        Rec.new_tys(Rec.ty_all_fields(fuel, env, h), fuel, env, ts),
        Rec.grow_go(r, fuel, env, ts))

# The types a nested block eliminates: the declared ones, and then the ones
# a walk of the constructors' fields reaches. `rounds` bounds the walk, and
# the number of motives is the bound the caller gives.
# The first `n` of a list of types. The walk may reach more than the block
# eliminates -- a field of `Lean.Syntax.ident` is a `List` of another type,
# which the walk meets once `List` is in the list -- and the count of
# motives is what says where to stop.
def Rec.take_tys(n: Nat, ts: List<&2, T.Term>) -> List<&2, T.Term>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      match ts:
        case Nil{}:
          Nil{}
        case Con{h, r}:
          Con{h, Rec.take_tys(k, r)}

def Rec.nest_go(
  rounds: Nat, +want: Nat, +fuel: Nat, +env: E.DTable,
  +ts: List<&2, T.Term>
) -> List<&2, T.Term>:
  match rounds:
    case 0n:
      ts
    case 1n+k:
      Rec.nest_go(
        k, want, fuel, env,
        Rec.take_tys(
          want,
          List.append(&2, T.Term, ts, Rec.grow_go(ts, fuel, env, ts))))

def Rec.nest_types(
  +rounds: Nat, +fuel: Nat, +env: E.DTable, +ts: List<&2, T.Term>
) -> List<&2, T.Term>:
  Rec.nest_go(rounds, rounds, fuel, env, ts)

# One constructor of a nested block: its name, which type of the list it
# belongs to, and the arguments and levels that type is applied at.
type NCtor is Data:
  MkNC{
    cn: Nat, j: Nat, args: List<&2, T.Term>, lvls: List<&2, L.Level>}

def Rec.nc_name(c: NCtor) -> Nat:
  match c:
    case MkNC{+cn, j, args, lvls}:
      cn

def Rec.nc_ty(c: NCtor) -> Nat:
  match c:
    case MkNC{cn, +j, args, lvls}:
      j

def Rec.nc_args(c: NCtor) -> List<&2, T.Term>:
  match c:
    case MkNC{cn, j, +args, lvls}:
      args

def Rec.nc_lvls(c: NCtor) -> List<&2, L.Level>:
  match c:
    case MkNC{cn, j, args, +lvls}:
      lvls

def Rec.nc_list(
  cs: List<&2, Nat>, +j: Nat, +args: List<&2, T.Term>,
  +lvls: List<&2, L.Level>
) -> List<&2, NCtor>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Con{MkNC{h, j, args, lvls}, Rec.nc_list(t, j, args, lvls)}

# Every constructor of the block, in the order the minor premises stand:
# the first type's, then the second's, and so on.
def Rec.nest_ctors(
  ts: List<&2, T.Term>, +env: E.DTable, +j: Nat
) -> List<&2, NCtor>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+h, r}:
      List.append(&2, NCtor,
        Rec.nc_list(
          E.Decl.ind_ctors(
            E.Lookup.get(
              E.Env.find(env, V.Eval.head_name(V.Eval.head(h))))),
          j, V.Eval.spine(h, Nil{}),
          V.Eval.head_levels(V.Eval.head(h))),
        Rec.nest_ctors(r, env, 1n+j))

# The variable of the `j`-th motive, seen from `d` binders below the motive
# block. The first motive is the outermost of the `k`, so the `j`-th stands
# `k - 1 - j` further out than the last one.
def Rec.mvar(+d: Nat, +k: Nat, +j: Nat) -> T.Term:
  T.TVar{Nat.add(d, Nat.sub(Nat.sub(k, 1n), j))}

# The motive types: one per type the block eliminates, each a predicate on
# that type.
def Rec.nest_motives(
  ts: List<&2, T.Term>, +mv: L.Level, +at: Nat
) -> List<&2, T.Term>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+h, r}:
      Con{
        T.TPi{T.Term.lift(h, at, 0n), T.TSort{mv}},
        Rec.nest_motives(r, mv, 1n+at)}

# A field that recurses: where it stands among the fields, and which type
# of the block it is.
type RF is Data:
  MkRF{pos: Nat, ty: Nat}

def Rec.rf_pos(r: RF) -> Nat:
  match r:
    case MkRF{+pos, ty}:
      pos

def Rec.rf_ty(r: RF) -> Nat:
  match r:
    case MkRF{pos, +ty}:
      ty

def Rec.rf_keep(
  ok: Bool, +s: Nat, +at: Nat, rest: List<&2, RF>
) -> List<&2, RF>:
  match ok:
    case True{}:
      Con{MkRF{at, s}, rest}
    case False{}:
      rest

# Which fields of a constructor recurse, in field order. Two passes rather
# than one: a test that is computed cannot be matched, and a pick runs both
# of its branches, so a one-pass version would call itself twice per field.
def Rec.rec_fields(
  fs: List<&2, T.Term>, +ts: List<&2, T.Term>, +at: Nat
) -> List<&2, RF>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{+h, r}:
      Rec.rf_keep(
        Nat.is_lt(
          Rec.which_ty(ts, Rec.fld_res(h)),
          List.length(&2, T.Term, ts)),
        Rec.which_ty(ts, Rec.fld_res(h)), at,
        Rec.rec_fields(r, ts, 1n+at))

# The hypothesis for each of them:
#
#   motive_s (f_i)
#
# where `f_i` stands under the fields and the hypotheses already placed.
def Rec.ihs_of(
  rs: List<&2, RF>, +k: Nat, +before: Nat, +nf: Nat, +nh: Nat
) -> List<&2, T.Term>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{+h, r}:
      Con{
        T.TApp{
          Rec.mvar(Nat.add(Nat.add(nf, nh), before), k, Rec.rf_ty(h)),
          T.TVar{
            Nat.add(Nat.sub(Nat.sub(nf, 1n), Rec.rf_pos(h)), nh)}},
        Rec.ihs_of(r, k, before, nf, 1n+nh)}

# The fields of a constructor, as variables: the one at `at` stands
# `nf - 1 - at` binders out, plus the hypotheses placed after them.
def Rec.nest_fields(
  n: Nat, +nf: Nat, +nh: Nat, +at: Nat
) -> List<&2, T.Term>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{
        T.TVar{Nat.add(Nat.sub(Nat.sub(nf, 1n), at), nh)},
        Rec.nest_fields(k, nf, nh, 1n+at)}

# The minor premise of one constructor of a nested block.
def Rec.nest_minor(
  +fuel: Nat, +env: E.DTable, +c: NCtor, +ts: List<&2, T.Term>, +k: Nat,
  +before: Nat
) -> T.Term:
  +ftys : List<&2, T.Term> =
    Rec.lift_all(
      Rec.ctor_fields(
        fuel, env, Rec.nc_name(c), Rec.nc_args(c), Rec.nc_lvls(c)),
      Nat.add(k, before))
  +nf : Nat = List.length(&2, T.Term, ftys)
  +rfs : List<&2, RF> = Rec.rec_fields(ftys, ts, 0n)
  +nh : Nat = List.length(&2, RF, Rec.rec_fields(ftys, ts, 0n))
  Rec.pis(
    ftys,
    Rec.pis(
      Rec.ihs_of(rfs, k, before, nf, 0n),
      T.TApp{
        Rec.mvar(Nat.add(Nat.add(nf, nh), before), k, Rec.nc_ty(c)),
        V.Eval.rebuild(
          List.append(&2, T.Term,
            Rec.lift_all(
              Rec.nc_args(c),
              Nat.add(Nat.add(Nat.add(k, before), nf), nh)),
            Rec.nest_fields(nf, nf, nh, 0n)),
          T.TConst{Rec.nc_name(c), Rec.nc_lvls(c)})}))

# Every minor premise, in order.
def Rec.nest_minors(
  cs: List<&2, NCtor>, +fuel: Nat, +env: E.DTable, +ts: List<&2, T.Term>,
  +k: Nat, +before: Nat
) -> List<&2, T.Term>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+h, r}:
      Con{
        Rec.nest_minor(fuel, env, h, ts, k, before),
        Rec.nest_minors(r, fuel, env, ts, k, 1n+before)}

# The `i`-th type of the list, or the unknown term.
def Rec.nth_ty(ts: List<&2, T.Term>, +i: Nat) -> T.Term:
  match ts:
    case Nil{}:
      T.TUnk{}
    case Con{+h, r}:
      match i:
        case 0n:
          h
        case 1n+k:
          Rec.nth_ty(r, k)

# The type of the recursor that eliminates the `i`-th type of the block.
def Rec.nest_type(
  +fuel: Nat, +env: E.DTable, +ts: List<&2, T.Term>, +i: Nat,
  +mv: L.Level
) -> T.Term:
  +k : Nat = List.length(&2, T.Term, ts)
  +ms : List<&2, T.Term> = Rec.nest_motives(ts, mv, 0n)
  +mins : List<&2, T.Term> =
    Rec.nest_minors(
      Rec.nest_ctors(ts, env, 0n), fuel, env, ts, k, 0n)
  +nmin : Nat = List.length(&2, T.Term, mins)
  Rec.pis(
    ms,
    Rec.pis(
      mins,
      T.TPi{
        T.Term.lift(Rec.nth_ty(ts, i), Nat.add(k, nmin), 0n),
        T.TApp{Rec.mvar(1n+nmin, k, i), T.TVar{0n}}}))


# The variables of a telescope already bound, outermost first: the motives,
# then the minor premises, seen from under the fields.
def Rec.var_run(n: Nat, +at: Nat) -> List<&2, T.Term>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{T.TVar{at}, Rec.var_run(k, Nat.sub(at, 1n))}

# Which type of the block a sibling recursor eliminates.
#
# Its stated type ends with the major premise, so the binder after the
# motives and the minors is the type it is about. Reading the statement is
# sound: what makes the derivation a check is the comparison, and a
# statement that lies about its own major premise fails it.
# A telescope's binders, stepped through with references resolved. A
# stated type holds a reference wherever the export shared a subterm, and
# `Term.pi_skip` reads syntax, so it stops at one.
def Rec.skip_pis(
  n: Nat, +fuel: Nat, +env: E.DTable, t: T.Term
) -> T.Term:
  match n:
    case 0n:
      V.Eval.whnf(fuel, env, V.Eval.dr(env, t), Nil{})
    case 1n+k:
      Rec.skip_pis(
        k, fuel, env,
        T.Term.pi_body(
          V.Eval.whnf(fuel, env, V.Eval.dr(env, t), Nil{})))

def Rec.sib_major(
  +fuel: Nat, +env: E.DTable, +sn: Nat, +k: Nat, +nmin: Nat
) -> T.Term:
  V.Eval.whnf(
    fuel, env,
    V.Eval.dr(
      env,
      T.Term.pi_ty(
        Rec.skip_pis(
          Nat.add(k, nmin), fuel, env,
          E.Decl.type_at(
            E.Lookup.get(E.Env.find(env, sn)),
            Rec.lvl_shift(
              List.length(&2, Nat,
                E.Decl.params(E.Lookup.get(E.Env.find(env, sn)))),
              0n, 0n))))),
    Nil{})

# The name of the recursor for the `s`-th type of the block.
#
# The parser hands the names in the order of their own suffixes -- `rec`,
# then `rec_1`, then `rec_2` -- which is the order of the types. Nothing
# rests on that order being honest: a wrong one makes the derived rule
# differ from the stated one, and the block stays trusted.
def Rec.rec_for(sibs: List<&2, Nat>, +s: Nat) -> Nat:
  match sibs:
    case Nil{}:
      0n
    case Con{+h, r}:
      match s:
        case 0n:
          h
        case 1n+k:
          Rec.rec_for(r, k)

# The recursive call for one field: the recursor of the field's own type,
# applied to every motive, every minor premise and the field.
def Rec.nest_call(
  +fuel: Nat, +env: E.DTable, +sibs: List<&2, Nat>,
  +ts: List<&2, T.Term>, +k: Nat, +nmin: Nat, +nf: Nat, +rf: RF,
  +rlvls: List<&2, L.Level>
) -> T.Term:
  V.Eval.rebuild(
    List.append(&2, T.Term,
      Rec.var_run(k, Nat.sub(Nat.add(Nat.add(nf, nmin), k), 1n)),
      List.append(&2, T.Term,
        Rec.var_run(nmin, Nat.sub(Nat.add(nf, nmin), 1n)),
        [T.TVar{Nat.sub(Nat.sub(nf, 1n), Rec.rf_pos(rf))}])),
    T.TConst{
      Rec.rec_for(sibs, Rec.rf_ty(rf)), rlvls})

def Rec.nest_calls(
  rs: List<&2, RF>, +fuel: Nat, +env: E.DTable, +sibs: List<&2, Nat>,
  +ts: List<&2, T.Term>, +k: Nat, +nmin: Nat, +nf: Nat,
  +rlvls: List<&2, L.Level>
) -> List<&2, T.Term>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{+h, r}:
      Con{
        Rec.nest_call(fuel, env, sibs, ts, k, nmin, nf, h, rlvls),
        Rec.nest_calls(r, fuel, env, sibs, ts, k, nmin, nf, rlvls)}

# The `j`-th constructor of the block, as the minors run.
def Rec.nth_nc(cs: List<&2, NCtor>, +j: Nat) -> NCtor:
  match cs:
    case Nil{}:
      MkNC{0n, 0n, Nil{}, Nil{}}
    case Con{+h, r}:
      match j:
        case 0n:
          h
        case 1n+k:
          Rec.nth_nc(r, k)

# The rule of the `j`-th constructor of a nested block:
#
#   Lam motive_1..motive_k, Lam minor_1..minor_n, Lam fields..,
#     minor_j fields.. (recursor of each recursive field's type ..)
def Rec.nest_rhs(
  +fuel: Nat, +env: E.DTable, +d: E.Decl, +ts: List<&2, T.Term>,
  +mv: L.Level, +j: Nat
) -> T.Term:
  +k : Nat = List.length(&2, T.Term, ts)
  +ms : List<&2, T.Term> = Rec.nest_motives(ts, mv, 0n)
  +mins : List<&2, T.Term> =
    Rec.nest_minors(Rec.nest_ctors(ts, env, 0n), fuel, env, ts, k, 0n)
  +nmin : Nat = List.length(&2, T.Term, mins)
  +c : NCtor = Rec.nth_nc(Rec.nest_ctors(ts, env, 0n), j)
  +ftys : List<&2, T.Term> =
    Rec.lift_all(
      Rec.ctor_fields(
        fuel, env, Rec.nc_name(c), Rec.nc_args(c), Rec.nc_lvls(c)),
      Nat.add(k, nmin))
  +nf : Nat = List.length(&2, T.Term, ftys)
  +rfs : List<&2, RF> = Rec.rec_fields(ftys, ts, 0n)
  +rlvls : List<&2, L.Level> =
    Rec.lvl_shift(List.length(&2, Nat, E.Decl.params(d)), 0n, 0n)
  Rec.lams(
    ms,
    Rec.lams(
      mins,
      Rec.lams(
        ftys,
        V.Eval.rebuild(
          List.append(&2, T.Term,
            Rec.nest_fields(nf, nf, 0n, 0n),
            Rec.nest_calls(
              rfs, fuel, env, E.Decl.rec_sibs(d), ts, k, nmin, nf,
              rlvls)),
          T.TVar{Nat.add(nf, Nat.sub(Nat.sub(nmin, 1n), j))}))))

# The whole derivation for a nested block, from the recursor alone.
#
# The declared types are the starting list, each at its own level
# parameters moved up by the levels the recursor has in front of the
# inductive's. The walk finds the rest.
def Rec.nest_starts(
  ns: List<&2, Nat>, +env: E.DTable, +by: Nat
) -> List<&2, T.Term>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{+n, t}:
      Con{
        T.TConst{
          n,
          Rec.lvl_shift(
            List.length(&2, Nat,
              E.Decl.params(E.Lookup.get(E.Env.find(env, n)))),
            by, 0n)},
        Rec.nest_starts(t, env, by)}

# How many levels the recursor has in front of the inductive's.
def Rec.nest_by(+env: E.DTable, +r: E.Decl) -> Nat:
  Nat.sub(
    List.length(&2, Nat, E.Decl.params(r)),
    List.length(&2, Nat,
      E.Decl.params(
        E.Lookup.get(
          E.Env.find(env, V.Eval.first_name(E.Decl.rec_inds(r)))))))

def Rec.nest_list(+fuel: Nat, +env: E.DTable, +r: E.Decl) -> List<&2, T.Term>:
  Rec.nest_types(
    E.Decl.rec_nm(r), fuel, env,
    Rec.nest_starts(
      E.Decl.rec_inds(r), env, Rec.nest_by(env, r)))

# Which of its block's eliminators this one is: its own place in the list
# the parser ordered.
def Rec.rec_index(sibs: List<&2, Nat>, +id: Nat, +at: Nat) -> Nat:
  match sibs:
    case Nil{}:
      at
    case Con{+h, t}:
      Rec.pick_nat(
        Nat.is_eq(h, id), at, Rec.rec_index(t, id, 1n+at))

# The type this nested recursor would have if the file told the truth.
def Rec.nest_derive(+fuel: Nat, +env: E.DTable, +r: E.Decl) -> T.Term:
  Rec.nest_type(
    fuel, env, Rec.nest_list(fuel, env, r),
    Rec.rec_index(E.Decl.rec_sibs(r), E.Decl.id(r), 0n),
    Rec.motive_level(Rec.nest_by(env, r)))

# Where a constructor stands among the block's minor premises.
def Rec.nc_index(cs: List<&2, NCtor>, +cn: Nat, +at: Nat) -> Nat:
  match cs:
    case Nil{}:
      at
    case Con{+h, t}:
      Rec.pick_nat(
        Nat.is_eq(Rec.nc_name(h), cn), at,
        Rec.nc_index(t, cn, 1n+at))

# The rule this nested recursor would have for one constructor.
def Rec.nest_rule(
  +fuel: Nat, +env: E.DTable, +r: E.Decl, +cn: Nat
) -> T.Term:
  Rec.nest_rhs(
    fuel, env, r, Rec.nest_list(fuel, env, r),
    Rec.motive_level(Rec.nest_by(env, r)),
    Rec.nc_index(
      Rec.nest_ctors(Rec.nest_list(fuel, env, r), env, 0n), cn, 0n))
