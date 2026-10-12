# Values: reduction that keeps what it has worked out.
#
# `Eval.whnf` reduces a term to a term, and a beta step substitutes, so the
# work it does is thrown away and done again. This reduces a term to a
# **value**, and a value holds what the reduction found: a lambda holds its
# body and the environment it closed over, and an environment holds values
# and not terms. A variable used twice therefore costs its value once, and
# `perf/shared-subterm` -- the depth of a tree of 2^1100 nodes, where a
# recursor rule asks for the same subtree twice -- is linear rather than
# impossible.
#
# This is normalisation by evaluation, and the reason for it rather than a
# closure in a `Term` is scope. The branch `closure` put a closure in a term
# and a heap slot under it, and the same slot was then read in two scopes
# that did not contain each other: `docs/closure-plan.md` records both of the
# wrong answers that came of it. A value is never a term until the read back
# makes it one, so it is never read in a scope it did not come from.
#
# A rigid variable carries a **level**, counted from the outside, and the
# read back turns it into an index with the depth it has reached. That is the
# one piece of arithmetic here, and it is in one place: `Val.quote`.

import Base
import ./Level.bend as L
import ./Term.bend as T
import ./Env.bend as E
import ./Eval.bend as V

# What a head that cannot reduce is.
type Head is Data:
  # A variable of the context, by level.
  HVar{lvl: Nat}
  # A constant with nothing to unfold: an axiom, an inductive type, a
  # recursor without its major premise, a constructor.
  HConst{n: Nat, ls: List<&2, L.Level>}
  # A projection whose structure did not reduce to a constructor.
  HProj{tn: Nat, idx: Nat}

type Val is Data:
  # A head applied to arguments, which is a term reduction is stuck on.
  VNe{hd: Head, sp: List<&2, Val>}
  # A lambda: the type as a value, the body as a term, and the environment
  # the body is read in.
  VLam{ty: Val, bd: T.Term, en: List<&2, Val>}
  VPi{ty: Val, bd: T.Term, en: List<&2, Val>}
  VSort{l: L.Level}
  VNat{v: Nat, nm: Nat, zr: Nat, sc: Nat}
  # Reduction gave up. Every verdict reads this as "do not know".
  VUnk{}

def Val.is_unk(v: Val) -> Bool:
  match v:
    case VUnk{}:
      True{}
    case o:
      False{}

def Val.unk_sp(sp: List<&2, Val>) -> Bool:
  match sp:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Val.is_unk(h), Val.unk_sp(t))

# The `i`-th value of the environment, innermost first.
def Val.at(i: Nat, en: List<&2, Val>) -> Val:
  match i:
    case 0n:
      match en:
        case Nil{}:
          VUnk{}
        case Con{+h, t}:
          h
    case 1n+j:
      match en:
        case Nil{}:
          VUnk{}
        case Con{h, t}:
          Val.at(j, t)

def Val.len(en: List<&2, Val>, +acc: Nat) -> Nat:
  match en:
    case Nil{}:
      acc
    case Con{h, t}:
      Val.len(t, 1n+acc)

# A variable of the context that no value was given to. Its level is the
# number of binders outside it.
def Val.rigid(+l: Nat) -> Val:
  VNe{HVar{l}, Nil{}}

def Val.sp_len(sp: List<&2, Val>, +acc: Nat) -> Nat:
  match sp:
    case Nil{}:
      acc
    case Con{h, t}:
      Val.sp_len(t, 1n+acc)

def Val.sp_nth(i: Nat, sp: List<&2, Val>) -> Val:
  match i:
    case 0n:
      match sp:
        case Nil{}:
          VUnk{}
        case Con{+h, t}:
          h
    case 1n+j:
      match sp:
        case Nil{}:
          VUnk{}
        case Con{h, t}:
          Val.sp_nth(j, t)

def Val.sp_drop(n: Nat, sp: List<&2, Val>) -> List<&2, Val>:
  match n:
    case 0n:
      sp
    case 1n+m:
      match sp:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          Val.sp_drop(m, t)

def Val.sp_take(n: Nat, sp: List<&2, Val>) -> List<&2, Val>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      match sp:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          Con{h, Val.sp_take(m, t)}

# What the evaluator is working on: a term with its environment, or a value.
#
# Both are needed in one type because a variable's value may be a lambda that
# the spine then applies, and Bend has no mutual recursion: an `apply` that
# called `eval` and an `eval` that called `apply` is two defs that call each
# other. One control type and one loop is the way around it.
type Ctrl is Data:
  CTerm{t: T.Term, en: List<&2, Val>}
  CVal{v: Val}

# Does this value's head say a rule may fire?
def Val.head_const(v: Val) -> Bool:
  match v:
    case VNe{hd, sp}:
      match hd:
        case HConst{n, ls}:
          True{}
        case o:
          False{}
    case o:
      False{}

def Val.head_name(v: Val) -> Nat:
  match v:
    case VNe{hd, sp}:
      match hd:
        case HConst{+n, ls}:
          n
        case o:
          0n
    case o:
      0n

def Val.head_levels(v: Val) -> List<&2, L.Level>:
  match v:
    case VNe{hd, sp}:
      match hd:
        case HConst{n, +ls}:
          ls
        case o:
          Nil{}
    case o:
      Nil{}

def Val.args(v: Val) -> List<&2, Val>:
  match v:
    case VNe{hd, +sp}:
      sp
    case o:
      Nil{}

# A literal read as a constructor application, the way `Eval.lit_ctor` does
# it for terms: a recursor on `Nat` needs `zero` or `succ` of something.
def Val.lit_ctor(v: Val) -> Val:
  match v:
    case VNat{+n, +nm, +zr, +sc}:
      match n:
        case 0n:
          VNe{HConst{zr, Nil{}}, Nil{}}
        case 1n+k:
          VNe{HConst{sc, Nil{}}, [VNat{k, nm, zr, sc}]}
    case o:
      o

# Which rule of a recursor the constructor at the head of the major premise
# selects, and whether there is one.
def Val.rule_of(+d: E.Decl, +mw: Val) -> E.RecRule:
  V.Eval.rule_get(
    E.Decl.rule_for(E.Decl.rec_rules(d), Val.head_name(Val.lit_ctor(mw))))

def Val.rule_ok(+d: E.Decl, +mw: Val) -> Bool:
  V.Eval.rule_ok(
    E.Decl.rule_for(E.Decl.rec_rules(d), Val.head_name(Val.lit_ctor(mw))))

def Val.rec_ready(+d: E.Decl, +sp: List<&2, Val>) -> Bool:
  Bool.and(
    E.Decl.is_rec(d),
    Nat.is_lt(V.Eval.major_idx(d), Val.sp_len(sp, 0n)))

# Choose between two values on a computed Bool. Both arms are evaluated,
# because an argument evaluates before the match picks an arm, so neither
# arm may be a reduction that must not run.
def Val.pick(b: Bool, x: Val, y: Val) -> Val:
  match b:
    case True{}:
      x
    case False{}:
      y

def Val.pick_sp(
  b: Bool, x: List<&2, Val>, y: List<&2, Val>
) -> List<&2, Val>:
  match b:
    case True{}:
      x
    case False{}:
      y

def Val.pick_c(b: Bool, x: Ctrl, y: Ctrl) -> Ctrl:
  match b:
    case True{}:
      x
    case False{}:
      y

# The value of a declaration, for a delta step.
# Structure eta on a value, which Lean calls `toCtorWhenStruct`.
#
# A structure has one constructor and no indices, so a value of that type is
# its own constructor applied to its own fields, whatever else it is. A
# recursor stuck on a variable of a structure type is therefore not stuck:
# `p` of a pair is `Prod.mk p.1 p.2`, and iota fires on that. Without it
# `good/tutorial/064_twoBoolRec` leaves the recursor standing where the
# reduction that substitutes reduces it.
def Val.proj_vals(+n: Nat, +tn: Nat, +i: Nat, +m: Val) -> List<&2, Val>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{VNe{HProj{tn, i}, [m]}, Val.proj_vals(k, tn, 1n+i, m)}

def Val.eta_ctor(
  +env: E.DTable, +ind: Nat, +di: E.Decl, +ls: List<&2, L.Level>,
  +sp: List<&2, Val>, +m: Val
) -> Val:
  +ctor : Nat = V.Eval.first_name(E.Decl.ind_ctors(di))
  VNe{
    HConst{ctor, V.Eval.tail_lv(ls)},
    List.append(&2, Val,
      Val.sp_take(E.Decl.ind_np(di), sp),
      Val.proj_vals(
        E.Decl.ctor_nf(E.Lookup.get(E.Env.find(env, ctor))),
        ind, 0n, m))}

def Val.eta_struct(
  +env: E.DTable, +d: E.Decl, +ls: List<&2, L.Level>,
  +sp: List<&2, Val>, +m: Val
) -> Val:
  +ind : Nat = V.Eval.first_name(E.Decl.rec_inds(d))
  +di : E.Decl = E.Lookup.get(E.Env.find(env, ind))
  Val.pick(
    Bool.and(
      Val.rec_ready(d, sp),
      Bool.and(
        Bool.not(Val.head_const(Val.lit_ctor(m))),
        V.Eval.is_struct(di))),
    Val.eta_ctor(env, ind, di, ls, sp, m),
    m)

def Val.can_iota(+d: E.Decl, +sp: List<&2, Val>, +mw: Val) -> Bool:
  Bool.and(
    Val.rec_ready(d, sp),
    Bool.and(Val.head_const(Val.lit_ctor(mw)), Val.rule_ok(d, mw)))

def Val.unfold(+d: E.Decl, +ls: List<&2, L.Level>) -> T.Term:
  V.Eval.val_or(E.Decl.value_at(d, ls), T.TUnk{})

# The last value of a spine.
def Val.sp_last(sp: List<&2, Val>) -> Val:
  match sp:
    case Nil{}:
      VUnk{}
    case Con{+h, t}:
      match t:
        case Nil{}:
          h
        case o:
          Val.sp_last(o)

# The arguments an iota step hands the rule.
#
# Three groups in this order, and the order is the rule's: the recursor's own
# arguments up to its minor premises, then the fields of the constructor at
# the head of the major premise, then whatever the recursor had after the
# major premise. Leaving the first group out puts the fields where the
# motive belongs, and every variable below it then reads the wrong value --
# which `bend/nfdiff.bend` shows as a bound variable replaced by a term.
def Val.iota_args(
  +env: E.DTable, +d: E.Decl, +sp: List<&2, Val>, +mw: Val
) -> List<&2, Val>:
  +cw : Val = Val.lit_ctor(mw)
  List.append(&2, Val,
    Val.sp_take(
      Nat.add(
        Nat.add(E.Decl.rec_np(d), E.Decl.rec_nm(d)),
        E.Decl.rec_nmin(d)),
      sp),
    List.append(&2, Val,
      Val.sp_take(
        E.RecRule.nfields(Val.rule_of(d, mw)),
        Val.sp_drop(
          E.Decl.ctor_np(
            E.Lookup.get(E.Env.find(env, Val.head_name(cw)))),
          Val.args(cw))),
      Val.sp_drop(1n+V.Eval.major_idx(d), sp)))

# A quotient lift or induction step: the function the quotient carries,
# applied to the value under `Quot.mk`.
def Val.quot_args(
  +d: E.Decl, +sp: List<&2, Val>, +mw: Val
) -> List<&2, Val>:
  Con{
    Val.sp_last(Val.args(mw)),
    Val.sp_drop(1n+V.Eval.quot_pos(d), sp)}

def Val.quot_fn(+d: E.Decl, +sp: List<&2, Val>) -> Val:
  Val.sp_nth(3n, sp)

def Val.quot_ready(
  +env: E.DTable, +d: E.Decl, +sp: List<&2, Val>, +mw: Val
) -> Bool:
  Bool.and(
    Nat.is_lt(V.Eval.quot_pos(d), Val.sp_len(sp, 0n)),
    Nat.is_eq(
      E.Decl.quot_kind(
        E.Lookup.get(E.Env.find(env, Val.head_name(mw)))),
      1n))

# Is this value a `Nat` literal?
def Val.is_nat(v: Val) -> Bool:
  match v:
    case VNat{n, nm, zr, sc}:
      True{}
    case o:
      False{}

def Val.nat_of(v: Val) -> Nat:
  match v:
    case VNat{+n, nm, zr, sc}:
      n
    case o:
      0n

def Val.prim_at(+d: E.Decl, +sp: List<&2, Val>) -> Bool:
  Bool.and(
    Bool.not(Nat.is_eq(E.Decl.prim_op(d), 0n)),
    Nat.is_le(2n, Val.sp_len(sp, 0n)))

def Val.prim_ready(+d: E.Decl, +sp: List<&2, Val>) -> Bool:
  Bool.and(
    Val.prim_at(d, sp),
    Bool.and(
      Val.is_nat(Val.sp_nth(0n, sp)), Val.is_nat(Val.sp_nth(1n, sp))))

# What a primitive answers: a number, or one of the two names a comparison
# answers with.
def Val.prim_val(+d: E.Decl, +sp: List<&2, Val>, +nm: Nat, +zr: Nat, +sc: Nat) -> Val:
  +x : Nat = Val.nat_of(Val.sp_nth(0n, sp))
  +y : Nat = Val.nat_of(Val.sp_nth(1n, sp))
  Val.pick(
    V.Eval.prim_cmp(E.Decl.prim_op(d)),
    VNe{
      HConst{
        V.Eval.pick_nat(
          V.Eval.prim_bool(E.Decl.prim_op(d), x, y),
          E.Decl.prim_yes(d),
          E.Decl.prim_no(d)),
        Nil{}},
      Nil{}},
    Val.pick(
      V.Eval.prim_fits(E.Decl.prim_op(d), x, y),
      VNat{V.Eval.prim_num(E.Decl.prim_op(d), x, y), nm, zr, sc},
      VUnk{}))

def Val.nat_name(v: Val) -> Nat:
  match v:
    case VNat{n, +nm, zr, sc}:
      nm
    case o:
      0n

def Val.nat_zr(v: Val) -> Nat:
  match v:
    case VNat{n, nm, +zr, sc}:
      zr
    case o:
      0n

def Val.nat_sc(v: Val) -> Nat:
  match v:
    case VNat{n, nm, zr, +sc}:
      sc
    case o:
      0n

# The next thing to work on when a constant is the control.
#
# The order is the one `Eval.whnf` uses: a primitive, then a definition, then
# iota, then a quotient, and a constant that none of them fit is stuck. Each
# of these is cheap to build, and only one of them is used.
def Val.const_next(
  +env: E.DTable, +d: E.Decl, +ls: List<&2, L.Level>,
  +sp: List<&2, Val>, +mw: Val
) -> Ctrl:
  Val.pick_c(
    E.Decl.is_def(d),
    CTerm{Val.unfold(d, ls), Nil{}},
    Val.pick_c(
      Val.can_iota(d, sp, mw),
      CTerm{
        T.Term.subst_levels(E.RecRule.rhs(Val.rule_of(d, mw)), ls), Nil{}},
      Val.pick_c(
        Val.quot_ready(env, d, sp, mw),
        CVal{Val.quot_fn(d, sp)},
        CVal{VUnk{}})))

def Val.const_sp(
  +env: E.DTable, +d: E.Decl, +sp: List<&2, Val>, +mw: Val
) -> List<&2, Val>:
  Val.pick_sp(
    E.Decl.is_def(d),
    sp,
    Val.pick_sp(
      Val.can_iota(d, sp, mw),
      Val.iota_args(env, d, sp, mw),
      Val.pick_sp(
        Val.quot_ready(env, d, sp, mw),
        Val.quot_args(d, sp, mw),
        Nil{})))

# Does any rule fit this constant?
def Val.const_fires(
  +env: E.DTable, +d: E.Decl, +sp: List<&2, Val>, +mw: Val
) -> Bool:
  Bool.or(
    E.Decl.is_def(d),
    Bool.or(
      Val.can_iota(d, sp, mw),
      Val.quot_ready(env, d, sp, mw)))

# Reduce to a value.
#
# `c` is the control: a term with its environment, or a value. `sp` holds the
# arguments already reduced, innermost first, so a lambda takes one off it
# and a head that cannot reduce keeps them.
#
# Every argument is reduced before it goes in the environment, and that is
# where the sharing comes from: an environment holds values, so a variable
# used twice costs its value once. A Lean term always terminates, so
# reducing an argument that the body throws away is work and never a loop.
def Val.go(
  +fuel: Nat, +env: E.DTable, c: Ctrl, +sp: List<&2, Val>
) -> Val:
  match fuel:
    case 0n:
      VUnk{}
    case 1n+(+f):
      match c:
        case CVal{v}:
          match v:
            case VLam{ty, bd, en}:
              match sp:
                case Nil{}:
                  VLam{ty, bd, en}
                case Con{a, rest}:
                  Val.go(f, env, CTerm{bd, Con{a, en}}, rest)
            case VNe{hd, s}:
              VNe{hd, List.append(&2, Val, s, sp)}
            case VPi{ty, bd, en}:
              VPi{ty, bd, en}
            case VSort{l}:
              VSort{l}
            case VNat{n, nm, zr, sc}:
              VNat{n, nm, zr, sc}
            case VUnk{}:
              VUnk{}
        case CTerm{+t, +en}:
          match t:
            case T.TVar{+i}:
              Val.go(f, env, CVal{Val.at(i, en)}, sp)
            case T.TSort{l}:
              Val.go(f, env, CVal{VSort{l}}, sp)
            case T.TNat{v, nm, zr, sc}:
              Val.go(f, env, CVal{VNat{v, nm, zr, sc}}, sp)
            case T.TUnk{}:
              VUnk{}
            case T.TLam{+ty, +bd}:
              Val.go(
                f, env,
                CVal{VLam{Val.go(f, env, CTerm{ty, en}, Nil{}), bd, en}}, sp)
            case T.TPi{+ty, +bd}:
              Val.go(
                f, env,
                CVal{VPi{Val.go(f, env, CTerm{ty, en}, Nil{}), bd, en}}, sp)
            case T.TApp{+g, +a}:
              Val.go(
                f, env, CTerm{g, en},
                Con{Val.go(f, env, CTerm{a, en}, Nil{}), sp})
            case T.TLet{+ty, +v, +bd}:
              Val.go(
                f, env,
                CTerm{bd, Con{Val.go(f, env, CTerm{v, en}, Nil{}), en}}, sp)
            case T.TRef{+i, +k, m}:
              # A reference stands for a term of the export's table, whose
              # variables belong to the place it is named from -- which is
              # here, so the environment carries over.
              Val.go(f, env, CTerm{E.Env.expr_at(env, i, k), en}, sp)
            case T.TProj{+tn, +idx, +st}:
              +sv : Val = Val.go(f, env, CTerm{st, en}, Nil{})
              +cw : Val = Val.lit_ctor(sv)
              Val.go(
                f, env,
                Val.pick_c(
                  Bool.and(
                    E.Decl.is_ctor(
                      E.Lookup.get(E.Env.find(env, Val.head_name(cw)))),
                    Nat.is_lt(
                      Nat.add(
                        E.Decl.ctor_np(
                          E.Lookup.get(
                            E.Env.find(env, Val.head_name(cw)))),
                        idx),
                      Val.sp_len(Val.args(cw), 0n))),
                  CVal{
                    Val.sp_nth(
                      Nat.add(
                        idx,
                        E.Decl.ctor_np(
                          E.Lookup.get(
                            E.Env.find(env, Val.head_name(cw))))),
                      Val.args(cw))},
                  CVal{VNe{HProj{tn, idx}, [sv]}}),
                sp)
            case T.TConst{+n, +ls}:
              +d : E.Decl = E.Lookup.get(E.Env.find(env, n))
              # the major premise of a recursor, or of a quotient, already
              # reduced: it is an argument, and arguments are values here
              +mw0 : Val =
                Val.pick(
                  Val.rec_ready(d, sp),
                  Val.sp_nth(V.Eval.major_idx(d), sp),
                  Val.pick(
                    Nat.is_lt(V.Eval.quot_pos(d), Val.sp_len(sp, 0n)),
                    Val.sp_nth(V.Eval.quot_pos(d), sp),
                    VSort{L.LZero{}}))
              # a value of a structure type is its own constructor applied
              # to its own fields, so a recursor stuck on one is not stuck
              +mw : Val = Val.eta_struct(env, d, ls, sp, mw0)
              Val.go(
                f, env,
                Val.pick_c(
                  Val.prim_ready(d, sp),
                  CVal{
                    Val.prim_val(
                      d, sp,
                      Val.nat_name(Val.sp_nth(0n, sp)),
                      Val.nat_zr(Val.sp_nth(0n, sp)),
                      Val.nat_sc(Val.sp_nth(0n, sp)))},
                  Val.pick_c(
                    Val.const_fires(env, d, sp, mw),
                    Val.const_next(env, d, ls, sp, mw),
                    CVal{VNe{HConst{n, ls}, Nil{}}})),
                Val.pick_sp(
                  Val.prim_ready(d, sp),
                  Val.sp_drop(2n, sp),
                  Val.pick_sp(
                    Val.const_fires(env, d, sp, mw),
                    Val.const_sp(env, d, sp, mw),
                    sp)))

def Val.budget() -> Nat:
  30000n

def Val.eval(+env: E.DTable, +t: T.Term) -> Val:
  Val.go(Val.budget(), env, CTerm{t, Nil{}}, Nil{})

def Val.eval_in(+fuel: Nat, +env: E.DTable, +t: T.Term) -> Val:
  Val.go(fuel, env, CTerm{t, Nil{}}, Nil{})

# What the read back is working on: a value, or a spine to apply to a term
# already built. One type again, because the walk over a spine has to quote
# each argument and Bend has no mutual recursion.
type QC is Data:
  QVal{v: Val}
  QSp{acc: T.Term, sp: List<&2, Val>}

# A level, counted from the outside, read as an index, counted from the
# inside: at depth `d` the binder of level `l` is `d - 1 - l` away. This is
# the only arithmetic of the read back, and the branch `closure` is a record
# of what happens when it is spread over more than one place.
def Val.index_of(+d: Nat, +l: Nat) -> Nat:
  Nat.sub(Nat.sub(d, l), 1n)

# Read a value back as a term of a context `d` binders deep.
def Val.quote_go(
  +fuel: Nat, +env: E.DTable, +d: Nat, c: QC
) -> T.Term:
  match fuel:
    case 0n:
      T.TUnk{}
    case 1n+(+f):
      match c:
        case QSp{+acc, sp}:
          match sp:
            case Nil{}:
              acc
            case Con{v, rest}:
              Val.quote_go(
                f, env, d,
                QSp{
                  T.TApp{acc, Val.quote_go(f, env, d, QVal{v})}, rest})
        case QVal{v}:
          match v:
            case VSort{l}:
              T.TSort{l}
            case VNat{n, nm, zr, sc}:
              T.TNat{n, nm, zr, sc}
            case VUnk{}:
              T.TUnk{}
            case VLam{+ty, +bd, +en}:
              T.TLam{
                Val.quote_go(f, env, d, QVal{ty}),
                Val.quote_go(
                  f, env, 1n+d,
                  QVal{
                    Val.go(
                      f, env, CTerm{bd, Con{Val.rigid(d), en}}, Nil{})})}
            case VPi{+ty, +bd, +en}:
              T.TPi{
                Val.quote_go(f, env, d, QVal{ty}),
                Val.quote_go(
                  f, env, 1n+d,
                  QVal{
                    Val.go(
                      f, env, CTerm{bd, Con{Val.rigid(d), en}}, Nil{})})}
            case VNe{hd, +sp}:
              match hd:
                case HVar{+l}:
                  Val.quote_go(
                    f, env, d, QSp{T.TVar{Val.index_of(d, l)}, sp})
                case HConst{+n, +ls}:
                  Val.quote_go(f, env, d, QSp{T.TConst{n, ls}, sp})
                case HProj{+tn, +idx}:
                  Val.quote_go(
                    f, env, d,
                    QSp{
                      T.TProj{
                        tn, idx,
                        Val.quote_go(
                          f, env, d, QVal{Val.sp_nth(0n, sp)})},
                      Val.sp_drop(1n, sp)})

def Val.quote(+env: E.DTable, +v: Val) -> T.Term:
  Val.quote_go(Val.budget(), env, 0n, QVal{v})

def Val.quote_at(+fuel: Nat, +env: E.DTable, +v: Val) -> T.Term:
  Val.quote_go(fuel, env, 0n, QVal{v})

# The normal form of a term, by evaluation and read back.
def Val.nf(+env: E.DTable, +t: T.Term) -> T.Term:
  Val.quote(env, Val.eval(env, t))

def Val.nf_in(+fuel: Nat, +env: E.DTable, +t: T.Term) -> T.Term:
  Val.quote_at(fuel, env, Val.eval_in(fuel, env, t))
