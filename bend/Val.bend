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
import ./Idx.bend as Ix

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
  # An argument waiting in a heap slot, not yet reduced.
  VSlot{n: Nat}
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
# A slot of the heap: an argument not yet reduced, or its value.
#
# This is call by need. An argument goes on the spine as a slot and is
# reduced where the body first reads it; the answer is written back, so a
# body that reads it twice pays once. Call by value pays for an argument the
# body throws away -- `perf/discarded-argument-match` is the file that says
# so -- and call by name pays twice for one it reads twice, which is the
# sharing this whole evaluator exists for.
type HCell is Data:
  HRaw{t: T.Term, en: List<&2, Val>}
  HDone{v: Val}

type HTab is Data:
  HTip{}
  HNode{v: Maybe<&2, HCell>, lo: HTab, hi: HTab}

type Hp is Data:
  MkHp{cells: HTab, nx: Nat}

# What reduction hands back: the value, and the heap as it stands after it.
# A Bend pair is a `Type` and may be used once; a `Data` record may be used
# twice, which both halves are.
type VR is Data:
  MkVR{v: Val, h: Hp}

def Hp.new() -> Hp:
  MkHp{HTip{}, 0n}

def HTab.or_none(m: Maybe<&2, HCell>) -> HCell:
  match m:
    case None{}:
      HDone{VUnk{}}
    case Some{v}:
      v

def HTab.at(t: HTab) -> HCell:
  match t:
    case HTip{}:
      HDone{VUnk{}}
    case HNode{v, lo, hi}:
      HTab.or_none(v)

def HTab.get(n: Nat, stop: Bool, b: Bool, t: HTab, +i: Nat) -> HCell:
  match n:
    case 0n:
      HDone{VUnk{}}
    case 1n+m:
      match stop:
        case True{}:
          HTab.at(t)
        case False{}:
          match b:
            case True{}:
              match t:
                case HTip{}:
                  HDone{VUnk{}}
                case HNode{v, lo, hi}:
                  HTab.get(
                    m, Ix.Idx.here(Ix.Idx.rest(i)),
                    Ix.Idx.low(Ix.Idx.rest(i)), lo, Ix.Idx.rest(i))
            case False{}:
              match t:
                case HTip{}:
                  HDone{VUnk{}}
                case HNode{v, lo, hi}:
                  HTab.get(
                    m, Ix.Idx.here(Ix.Idx.rest(i)),
                    Ix.Idx.low(Ix.Idx.rest(i)), hi, Ix.Idx.rest(i))

def HTab.set(
  n: Nat, stop: Bool, b: Bool, t: HTab, +i: Nat, +v: HCell
) -> HTab:
  match n:
    case 0n:
      t
    case 1n+m:
      match stop:
        case True{}:
          match t:
            case HTip{}:
              HNode{Some{v}, HTip{}, HTip{}}
            case HNode{o, lo, hi}:
              HNode{Some{v}, lo, hi}
        case False{}:
          match b:
            case True{}:
              match t:
                case HTip{}:
                  HNode{
                    None{},
                    HTab.set(
                      m, Ix.Idx.here(Ix.Idx.rest(i)),
                      Ix.Idx.low(Ix.Idx.rest(i)), HTip{}, Ix.Idx.rest(i), v),
                    HTip{}}
                case HNode{o, lo, hi}:
                  HNode{
                    o,
                    HTab.set(
                      m, Ix.Idx.here(Ix.Idx.rest(i)),
                      Ix.Idx.low(Ix.Idx.rest(i)), lo, Ix.Idx.rest(i), v),
                    hi}
            case False{}:
              match t:
                case HTip{}:
                  HNode{
                    None{},
                    HTip{},
                    HTab.set(
                      m, Ix.Idx.here(Ix.Idx.rest(i)),
                      Ix.Idx.low(Ix.Idx.rest(i)), HTip{}, Ix.Idx.rest(i), v)}
                case HNode{o, lo, hi}:
                  HNode{
                    o,
                    lo,
                    HTab.set(
                      m, Ix.Idx.here(Ix.Idx.rest(i)),
                      Ix.Idx.low(Ix.Idx.rest(i)), hi, Ix.Idx.rest(i), v)}

def Hp.cell(+h: Hp, +i: Nat) -> HCell:
  match h:
    case MkHp{+cs, nx}:
      HTab.get(
        Ix.Idx.bits(), Ix.Idx.here(Ix.Idx.path(i)),
        Ix.Idx.low(Ix.Idx.path(i)), cs, Ix.Idx.path(i))

def Hp.put(+h: Hp, +i: Nat, +v: HCell) -> Hp:
  match h:
    case MkHp{+cs, +nx}:
      MkHp{
        HTab.set(
          Ix.Idx.bits(), Ix.Idx.here(Ix.Idx.path(i)),
          Ix.Idx.low(Ix.Idx.path(i)), cs, Ix.Idx.path(i), v),
        nx}

def Hp.next(+h: Hp) -> Nat:
  match h:
    case MkHp{cs, +nx}:
      nx

# Take the next slot for an argument that has not been reduced.
def Hp.alloc(+h: Hp, +t: T.Term, +en: List<&2, Val>) -> Hp:
  match h:
    case MkHp{+cs, +nx}:
      MkHp{
        HTab.set(
          Ix.Idx.bits(), Ix.Idx.here(Ix.Idx.path(nx)),
          Ix.Idx.low(Ix.Idx.path(nx)), cs, Ix.Idx.path(nx), HRaw{t, en}),
        1n+nx}

def HCell.is_done(c: HCell) -> Bool:
  match c:
    case HRaw{t, en}:
      False{}
    case HDone{v}:
      True{}

def HCell.val(c: HCell) -> Val:
  match c:
    case HRaw{t, en}:
      VUnk{}
    case HDone{+v}:
      v

def HCell.term(c: HCell) -> T.Term:
  match c:
    case HRaw{+t, en}:
      t
    case HDone{v}:
      T.TUnk{}

def HCell.env(c: HCell) -> List<&2, Val>:
  match c:
    case HRaw{t, +en}:
      en
    case HDone{v}:
      Nil{}

def VR.val(r: VR) -> Val:
  match r:
    case MkVR{v, h}:
      v

def VR.heap(r: VR) -> Hp:
  match r:
    case MkVR{v, h}:
      h

def Hp.pick(b: Bool, x: Hp, y: Hp) -> Hp:
  match b:
    case True{}:
      x
    case False{}:
      y

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
  +env: E.DTable, +dl: Bool, +d: E.Decl, +ls: List<&2, L.Level>,
  +sp: List<&2, Val>, +mw: Val
) -> Ctrl:
  Val.pick_c(
    Bool.and(dl, E.Decl.is_def(d)),
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
  +env: E.DTable, +dl: Bool, +d: E.Decl, +sp: List<&2, Val>, +mw: Val
) -> List<&2, Val>:
  Val.pick_sp(
    Bool.and(dl, E.Decl.is_def(d)),
    sp,
    Val.pick_sp(
      Val.can_iota(d, sp, mw),
      Val.iota_args(env, d, sp, mw),
      Val.pick_sp(
        Val.quot_ready(env, d, sp, mw),
        Val.quot_args(d, sp, mw),
        Nil{})))

# Does any rule fit this constant?
#
# `dl` says whether a definition may be unfolded. Conversion wants it off at
# first: two spines with the same head are compared argument by argument,
# and unfolding before that is what makes `perf/identical-nesting` build
# twelve nested structures twice. Lean draws the same line between `whnfCore`
# and `whnf`.
def Val.const_fires(
  +env: E.DTable, +dl: Bool, +d: E.Decl, +sp: List<&2, Val>, +mw: Val
) -> Bool:
  Bool.or(
    Bool.and(dl, E.Decl.is_def(d)),
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
  +fuel: Nat, +env: E.DTable, +dl: Bool, c: Ctrl, +sp: List<&2, Val>
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
                  Val.go(f, env, dl, CTerm{bd, Con{a, en}}, rest)
            case VNe{hd, s}:
              # A neutral stays one. Going back through the constant rule
              # here looks tempting -- a definition could unfold with delta
              # on -- and it does not terminate: the answer is a neutral
              # again and the loop meets it again. Conversion asks for that
              # one step by name, with `Val.delta`.
              VNe{hd, List.append(&2, Val, s, sp)}
            case VPi{ty, bd, en}:
              VPi{ty, bd, en}
            case VSort{l}:
              VSort{l}
            case VNat{n, nm, zr, sc}:
              VNat{n, nm, zr, sc}
            case VSlot{n}:
              # Nothing takes a slot yet. The arm that reads one belongs
              # here, and it needs the heap threaded through this loop.
              VUnk{}
            case VUnk{}:
              VUnk{}
        case CTerm{+t, +en}:
          match t:
            case T.TVar{+i}:
              Val.go(f, env, dl, CVal{Val.at(i, en)}, sp)
            case T.TSort{l}:
              Val.go(f, env, dl, CVal{VSort{l}}, sp)
            case T.TNat{v, nm, zr, sc}:
              Val.go(f, env, dl, CVal{VNat{v, nm, zr, sc}}, sp)
            case T.TUnk{}:
              VUnk{}
            case T.TLam{+ty, +bd}:
              Val.go(
                f, env, dl,
                CVal{VLam{Val.go(f, env, dl, CTerm{ty, en}, Nil{}), bd, en}}, sp)
            case T.TPi{+ty, +bd}:
              Val.go(
                f, env, dl,
                CVal{VPi{Val.go(f, env, dl, CTerm{ty, en}, Nil{}), bd, en}}, sp)
            case T.TApp{+g, +a}:
              Val.go(
                f, env, dl, CTerm{g, en},
                Con{Val.go(f, env, dl, CTerm{a, en}, Nil{}), sp})
            case T.TLet{+ty, +v, +bd}:
              Val.go(
                f, env, dl,
                CTerm{bd, Con{Val.go(f, env, dl, CTerm{v, en}, Nil{}), en}}, sp)
            case T.TRef{+i, +k, m}:
              # A reference stands for a term of the export's table, whose
              # variables belong to the place it is named from -- which is
              # here, so the environment carries over.
              Val.go(f, env, dl, CTerm{E.Env.expr_at(env, i, k), en}, sp)
            case T.TProj{+tn, +idx, +st}:
              +sv : Val = Val.go(f, env, dl, CTerm{st, en}, Nil{})
              +cw : Val = Val.lit_ctor(sv)
              Val.go(
                f, env, dl,
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
                f, env, dl,
                Val.pick_c(
                  Val.prim_ready(d, sp),
                  CVal{
                    Val.prim_val(
                      d, sp,
                      Val.nat_name(Val.sp_nth(0n, sp)),
                      Val.nat_zr(Val.sp_nth(0n, sp)),
                      Val.nat_sc(Val.sp_nth(0n, sp)))},
                  Val.pick_c(
                    Val.const_fires(env, dl, d, sp, mw),
                    Val.const_next(env, dl, d, ls, sp, mw),
                    CVal{VNe{HConst{n, ls}, Nil{}}})),
                Val.pick_sp(
                  Val.prim_ready(d, sp),
                  Val.sp_drop(2n, sp),
                  Val.pick_sp(
                    Val.const_fires(env, dl, d, sp, mw),
                    Val.const_sp(env, dl, d, sp, mw),
                    sp)))

def Val.budget() -> Nat:
  30000n

# Reduce with every rule, a definition included.
def Val.eval(+env: E.DTable, +t: T.Term) -> Val:
  Val.go(Val.budget(), env, True{}, CTerm{t, Nil{}}, Nil{})

def Val.eval_in(+fuel: Nat, +env: E.DTable, +t: T.Term) -> Val:
  Val.go(fuel, env, True{}, CTerm{t, Nil{}}, Nil{})

# Reduce everything but a definition, and stop at a constant that could
# unfold. This is what conversion starts with.
def Val.core(+fuel: Nat, +env: E.DTable, +t: T.Term) -> Val:
  Val.go(fuel, env, False{}, CTerm{t, Nil{}}, Nil{})

# An environment of rigid binders, innermost first: the environment a term
# of a context `d` binders deep is read in.
#
# A term that comes back out of inference or out of a rule is written in that
# context, and reading it in an empty environment makes every one of its
# variables unknown. That is what made the K-like rule answer no and what
# made thirty-one files answer "do not know".
def Val.rigids_go(+n: Nat, +d: Nat, +acc: List<&2, Val>) -> List<&2, Val>:
  match n:
    case 0n:
      acc
    case 1n+k:
      Val.rigids_go(k, d, List.append(&2, Val, acc, [Val.rigid(k)]))

def Val.rigids(+d: Nat) -> List<&2, Val>:
  Val.rigids_go(d, d, Nil{})

# The same two, in a context.
def Val.core_in(
  +fuel: Nat, +env: E.DTable, +d: Nat, +t: T.Term
) -> Val:
  Val.go(fuel, env, False{}, CTerm{t, Val.rigids(d)}, Nil{})

def Val.eval_at(
  +fuel: Nat, +env: E.DTable, +d: Nat, +t: T.Term
) -> Val:
  Val.go(fuel, env, True{}, CTerm{t, Val.rigids(d)}, Nil{})

# Carry on reducing a value, with or without unfolding.
def Val.more(+fuel: Nat, +env: E.DTable, +dl: Bool, +v: Val) -> Val:
  Val.go(fuel, env, dl, CVal{v}, Nil{})

# What the unfolding walk is working on: a value, or a spine whose arguments
# are being unfolded one at a time.
type DC is Data:
  DV{v: Val}
  DS{hd: Head, done: List<&2, Val>, rest: List<&2, Val>}

# The head put back together with its arguments, and the constant rule given
# another chance now that the arguments have unfolded.
def Val.head_back(
  +fuel: Nat, +env: E.DTable, hd: Head, +sp: List<&2, Val>
) -> Val:
  match hd:
    case HConst{+n, +ls}:
      Val.go(fuel, env, True{}, CTerm{T.TConst{n, ls}, Nil{}}, sp)
    case o:
      VNe{o, sp}

# Unfold a neutral with every rule, arguments included.
#
# The arguments matter and that is not obvious. A primitive fires only when
# both of its arguments are literals, and in `good/other/nat-lit-ble` they
# arrive as `OfNat.ofNat 1000000 (instOfNatNat 1000000)`: a definition that
# has to unfold before the literal is there to see. Unfolding only the head
# leaves them neutral and the comparison then answers no.
def Val.dgo(+fuel: Nat, +env: E.DTable, c: DC) -> Val:
  match fuel:
    case 0n:
      VUnk{}
    case 1n+(+f):
      match c:
        case DS{+hd, +done, rest}:
          match rest:
            case Nil{}:
              Val.head_back(f, env, hd, done)
            case Con{v, more}:
              Val.dgo(
                f, env,
                DS{
                  hd,
                  List.append(&2, Val, done, [Val.dgo(f, env, DV{v})]),
                  more})
        case DV{v}:
          match v:
            case VNe{+hd, +sp}:
              Val.dgo(f, env, DS{hd, Nil{}, sp})
            case o:
              o

# The step conversion takes when the cheap route -- two spines with the same
# head, compared argument by argument -- answers no.
def Val.delta(+fuel: Nat, +env: E.DTable, +v: Val) -> Val:
  Val.dgo(fuel, env, DV{v})

# Apply a value to arguments.
def Val.app(
  +fuel: Nat, +env: E.DTable, +dl: Bool, +v: Val, +sp: List<&2, Val>
) -> Val:
  Val.go(fuel, env, dl, CVal{v}, sp)

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
            case VSlot{n}:
              T.TUnk{}
            case VUnk{}:
              T.TUnk{}
            case VLam{+ty, +bd, +en}:
              T.TLam{
                Val.quote_go(f, env, d, QVal{ty}),
                Val.quote_go(
                  f, env, 1n+d,
                  QVal{
                    Val.go(
                      f, env, True{}, CTerm{bd, Con{Val.rigid(d), en}},
                      Nil{})})}
            case VPi{+ty, +bd, +en}:
              T.TPi{
                Val.quote_go(f, env, d, QVal{ty}),
                Val.quote_go(
                  f, env, 1n+d,
                  QVal{
                    Val.go(
                      f, env, True{}, CTerm{bd, Con{Val.rigid(d), en}},
                      Nil{})})}
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

# Read a value back in a context that is already `d` binders deep. A value
# taken from inside a comparison lives there, and reading it back at zero
# gives its rigid variables the wrong indices.
def Val.quote_d(+fuel: Nat, +env: E.DTable, +d: Nat, +v: Val) -> T.Term:
  Val.quote_go(fuel, env, d, QVal{v})

# The normal form of a term, by evaluation and read back.
def Val.nf(+env: E.DTable, +t: T.Term) -> T.Term:
  Val.quote(env, Val.eval(env, t))

def Val.nf_in(+fuel: Nat, +env: E.DTable, +t: T.Term) -> T.Term:
  Val.quote_at(fuel, env, Val.eval_in(fuel, env, t))

# A binder's body, with a value given to the binder.
def Val.under(
  +fuel: Nat, +env: E.DTable, +dl: Bool, +bd: T.Term,
  +en: List<&2, Val>, +v: Val
) -> Val:
  Val.go(fuel, env, dl, CTerm{bd, Con{v, en}}, Nil{})

def Val.is_lam(v: Val) -> Bool:
  match v:
    case VLam{ty, bd, en}:
      True{}
    case o:
      False{}

def Val.is_pi(v: Val) -> Bool:
  match v:
    case VPi{ty, bd, en}:
      True{}
    case o:
      False{}

def Val.is_sort(v: Val) -> Bool:
  match v:
    case VSort{l}:
      True{}
    case o:
      False{}

def Val.sort_of(v: Val) -> L.Level:
  match v:
    case VSort{+l}:
      l
    case o:
      L.LZero{}

def Val.bind_ty(v: Val) -> Val:
  match v:
    case VLam{+ty, bd, en}:
      ty
    case VPi{+ty, bd, en}:
      ty
    case o:
      VUnk{}

def Val.bind_bd(v: Val) -> T.Term:
  match v:
    case VLam{ty, +bd, en}:
      bd
    case VPi{ty, +bd, en}:
      bd
    case o:
      T.TUnk{}

def Val.bind_en(v: Val) -> List<&2, Val>:
  match v:
    case VLam{ty, bd, +en}:
      en
    case VPi{ty, bd, +en}:
      en
    case o:
      Nil{}

# Is this value a head that a definition could still unfold?
def Val.can_delta(+env: E.DTable, v: Val) -> Bool:
  match v:
    case VNe{hd, sp}:
      match hd:
        case HConst{+n, ls}:
          E.Decl.is_def(E.Lookup.get(E.Env.find(env, n)))
        case o:
          False{}
    case o:
      False{}

# Two level lists, compared as levels and not as syntax.
#
# `max p0 p1` and `max p1 p0` are one level written two ways, and a head
# comparison that reads them as syntax answers no. That is a wrong answer:
# `perf/fueled-chain` is 869 kB and its declaration 557 turns on exactly
# this. The term conversion has always compared them with `Level.eq`.
def Val.levels_eq(
  +fuel: Nat, xs: List<&2, L.Level>, ys: List<&2, L.Level>
) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xr} Con{y, yr}:
      Bool.and(L.Level.eq(x, y), Val.levels_eq(fuel, xr, yr))
    case x y:
      False{}

def Val.same_hd(+fuel: Nat, a: Head, b: Head) -> Bool:
  match a b:
    case HVar{i} HVar{j}:
      Nat.is_eq(i, j)
    case HConst{n1, l1} HConst{n2, l2}:
      Bool.and(Nat.is_eq(n1, n2), Val.levels_eq(fuel, l1, l2))
    case HProj{t1, i1} HProj{t2, i2}:
      Bool.and(Nat.is_eq(t1, t2), Nat.is_eq(i1, i2))
    case x y:
      False{}

# Two heads that are the same constant with the same universes.
def Val.same_head(+fuel: Nat, a: Val, b: Val) -> Bool:
  match a b:
    case VNe{h1, s1} VNe{h2, s2}:
      Val.same_hd(fuel, h1, h2)
    case x y:
      False{}

def Val.is_ne(v: Val) -> Bool:
  match v:
    case VNe{hd, sp}:
      True{}
    case o:
      False{}

def Val.is_nat_v(v: Val) -> Bool:
  Val.is_nat(v)
