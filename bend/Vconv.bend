# Conversion on values.
#
# `Conv.bend` asks whether two **terms** are definitionally equal, and every
# question it asks reduces them again. This asks it of two **values**, so the
# reduction is done once and what it found is kept: that is the sharing the
# whole of `docs/closure-plan.md` is about.
#
# The shape of the walk is `Conv.eq_all`'s, and for the reasons recorded
# there: the answer travels in as a parameter so a definite no can stop
# without draining the queue and the recursive call stays in tail position;
# a pair that offers two routes puts the dear one on a stack, and a definite
# no pops the stack rather than ending the walk.
#
# The cheap route is why reduction starts without unfolding a definition.
# Two spines with the same head and the same number of arguments are equal
# when their arguments are, and that holds whatever the head unfolds to. Only
# when it fails does the walk unfold, which is the `dear` route.

import Base
import ./Level.bend as L
import ./Term.bend as T
import ./Env.bend as E
import ./Eval.bend as V
import ./Val.bend as W
import ./Shape.bend as H
import ./Conv.bend as C
import ./Ans.bend as A

# A pair still to be shown equal, at a depth: the number of binders the walk
# has gone under, which is what a rigid variable's level counts from.
# The context carries the binder types as terms, and its length is the depth
# a rigid variable's level counts from. Terms rather than values because the
# two rules that need a type -- proof irrelevance and the K-like rule -- are
# the kernel's own and read a context of terms; a value is read back at
# those two points and nowhere else.
type VPair is Data:
  VP{cx: List<&2, T.Term>, a: W.Val, b: W.Val}
  # the same pair with the cheap route spent: unfold and look again
  VDeep{cx: List<&2, T.Term>, a: W.Val, b: W.Val}

type VStep is Data:
  SNo{}
  SYes{}
  SUnk{}
  SMore{ps: List<&2, VPair>}
  SEither{cheap: List<&2, VPair>, dear: List<&2, VPair>}

type VAlt is Data:
  MkVA{acc: A.Ans, work: List<&2, VPair>}

# A step, and the heap as it stands after the work that found it.
#
# A value of a pair may hold a slot of the heap, so the heap travels with
# the queue. It only grows: a cell is written once and a number is never
# given out twice, so a pair that waited in an alternative reads the same
# slot it did when it went in. That is what makes an alternative safe to
# take up again against a later heap.
type VSH is Data:
  MkSH{s: VStep, h: W.Hp}

def Vconv.sh_step(r: VSH) -> VStep:
  match r:
    case MkSH{s, h}:
      s

def Vconv.sh_heap(r: VSH) -> W.Hp:
  match r:
    case MkSH{s, h}:
      h

def Vconv.of(b: Bool) -> VStep:
  match b:
    case True{}:
      SYes{}
    case False{}:
      SNo{}

def Vconv.step_ans(s: VStep) -> A.Ans:
  match s:
    case SNo{}:
      A.ANo{}
    case SYes{}:
      A.AYes{}
    case SUnk{}:
      A.AUnk{}
    case SMore{ps}:
      A.AYes{}
    case SEither{cheap, dear}:
      A.AYes{}

def Vconv.step_more(s: VStep) -> List<&2, VPair>:
  match s:
    case SMore{ps}:
      ps
    case SEither{cheap, dear}:
      cheap
    case o:
      Nil{}

def Vconv.step_alts(
  s: VStep, acc: A.Ans, rest: List<&2, VPair>, alts: List<&2, VAlt>
) -> List<&2, VAlt>:
  match s alts:
    case SEither{cheap, dear} Nil{}:
      [MkVA{acc, List.append(&2, VPair, dear, rest)}]
    case o as:
      as

def Vconv.out_of_fuel(acc: A.Ans, alts: List<&2, VAlt>) -> A.Ans:
  match alts:
    case Nil{}:
      A.Ans.unk_unless_no(acc)
    case Con{h, t}:
      A.AUnk{}

# Are these two values the same slot of the heap?
#
# Two arguments in one slot are one argument. The question they pose is the
# same question, and proving it once proves it for both.
def Vconv.same_slot(a: W.Val, b: W.Val) -> Bool:
  match a b:
    case W.VSlot{+i} W.VSlot{+j}:
      Nat.is_eq(i, j)
    case x y:
      False{}

def Vconv.pair_same(p: VPair, +x: W.Val, +y: W.Val) -> Bool:
  match p:
    case VP{cx, a, b}:
      Bool.and(Vconv.same_slot(a, x), Vconv.same_slot(b, y))
    case o:
      False{}

def Vconv.has_pair(
  ps: List<&2, VPair>, +x: W.Val, +y: W.Val
) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{+h, t}:
      Bool.or(Vconv.pair_same(h, x, y), Vconv.has_pair(t, x, y))

def Vconv.pairs_pick(
  b: Bool, +ps: List<&2, VPair>, +p: VPair
) -> List<&2, VPair>:
  match b:
    case True{}:
      ps
    case False{}:
      Con{p, ps}

# Are these two the same value?
#
# The comparison asks this before any rule, because two sides that are the
# same value need no rule -- and the rules are where the cost is. Lean asks
# the same question first and answers it by the address of the expression.
# There is no address here, so the walk compares the structure.
#
# A slot has to be read for the walk to see anything, and reading one needs
# the heap, so the answer carries the heap back out. Comparing two slot
# numbers across two **dropped** heaps would be unsound: the numbers start
# again in a new heap, so two different thunks can wear the same number.
#
# `ByteArray.IsValidUTF8.recOn` of `good/init-prelude` is the declaration
# that wants this. Its minor premise appears twice, once in the type the
# file states and once in the type its recursor gives, and the two are the
# same value. Without this they go to the dear route, which opens
# `List.utf8Encode`, then `String.utf8EncodeChar`, and then the `Nat.div`
# and `Nat.mod` those hold: the file does not answer in ninety seconds, and
# it answers in a fifth of a second when any link of that chain is an
# axiom.
type VPr is Data:
  MkVPr{a: W.Val, b: W.Val}

# The answer, and the heap the reading left behind.
type VSame is Data:
  MkVS{ok: Bool, h: W.Hp}

def Vconv.vs_ok(r: VSame) -> Bool:
  match r:
    case MkVS{ok, h}:
      ok

def Vconv.vs_heap(r: VSame) -> W.Hp:
  match r:
    case MkVS{ok, h}:
      h

# What the walk is doing: reading the slots of one pair, comparing a pair
# whose slots are read, or stopping. The decision travels in the control
# because a match reads a parameter and not a computed value, and Bend has
# no mutual recursion to put the decision in a helper.
type SC is Data:
  SForce{a: W.Val, b: W.Val, rest: List<&2, VPr>}
  SCmp{a: W.Val, b: W.Val, rest: List<&2, VPr>}
  SBad{}
  # Every pair has been compared. This is a constructor of its own and not
  # a pair of unknown values: two sides that reduction gave up on are not
  # known to be the same, and reading them as the same was two wrong
  # accepts.
  SDone{}

def Vconv.same_cap() -> Nat:
  48n

def Vconv.pair_up(
  xs: List<&2, W.Val>, ys: List<&2, W.Val>, +acc: List<&2, VPr>
) -> List<&2, VPr>:
  match xs ys:
    case Con{x, xr} Con{y, yr}:
      Con{MkVPr{x, y}, Vconv.pair_up(xr, yr, acc)}
    case x y:
      acc

# A cell that holds a value is read for nothing. A cell that still holds a
# term is reduced, with the budget the comparison itself has.
#
# The budget is not a small one, and that is the point. A reduction that
# runs out leaves a value with the unknown value **inside** it -- a neutral
# whose spine holds one -- and the answer goes back into the cell, where
# every later reader takes it for the whole truth. A budget of eight steps
# made `good/init-prelude` answer `reject` in 1.8 s for exactly that
# reason. With the comparison's own budget a reduction that does not finish
# means the comparison has not finished either.
def Vconv.force_if(
  slot: Bool, +fuel: Nat, +env: E.DTable, +hp: W.Hp, +v: W.Val
) -> W.VR:
  match slot:
    case True{}:
      W.Val.more_h(fuel, env, False{}, hp, v)
    case False{}:
      W.MkVR{v, hp}

def Vconv.read_slot(
  +fuel: Nat, +env: E.DTable, +hp: W.Hp, +v: W.Val
) -> W.VR:
  Vconv.force_if(
    W.Val.is_slot(W.Hp.read_done(hp, v)), fuel, env, hp,
    W.Hp.read_done(hp, v))

# The next pair, or the empty pair that answers yes.
def Vconv.same_next(work: List<&2, VPr>) -> SC:
  match work:
    case Nil{}:
      SDone{}
    case Con{MkVPr{+a, +b}, +rest}:
      SForce{a, b, rest}

def Vconv.same_cont(ok: Bool, +rest: List<&2, VPr>) -> SC:
  match ok:
    case True{}:
      Vconv.same_next(rest)
    case False{}:
      SBad{}

def Vconv.same_go(
  +fuel: Nat, +env: E.DTable, +hp: W.Hp, c: SC
) -> VSame:
  match fuel:
    case 0n:
      MkVS{False{}, hp}
    case 1n+(+f):
      match c:
        case SBad{}:
          MkVS{False{}, hp}
        case SDone{}:
          MkVS{True{}, hp}
        case SForce{+a, +b, +rest}:
          +ra : W.VR = Vconv.read_slot(fuel, env, hp, a)
          +rb : W.VR = Vconv.read_slot(fuel, env, W.VR.heap(ra), b)
          Vconv.same_go(
            f, env, W.VR.heap(rb),
            SCmp{W.VR.val(ra), W.VR.val(rb), rest})
        case SCmp{a, b, +rest}:
          match a b:
            case W.VSlot{+i} W.VSlot{+j}:
              Vconv.same_go(
                f, env, hp, Vconv.same_cont(Nat.is_eq(i, j), rest))
            case W.VNat{v1, m1, z1, s1} W.VNat{v2, m2, z2, s2}:
              Vconv.same_go(
                f, env, hp, Vconv.same_cont(Nat.is_eq(v1, v2), rest))
            case W.VSort{x} W.VSort{y}:
              Vconv.same_go(
                f, env, hp,
                Vconv.same_cont(L.Level.same(x, y), rest))
            case W.VNe{h1, +s1} W.VNe{h2, +s2}:
              Vconv.same_go(
                f, env, hp,
                Vconv.same_cont(
                  Bool.and(
                    W.Val.same_hd(f, h1, h2),
                    Nat.is_eq(
                      W.Val.sp_len(s1, 0n), W.Val.sp_len(s2, 0n))),
                  Vconv.pair_up(s1, s2, rest)))
            case W.VLam{+t1, +b1, +e1} W.VLam{+t2, +b2, +e2}:
              Vconv.same_go(
                f, env, hp,
                Vconv.same_cont(
                  C.Conv.same_in(Vconv.same_cap(), env, b1, b2),
                  Con{MkVPr{t1, t2}, Vconv.pair_up(e1, e2, rest)}))
            case W.VPi{+t1, +b1, +e1} W.VPi{+t2, +b2, +e2}:
              Vconv.same_go(
                f, env, hp,
                Vconv.same_cont(
                  C.Conv.same_in(Vconv.same_cap(), env, b1, b2),
                  Con{MkVPr{t1, t2}, Vconv.pair_up(e1, e2, rest)}))
            case x y:
              MkVS{False{}, hp}

def Vconv.same_val(
  +fuel: Nat, +env: E.DTable, +hp: W.Hp, +a: W.Val, +b: W.Val
) -> VSame:
  Vconv.same_go(Vconv.same_cap(), env, hp, SForce{a, b, Nil{}})

# Two values that reduction gave up on are not the same value.

# One pair per argument, at the same depth, and a pair that is already in
# the list only once.
#
# `perf/repeated-subproblem` is built out of this. It compares `Tr.node u u`
# against `Tr.node v v` at every level, where both argument positions hold
# the same slot, so the pairs double at each level: the comparison meets
# `2^n` of them where `n` are distinct.
def Vconv.zip(
  +cx: List<&2, T.Term>, xs: List<&2, W.Val>, ys: List<&2, W.Val>
) -> List<&2, VPair>:
  match xs ys:
    case Con{+x, xr} Con{+y, yr}:
      +rest : List<&2, VPair> = Vconv.zip(cx, xr, yr)
      Vconv.pairs_pick(
        Vconv.has_pair(rest, x, y), rest, VP{cx, x, y})
    case x y:
      Nil{}

# How many binders the walk is inside, which is where a rigid variable's
# level is counted from.
def Vconv.depth(cx: List<&2, T.Term>, +acc: Nat) -> Nat:
  match cx:
    case Nil{}:
      acc
    case Con{h, t}:
      Vconv.depth(t, 1n+acc)

def Vconv.pick_step(b: Bool, x: VStep, y: VStep) -> VStep:
  match b:
    case True{}:
      x
    case False{}:
      y

# Both branches of a pick run, here as everywhere. The one that is not
# taken is thrown away whole, slots and all, so the slots it took are never
# read and the heap of the branch that wins is the one that goes on.
def Vconv.pick_sh(b: Bool, x: VSH, y: VSH) -> VSH:
  match b:
    case True{}:
      x
    case False{}:
      y

# Could a step unfold the head of this value?
#
# A projection counts when its subject could unfold. The projection of a
# constructor application is one of its fields, so unfolding the subject is
# what makes the projection reduce -- and reducing it is the cheap answer.
# Comparing the two subjects instead is what `perf/proj-lazy-struct` is
# about: there each subject holds a hundred thousand steps of work and the
# two fields the question is about are both zero.
def Vconv.proj_hd(hd: W.Head, +sp: List<&2, W.Val>) -> Bool:
  match hd:
    case W.HProj{tn, idx}:
      W.Val.head_const(W.Val.sp_nth(0n, sp))
    case o:
      False{}

def Vconv.can_unfold(v: W.Val) -> Bool:
  match v:
    case W.VNe{+hd, +sp}:
      Bool.or(W.Val.head_const(W.VNe{hd, sp}), Vconv.proj_hd(hd, sp))
    case o:
      False{}

# Offer the cheap route when the two sides are the same head applied to the
# same number of arguments, and keep the dear one for a no.
#

# Do these two spines have the same head and the same length, with at least
# one argument? That is the cheap route.
def Vconv.spine_match(+fuel: Nat, +a: W.Val, +b: W.Val) -> Bool:
  Bool.and(
    W.Val.same_head(fuel, a, b),
    Bool.and(
      Nat.is_eq(
        W.Val.sp_len(W.Val.args(a), 0n), W.Val.sp_len(W.Val.args(b), 0n)),
      Nat.is_lt(0n, W.Val.sp_len(W.Val.args(a), 0n))))

def Vconv.ne_step(
  +fuel: Nat, +cx: List<&2, T.Term>, ok: Bool, s1: List<&2, W.Val>, s2: List<&2, W.Val>
) -> VStep:
  match ok:
    case True{}:
      SMore{Vconv.zip(cx, s1, s2)}
    case False{}:
      SNo{}

# Proof irrelevance: two proofs of one proposition are equal.
#

# Could this value be a proof? A sort, a pi or a lambda is not one, and
# neither is a literal.
def Vconv.maybe_proof(v: W.Val) -> Bool:
  match v:
    case W.VSort{l}:
      False{}
    case W.VPi{ty, bd, en}:
      False{}
    case W.VNat{n, nm, zr, sc}:
      False{}
    case W.VUnk{}:
      False{}
    case o:
      True{}

# Two values whose heads cannot reduce further, compared as they stand.
def Vconv.rigid(
  +fuel: Nat, +env: E.DTable, +hp: W.Hp, +cx: List<&2, T.Term>, a: W.Val,
  b: W.Val
) -> VSH:
  match a b:
    case W.VSort{x} W.VSort{y}:
      MkSH{Vconv.of(L.Level.eq(x, y)), hp}
    case W.VNat{v1, m1, z1, s1} W.VNat{v2, m2, z2, s2}:
      MkSH{Vconv.of(Nat.is_eq(v1, v2)), hp}
    case W.VUnk{} y:
      MkSH{SUnk{}, hp}
    case x W.VUnk{}:
      MkSH{SUnk{}, hp}
    case W.VLam{+t1, b1, e1} W.VLam{t2, b2, e2}:
      +r1 : W.VR =
        W.Val.under_h(
          fuel, env, False{}, hp, b1, e1,
          W.Val.rigid(Vconv.depth(cx, 0n)))
      +r2 : W.VR =
        W.Val.under_h(
          fuel, env, False{}, W.VR.heap(r1), b2, e2,
          W.Val.rigid(Vconv.depth(cx, 0n)))
      MkSH{
        SMore{
          [VP{
            Con{
              W.Val.quote_d_h(
                fuel, env, W.VR.heap(r2), Vconv.depth(cx, 0n), t1),
              cx},
            W.VR.val(r1), W.VR.val(r2)}]},
        W.VR.heap(r2)}
    case W.VPi{+t1, b1, e1} W.VPi{t2, b2, e2}:
      +r1 : W.VR =
        W.Val.under_h(
          fuel, env, False{}, hp, b1, e1,
          W.Val.rigid(Vconv.depth(cx, 0n)))
      +r2 : W.VR =
        W.Val.under_h(
          fuel, env, False{}, W.VR.heap(r1), b2, e2,
          W.Val.rigid(Vconv.depth(cx, 0n)))
      MkSH{
        SMore{
          [VP{cx, t1, t2},
           VP{
             Con{
               W.Val.quote_d_h(
                 fuel, env, W.VR.heap(r2), Vconv.depth(cx, 0n), t1),
               cx},
             W.VR.val(r1), W.VR.val(r2)}]},
        W.VR.heap(r2)}
    # eta: a lambda against anything else is the body against that thing
    # applied to the binder
    case W.VLam{+t1, b1, e1} y:
      +r1 : W.VR =
        W.Val.under_h(
          fuel, env, False{}, hp, b1, e1,
          W.Val.rigid(Vconv.depth(cx, 0n)))
      +r2 : W.VR =
        W.Val.app_h(
          fuel, env, False{}, W.VR.heap(r1), y,
          [W.Val.rigid(Vconv.depth(cx, 0n))])
      MkSH{
        SMore{
          [VP{
            Con{
              W.Val.quote_d_h(
                fuel, env, W.VR.heap(r2), Vconv.depth(cx, 0n), t1),
              cx},
            W.VR.val(r1), W.VR.val(r2)}]},
        W.VR.heap(r2)}
    case x W.VLam{+t2, b2, e2}:
      +r1 : W.VR =
        W.Val.app_h(
          fuel, env, False{}, hp, x,
          [W.Val.rigid(Vconv.depth(cx, 0n))])
      +r2 : W.VR =
        W.Val.under_h(
          fuel, env, False{}, W.VR.heap(r1), b2, e2,
          W.Val.rigid(Vconv.depth(cx, 0n)))
      MkSH{
        SMore{
          [VP{
            Con{
              W.Val.quote_d_h(
                fuel, env, W.VR.heap(r2), Vconv.depth(cx, 0n), t2),
              cx},
            W.VR.val(r1), W.VR.val(r2)}]},
        W.VR.heap(r2)}
    # a literal against a constructor application
    case W.VNat{v1, m1, z1, s1} y:
      MkSH{SMore{[VDeep{cx, W.Val.lit_ctor(W.VNat{v1, m1, z1, s1}), y}]}, hp}
    case x W.VNat{v2, m2, z2, s2}:
      MkSH{SMore{[VDeep{cx, x, W.Val.lit_ctor(W.VNat{v2, m2, z2, s2})}]}, hp}
    case W.VNe{h1, +s1} W.VNe{h2, +s2}:
      MkSH{
        Vconv.ne_step(
          fuel, cx,
          Bool.and(
            W.Val.same_hd(fuel, h1, h2),
            Nat.is_eq(
              W.Val.sp_len(s1, 0n), W.Val.sp_len(s2, 0n))),
          s1, s2),
        hp}
    case x y:
      MkSH{SNo{}, hp}

def Vconv.ctor_of_struct(+env: E.DTable, +d: E.Decl) -> Bool:
  Bool.and(
    E.Decl.is_ctor(d),
    V.Eval.is_struct(
      E.Lookup.get(E.Env.find(env, E.Decl.ctor_ind(d)))))

# A constructor application of a structure against something that is not one
# is still a question worth asking: the other side **is** its own
# constructor applied to its own fields. `tutorial/112_structEta` is the file
# that says so. The evaluator has this rule for a recursor whose major
# premise is stuck; a comparison needs it too, and the two are not the same
# place.
def Vconv.ctor_struct(+env: E.DTable, +v: W.Val) -> Bool:
  Bool.and(
    W.Val.head_const(v),
    Vconv.ctor_of_struct(
      env, E.Lookup.get(E.Env.find(env, W.Val.head_name(v)))))

# The other side, as that constructor applied to its own fields.
def Vconv.eta_as(
  +env: E.DTable, +ctor: W.Val, +other: W.Val
) -> W.Val:
  +d : E.Decl = E.Lookup.get(E.Env.find(env, W.Val.head_name(ctor)))
  W.VNe{
    W.HConst{W.Val.head_name(ctor), W.Val.head_levels(ctor)},
    List.append(&2, W.Val,
      W.Val.sp_take(E.Decl.ctor_np(d), W.Val.args(ctor)),
      W.Val.proj_vals(
        E.Decl.ctor_nf(d), E.Decl.ctor_ind(d), 0n, other))}

# Is the other side one this rule may expand? A lambda, a sort or a pi is
# not a structure value, and a constructor application needs no expanding.
def Vconv.eta_target(+env: E.DTable, +v: W.Val) -> Bool:
  Bool.and(
    W.Val.is_ne(v), Bool.not(Vconv.ctor_struct(env, v)))

def Vconv.eta_struct(
  +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>, +a: W.Val, +b: W.Val
) -> VStep:
  Vconv.pick_step(
    Bool.and(Vconv.ctor_struct(env, a), Vconv.eta_target(env, b)),
    SMore{[VP{cx, a, Vconv.eta_as(env, a, b)}]},
    Vconv.pick_step(
      Bool.and(Vconv.ctor_struct(env, b), Vconv.eta_target(env, a)),
      SMore{[VP{cx, Vconv.eta_as(env, b, a), b}]},
      SNo{}))

# Structure first, proof irrelevance only on a no.
#

def Vconv.eta_or(
  st: VStep, +fuel: Nat, +env: E.DTable, +hp: W.Hp,
  +cx: List<&2, T.Term>, +a: W.Val, +b: W.Val
) -> VSH:
  match st:
    case SNo{}:
      MkSH{Vconv.eta_struct(fuel, env, cx, a, b), hp}
    case o:
      MkSH{o, hp}

# The rule needs the type of each side, inference reads a term, and reading
# a value back costs the size of the value. Asking it of every pair spent
# the budget: at the kernel's own fuel of 30000, nine files answered "do not
# know" that used to answer. Asking it only where the structural comparison
# has already failed costs nothing on the pairs that agree, which is nearly
# all of them.
# Proof irrelevance first, then structure, then structure eta.
#
# The order is the kernel's own and it is not only about cost. Two proofs of
# one proposition are equal **whatever their arguments are**, so a
# comparison that comes first and compares the arguments answers no where
# irrelevance would have answered yes: that is
# `tutorial/107_proofIrrelevanceUnderBinder`.
#

# Structure, and structure eta on a no.
def Vconv.struct_then(
  +fuel: Nat, +env: E.DTable, +hp: W.Hp, +cx: List<&2, T.Term>, +a: W.Val,
  +b: W.Val
) -> VSH:
  +r : VSH = Vconv.rigid(fuel, env, hp, cx, a, b)
  Vconv.eta_or(
    Vconv.sh_step(r), fuel, env, Vconv.sh_heap(r), cx, a, b)

# The test is the kernel's own, `Conv.irrel`, and it needs the type of each
# side. That is where a value is read back -- here and in the K-like rule,
# and nowhere else -- because inference reads a term in a context of terms.
# It costs the size of the two sides, and it is asked only where both sides
# could be proofs at all.
def Vconv.irrel_ok(
  +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>, +a: T.Term, +b: T.Term
) -> Bool:
  +ra = H.Shape.infer(fuel, env, cx, a)
  +rb = H.Shape.infer(fuel, env, cx, b)
  Bool.and(
    Bool.and(H.Shape.ok(ra), H.Shape.ok(rb)),
    Bool.or(
      H.Shape.prop_sort(fuel, env, cx, H.Shape.ty(ra)),
      C.Conv.is_unit(
        env, V.Eval.whnf(fuel, env, H.Shape.ty(ra), Nil{}))))

# The type each side has, for the pair the rule leaves behind.
def Vconv.ty_of(
  +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>, +t: T.Term
) -> T.Term:
  H.Shape.ty(H.Shape.infer(fuel, env, cx, t))

# Proof irrelevance does not answer yes on its own: two proofs are equal
# when they prove **the same** proposition, so the rule leaves the two types
# behind as a pair. Answering yes without that is a wrong accept, and
# `bad/tutorial/105_proofIrrelevanceBad` is the file that says so.
# The two terms arrive read back, and their types are inferred here and not
# before. The rule fires on few pairs, and inference is the dearest thing a
# comparison does: asking for both types where the test says no paid for
# two inferences that nothing read.
# What the rule may spend on reading a side back.
#
# The test reads both sides back and infers a type for each, and both cost
# the size of the side. Lean asks the rule of every pair and can afford to,
# because its inference is remembered; nothing here remembers one. So the
# read back gets a small budget of its own: a side that does not fit leaves
# `TUnk` behind, inference fails on that, and the rule does not fire.
#
# `perf/church-numerals` is the file that sets this. Its two sides are
# normal forms of fourteen thousand applications that agree, and asking the
# rule of every pair of them cost forty-five seconds against a tenth of a
# second for the comparison alone.
def Vconv.quote_cap() -> Nat:
  80n

# The rule in earnest, with the kernel's own budget and no structural route
# to fall back on.
#
# This is what a no is worth asking. The small budget above answers most
# pairs for almost nothing, and the pairs it cuts off are answered here --
# but only the ones where everything else has already said no, and a no
# ends the comparison. `bad/perf/rec-missing-ih` is the file that needs it:
# its sides do not fit the small budget, and leaving the pair as "do not
# know" turned a correct rejection into a decline.
def Vconv.irrel_full_step(
  ok: Bool, +fuel: Nat, +env: E.DTable, +hp: W.Hp,
  +cx: List<&2, T.Term>, +qa: T.Term, +qb: T.Term
) -> VSH:
  match ok:
    case False{}:
      MkSH{SNo{}, hp}
    case True{}:
      +r1 : W.VR =
        W.Val.core_in_h(
          fuel, env, hp, Vconv.depth(cx, 0n),
          Vconv.ty_of(fuel, env, cx, qa))
      +r2 : W.VR =
        W.Val.core_in_h(
          fuel, env, W.VR.heap(r1), Vconv.depth(cx, 0n),
          Vconv.ty_of(fuel, env, cx, qb))
      MkSH{
        SMore{[VP{cx, W.VR.val(r1), W.VR.val(r2)}]}, W.VR.heap(r2)}

def Vconv.irrel_full(
  +fuel: Nat, +env: E.DTable, +hp: W.Hp, +cx: List<&2, T.Term>, +a: W.Val,
  +b: W.Val
) -> VSH:
  +qa : T.Term = W.Val.quote_d_h(fuel, env, hp, Vconv.depth(cx, 0n), a)
  +qb : T.Term = W.Val.quote_d_h(fuel, env, hp, Vconv.depth(cx, 0n), b)
  Vconv.irrel_full_step(
    Vconv.irrel_ok(fuel, env, cx, qa, qb), fuel, env, hp, cx, qa, qb)

# A no that rests on a side which was cut off is not a no yet. The rule gets
# its full budget before the pair is given up on.
def Vconv.cut_no(
  st: VStep, +fuel: Nat, +env: E.DTable, +hp: W.Hp,
  +cx: List<&2, T.Term>, +a: W.Val, +b: W.Val
) -> VSH:
  match st:
    case SNo{}:
      Vconv.irrel_full(fuel, env, hp, cx, a, b)
    case o:
      MkSH{o, hp}

def Vconv.struct_maybe(
  cut: Bool, +fuel: Nat, +env: E.DTable, +hp: W.Hp,
  +cx: List<&2, T.Term>, +a: W.Val, +b: W.Val
) -> VSH:
  match cut:
    case False{}:
      Vconv.struct_then(fuel, env, hp, cx, a, b)
    case True{}:
      +r : VSH = Vconv.struct_then(fuel, env, hp, cx, a, b)
      Vconv.cut_no(
        Vconv.sh_step(r), fuel, env, Vconv.sh_heap(r), cx, a, b)

def Vconv.irrel_step(
  ok: Bool, +fuel: Nat, +env: E.DTable, +hp: W.Hp,
  +cx: List<&2, T.Term>, +a: W.Val, +b: W.Val, +qa: T.Term, +qb: T.Term
) -> VSH:
  match ok:
    case True{}:
      +r1 : W.VR =
        W.Val.core_in_h(
          fuel, env, hp, Vconv.depth(cx, 0n),
          Vconv.ty_of(fuel, env, cx, qa))
      +r2 : W.VR =
        W.Val.core_in_h(
          fuel, env, W.VR.heap(r1), Vconv.depth(cx, 0n),
          Vconv.ty_of(fuel, env, cx, qb))
      MkSH{
        SMore{[VP{cx, W.VR.val(r1), W.VR.val(r2)}]}, W.VR.heap(r2)}
    case False{}:
      Vconv.struct_maybe(
        Bool.or(
          T.Term.any_unk(Vconv.quote_cap(), qa),
          T.Term.any_unk(Vconv.quote_cap(), qb)),
        fuel, env, hp, cx, a, b)

def Vconv.irrel_go(
  +fuel: Nat, +env: E.DTable, +hp: W.Hp, +cx: List<&2, T.Term>, +a: W.Val,
  +b: W.Val
) -> VSH:
  # Reading a value back hands back a term, not a value, so no slot leaves
  # the heap here and the two readings can start from the same one.
  +qa : T.Term =
    W.Val.quote_d_h(
      Vconv.quote_cap(), env, hp, Vconv.depth(cx, 0n), a)
  +qb : T.Term =
    W.Val.quote_d_h(
      Vconv.quote_cap(), env, hp, Vconv.depth(cx, 0n), b)
  Vconv.irrel_step(
    Vconv.irrel_ok(fuel, env, cx, qa, qb),
    fuel, env, hp, cx, a, b, qa, qb)

def Vconv.irrel_pick(
  maybe: Bool, +fuel: Nat, +env: E.DTable, +hp: W.Hp,
  +cx: List<&2, T.Term>, +a: W.Val, +b: W.Val
) -> VSH:
  match maybe:
    case True{}:
      Vconv.irrel_go(fuel, env, hp, cx, a, b)
    case False{}:
      Vconv.struct_then(fuel, env, hp, cx, a, b)

# Where neither route is the cheap one and a head could still unfold, the
# answer is not "no": it is "unfold and look again". Saying no there is what
# made `perf/church-numerals` reject, since `CNat` and its unfolding are the
# same type and only a delta step shows it.
# The K-like rule, on a value.
#

# It costs. The rule needs the type of each side, inference reads a term,
# and reading a value back costs the size of the value, which is why nine
# files answer "do not know" at the kernel's own budget. Inference on values
# is what makes this order affordable, and it is the next piece of work.
def Vconv.irrel(
  +fuel: Nat, +env: E.DTable, +hp: W.Hp, +cx: List<&2, T.Term>, +a: W.Val,
  +b: W.Val
) -> VSH:
  Vconv.irrel_pick(
    Bool.and(Vconv.maybe_proof(a), Vconv.maybe_proof(b)),
    fuel, env, hp, cx, a, b)

# A recursor whose inductive is a proposition with one constructor and no
# fields -- `Eq` is the one that matters -- may take any proof of its major
# premise as that constructor, because proof irrelevance makes every proof
# equal. The conditions are the kernel's own and all of them are needed:
# `Conv.k_ok` also checks that the subject's type is an application of that
# inductive and that its arguments fit, and firing without those is a wrong
# accept rather than a missing one.
def Vconv.k_sp(
  +sp: List<&2, W.Val>, +i: Nat, +v: W.Val
) -> List<&2, W.Val>:
  List.append(&2, W.Val,
    W.Val.sp_take(i, sp),
    Con{v, W.Val.sp_drop(1n+i, sp)})

def Vconv.k_rec(
  +env: E.DTable, +d: E.Decl, +sp: List<&2, W.Val>
) -> Bool:
  Bool.and(
    Bool.and(
      E.Decl.is_rec(d),
      Nat.is_lt(V.Eval.major_idx(d), W.Val.sp_len(sp, 0n))),
    C.Conv.k_single(env, d))

def Vconv.k_near(+env: E.DTable, +v: W.Val) -> Bool:
  Bool.and(
    W.Val.head_const(v),
    Vconv.k_rec(
      env, E.Lookup.get(E.Env.find(env, W.Val.head_name(v))),
      W.Val.args(v)))

# Put the constructor in the major premise's place and reduce again.
def Vconv.k_use(
  +fuel: Nat, +env: E.DTable, +hp: W.Hp, +cx: List<&2, T.Term>, +v: W.Val,
  +d: E.Decl, +ty: T.Term
) -> W.VR:
  # `Val.head_back` and not `Val.app`: applying a neutral only lengthens its
  # spine, and the point of the rule is that the constant rule runs again
  # with the constructor in the major premise's place. Without that the
  # recursor comes back unreduced, which is what
  # `good/tutorial/099_ruleK` answered `reject` on.
  +r : W.VR =
    W.Val.core_in_h(
      fuel, env, hp, Vconv.depth(cx, 0n), C.Conv.k_ctor(env, d, ty))
  W.Val.head_back_h(
    fuel, env, W.VR.heap(r),
    W.HConst{W.Val.head_name(v), W.Val.head_levels(v)},
    Vconv.k_sp(W.Val.args(v), V.Eval.major_idx(d), W.VR.val(r)))

def Vconv.k_pick(
  ok: Bool, +fuel: Nat, +env: E.DTable, +hp: W.Hp,
  +cx: List<&2, T.Term>, +v: W.Val, +d: E.Decl, +ty: T.Term
) -> W.VR:
  match ok:
    case True{}:
      Vconv.k_use(fuel, env, hp, cx, v, d, ty)
    case False{}:
      W.MkVR{v, hp}

def Vconv.k_go(
  +fuel: Nat, +env: E.DTable, +hp: W.Hp, +cx: List<&2, T.Term>, +v: W.Val,
  +d: E.Decl
) -> W.VR:
  # The major premise is an argument, so it may still be in a slot. Reading
  # it back reduces it and hands back a term.
  +sj : W.Val = W.Val.sp_nth(V.Eval.major_idx(d), W.Val.args(v))
  +ty : T.Term =
    V.Eval.whnf(
      fuel, env,
      H.Shape.ty(
        H.Shape.infer(
          fuel, env, cx,
          W.Val.quote_d_h(fuel, env, hp, Vconv.depth(cx, 0n), sj))),
      Nil{})
  Vconv.k_pick(
    Bool.and(
      C.Conv.k_type_ok(d, ty),
      C.Conv.k_fits(fuel, env, cx, d, ty)),
    fuel, env, hp, cx, v, d, ty)

def Vconv.k_try(
  near: Bool, +fuel: Nat, +env: E.DTable, +hp: W.Hp,
  +cx: List<&2, T.Term>, +v: W.Val
) -> W.VR:
  match near:
    case True{}:
      Vconv.k_go(
        fuel, env, hp, cx, v,
        E.Lookup.get(E.Env.find(env, W.Val.head_name(v))))
    case False{}:
      W.MkVR{v, hp}

def Vconv.k_fix(
  +fuel: Nat, +env: E.DTable, +hp: W.Hp, +cx: List<&2, T.Term>, +v: W.Val
) -> W.VR:
  Vconv.k_try(Vconv.k_near(env, v), fuel, env, hp, cx, v)

# The irrelevance test, and the structural comparison when it does not fit.
# Structure eta in a comparison, which Lean calls `isDefEqEtaStruct`.
#

# One step on one side of the dear route.
#
# A stuck projection takes its own step: the head of its subject unfolds and
# the projection is tried again, and nothing else of the subject is touched.
# The general walk unfolds the subject's arguments as well, which is what
# `perf/proj-lazy-struct` is about.
def Vconv.one_delta(
  proj: Bool, +fuel: Nat, +env: E.DTable, +hp: W.Hp, +v: W.Val
) -> W.VR:
  match proj:
    case True{}:
      W.Val.proj_step_h(fuel, env, hp, v)
    case False{}:
      W.Val.delta_h(fuel, env, hp, v)

# The dear route: unfold both heads and look again.
def Vconv.deep(
  +fuel: Nat, +env: E.DTable, +hp: W.Hp, +cx: List<&2, T.Term>, +a: W.Val,
  +b: W.Val
) -> VSH:
  +d1 : W.VR =
    Vconv.one_delta(W.Val.is_stuck_proj(a), fuel, env, hp, a)
  +k1 : W.VR =
    Vconv.k_fix(fuel, env, W.VR.heap(d1), cx, W.VR.val(d1))
  +d2 : W.VR =
    Vconv.one_delta(
      W.Val.is_stuck_proj(b), fuel, env, W.VR.heap(k1), b)
  +k2 : W.VR =
    Vconv.k_fix(fuel, env, W.VR.heap(d2), cx, W.VR.val(d2))
  Vconv.irrel(
    fuel, env, W.VR.heap(k2), cx, W.VR.val(k1), W.VR.val(k2))

# Any constant head earns the dear route, not only a definition. A recursor
# stands with its rule unfired until its major premise reduces, and that may
# need a definition unfolded **inside an argument**: `Val.delta_h` does
# that, and asking only whether the head itself unfolds leaves
# `perf/magma-list-pair-n7` answering no.
#
# These three arms are three definitions and not one `pick`, and that is
# not a matter of taste. An argument reduces before a match picks an arm,
# so a `pick` over the three runs all three -- and the last one is proof
# irrelevance, which reads both values back and infers a type for each. A
# `pick` here asked that of every pair of the file, where the rule wants it
# asked of the pairs that nothing cheaper settles.
def Vconv.offer_last(
  near: Bool, +fuel: Nat, +env: E.DTable, +hp: W.Hp,
  +cx: List<&2, T.Term>, +a: W.Val, +b: W.Val
) -> VSH:
  match near:
    case True{}:
      MkSH{SMore{[VDeep{cx, a, b}]}, hp}
    case False{}:
      Vconv.irrel(fuel, env, hp, cx, a, b)

def Vconv.offer_go(
  cheap: Bool, +fuel: Nat, +env: E.DTable, +hp: W.Hp,
  +cx: List<&2, T.Term>, +a: W.Val, +b: W.Val
) -> VSH:
  match cheap:
    case True{}:
      MkSH{
        SEither{
          Vconv.zip(cx, W.Val.args(a), W.Val.args(b)),
          [VDeep{cx, a, b}]},
        hp}
    case False{}:
      Vconv.offer_last(
        Bool.or(Vconv.can_unfold(a), Vconv.can_unfold(b)),
        fuel, env, hp, cx, a, b)

def Vconv.offer(
  +fuel: Nat, +env: E.DTable, +hp: W.Hp, +cx: List<&2, T.Term>, +a: W.Val,
  +b: W.Val
) -> VSH:
  Vconv.offer_go(
    Bool.and(
      Vconv.spine_match(fuel, a, b),
      Bool.or(W.Val.head_const(a), W.Val.head_const(b))),
    fuel, env, hp, cx, a, b)

# The same value needs nothing further asked of it.
def Vconv.offer_or_same(
  same: Bool, +fuel: Nat, +env: E.DTable, +hp: W.Hp,
  +cx: List<&2, T.Term>, +a: W.Val, +b: W.Val
) -> VSH:
  match same:
    case True{}:
      MkSH{SYes{}, hp}
    case False{}:
      Vconv.offer(fuel, env, hp, cx, a, b)

# What to do with one pair.
def Vconv.classify(
  +fuel: Nat, +env: E.DTable, +hp: W.Hp, p: VPair
) -> VSH:
  match p:
    case VDeep{+cx, +a, +b}:
      Vconv.deep(fuel, env, hp, cx, a, b)
    case VP{+cx, +a, +b}:
      # the K-like rule first, as `Conv.classify_work` does it: a recursor
      # on a proposition with one constructor and no fields may take any
      # proof of its major premise as that constructor, and the cheap route
      # has to see the result
      # Both sides leave their slots here, and this is the one place that
      # has to make them. Every rule below reads a value, and a slot is
      # not one.
      +m1 : W.VR = W.Val.more_h(fuel, env, False{}, hp, a)
      +k1 : W.VR =
        Vconv.k_fix(fuel, env, W.VR.heap(m1), cx, W.VR.val(m1))
      +m2 : W.VR =
        W.Val.more_h(fuel, env, False{}, W.VR.heap(k1), b)
      +k2 : W.VR =
        Vconv.k_fix(fuel, env, W.VR.heap(m2), cx, W.VR.val(m2))
      # Two sides that are the same value need no rule, and this is where
      # that is asked. Everything the rules do is dearer than the asking.
      +sv : VSame =
        Vconv.same_val(
          fuel, env, W.VR.heap(k2), W.VR.val(k1), W.VR.val(k2))
      Vconv.offer_or_same(
        Vconv.vs_ok(sv), fuel, env, Vconv.vs_heap(sv), cx,
        W.VR.val(k1), W.VR.val(k2))

# Work the queue. It empties exactly when every pair in it is equal.
def Vconv.all(
  +fuel: Nat, +env: E.DTable, +hp: W.Hp, acc: A.Ans, alts: List<&2, VAlt>,
  work: List<&2, VPair>
) -> A.Ans:
  match fuel:
    case 0n:
      Vconv.out_of_fuel(acc, alts)
    case 1n+f:
      match acc alts work:
        case A.ANo{} Nil{} w:
          A.ANo{}
        case A.ANo{} Con{MkVA{a2, w2}, r2} w:
          Vconv.all(f, env, hp, a2, r2, w2)
        case A.AUnk{} Con{MkVA{a3, w3}, r3} w:
          # The cheap route could not answer, which is as good a reason to
          # take the alternative as a no. `perf/proj-lazy-struct` is the
          # file that needs it: comparing the two structures of
          # `(P (slow 100000)).1` and `(Q (slow 100001)).1` runs reduction
          # out of its depth inside the field the question is not about,
          # and unfolding the projection instead answers in one step.
          #
          # The alternative proves the pair that was asked, so nothing the
          # cheap route left behind is lost: its own pairs are derived from
          # that pair, and the pairs that were waiting beside it travel in
          # the alternative as well.
          Vconv.all(f, env, hp, a3, r3, w3)
        case a as Nil{}:
          a
        case +a as Con{p, +rest}:
          +r : VSH = Vconv.classify(f, env, hp, p)
          +st : VStep = Vconv.sh_step(r)
          Vconv.all(
            f, env, Vconv.sh_heap(r),
            A.Ans.and(a, Vconv.step_ans(st)),
            Vconv.step_alts(st, a, rest, as),
            List.append(&2, VPair, Vconv.step_more(st), rest))

# Where this comparison does not know, the one that substitutes is asked.
#
# The two decide the same relation, and this one is faster on nearly every
# file; where it gives up, the older one often does not. `Nat.modCoreGo_lt`
# of `good/init-prelude` is the file that says so: its proof applies a motive
# held behind a reference, and the comparison of the motive's instance with
# the type the argument has answers "do not know" here and yes there. The
# whole closure of that theorem is 152 declarations, and it declines in 7.3 s
# by this comparison and accepts in 0.2 s by that one.
#
# The fallback is a match and not a `pick`, so the comparison that
# substitutes runs only where this one has already given up. A pair that
# settles never pays for it.
def Vconv.or_terms(
  a: A.Ans, +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>, +x: T.Term,
  +y: T.Term
) -> A.Ans:
  match a:
    case A.AUnk{}:
      C.Conv.eq_in(fuel, env, cx, x, y)
    case o:
      o

# Are these two terms definitionally equal? The context tells the walk how
# many binders it starts inside, which is where a rigid variable's level
# counts from.
# What a first attempt by the comparison that substitutes may cost.
#
# The two comparisons are good at different questions. This one walks
# values and is good where the answer is a computation:
# `perf/beta-ladder`, `perf/shared-subterm`, `perf/church-numerals`. The
# one that substitutes is good where the two sides are nearly the same
# syntax, which is what a telescope comparison is -- and those are the
# files this one cannot finish. `perf/fueled-chain`'s `chain6_datF` cuts to
# 97 declarations that the term kernel accepts in 4.4 s and this one does
# not answer in sixty.
#
# So the term comparison goes first with a budget of its own. A yes or a no
# from it is an answer, because it decides the same relation; "do not know"
# costs that budget and the value comparison carries on. The budget is
# small enough that a file whose answer is a computation loses little, and
# large enough to settle a telescope.
def Vconv.try_cap() -> Nat:
  3000n

def Vconv.eq_values(
  +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>, +a: T.Term,
  +b: T.Term
) -> A.Ans:
  # The two terms are written in the context, so they are read in an
  # environment of its rigid binders. Reading them in an empty one makes
  # every free variable unknown, and the kernel -- which asks this with a
  # context, unlike the gate -- then answers "do not know" at once.
  # One heap for the two sides and for everything the queue does with
  # them. It starts here and it is dropped when the answer comes out, and
  # no value outlives it.
  +r1 : W.VR =
    W.Val.core_in_h(fuel, env, W.Hp.new(), Vconv.depth(cx, 0n), a)
  +r2 : W.VR =
    W.Val.core_in_h(fuel, env, W.VR.heap(r1), Vconv.depth(cx, 0n), b)
  Vconv.or_terms(
    Vconv.all(
      fuel, env, W.VR.heap(r2), A.AYes{}, Nil{},
      [VP{cx, W.VR.val(r1), W.VR.val(r2)}]),
    fuel, env, cx, a, b)

def Vconv.after_try(
  t: A.Ans, +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>,
  +a: T.Term, +b: T.Term
) -> A.Ans:
  match t:
    case A.AUnk{}:
      Vconv.eq_values(fuel, env, cx, a, b)
    case o:
      o

def Vconv.eq_in(
  +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>, +a: T.Term, +b: T.Term
) -> A.Ans:
  Vconv.after_try(
    C.Conv.eq_in(Vconv.try_cap(), env, cx, a, b), fuel, env, cx, a, b)

# Conversion, unless the question is already settled. The left answer
# arrives as a parameter so a definite no returns without the work, which is
# why `Conv.eq_unless_no` exists and the same reason holds here.
def Vconv.eq_unless_no(
  a: A.Ans, +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>,
  +x: T.Term, +y: T.Term
) -> A.Ans:
  match a:
    case A.ANo{}:
      A.ANo{}
    case o:
      A.Ans.and(o, Vconv.eq_in(fuel, env, cx, x, y))

# Are these two closed terms definitionally equal?
def Vconv.eq(
  +fuel: Nat, +env: E.DTable, +a: T.Term, +b: T.Term
) -> A.Ans:
  Vconv.eq_in(fuel, env, Nil{}, a, b)
