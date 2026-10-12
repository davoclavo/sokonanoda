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

# One pair per argument, at the same depth.
def Vconv.zip(
  +cx: List<&2, T.Term>, xs: List<&2, W.Val>, ys: List<&2, W.Val>
) -> List<&2, VPair>:
  match xs ys:
    case Con{x, xr} Con{y, yr}:
      Con{VP{cx, x, y}, Vconv.zip(cx, xr, yr)}
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
  +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>, a: W.Val, b: W.Val
) -> VStep:
  match a b:
    case W.VSort{x} W.VSort{y}:
      Vconv.of(L.Level.eq(x, y))
    case W.VNat{v1, m1, z1, s1} W.VNat{v2, m2, z2, s2}:
      Vconv.of(Nat.is_eq(v1, v2))
    case W.VUnk{} y:
      SUnk{}
    case x W.VUnk{}:
      SUnk{}
    case W.VLam{+t1, b1, e1} W.VLam{t2, b2, e2}:
      SMore{
        [VP{
          Con{W.Val.quote_d(fuel, env, Vconv.depth(cx, 0n), t1), cx},
          W.Val.under(
            fuel, env, False{}, b1, e1,
            W.Val.rigid(Vconv.depth(cx, 0n))),
          W.Val.under(
            fuel, env, False{}, b2, e2,
            W.Val.rigid(Vconv.depth(cx, 0n)))}]}
    case W.VPi{+t1, b1, e1} W.VPi{t2, b2, e2}:
      SMore{
        [VP{cx, t1, t2},
         VP{
           Con{W.Val.quote_d(fuel, env, Vconv.depth(cx, 0n), t1), cx},
           W.Val.under(
             fuel, env, False{}, b1, e1,
             W.Val.rigid(Vconv.depth(cx, 0n))),
           W.Val.under(
             fuel, env, False{}, b2, e2,
             W.Val.rigid(Vconv.depth(cx, 0n)))}]}
    # eta: a lambda against anything else is the body against that thing
    # applied to the binder
    case W.VLam{+t1, b1, e1} y:
      SMore{
        [VP{
          Con{W.Val.quote_d(fuel, env, Vconv.depth(cx, 0n), t1), cx},
          W.Val.under(
            fuel, env, False{}, b1, e1,
            W.Val.rigid(Vconv.depth(cx, 0n))),
          W.Val.app(
            fuel, env, False{}, y,
            [W.Val.rigid(Vconv.depth(cx, 0n))])}]}
    case x W.VLam{+t2, b2, e2}:
      SMore{
        [VP{
          Con{W.Val.quote_d(fuel, env, Vconv.depth(cx, 0n), t2), cx},
          W.Val.app(
            fuel, env, False{}, x,
            [W.Val.rigid(Vconv.depth(cx, 0n))]),
          W.Val.under(
            fuel, env, False{}, b2, e2,
            W.Val.rigid(Vconv.depth(cx, 0n)))}]}
    # a literal against a constructor application
    case W.VNat{v1, m1, z1, s1} y:
      SMore{[VDeep{cx, W.Val.lit_ctor(W.VNat{v1, m1, z1, s1}), y}]}
    case x W.VNat{v2, m2, z2, s2}:
      SMore{[VDeep{cx, x, W.Val.lit_ctor(W.VNat{v2, m2, z2, s2})}]}
    case W.VNe{h1, +s1} W.VNe{h2, +s2}:
      Vconv.ne_step(
        fuel, cx,
        Bool.and(
          W.Val.same_hd(fuel, h1, h2),
          Nat.is_eq(
            W.Val.sp_len(s1, 0n), W.Val.sp_len(s2, 0n))),
        s1, s2)
    case x y:
      SNo{}

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
def Vconv.irrel_step(
  ok: Bool, +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>,
  +a: W.Val, +b: W.Val, +ta: T.Term, +tb: T.Term
) -> VStep:
  match ok:
    case True{}:
      SMore{
        [VP{
          cx, W.Val.core(fuel, env, ta), W.Val.core(fuel, env, tb)}]}
    case False{}:
      Vconv.rigid(fuel, env, cx, a, b)

def Vconv.irrel_go(
  +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>, +a: W.Val, +b: W.Val
) -> VStep:
  +qa : T.Term = W.Val.quote_d(fuel, env, Vconv.depth(cx, 0n), a)
  +qb : T.Term = W.Val.quote_d(fuel, env, Vconv.depth(cx, 0n), b)
  Vconv.irrel_step(
    Vconv.irrel_ok(fuel, env, cx, qa, qb),
    fuel, env, cx, a, b,
    Vconv.ty_of(fuel, env, cx, qa),
    Vconv.ty_of(fuel, env, cx, qb))

def Vconv.irrel_pick(
  maybe: Bool, +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>,
  +a: W.Val, +b: W.Val
) -> VStep:
  match maybe:
    case True{}:
      Vconv.irrel_go(fuel, env, cx, a, b)
    case False{}:
      Vconv.rigid(fuel, env, cx, a, b)

# Where neither route is the cheap one and a head could still unfold, the
# answer is not "no": it is "unfold and look again". Saying no there is what
# made `perf/church-numerals` reject, since `CNat` and its unfolding are the
# same type and only a delta step shows it.
# The K-like rule, on a value.
#
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
  +fuel: Nat, +env: E.DTable, +v: W.Val, +d: E.Decl, +ty: T.Term
) -> W.Val:
  W.Val.app(
    fuel, env, True{},
    W.VNe{W.HConst{W.Val.head_name(v), W.Val.head_levels(v)}, Nil{}},
    Vconv.k_sp(
      W.Val.args(v), V.Eval.major_idx(d),
      W.Val.core(fuel, env, C.Conv.k_ctor(env, d, ty))))

def Vconv.k_pick(
  ok: Bool, +fuel: Nat, +env: E.DTable, +v: W.Val, +d: E.Decl, +ty: T.Term
) -> W.Val:
  match ok:
    case True{}:
      Vconv.k_use(fuel, env, v, d, ty)
    case False{}:
      v

def Vconv.k_go(
  +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>, +v: W.Val, +d: E.Decl
) -> W.Val:
  +sj : W.Val = W.Val.sp_nth(V.Eval.major_idx(d), W.Val.args(v))
  +ty : T.Term =
    V.Eval.whnf(
      fuel, env,
      H.Shape.ty(
        H.Shape.infer(
          fuel, env, cx,
          W.Val.quote_d(fuel, env, Vconv.depth(cx, 0n), sj))),
      Nil{})
  Vconv.k_pick(
    Bool.and(
      C.Conv.k_type_ok(d, ty),
      C.Conv.k_fits(fuel, env, cx, d, ty)),
    fuel, env, v, d, ty)

def Vconv.k_try(
  near: Bool, +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>, +v: W.Val
) -> W.Val:
  match near:
    case True{}:
      Vconv.k_go(
        fuel, env, cx, v,
        E.Lookup.get(E.Env.find(env, W.Val.head_name(v))))
    case False{}:
      v

def Vconv.k_fix(
  +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>, +v: W.Val
) -> W.Val:
  Vconv.k_try(Vconv.k_near(env, v), fuel, env, cx, v)

# The irrelevance test, and the structural comparison when it does not fit.
def Vconv.irrel(
  +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>, +a: W.Val, +b: W.Val
) -> VStep:
  Vconv.irrel_pick(
    Bool.and(Vconv.maybe_proof(a), Vconv.maybe_proof(b)),
    fuel, env, cx,
    Vconv.k_fix(fuel, env, cx, a),
    Vconv.k_fix(fuel, env, cx, b))

# The dear route: unfold both heads and look again.
def Vconv.deep(
  +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>, +a: W.Val, +b: W.Val
) -> VStep:
  Vconv.irrel(
    fuel, env, cx,
    W.Val.delta(fuel, env, a),
    W.Val.delta(fuel, env, b))

def Vconv.pick_step(b: Bool, x: VStep, y: VStep) -> VStep:
  match b:
    case True{}:
      x
    case False{}:
      y

# Offer the cheap route when the two sides are the same head applied to the
# same number of arguments, and keep the dear one for a no.
#

def Vconv.offer(
  +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>, +a: W.Val, +b: W.Val
) -> VStep:
  Vconv.pick_step(
    Bool.and(
      Vconv.spine_match(fuel, a, b),
      Bool.or(W.Val.can_delta(env, a), W.Val.can_delta(env, b))),
    SEither{
      Vconv.zip(cx, W.Val.args(a), W.Val.args(b)),
      [VDeep{cx, a, b}]},
    Vconv.pick_step(
      Bool.or(W.Val.can_delta(env, a), W.Val.can_delta(env, b)),
      SMore{[VDeep{cx, a, b}]},
      Vconv.irrel(fuel, env, cx, a, b)))

# What to do with one pair.
def Vconv.classify(+fuel: Nat, +env: E.DTable, p: VPair) -> VStep:
  match p:
    case VDeep{+cx, +a, +b}:
      Vconv.deep(fuel, env, cx, a, b)
    case VP{+cx, +a, +b}:
      Vconv.offer(
        fuel, env, cx,
        W.Val.more(fuel, env, False{}, a),
        W.Val.more(fuel, env, False{}, b))

# Work the queue. It empties exactly when every pair in it is equal.
def Vconv.all(
  +fuel: Nat, +env: E.DTable, acc: A.Ans, alts: List<&2, VAlt>,
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
          Vconv.all(f, env, a2, r2, w2)
        case a as Nil{}:
          a
        case +a as Con{p, +rest}:
          +st : VStep = Vconv.classify(f, env, p)
          Vconv.all(
            f, env,
            A.Ans.and(a, Vconv.step_ans(st)),
            Vconv.step_alts(st, a, rest, as),
            List.append(&2, VPair, Vconv.step_more(st), rest))

# Are these two terms definitionally equal? The context tells the walk how
# many binders it starts inside, which is where a rigid variable's level
# counts from.
def Vconv.eq_in(
  +fuel: Nat, +env: E.DTable, +cx: List<&2, T.Term>, +a: T.Term, +b: T.Term
) -> A.Ans:
  Vconv.all(
    fuel, env, A.AYes{}, Nil{},
    [VP{cx, W.Val.core(fuel, env, a), W.Val.core(fuel, env, b)}])
