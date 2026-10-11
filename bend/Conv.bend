# Definitional equality.
#
# The shape here is forced by Bend. A conversion checker normally reduces both
# sides, inspects the two results, and recurses on their subterms. In Bend that
# is two functions calling each other, which is mutual recursion, and a match
# cannot inspect the reduced terms because they are computed values.
#
# So this is a worklist. `Conv.eq_all` holds a queue of pairs still to be shown
# equal. It takes one pair, reduces both sides, and hands the two results to
# `Conv.classify`, which matches its own parameters and answers whether the
# pair fails, succeeds, or reduces to further pairs. Those go on the front of
# the queue. The queue empties exactly when the two terms are equal.
#
# A pair carries its own local context, because a pair pushed from under a
# binder is open: its terms mention the binder. Proof irrelevance needs the
# type of each side, and a type cannot be found without that context. The
# arena's `107_proofIrrelevanceUnderBinder` is the test that says so.
#
# Proof irrelevance is tried before the two sides are taken apart. Two proofs
# of one proposition are equal whatever they look like, and once an
# application has been split into its function and its argument the chance is
# gone: `f (h a)` and `f (h b)` decompose to `a` against `b`, which no rule
# can settle.
#
# What is missing against the Lean kernel: eta for functions and structures,
# and the case split on an imax whose right side is a bare parameter.

import Base
import ./Level.bend as L
import ./Term.bend as T
import ./Env.bend as E
import ./Eval.bend as V
import ./Shape.bend as S
import ./Ans.bend as A

# A pair of terms still to be shown equal, with the context they live in.
#
# `MkDeep` is the same question with the cheap route already spent: reduce the
# two sides, do not offer to compare their spines again. See "Comparing a
# spine before unfolding it" below.
type TPair is Data:
  MkPair{ctx: List<&2, T.Term>, a: T.Term, b: T.Term}
  MkDeep{ctx: List<&2, T.Term>, a: T.Term, b: T.Term}

# What one pair reduces to.
#
# `SEither` holds two routes to the same answer, the cheap one first. The
# queue takes the cheap one and puts the other aside.
type Step is Data:
  SNo{}
  SYes{}
  SUnk{}
  SMore{ps: List<&2, TPair>}
  SEither{cheap: List<&2, TPair>, dear: List<&2, TPair>}

# A route put aside: the queue to work if the cheap one fails, and the answer
# that stood when it was set down.
type Alt is Data:
  MkAlt{acc: A.Ans, work: List<&2, TPair>}

# Choose between two Bools on a computed Bool.
def Conv.pick_b(b: Bool, x: Bool, y: Bool) -> Bool:
  match b:
    case True{}:
      x
    case False{}:
      y

# Choose between two steps on a computed Bool.
def Conv.pick_step(b: Bool, x: Step, y: Step) -> Step:
  match b:
    case True{}:
      x
    case False{}:
      y

# What this step says on its own, before its further pairs are worked.
def Conv.step_ans(s: Step) -> A.Ans:
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

# The further pairs a step asks for. For a step with two routes that is the
# cheap one; the other goes on the stack of routes put aside.
def Conv.step_more(s: Step) -> List<&2, TPair>:
  match s:
    case SNo{}:
      Nil{}
    case SYes{}:
      Nil{}
    case SUnk{}:
      Nil{}
    case SMore{ps}:
      ps
    case SEither{cheap, dear}:
      cheap

# The routes put aside, with this step's own added if it has one. The rest of
# the queue goes with it, because the cheap route replaced a pair in it.
def Conv.step_alts(
  s: Step, acc: A.Ans, rest: List<&2, TPair>, alts: List<&2, Alt>
) -> List<&2, Alt>:
  match s alts:
    case SEither{cheap, dear} Nil{}:
      [MkAlt{acc, List.append(&2, TPair, dear, rest)}]
    case o as:
      as

# The answer when the budget runs out. A route still on the stack might have
# answered yes, so a no that is waiting for one is not a no.
def Conv.out_of_fuel(acc: A.Ans, alts: List<&2, Alt>) -> A.Ans:
  match alts:
    case Nil{}:
      A.Ans.and(acc, A.AUnk{})
    case o:
      A.AUnk{}

# A yes or no step from a Bool.
def Conv.step_of(b: Bool) -> Step:
  match b:
    case True{}:
      SYes{}
    case False{}:
      SNo{}

# Structural equality of two terms.
# A reference against anything else resolves, so a value that holds one still
# matches a type that was expanded. Without that the test fails on every pair
# and `perf/church-numerals` runs out of budget. Two references to one entry
# are equal without resolving at all, which is the cheap case and the common
# one.

#
# This is equality of syntax, not of meaning, and that is what it is for: a
# guard that must never say yes to two terms that differ.
#
# It is a worklist and not a plain recursion, for the same reason
# `Conv.eq_all` is one. `Bool.and` evaluates both of its sides, because an
# argument evaluates before the match picks an arm, so `and(same(f1, f2),
# same(a1, a2))` walked the whole of both terms even when the heads already
# differed. Conversion asks this of every pair it takes off its queue, and
# most of those pairs differ, so most of that walking was waste.
#
# The answer so far travels in as a parameter, which a match can inspect, so
# a difference stops the walk. The budget bounds what one question may cost,
# and running out answers no: this is a guard, and a guard that gives up must
# give up on the side that does more work rather than less.

# One pair still to be compared.
type TwoT is Data:
  MkTT{a: T.Term, b: T.Term}

# What comparing the heads of one pair settles.
type SameStep is Data:
  SDiff{}
  SNext{ps: List<&2, TwoT>}

def Conv.step_ok(s: SameStep) -> Bool:
  match s:
    case SDiff{}:
      False{}
    case SNext{ps}:
      True{}

def Conv.step_next(s: SameStep) -> List<&2, TwoT>:
  match s:
    case SDiff{}:
      Nil{}
    case SNext{ps}:
      ps

def Conv.same_of(b: Bool) -> SameStep:
  match b:
    case True{}:
      SNext{Nil{}}
    case False{}:
      SDiff{}

def Conv.same_proj(ok: Bool, s1: T.Term, s2: T.Term) -> SameStep:
  match ok:
    case True{}:
      SNext{[MkTT{s1, s2}]}
    case False{}:
      SDiff{}

# The heads of one pair, and the pairs they leave behind.
def Conv.same_step(+env: E.DTable, a: T.Term, b: T.Term) -> SameStep:
  match a b:
    case T.TVar{i} T.TVar{j}:
      Conv.same_of(Nat.is_eq(i, j))
    case T.TSort{x} T.TSort{y}:
      Conv.same_of(L.Level.same(x, y))
    case T.TConst{n1, l1} T.TConst{n2, l2}:
      Conv.same_of(
        Bool.and(Nat.is_eq(n1, n2), T.Term.same_levels(l1, l2)))
    case T.TApp{f1, a1} T.TApp{f2, a2}:
      SNext{[MkTT{f1, f2}, MkTT{a1, a2}]}
    case T.TLam{t1, b1} T.TLam{t2, b2}:
      SNext{[MkTT{t1, t2}, MkTT{b1, b2}]}
    case T.TPi{t1, b1} T.TPi{t2, b2}:
      SNext{[MkTT{t1, t2}, MkTT{b1, b2}]}
    case T.TProj{n1, i1, s1} T.TProj{n2, i2, s2}:
      Conv.same_proj(
        Bool.and(Nat.is_eq(n1, n2), Nat.is_eq(i1, i2)), s1, s2)
    case T.TNat{v1, m1, z1, s1} T.TNat{v2, m2, z2, s2}:
      Conv.same_of(Nat.is_eq(v1, v2))
    case T.TLet{t1, v1, b1} T.TLet{t2, v2, b2}:
      SNext{[MkTT{t1, t2}, MkTT{v1, v2}, MkTT{b1, b2}]}
    case T.TUnk{} T.TUnk{}:
      SNext{Nil{}}
    case T.TRef{i} T.TRef{j}:
      Conv.same_of(Nat.is_eq(i, j))
    case T.TRef{+i} y:
      SNext{[MkTT{E.Env.expr(env, i), y}]}
    case x T.TRef{+j}:
      SNext{[MkTT{x, E.Env.expr(env, j)}]}
    case x y:
      SDiff{}

def Conv.same_all(
  +fuel: Nat, +env: E.DTable, ok: Bool, work: List<&2, TwoT>
) -> Bool:
  match fuel:
    case 0n:
      False{}
    case 1n+f:
      match ok work:
        case False{} w:
          False{}
        case True{} Nil{}:
          True{}
        case True{} Con{MkTT{a, b}, rest}:
          +st : SameStep = Conv.same_step(env, a, b)
          Conv.same_all(
            f, env,
            Conv.step_ok(st),
            List.append(&2, TwoT, Conv.step_next(st), rest))

# How many pairs one question may cost. Large enough that no pair in the
# arena's corpus reaches it, and small enough that a pathological pair cannot
# cost the whole run.
def Conv.same_budget() -> Nat:
  1000000n

def Conv.same(+env: E.DTable, a: T.Term, b: T.Term) -> Bool:
  Conv.same_all(Conv.same_budget(), env, True{}, [MkTT{a, b}])

# Compare two lists of levels pairwise.
def Conv.levels_eq(+fuel: Nat, xs: List<&2, L.Level>, ys: List<&2, L.Level>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xr} Con{y, yr}:
      Bool.and(L.Level.eq(x, y), Conv.levels_eq(fuel, xr, yr))
    case x y:
      False{}

# Two projections are equal when they take the same field of the same
# structure type from structures that are equal. Without this case two
# projections fall through to a definite no, and every declaration whose type
# mentions one is rejected. That is what happened: the projection machinery
# was right and conversion never got to use it.
def Conv.proj_step(
  same_field: Bool, +ctx: List<&2, T.Term>, s1: T.Term, s2: T.Term
) -> Step:
  match same_field:
    case True{}:
      SMore{[MkPair{ctx, s1, s2}]}
    case False{}:
      SNo{}

# Take the two sides apart. Both are already in weak head normal form. A pair
# pushed from under a binder carries the extended context.
#
# The two mixed lambda cases are eta for functions: `f` and `fun x => f x` are
# the same function, so a lambda against anything else goes under the binder
# and compares the body with the other side applied to the new variable. The
# other side is lifted, because it was written one scope out.
def Conv.structural(
  +fuel: Nat, +ctx: List<&2, T.Term>, a: T.Term, b: T.Term
) -> Step:
  match a b:
    case T.TVar{i} T.TVar{j}:
      Conv.step_of(Nat.is_eq(i, j))
    case T.TSort{x} T.TSort{y}:
      Conv.step_of(L.Level.eq(x, y))
    case T.TConst{n1, l1} T.TConst{n2, l2}:
      Conv.step_of(Bool.and(Nat.is_eq(n1, n2), Conv.levels_eq(fuel, l1, l2)))
    case T.TApp{f1, a1} T.TApp{f2, a2}:
      SMore{[MkPair{ctx, f1, f2}, MkPair{ctx, a1, a2}]}
    case T.TLam{+t1, b1} T.TLam{t2, b2}:
      SMore{[MkPair{ctx, t1, t2}, MkPair{Con{t1, ctx}, b1, b2}]}
    case T.TPi{+t1, b1} T.TPi{t2, b2}:
      SMore{[MkPair{ctx, t1, t2}, MkPair{Con{t1, ctx}, b1, b2}]}
    case T.TProj{n1, i1, s1} T.TProj{n2, i2, s2}:
      Conv.proj_step(
        Bool.and(Nat.is_eq(n1, n2), Nat.is_eq(i1, i2)),
        ctx, s1, s2)
    case T.TNat{v1, m1, z1, s1} T.TNat{v2, m2, z2, s2}:
      Conv.step_of(Nat.is_eq(v1, v2))
    case T.TNat{+v1, +m1, +z1, +s1} y:
      SMore{[MkPair{ctx, V.Eval.lit_ctor(T.TNat{v1, m1, z1, s1}), y}]}
    case x T.TNat{+v2, +m2, +z2, +s2}:
      SMore{[MkPair{ctx, x, V.Eval.lit_ctor(T.TNat{v2, m2, z2, s2})}]}
    case T.TLam{+t1, b1} y:
      SMore{[MkPair{Con{t1, ctx}, b1, T.TApp{T.Term.lift(y, 1n, 0n), T.TVar{0n}}}]}
    case x T.TLam{+t2, b2}:
      SMore{[MkPair{Con{t2, ctx}, T.TApp{T.Term.lift(x, 1n, 0n), T.TVar{0n}}, b2}]}
    case T.TUnk{} y:
      SUnk{}
    case x T.TUnk{}:
      SUnk{}
    case x y:
      SNo{}

# Could this term be a proof? A sort and a pi are types, and the type of a
# type is never `Prop`, so neither can ever be a proof. The test is syntactic
# and costs nothing, which matters: a pair that cannot be two proofs must not
# pay for an inference pass.
#
# The test alone was not enough. `Conv.irrel` read it through
# `Conv.pick_step`, which evaluates both of its branches, so every pair paid
# for the inference anyway. `Conv.irrel_pick` matches the test instead.
def Conv.maybe_proof(t: T.Term) -> Bool:
  match t:
    case T.TSort{l}:
      False{}
    case T.TPi{ty, bd}:
      False{}
    case x:
      True{}

# The head of an application.
def Conv.head(t: T.Term) -> T.Term:
  match t:
    case T.TApp{f, a}:
      Conv.head(f)
    case x:
      x

# The name a head names, or zero.
def Conv.head_name(t: T.Term) -> Nat:
  match t:
    case T.TConst{n, ls}:
      n
    case x:
      0n

# Does this declaration describe a unit type?
def Conv.unit_of(+env: E.DTable, +d: E.Decl) -> Bool:
  Bool.and(
    Bool.and(E.Decl.is_ind(d), Nat.is_eq(E.Decl.ind_ni(d), 0n)),
    Bool.and(
      E.Decl.is_one(E.Decl.ind_ctors(d)),
      Nat.is_eq(
        E.Decl.ctor_nf(
          E.Lookup.get(E.Env.find(env, E.Decl.only(E.Decl.ind_ctors(d))))),
        0n)))

# Is this type a unit: an inductive with no indices and exactly one
# constructor that takes no fields?
#
# Every element of such a type is that constructor, so any two of them are
# equal. This is eta for a structure with no fields, and it is what settles
# the arena's `unitEta` tests. The general structure rule, where an element
# equals its constructor applied to its own projections, needs projections and
# is not here.
def Conv.is_unit(+env: E.DTable, +t: T.Term) -> Bool:
  Conv.unit_of(env, E.Lookup.get(E.Env.find(env, Conv.head_name(Conv.head(t)))))

# The two types on the queue, or the two terms taken apart.
def Conv.irrel_step(
  ok: Bool, +fuel: Nat, +ctx: List<&2, T.Term>, +a: T.Term, +b: T.Term,
  +ta: T.Term, +tb: T.Term
) -> Step:
  match ok:
    case True{}:
      SMore{[MkPair{ctx, ta, tb}]}
    case False{}:
      Conv.structural(fuel, ctx, a, b)

# Try proof irrelevance in earnest, now that it is worth the inference.
def Conv.irrel_go(
  +fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>, +a: T.Term, +b: T.Term
) -> Step:
  +ra = S.Shape.infer(fuel, env, ctx, a)
  +rb = S.Shape.infer(fuel, env, ctx, b)
  Conv.irrel_step(
    Bool.and(
      Bool.and(S.Shape.ok(ra), S.Shape.ok(rb)),
      Bool.or(
        S.Shape.prop_sort(fuel, env, ctx, S.Shape.ty(ra)),
        Conv.is_unit(
          env,
          V.Eval.whnf(fuel, env, S.Shape.ty(ra), Nil{})))),
    fuel, ctx, a, b, S.Shape.ty(ra), S.Shape.ty(rb))

# Two terms are equal when their types are, in two cases: the type is a
# proposition, which is proof irrelevance, or the type is a unit, which is eta
# for a structure with no fields. Both put the two types on the queue instead
# of the two terms.
#
# The two types are inferred once and bound, not inferred again for each use.
def Conv.irrel_pick(
  maybe: Bool, +fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>,
  +a: T.Term, +b: T.Term
) -> Step:
  match maybe:
    case True{}:
      Conv.irrel_go(fuel, env, ctx, a, b)
    case False{}:
      Conv.structural(fuel, ctx, a, b)

def Conv.irrel(
  +fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>, +a: T.Term, +b: T.Term
) -> Step:
  Conv.irrel_pick(
    Bool.and(Conv.maybe_proof(a), Conv.maybe_proof(b)),
    fuel, env, ctx, a, b)

# Choose between two terms on a computed Bool.
def Conv.pick_t(b: Bool, x: T.Term, y: T.Term) -> T.Term:
  match b:
    case True{}:
      x
    case False{}:
      y

# K-like reduction
# ----------------
#
# A recursor whose inductive has one constructor that takes no fields may fire
# even when the major premise is not written as that constructor, because that
# is the only thing it could be. The Lean kernel reaches this two ways, as the
# K rule for something like `Eq` and as eta for a structure for something like
# a one-element type, and both land in the same place here.
#
# The flag the export carries is not the condition. The arena's
# `075_typeSingletonRecReduction` has `k` unset and still reduces, because its
# inductive is a structure; its `101_ruleKAcc` has one constructor that does
# carry data, so it must not reduce. What decides it is the shape of the
# constructor and the type check below.
#
# It may not fire unguarded. The Lean kernel infers the major premise's type
# first and requires it to be an application of the recursor's own inductive;
# without that, the rule fires on a premise of the wrong type and the arena's
# `100_ruleKbad` passes. Reduction cannot infer a type, because that would
# make reduction and inference call each other, which Bend forbids.
#
# So the rule lives here instead. Conversion already depends on `Shape`, so it
# can ask for a type, and it already depends on `Eval`, so it can reduce the
# result. The premise is replaced by the constructor applied to the type's
# parameters, and ordinary iota does the rest.

# The arguments of an application, in order.
def Conv.args(t: T.Term) -> List<&2, T.Term>:
  V.Eval.spine(t, Nil{})

# The level arguments of a head constant, or none.
def Conv.head_levels(t: T.Term) -> List<&2, L.Level>:
  match t:
    case T.TConst{n, ls}:
      ls
    case x:
      Nil{}

# Replace the `i`-th argument of a list.
def Conv.put(+xs: List<&2, T.Term>, +i: Nat, +v: T.Term) -> List<&2, T.Term>:
  List.append(&2, T.Term,
    V.Eval.take(xs, i),
    Con{v, V.Eval.drop(xs, 1n+i)})

# Does this type head the recursor's own inductive?
def Conv.k_type_ok(+d: E.Decl, +ty: T.Term) -> Bool:
  Nat.is_eq(Conv.head_name(Conv.head(ty)), E.Decl.only(E.Decl.rec_inds(d)))

# The constructor, applied to the parameters the major premise's type carries.
def Conv.k_ctor(+env: E.DTable, +d: E.Decl, +ty: T.Term) -> T.Term:
  V.Eval.rebuild(
    V.Eval.take(Conv.args(ty), E.Decl.rec_np(d)),
    T.TConst{
      E.Decl.only(
        E.Decl.ind_ctors(
          E.Lookup.get(E.Env.find(env, E.Decl.only(E.Decl.rec_inds(d)))))),
      Conv.head_levels(Conv.head(ty))})

# Is putting the constructor in place of the major premise type correct?
#
# This is the guard. The arena states the rule as "the recursor reduces even
# if the major argument is not a constructor, as long as replacing the major
# argument with a constructor is type correct", and the two tests are the two
# sides of it. With `h : true = true` the premise's type is `Eq Bool true
# true` and the constructor's is the same, so the rule fires. With `h : true =
# false` the premise's type is `Eq Bool true false` while the constructor's is
# still `Eq Bool true true`, so it must not. The comparison is syntactic,
# which tells those two apart and can only ever be too strict.
def Conv.k_fits(
  +fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>,
  +d: E.Decl, +ty: T.Term
) -> Bool:
  Conv.same(env,
    V.Eval.whnf(
      fuel, env,
      S.Shape.ty(S.Shape.infer(fuel, env, ctx, Conv.k_ctor(env, d, ty))),
      Nil{}),
    ty)

# Does this recursor's inductive have exactly one constructor, and does that
# constructor take no fields?
#
# No fields is what lets the constructor be written without projections. A
# constructor that carries data needs them, so `Acc`, whose one constructor
# does carry data, is left alone. That is the arena's `101_ruleKAcc`.
def Conv.k_single(+env: E.DTable, +d: E.Decl) -> Bool:
  Bool.and(
    E.Decl.is_one(
      E.Decl.ind_ctors(
        E.Lookup.get(E.Env.find(env, E.Decl.only(E.Decl.rec_inds(d)))))),
    Nat.is_eq(
      E.Decl.ctor_nf(
        E.Lookup.get(
          E.Env.find(
            env,
            E.Decl.only(
              E.Decl.ind_ctors(
                E.Lookup.get(
                  E.Env.find(env, E.Decl.only(E.Decl.rec_inds(d))))))))),
      0n))

# Is the K rule allowed on this application? The declaration must be a
# recursor with the flag set and enough arguments, its inductive must have one
# constructor, and the major premise's type must head that inductive.
def Conv.k_ok(
  +fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>,
  +d: E.Decl, +args: List<&2, T.Term>, +ty: T.Term
) -> Bool:
  Bool.and(
    Bool.and(
      E.Decl.is_rec(d),
      Nat.is_lt(V.Eval.major_idx(d), V.Eval.len(args, 0n))),
    Bool.and(
      Bool.and(Conv.k_single(env, d), Conv.k_type_ok(d, ty)),
      Conv.k_fits(fuel, env, ctx, d, ty)))

# The application with its major premise replaced by the constructor.
def Conv.k_rebuilt(
  +env: E.DTable, +d: E.Decl, +t: T.Term, +args: List<&2, T.Term>, +ty: T.Term
) -> T.Term:
  V.Eval.rebuild(
    Conv.put(args, V.Eval.major_idx(d), Conv.k_ctor(env, d, ty)),
    Conv.head(t))

# Fire it, or leave the term alone. The rebuilt application is reduced only
# when the rule fires, because `Conv.pick_t` evaluates both of its branches
# and that reduction is a whole whnf pass over the application.
def Conv.k_pick(
  ok: Bool, +fuel: Nat, +env: E.DTable, +t: T.Term,
  +d: E.Decl, +args: List<&2, T.Term>, +ty: T.Term
) -> T.Term:
  match ok:
    case True{}:
      V.Eval.whnf(fuel, env, Conv.k_rebuilt(env, d, t, args, ty), Nil{})
    case False{}:
      t

def Conv.k_go(
  +fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>, +t: T.Term,
  +d: E.Decl, +args: List<&2, T.Term>, +ty: T.Term
) -> T.Term:
  Conv.k_pick(
    Conv.k_ok(fuel, env, ctx, d, args, ty),
    fuel, env, t, d, args, ty)

# Could the rule fire at all? Everything here is a trie read or a length, and
# `Conv.k_ok` holds only when this does, so a cheap no is a real no.
def Conv.k_near(+env: E.DTable, +d: E.Decl, +args: List<&2, T.Term>) -> Bool:
  Bool.and(
    Bool.and(
      E.Decl.is_rec(d),
      Nat.is_lt(V.Eval.major_idx(d), V.Eval.len(args, 0n))),
    Conv.k_single(env, d))

# The term whose type the rule needs, or a sort when the rule cannot fire.
# A branch of `Conv.pick_t` is evaluated whether or not it is chosen, so the
# type of a sort is what the common case pays for. Without this every pair on
# the conversion queue paid for an inference pass over an argument.
def Conv.k_subj(
  +env: E.DTable, +d: E.Decl, +args: List<&2, T.Term>
) -> T.Term:
  Conv.pick_t(
    Conv.k_near(env, d, args),
    V.Eval.nth(args, V.Eval.major_idx(d)),
    T.TSort{L.LZero{}})

# Apply the K rule to a term already in weak head normal form, if it applies.
def Conv.k_fix(
  +fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>, +t: T.Term
) -> T.Term:
  Conv.k_go(
    fuel, env, ctx, t,
    E.Lookup.get(E.Env.find(env, Conv.head_name(Conv.head(t)))),
    Conv.args(t),
    V.Eval.whnf(
      fuel, env,
      S.Shape.ty(
        S.Shape.infer(
          fuel, env, ctx,
          Conv.k_subj(
            env,
            E.Lookup.get(E.Env.find(env, Conv.head_name(Conv.head(t)))),
            Conv.args(t)))),
      Nil{}))

# Eta for a structure that carries data.
#
# An element of a structure is its constructor applied to its own fields, so
# `p` and `Prod.mk p.0 p.1` are the same pair. `Conv.is_unit` settles this
# when the structure has no fields; this is the general rule, and it needs
# projections, which now work. It is the arena's `112_structEta`.
#
# The rule rewrites the side that is not a constructor application into one,
# and leaves the rest to `Conv.structural`. That way the parameters are
# compared too, and nothing here has to know they match.

# The fields of `b`, as projections, from the `i`-th on.
def Conv.eta_fields(n: Nat, +ind: Nat, +b: T.Term, +i: Nat) -> List<&2, T.Term>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{T.TProj{ind, i, b}, Conv.eta_fields(m, ind, b, 1n+i)}

# Is `a` a saturated application of the one constructor of an index-free
# inductive, with `b` not an application of that same constructor?
#
# This is the whole cheap test. It guards the one expensive step, which is
# inferring the type of `b`.
def Conv.eta_ready(+env: E.DTable, +d: E.Decl, +b: T.Term, +nargs: Nat) -> Bool:
  Bool.and(
    Bool.and(
      E.Decl.is_ctor(d),
      Nat.is_eq(nargs, Nat.add(E.Decl.ctor_np(d), E.Decl.ctor_nf(d)))),
    Bool.and(
      Conv.pick_b(Nat.is_eq(Conv.head_name(Conv.head(b)), E.Decl.id(d)),
        False{}, True{}),
      Bool.and(
        E.Decl.is_one(
          E.Decl.ind_ctors(
            E.Lookup.get(E.Env.find(env, E.Decl.ctor_ind(d))))),
        Nat.is_eq(
          E.Decl.ind_ni(
            E.Lookup.get(E.Env.find(env, E.Decl.ctor_ind(d)))),
          0n))))

# The term whose type the rule needs, or a sort when the rule cannot fire.
# A branch of `Conv.pick_t` is evaluated whether or not it is chosen, so the
# type of a sort is what the common case pays for.
def Conv.eta_subj(
  +env: E.DTable, +d: E.Decl, +b: T.Term, +nargs: Nat
) -> T.Term:
  Conv.pick_t(Conv.eta_ready(env, d, b, nargs), b, T.TSort{L.LZero{}})

# May the rule fire? The cheap test must hold, and the type of `b` must head
# the constructor's own inductive. Without the second part the rule rewrites a
# term of some other type and the comparison that follows means nothing.
def Conv.eta_ok(
  +env: E.DTable, +d: E.Decl, +b: T.Term, +nargs: Nat, +ty: T.Term
) -> Bool:
  Bool.and(
    Conv.eta_ready(env, d, b, nargs),
    Nat.is_eq(Conv.head_name(Conv.head(ty)), E.Decl.ctor_ind(d)))

# `b` written as a constructor application: the parameters its type carries,
# then its own fields.
def Conv.eta_mk(+d: E.Decl, +b: T.Term, +ty: T.Term) -> T.Term:
  V.Eval.rebuild(
    List.append(&2, T.Term,
      V.Eval.take(Conv.args(ty), E.Decl.ctor_np(d)),
      Conv.eta_fields(E.Decl.ctor_nf(d), E.Decl.ctor_ind(d), b, 0n)),
    T.TConst{E.Decl.id(d), Conv.head_levels(Conv.head(ty))})

def Conv.eta_pick(
  ok: Bool, +d: E.Decl, +b: T.Term, +ty: T.Term
) -> T.Term:
  match ok:
    case True{}:
      Conv.eta_mk(d, b, ty)
    case False{}:
      b

def Conv.eta_go(
  +env: E.DTable, +d: E.Decl, +b: T.Term, +nargs: Nat, +ty: T.Term
) -> T.Term:
  Conv.eta_pick(Conv.eta_ok(env, d, b, nargs, ty), d, b, ty)

# Rewrite `b` into a constructor application when `a` is one. Both sides are
# already in weak head normal form.
def Conv.eta_fix(
  +fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>, +a: T.Term, +b: T.Term
) -> T.Term:
  Conv.eta_go(
    env,
    E.Lookup.get(E.Env.find(env, Conv.head_name(Conv.head(a)))),
    b,
    V.Eval.len(Conv.args(a), 0n),
    V.Eval.whnf(
      fuel, env,
      S.Shape.ty(
        S.Shape.infer(
          fuel, env, ctx,
          Conv.eta_subj(
            env,
            E.Lookup.get(E.Env.find(env, Conv.head_name(Conv.head(a)))),
            b,
            V.Eval.len(Conv.args(a), 0n)))),
      Nil{}))

# Reduce the two sides of a pair, then try proof irrelevance before taking
# them apart.
def Conv.classify_work(
  +fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>, a: T.Term, b: T.Term
) -> Step:
  +ka = Conv.k_fix(fuel, env, ctx, V.Eval.whnf(fuel, env, a, Nil{}))
  +kb = Conv.k_fix(fuel, env, ctx, V.Eval.whnf(fuel, env, b, Nil{}))
  Conv.irrel(
    fuel,
    env,
    ctx,
    Conv.eta_fix(fuel, env, ctx, kb, ka),
    Conv.eta_fix(fuel, env, ctx, ka, kb))

# Two terms that are the same syntax are the same term, and no reduction can
# tell anyone anything new about them.
#
# This is not a small saving. `Conv.structural` takes two applications apart
# into a pair per argument, and most of those pairs are a term against itself,
# because the two sides of a real conversion question differ in one place. Each
# one used to pay for two whnf passes, two K rule passes and two eta passes
# before anything looked at it.
# Comparing a spine before unfolding it
# -------------------------------------
#
# `f x` and `f y` are the same term when `x` and `y` are, whatever `f` does,
# and finding that out costs one pair per argument. Reducing them instead
# unfolds `f` on both sides, and if `f` is a definition over a recursor that
# can cost everything.
#
# The arena's `proj-stuck-struct` is this and nothing else. It asks the kernel
# to see that `Prod.fst (step (id n) 12 m)` and `Prod.fst (step n 12 m)` are
# the same, where `step` runs through `Nat.brecOn` and `Nat.below`. Compared
# spine by spine it comes down to `id n` against `n`, which is one delta step.
# Reduced, it builds twelve nested structures twice and does not finish in six
# minutes.
#
# The cheap route is sufficient and not necessary: `f x` and `f y` can be
# equal with `x` and `y` not equal, when `f` throws its argument away. So the
# route cannot simply be taken. `SEither` offers both, the queue takes the
# cheap one and puts the other on a stack, and a definite no pops the stack
# instead of ending the walk. Nothing is lost and nothing is unsound.
#
# The route put aside is a `MkDeep`, which is the same question with the cheap
# route spent, so the offer is never made twice on one pair and the walk
# always moves.

# Are these two terms the same constant applied to the same number of
# arguments? The levels have to agree as well, since the head carries them.
def Conv.spine_match(+fuel: Nat, +a: T.Term, +b: T.Term) -> Bool:
  Bool.and(
    Bool.and(
      V.Eval.head_is_const(Conv.head(a)),
      V.Eval.head_is_const(Conv.head(b))),
    Bool.and(
      Bool.and(
        Nat.is_eq(
          Conv.head_name(Conv.head(a)), Conv.head_name(Conv.head(b))),
        Conv.levels_eq(
          fuel,
          Conv.head_levels(Conv.head(a)),
          Conv.head_levels(Conv.head(b)))),
      Bool.and(
        Nat.is_eq(
          V.Eval.len(Conv.args(a), 0n), V.Eval.len(Conv.args(b), 0n)),
        Nat.is_lt(0n, V.Eval.len(Conv.args(a), 0n)))))

# One pair per argument, in the context the application lives in.
def Conv.zip_pairs(
  xs: List<&2, T.Term>, ys: List<&2, T.Term>, +ctx: List<&2, T.Term>
) -> List<&2, TPair>:
  match xs ys:
    case Con{x, xr} Con{y, yr}:
      Con{MkPair{ctx, x, y}, Conv.zip_pairs(xr, yr, ctx)}
    case x y:
      Nil{}

def Conv.spine_or(
  spine: Bool, +fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>,
  +a: T.Term, +b: T.Term
) -> Step:
  match spine:
    case True{}:
      SEither{
        Conv.zip_pairs(Conv.args(a), Conv.args(b), ctx),
        [MkDeep{ctx, a, b}]}
    case False{}:
      Conv.classify_work(fuel, env, ctx, a, b)

def Conv.same_or(
  eq: Bool, +fuel: Nat, +env: E.DTable, +ctx: List<&2, T.Term>,
  +a: T.Term, +b: T.Term
) -> Step:
  match eq:
    case True{}:
      SYes{}
    case False{}:
      Conv.spine_or(Conv.spine_match(fuel, a, b), fuel, env, ctx, a, b)

def Conv.classify_pair(+fuel: Nat, +env: E.DTable, p: TPair) -> Step:
  match p:
    case MkPair{+ctx, +a, +b}:
      Conv.same_or(Conv.same(env, a, b), fuel, env, ctx, a, b)
    case MkDeep{+ctx, a, b}:
      Conv.classify_work(fuel, env, ctx, a, b)

# Work the queue. It empties exactly when every pair in it is equal.
#
# The answer so far travels in as a parameter, which buys two things a
# conjunction over the recursive call cannot.
#
# A definite no stops the walk. `A.Ans.and(step, eq_all(..))` had to drain the
# whole queue, because an argument evaluates before the match picks an arm,
# and a helper that matched the step would have to call `eq_all` from above
# it, which is mutual recursion. A parameter can be matched, so the no arm
# returns without the call.
#
# The call is now in tail position. The old one sat inside an argument, so the
# depth of the queue was the depth of the host stack, and a fuel near ten
# thousand overflowed it.
#
# Not knowing one pair leaves the whole answer unknown unless some other pair
# is a definite no, so an unknown keeps the walk going.
def Conv.eq_all(
  +fuel: Nat, +env: E.DTable, acc: A.Ans, alts: List<&2, Alt>,
  work: List<&2, TPair>
) -> A.Ans:
  match fuel:
    case 0n:
      Conv.out_of_fuel(acc, alts)
    case 1n+f:
      match acc alts work:
        case A.ANo{} Nil{} w:
          A.ANo{}
        case A.ANo{} Con{MkAlt{a2, w2}, r2} w:
          Conv.eq_all(f, env, a2, r2, w2)
        case a as Nil{}:
          a
        case +a as Con{p, +rest}:
          +st = Conv.classify_pair(f, env, p)
          Conv.eq_all(
            f, env,
            A.Ans.and(a, Conv.step_ans(st)),
            Conv.step_alts(st, a, rest, as),
            List.append(&2, TPair, Conv.step_more(st), rest))

# Are these two terms definitionally equal in the given context?
def Conv.eq_in(
  +fuel: Nat, +env: E.DTable, ctx: List<&2, T.Term>, a: T.Term, b: T.Term
) -> A.Ans:
  Conv.eq_all(fuel, env, A.AYes{}, Nil{}, [MkPair{ctx, a, b}])

# Conversion, unless the question is already settled.
#
# A conjunction cannot skip its right side, because an argument evaluates
# before the match picks an arm. So the left side arrives as a parameter here,
# and a definite no returns without the conversion work. A declaration whose
# function is not a pi paid for a full conversion pass before this existed.
def Conv.eq_unless_no(
  a: A.Ans, +fuel: Nat, +env: E.DTable, ctx: List<&2, T.Term>, x: T.Term, y: T.Term
) -> A.Ans:
  match a:
    case A.ANo{}:
      A.ANo{}
    case o:
      A.Ans.and(o, Conv.eq_in(fuel, env, ctx, x, y))

# Are these two closed terms definitionally equal?
def Conv.eq(+fuel: Nat, +env: E.DTable, a: T.Term, b: T.Term) -> A.Ans:
  Conv.eq_in(fuel, env, Nil{}, a, b)
