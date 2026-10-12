# Weak head normal form: beta, delta and zeta reduction.
#
# This is one self-recursive def with an explicit argument spine, because Bend
# forbids mutual recursion. The usual shape, where `whnf` reduces the head and
# a second function inspects the result, would be two functions calling each
# other. Carrying the arguments in `sp` instead keeps everything in one def.
#
# `fuel` strictly decreases on every recursive call, which is how this passes
# Bend's termination check. A kernel's whnf genuinely does not terminate on
# every input, so the fuel is not a formality: it is the honest statement that
# this function answers within a budget.
#
# When the budget runs out it hands back `TUnk` rather than the term
# unreduced. The difference matters. An unreduced term looks like an answer,
# and conversion then compares it with something and says they differ, so the
# declaration is rejected for want of budget. `TUnk` says what happened, and
# everything that meets it answers that it does not know.
#
# Every test on a computed value goes through a helper that matches its own
# parameter, since a Bend match may not scrutinize a computed value.

import Base
import ./Level.bend as L
import ./Term.bend as T
import ./Env.bend as E

# Choose between two terms on a computed Bool.
def Eval.pick_t(b: Bool, x: T.Term, y: T.Term) -> T.Term:
  match b:
    case True{}:
      x
    case False{}:
      y

# Apply a term to a spine of arguments, in application order. The spine comes
# first because Bend needs the shrinking parameter in that position.
def Eval.rebuild(sp: List<&2, T.Term>, t: T.Term) -> T.Term:
  match sp:
    case Nil{}:
      t
    case Con{h, r}:
      Eval.rebuild(r, T.TApp{t, h})

# Unwrap a value, or answer the default.
def Eval.val_or(m: Maybe<&2, T.Term>, dflt: T.Term) -> T.Term:
  match m:
    case Some{v}:
      v
    case None{}:
      dflt

# True when a lookup found a declaration that has a value.
def Eval.is_def(lk: E.Lookup) -> Bool:
  match lk:
    case E.LFound{d}:
      E.Decl.is_def(d)
    case E.LMissing{}:
      False{}

# The value a lookup unfolds to, with its level parameters replaced, or the
# default when there is nothing to unfold.
def Eval.unfold_of(lk: E.Lookup, +ls: List<&2, L.Level>, dflt: T.Term) -> T.Term:
  match lk:
    case E.LFound{d}:
      Eval.val_or(E.Decl.value_at(d, ls), dflt)
    case E.LMissing{}:
      dflt

# Iota reduction
# --------------
#
# A recursor applied to a constructor computes. Its arguments come in the
# order the declaration states: parameters, motives, minor premises, indices,
# then the major premise. When the major premise reduces to a constructor,
# the rule for that constructor replaces the whole application.
#
# The right-hand side of a rule expects the recursor's parameters, motives and
# minor premises, then the constructor's fields, which are its arguments past
# its parameters. Whatever followed the major premise is applied after that.

# The position of the major premise among a recursor's arguments.
def Eval.major_idx(+d: E.Decl) -> Nat:
  Nat.add(
    Nat.add(E.Decl.rec_np(d), E.Decl.rec_nm(d)),
    Nat.add(E.Decl.rec_nmin(d), E.Decl.rec_ni(d)))

# How long is this list?
def Eval.len(xs: List<&2, T.Term>, +acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      Eval.len(t, 1n+acc)

# The i-th term, or a sort when the list is too short.
def Eval.nth(xs: List<&2, T.Term>, i: Nat) -> T.Term:
  match xs:
    case Nil{}:
      T.TSort{L.LZero{}}
    case Con{h, t}:
      match i:
        case 0n:
          h
        case 1n+p:
          Eval.nth(t, p)

# The first `n` terms.
def Eval.take(xs: List<&2, T.Term>, n: Nat) -> List<&2, T.Term>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match n:
        case 0n:
          Nil{}
        case 1n+p:
          Con{h, Eval.take(t, p)}

# Everything past the first `n` terms.
def Eval.drop(xs: List<&2, T.Term>, n: Nat) -> List<&2, T.Term>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match n:
        case 0n:
          Con{h, t}
        case 1n+p:
          Eval.drop(t, p)

# Peel an application into its head and its arguments, in order.
def Eval.spine(t: T.Term, +acc: List<&2, T.Term>) -> List<&2, T.Term>:
  match t:
    case T.TApp{f, a}:
      Eval.spine(f, Con{a, acc})
    case x:
      acc

# The head of an application.
def Eval.head(t: T.Term) -> T.Term:
  match t:
    case T.TApp{f, a}:
      Eval.head(f)
    case x:
      x

# The name a head names, or zero. Guard with `Eval.head_is_const`.
def Eval.head_name(t: T.Term) -> Nat:
  match t:
    case T.TConst{n, ls}:
      n
    case x:
      0n

# Is the head of this application a constant?
def Eval.head_is_const(t: T.Term) -> Bool:
  match t:
    case T.TConst{n, ls}:
      True{}
    case x:
      False{}

# Unwrap a rule, or none.
def Eval.rule_ok(m: Maybe<&2, E.RecRule>) -> Bool:
  match m:
    case Some{r}:
      True{}
    case None{}:
      False{}

def Eval.rule_get(m: Maybe<&2, E.RecRule>) -> E.RecRule:
  match m:
    case Some{r}:
      r
    case None{}:
      E.MkRule{0n, 0n, T.TSort{L.LZero{}}}

# Quotients
# ---------
#
# `Quot.lift f h (Quot.mk r a)` reduces to `f a`, and `Quot.ind h (Quot.mk r
# a)` to `h a`. The only difference between them is where the quotient sits
# among the arguments: the sixth for lift and the fifth for ind, with the
# function or the minor premise fourth in both.

# The last term of a list.
def Eval.last_or(xs: List<&2, T.Term>, h: T.Term) -> T.Term:
  match xs:
    case Nil{}:
      h
    case Con{h2, t2}:
      Eval.last_or(t2, h2)

def Eval.last(xs: List<&2, T.Term>) -> T.Term:
  match xs:
    case Nil{}:
      T.TSort{L.LZero{}}
    case Con{h, t}:
      Eval.last_or(t, h)

# Choose between two numbers on a computed Bool.
def Eval.pick_nat(b: Bool, x: Nat, y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

# Where the quotient sits among the arguments. A declaration that is not
# `Quot.lift` or `Quot.ind` answers a position no spine reaches.
def Eval.quot_pos(+d: E.Decl) -> Nat:
  Eval.pick_nat(
    Nat.is_eq(E.Decl.quot_kind(d), 2n),
    5n,
    Eval.pick_nat(Nat.is_eq(E.Decl.quot_kind(d), 3n), 4n, 9999n))

# Can a quotient rule fire? The declaration must be lift or ind with enough
# arguments, and the quotient itself must reduce to `Quot.mk`.
def Eval.quot_ready(
  +env: E.DTable, +d: E.Decl, +sp: List<&2, T.Term>, +mw: T.Term
) -> Bool:
  Bool.and(
    Nat.is_lt(Eval.quot_pos(d), Eval.len(sp, 0n)),
    Nat.is_eq(
      E.Decl.quot_kind(
        E.Lookup.get(E.Env.find(env, Eval.head_name(Eval.head(mw))))),
      1n))

# `f a`, then whatever followed the quotient. A sort when the spine is too
# short to hold a quotient rule, for the same reason as `Eval.major_or_sort`:
# the caller reduces this term, and for a plain definition the unguarded
# version handed back an application of two unrelated arguments, which cost
# the whole remaining fuel.
def Eval.quot_term(+d: E.Decl, +sp: List<&2, T.Term>, +mw: T.Term) -> T.Term:
  Eval.pick_t(
    Nat.is_lt(Eval.quot_pos(d), Eval.len(sp, 0n)),
    Eval.rebuild(
      Eval.drop(sp, 1n+Eval.quot_pos(d)),
      T.TApp{Eval.nth(sp, 3n), Eval.last(Eval.spine(mw, Nil{}))}),
    T.TSort{L.LZero{}})

# A branch of `Eval.pick_t` is evaluated whether or not it is chosen, so a
# branch that is about to be thrown away must still be cheap. These two
# functions make that so: each hands back a term that reduces at once unless
# the branch is the one that matters.
#
# This is not a detail. Without it, the branch that unfolds a definition runs
# on a constant that has no value, where it rebuilds the same constant and
# calls itself again, and every such constant costs the whole remaining fuel.
# That alone was enough to stop the recursion-heavy tests from finishing.

# Is this a recursor with enough arguments to reach its major premise? This is
# the cheap test, and it guards the expensive one. Reducing the major premise
# for every constant, rather than only for a recursor, is what made the
# recursion-heavy tests fail to finish.
def Eval.rec_ready(+d: E.Decl, +sp: List<&2, T.Term>) -> Bool:
  Bool.and(
    E.Decl.is_rec(d),
    Nat.is_lt(Eval.major_idx(d), Eval.len(sp, 0n)))

# The value a declaration unfolds to, or a sort when it has none. The sort is
# never used: the branch that reads it is only chosen for a definition.
def Eval.unfold_decl(+d: E.Decl, +ls: List<&2, L.Level>) -> T.Term:
  Eval.pick_t(
    E.Decl.is_def(d),
    Eval.val_or(E.Decl.value_at(d, ls), T.TSort{L.LZero{}}),
    T.TSort{L.LZero{}})

# The argument a rule needs reduced: a recursor's major premise, or the
# quotient a `Quot.lift` or `Quot.ind` is applied to. A sort when neither
# applies, which is never used, for the same reason.
def Eval.major_or_sort(+d: E.Decl, +sp: List<&2, T.Term>) -> T.Term:
  Eval.pick_t(
    Eval.rec_ready(d, sp),
    Eval.nth(sp, Eval.major_idx(d)),
    Eval.pick_t(
      Nat.is_lt(Eval.quot_pos(d), Eval.len(sp, 0n)),
      Eval.nth(sp, Eval.quot_pos(d)),
      T.TSort{L.LZero{}}))

# Can iota fire here? The declaration must be a recursor, the spine must reach
# the major premise, and the reduced major premise must be a constructor this
# recursor has a rule for.
def Eval.can_iota(+d: E.Decl, +sp: List<&2, T.Term>, +mw: T.Term) -> Bool:
  Bool.and(
    Eval.rec_ready(d, sp),
    Bool.and(
      Eval.head_is_const(Eval.head(mw)),
      Eval.rule_ok(
        E.Decl.rule_for(E.Decl.rec_rules(d), Eval.head_name(Eval.head(mw))))))

# The term a fired rule reduces to. Guard with `Eval.can_iota`.
#
# The constructor's fields are its arguments past its own parameters, and the
# count to drop is the **constructor's**, not the recursor's. For a block with
# no nested inductive the two are the same number, which is why reading the
# recursor's worked for every file in the arena's small set but one.
#
# `init-prelude` is that one. `Lean.Syntax.rec_2` eliminates a nested block
# and states no parameters, while the auxiliary constructor `Array.mk` has
# one, so dropping the recursor's zero took the type argument for the field.
# The rule then never fired, the term stayed stuck, and conversion compared a
# stuck application against a `PProd` and called them different.
def Eval.iota_term(
  +env: E.DTable, +d: E.Decl, +ls: List<&2, L.Level>,
  +sp: List<&2, T.Term>, +mw: T.Term
) -> T.Term:
  +rule = Eval.rule_get(
    E.Decl.rule_for(E.Decl.rec_rules(d), Eval.head_name(Eval.head(mw))))
  Eval.rebuild(
    List.append(&2, T.Term,
      Eval.take(
        Eval.drop(
          Eval.spine(mw, Nil{}),
          E.Decl.ctor_np(
            E.Lookup.get(
              E.Env.find(env, Eval.head_name(Eval.head(mw)))))),
        E.RecRule.nfields(rule)),
      Eval.drop(sp, 1n+Eval.major_idx(d))),
    Eval.rebuild(
      Eval.take(
        sp,
        Nat.add(
          Nat.add(E.Decl.rec_np(d), E.Decl.rec_nm(d)),
          E.Decl.rec_nmin(d))),
      T.Term.subst_levels(E.RecRule.rhs(rule), ls)))

# The level arguments of a head constant.
def Eval.head_levels(t: T.Term) -> List<&2, L.Level>:
  match t:
    case T.TConst{n, ls}:
      ls
    case x:
      Nil{}

# Projections
# -----------
#
# A projection of a structure reduces when the structure does. If `s` reduces
# to its constructor applied to the parameters and then the fields, the
# `idx`-th field is the answer. The constructor's own parameters come first
# and are skipped.

# Is this reduced structure a constructor application with the field present?
def Eval.proj_ready(+env: E.DTable, +idx: Nat, +sw: T.Term) -> Bool:
  Bool.and(
    E.Decl.is_ctor(E.Lookup.get(E.Env.find(env, Eval.head_name(Eval.head(sw))))),
    Nat.is_lt(
      Nat.add(
        E.Decl.ctor_np(
          E.Lookup.get(E.Env.find(env, Eval.head_name(Eval.head(sw))))),
        idx),
      Eval.len(Eval.spine(sw, Nil{}), 0n)))

# The field itself. Guard with `Eval.proj_ready`.
def Eval.proj_field(+env: E.DTable, +idx: Nat, +sw: T.Term) -> T.Term:
  Eval.nth(
    Eval.spine(sw, Nil{}),
    Nat.add(
      E.Decl.ctor_np(
        E.Lookup.get(E.Env.find(env, Eval.head_name(Eval.head(sw))))),
      idx))

# Native arithmetic on two literals.
# ---------------------------------
#
# The arena enables a native `Nat`. A literal is one term, and the kernel
# computes on two of them rather than unfolding the Lean definition. Without
# this a literal has to be a tower of `Nat.succ`, and the arena's own numbers
# do not fit in one: `Nat.sub 1000001 1000000` would take a million steps to
# build and a million more to reduce.
#
# The rule fires only when both arguments are literals. When one is not, the
# definition is still in the environment and unfolds as it always did.

# The value of a literal, or zero.
def Eval.nat_val(t: T.Term) -> Nat:
  match t:
    case T.TNat{v, nm, zr, sc}:
      v
    case x:
      0n

# Is this term a literal?
def Eval.is_nat(t: T.Term) -> Bool:
  match t:
    case T.TNat{v, nm, zr, sc}:
      True{}
    case x:
      False{}

# The three names a literal carries, or zero.
def Eval.nat_name(t: T.Term) -> Nat:
  match t:
    case T.TNat{v, nm, zr, sc}:
      nm
    case x:
      0n

def Eval.nat_zr(t: T.Term) -> Nat:
  match t:
    case T.TNat{v, nm, zr, sc}:
      zr
    case x:
      0n

def Eval.nat_sc(t: T.Term) -> Nat:
  match t:
    case T.TNat{v, nm, zr, sc}:
      sc
    case x:
      0n

# A literal as a constructor application: zero, or the successor of one less.
# Any other term comes back unchanged, which is what makes this cheap enough
# to put on the path every reduction takes.
#
# A recursor needs its major premise in constructor form, and so does the
# comparison in `Conv`. Going the other way, from a tower of successors to a
# literal, is not needed: no export writes one.
def Eval.lit_ctor(t: T.Term) -> T.Term:
  match t:
    case T.TNat{v, +nm, +zr, +sc}:
      match v:
        case 0n:
          T.TConst{zr, Nil{}}
        case 1n+k:
          T.TApp{T.TConst{sc, Nil{}}, T.TNat{k, nm, zr, sc}}
    case x:
      x

# Choose one of eight numbers on an op code. Code zero and anything past the
# eighth answer zero; `Eval.prim_ready` has already ruled those out.
# The largest number this kernel will compute.
#
# Bend's immediate holds up to 2^48-1 and the runtime stops the program dead
# past it: `a Nat past the largest immediate 2^48-1`. A crash is the one
# answer worse than not knowing, and the prelude reaches it. `UInt64.size` is
# `2 ^ 64`, and the native power computed it.
#
# This is 2^47. Every operation below is guarded so that it never forms a
# number past this, and `Eval.prim_fits` turns a result at the cap into the
# unknown term, so a file that needs `2 ^ 64` declines rather than dies.
# `2 ^ 32`, which `Char` and `UInt32` need, is far below it.
# A `Nat` literal in Bend source stops at 2^32-1, so this is written as a
# product.
def Eval.num_cap() -> Nat:
  Nat.mul(1073741824n, 131072n)

def Eval.mul_pick(ok: Bool, +a: Nat, +b: Nat) -> Nat:
  match ok:
    case True{}:
      Nat.mul(a, b)
    case False{}:
      Eval.num_cap()

# A product, or the cap. The test is a division, so the product is formed only
# when it fits.
def Eval.mul_cap(+a: Nat, +b: Nat) -> Nat:
  Eval.mul_pick(
    Bool.or(
      Nat.is_eq(b, 0n),
      Nat.is_le(a, Nat.div(Eval.num_cap(), b))),
    a, b)

def Eval.add_pick(ok: Bool, +a: Nat, +b: Nat) -> Nat:
  match ok:
    case True{}:
      Nat.add(a, b)
    case False{}:
      Eval.num_cap()

def Eval.add_cap(+a: Nat, +b: Nat) -> Nat:
  Eval.add_pick(Nat.is_le(a, Nat.sub(Eval.num_cap(), b)), a, b)

# `x` to the `y`, capped. Once the running value reaches the cap it stays
# there, because the cap is not below the cap divided by anything above one.
def Eval.pow_cap(+x: Nat, y: Nat, +acc: Nat) -> Nat:
  match y:
    case 0n:
      acc
    case 1n+k:
      Eval.pow_cap(x, k, Eval.mul_cap(acc, x))

# Division by zero is zero, as Lean defines it, and the same for the
# remainder. Bend's own division does not promise that.
def Eval.div_pick(ok: Bool, +a: Nat, +b: Nat) -> Nat:
  match ok:
    case True{}:
      Nat.div(a, b)
    case False{}:
      0n

def Eval.mod_pick(ok: Bool, +a: Nat, +b: Nat) -> Nat:
  match ok:
    case True{}:
      Nat.mod(a, b)
    case False{}:
      0n

def Eval.prim_num(+op: Nat, +x: Nat, +y: Nat) -> Nat:
  match op:
    case 1n:
      Eval.add_cap(x, y)
    case 2n:
      Nat.sub(x, y)
    case 3n:
      Eval.mul_cap(x, y)
    case 4n:
      Eval.div_pick(Bool.not(Nat.is_eq(y, 0n)), x, y)
    case 5n:
      Eval.mod_pick(Bool.not(Nat.is_eq(y, 0n)), x, y)
    case 8n:
      Eval.pow_cap(x, y, 1n)
    case o:
      0n

# Does this op answer a `Bool` rather than a number?
def Eval.prim_cmp(+op: Nat) -> Bool:
  Bool.or(Nat.is_eq(op, 6n), Nat.is_eq(op, 7n))

# Choose between two Bools on a computed Bool.
# Does this operation's answer fit? A comparing op always does, and a number
# that reached the cap did not.
def Eval.prim_fits(+op: Nat, +x: Nat, +y: Nat) -> Bool:
  Bool.or(
    Eval.prim_cmp(op),
    Nat.is_lt(Eval.prim_num(op, x, y), Eval.num_cap()))

def Eval.pick_b(b: Bool, x: Bool, y: Bool) -> Bool:
  match b:
    case True{}:
      x
    case False{}:
      y

# The answer of a comparing op.
def Eval.prim_bool(+op: Nat, +x: Nat, +y: Nat) -> Bool:
  Eval.pick_b(Nat.is_eq(op, 6n), Nat.is_eq(x, y), Nat.is_le(x, y))

# Is this declaration one the kernel computes, with two arguments to work on?
def Eval.prim_at(+d: E.Decl, +sp: List<&2, T.Term>) -> Bool:
  Bool.and(
    Bool.not(Nat.is_eq(E.Decl.prim_op(d), 0n)),
    Nat.is_le(2n, Eval.len(sp, 0n)))

# The `i`-th argument a native rule needs, or a sort when there is no rule
# here. The caller reduces this, and the arena writes a literal as
# `OfNat.ofNat Nat 1000000 ..` rather than bare, so reducing is what turns an
# argument into the literal the rule needs. The sort keeps every other
# constant from paying for that.
def Eval.prim_arg(+d: E.Decl, +sp: List<&2, T.Term>, +i: Nat) -> T.Term:
  Eval.pick_t(Eval.prim_at(d, sp), Eval.nth(sp, i), T.TSort{L.LZero{}})

# Can a native rule fire? The declaration must carry one, the spine must hold
# at least two arguments, and both must have reduced to literals.
def Eval.prim_ready(
  +d: E.Decl, +sp: List<&2, T.Term>, +x: T.Term, +y: T.Term
) -> Bool:
  Bool.and(
    Eval.prim_at(d, sp),
    Bool.and(Eval.is_nat(x), Eval.is_nat(y)))

# The answer, with whatever followed the two arguments still applied. A sort
# when the rule cannot fire, because a branch of `Eval.pick_t` is evaluated
# whether or not it is chosen and the caller reduces this.
# The number, or the unknown term when it does not fit.
def Eval.prim_fit_term(
  fits: Bool, +op: Nat, +x: T.Term, +y: T.Term
) -> T.Term:
  match fits:
    case False{}:
      T.TUnk{}
    case True{}:
      T.TNat{
        Eval.prim_num(op, Eval.nat_val(x), Eval.nat_val(y)),
        Eval.nat_name(x),
        Eval.nat_zr(x),
        Eval.nat_sc(x)}

def Eval.prim_term(
  +d: E.Decl, +sp: List<&2, T.Term>, +x: T.Term, +y: T.Term
) -> T.Term:
  Eval.pick_t(
    Eval.prim_ready(d, sp, x, y),
    Eval.rebuild(
      Eval.drop(sp, 2n),
      Eval.pick_t(
        Eval.prim_cmp(E.Decl.prim_op(d)),
        T.TConst{
          Eval.pick_nat(
            Eval.prim_bool(
              E.Decl.prim_op(d), Eval.nat_val(x), Eval.nat_val(y)),
            E.Decl.prim_yes(d),
            E.Decl.prim_no(d)),
          Nil{}},
        Eval.prim_fit_term(
          Eval.prim_fits(
            E.Decl.prim_op(d), Eval.nat_val(x), Eval.nat_val(y)),
          E.Decl.prim_op(d), x, y))),
    T.TSort{L.LZero{}})

# Reduce `t` applied to `sp` to weak head normal form.
#
# When the premise a rule needs cannot be reduced, because the budget ran out,
# the answer is `TUnk` and not the constant rebuilt. A rebuilt constant looks
# stuck, and two stuck terms that differ are a definite no, so without this a
# shortage of budget is reported as a rejection. The projection case has
# always done this; the constant case did not, and that is what made the
# arena's `beta-ladder` and `folded-constant-first` reject.
# How deep a chain of references may run. The table never stores a bare
# reference, so one step is enough and this is only a bound.
def Eval.deref_budget() -> Nat:
  64n

# Resolve a reference against the table.
#
# This is deliberately outside the reduction budget. Resolving is not a
# reduction step, and charging the declaration's fuel for it was expensive
# enough to matter: `perf/church-numerals` went from accepted to out of budget
# when every resolution cost a step.
#
# The resolution happens in the caller rather than in an arm of `Eval.whnf`,
# because an arm would have to call `Eval.whnf` again and Bend needs a
# shrinking argument for that. So every call hands `Eval.whnf` a term whose
# head is already resolved, and `Eval.whnf` needs no arm for a reference at
# all.
def Eval.deref(+n: Nat, +env: E.DTable, t: T.Term) -> T.Term:
  match n:
    case 0n:
      t
    case 1n+k:
      match t:
        case T.TRef{+i, +sh, m}:
          Eval.deref(k, env, E.Env.expr_at(env, i, sh))
        case o:
          o

def Eval.dr(+env: E.DTable, t: T.Term) -> T.Term:
  Eval.deref(Eval.deref_budget(), env, t)

def Eval.whnf(+fuel: Nat, +env: E.DTable, t: T.Term, +sp: List<&2, T.Term>) -> T.Term:
  match fuel:
    case 0n:
      T.TUnk{}
    case 1n+f:
      match t:
        case T.TVar{i}:
          Eval.rebuild(sp, T.TVar{i})
        case T.TSort{l}:
          Eval.rebuild(sp, T.TSort{l})
        case T.TConst{+n, +ls}:
          +d = E.Lookup.get(E.Env.find(env, n))
          +mw = Eval.lit_ctor(Eval.whnf(f, env, Eval.dr(env, Eval.major_or_sort(d, sp)), Nil{}))
          +px = Eval.whnf(f, env, Eval.dr(env, Eval.prim_arg(d, sp, 0n)), Nil{})
          +py = Eval.whnf(f, env, Eval.dr(env, Eval.prim_arg(d, sp, 1n)), Nil{})
          Eval.pick_t(
            Eval.prim_ready(d, sp, px, py),
            Eval.whnf(f, env, Eval.dr(env, Eval.prim_term(d, sp, px, py)), Nil{}),
            Eval.pick_t(
            E.Decl.is_def(d),
            Eval.whnf(f, env, Eval.dr(env, Eval.unfold_decl(d, ls)), sp),
            Eval.pick_t(
              T.Term.is_unk(mw),
              T.TUnk{},
              Eval.pick_t(
              Eval.can_iota(d, sp, mw),
              Eval.whnf(f, env, Eval.dr(env, Eval.iota_term(env, d, ls, sp, mw)), Nil{}),
              Eval.pick_t(
                Eval.quot_ready(env, d, sp, mw),
                Eval.whnf(f, env, Eval.dr(env, Eval.quot_term(d, sp, mw)), Nil{}),
                Eval.rebuild(sp, T.TConst{n, ls}))))))
        case T.TApp{g, a}:
          Eval.whnf(f, env, Eval.dr(env, g), Con{a, sp})
        case T.TLam{ty, bd}:
          match sp:
            case Nil{}:
              T.TLam{ty, bd}
            case Con{a, rest}:
              Eval.whnf(
                f, env,
                Eval.dr(env, T.Term.inst_at(E.Env.tab(env), bd, a)), rest)
        case T.TPi{ty, bd}:
          Eval.rebuild(sp, T.TPi{ty, bd})
        case T.TLet{ty, v, bd}:
          Eval.whnf(
            f, env, Eval.dr(env, T.Term.inst_at(E.Env.tab(env), bd, v)), sp)
        case T.TNat{v, nm, zr, sc}:
          Eval.rebuild(sp, T.TNat{v, nm, zr, sc})
        case T.TUnk{}:
          T.TUnk{}
        case T.TRef{+i, +k, m}:
          # A caller that did not resolve first. Every call inside this def
          # resolves, so this fires once for a term handed in from outside and
          # costs one step, not one step per use.
          Eval.whnf(f, env, E.Env.expr_at(env, i, k), sp)
        case T.TProj{tn, +idx, st}:
          +sw = Eval.lit_ctor(Eval.whnf(f, env, Eval.dr(env, st), Nil{}))
          Eval.pick_t(
            T.Term.is_unk(sw),
            T.TUnk{},
            Eval.pick_t(
              Eval.proj_ready(env, idx, sw),
              Eval.whnf(f, env, Eval.dr(env, Eval.proj_field(env, idx, sw)), sp),
              Eval.rebuild(sp, T.TProj{tn, idx, sw})))
