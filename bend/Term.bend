# Lean terms, with de Bruijn indices.
#
# A constant is a Nat id rather than a name, for the same reason levels use an
# index: a Bend string is a linked list of characters.
#
# `TLam` and `TPi` carry the binder's type and the body. The binder's name is
# not kept, because nothing here prints a term back to the user.

import Base
import ./Level.bend as L
import ./Idx.bend as Ix

type Term is Data:
  TVar{i: Nat}
  TSort{l: L.Level}
  TConst{n: Nat, ls: List<&2, L.Level>}
  TApp{f: Term, a: Term}
  TLam{ty: Term, bd: Term}
  TPi{ty: Term, bd: Term}
  TLet{ty: Term, v: Term, bd: Term}
  # The `idx`-th field of a structure. `tn` is the inductive's name, which the
  # export carries and which the type of the field is read from.
  TProj{tn: Nat, idx: Nat, s: Term}
  # A `Nat` literal, with the name the export gives the type `Nat`.
  #
  # The arena enables a native `Nat`, where a literal is one term rather than
  # a tower of `Nat.succ`, and arithmetic on two of them is a rule of the
  # kernel. A tower cannot hold the arena's own numbers: `1000000` is one of
  # them. The name travels in the term because inference has to answer with
  # it and has no other way to learn it. `zr` and `sc` are the names of
  # `Nat.zero` and `Nat.succ`, which let a literal be written as a
  # constructor application when a recursor or a comparison needs one.
  TNat{v: Nat, nm: Nat, zr: Nat, sc: Nat}
  # A `String` literal, with the name the export gives the type `String`.
  #
  # Lean's own kernel expands one to the constructor application it stands
  # for when a rule needs its parts. That form is not available here: in the
  # Lean this corpus was exported from, `String` is a structure over a
  # `ByteArray` with a proof that the bytes are valid UTF-8, so its
  # constructor takes a proof and a kernel cannot write one. There is no
  # `String.mk` in any export of the corpus.
  #
  # So the literal is a term of its own, and an opaque one. Its type is
  # `String`, two literals are equal when their bytes are, and anything that
  # needs its parts -- a projection of it, a recursor on it -- answers the
  # unknown term. A file that computes with a string therefore declines,
  # which is the answer this kernel is entitled to, and a file that only
  # names one goes through: `String.instInhabited` is `Inhabited.mk String
  # ""`, and it is where two of the magma files stopped.
  TStr{sn: Nat, bs: List<&2, U32>}
  # A `Nat` literal that a machine word does not hold, as a list of digits
  # in base 2^24. See `bend/Big.bend` for why there is one: the prelude
  # writes `18446744073709551616`, and a Bend `Nat` stops at 2^48-1.
  #
  # The form is canonical. A number that fits below `Bytes.nat_cap` is a
  # `TNat` and never this, so the two forms are never two spellings of one
  # number -- but the comparison does not rely on that, it compares the
  # digits with the word.
  TBig{ds: List<&2, Nat>, nm: Nat, zr: Nat, sc: Nat}
  # The term reduction gives back when it runs out of budget.
  #
  # Running out is not an answer. A kernel that treats it as one reports
  # falsely: it rejects a declaration it merely failed to reduce far enough.
  # So reduction hands back this instead, and everything that meets it answers
  # "I do not know" rather than yes or no.
  TUnk{}
  # A reference to an expression of the export's own table.
  #
  # The table holds each expression once, and the export's expressions form a
  # graph: one expression is named by many others. This kernel read that graph
  # as a tree, which copies a subterm once per reference, because Bend is
  # affine and a value read twice is copied. An 869 kB export built 206
  # million nodes that way, and a 1.3 MB one could not be read at all.
  #
  # A reference is one word. `Eval.whnf` resolves it against the table, and
  # what it finds has references for its own children, so every step is
  # shallow.
  #
  # `i` names the entry. `k` is a shift: a free variable of the entry stands
  # for the variable `k` higher here. `m` bounds the entry's own free
  # variables, so the variables this reference uses are the ones from `k` up
  # to `k + m`, and an entry with `m` of zero is closed.
  #
  # Those two numbers are what let a reference stand for an **open**
  # expression, which is 94 to 99 percent of what a large export holds. A
  # closed reference alone took the stored table of `perf/app-lam` from
  # 10^17 nodes to 10^17 nodes, because the entry that is copied is the open
  # one. With the shift it stores 65 thousand.
  #
  # The parser emits one only for an expression with no level parameter in
  # it. A level-free term needs no remapping, and the remapping is per
  # declaration while the table is shared by all of them.
  TRef{i: Nat, k: Nat, m: Nat}

# The export's table of expressions.
#
# This is a binary trie on the bits of the index, holding a value at every
# node. It stands here rather than in `Table.bend` because `Term.subst` and
# `Term.lift` must resolve a reference, and `Table.bend` imports this file.
type ETable is Data:
  ExTip{}
  ExNode{v: Maybe<&2, Term>, lo: ETable, hi: ETable}

def ETable.new() -> ETable:
  ExTip{}

# A slot nothing was written to answers the unknown term, so a line that names
# an expression the export never wrote is not mistaken for a real one.
def ETable.or_unk(m: Maybe<&2, Term>) -> Term:
  match m:
    case None{}:
      TUnk{}
    case Some{v}:
      v

def ETable.at(t: ETable) -> Term:
  match t:
    case ExTip{}:
      TUnk{}
    case ExNode{v, lo, hi}:
      ETable.or_unk(v)

def ETable.get(n: Nat, stop: Bool, b: Bool, t: ETable, +i: Nat) -> Term:
  match n:
    case 0n:
      TUnk{}
    case 1n+m:
      match stop:
        case True{}:
          ETable.at(t)
        case False{}:
          match b:
            case True{}:
              match t:
                case ExTip{}:
                  TUnk{}
                case ExNode{v, lo, hi}:
                  ETable.get(
                    m, Ix.Idx.here(Ix.Idx.rest(i)), Ix.Idx.low(Ix.Idx.rest(i)),
                    lo, Ix.Idx.rest(i))
            case False{}:
              match t:
                case ExTip{}:
                  TUnk{}
                case ExNode{v, lo, hi}:
                  ETable.get(
                    m, Ix.Idx.here(Ix.Idx.rest(i)), Ix.Idx.low(Ix.Idx.rest(i)),
                    hi, Ix.Idx.rest(i))

def ETable.set(n: Nat, stop: Bool, b: Bool, t: ETable, +i: Nat, +v: Term) -> ETable:
  match n:
    case 0n:
      t
    case 1n+m:
      match stop:
        case True{}:
          match t:
            case ExTip{}:
              ExNode{Some{v}, ExTip{}, ExTip{}}
            case ExNode{o, lo, hi}:
              ExNode{Some{v}, lo, hi}
        case False{}:
          match b:
            case True{}:
              match t:
                case ExTip{}:
                  ExNode{
                    None{},
                    ETable.set(
                      m, Ix.Idx.here(Ix.Idx.rest(i)), Ix.Idx.low(Ix.Idx.rest(i)),
                      ExTip{}, Ix.Idx.rest(i), v),
                    ExTip{}}
                case ExNode{o, lo, hi}:
                  ExNode{
                    o,
                    ETable.set(
                      m, Ix.Idx.here(Ix.Idx.rest(i)), Ix.Idx.low(Ix.Idx.rest(i)),
                      lo, Ix.Idx.rest(i), v),
                    hi}
            case False{}:
              match t:
                case ExTip{}:
                  ExNode{
                    None{},
                    ExTip{},
                    ETable.set(
                      m, Ix.Idx.here(Ix.Idx.rest(i)), Ix.Idx.low(Ix.Idx.rest(i)),
                      ExTip{}, Ix.Idx.rest(i), v)}
                case ExNode{o, lo, hi}:
                  ExNode{
                    o,
                    lo,
                    ETable.set(
                      m, Ix.Idx.here(Ix.Idx.rest(i)), Ix.Idx.low(Ix.Idx.rest(i)),
                      hi, Ix.Idx.rest(i), v)}

def Term.read_ex(+t: ETable, +i: Nat) -> Term:
  ETable.get(
    Ix.Idx.bits(), Ix.Idx.here(Ix.Idx.path(i)), Ix.Idx.low(Ix.Idx.path(i)),
    t, Ix.Idx.path(i))

def Term.write_ex(+t: ETable, +i: Nat, +v: Term) -> ETable:
  ETable.set(
    Ix.Idx.bits(), Ix.Idx.here(Ix.Idx.path(i)), Ix.Idx.low(Ix.Idx.path(i)),
    t, Ix.Idx.path(i), v)

# Choose between two terms on a computed Bool.
def Term.pick(b: Bool, x: Term, y: Term) -> Term:
  match b:
    case True{}:
      x
    case False{}:
      y

# Structural equality of two level lists.
def Term.same_levels(xs: List<&2, L.Level>, ys: List<&2, L.Level>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xr} Con{y, yr}:
      Bool.and(L.Level.same(x, y), Term.same_levels(xr, yr))
    case x y:
      False{}

# Is this the term reduction gives back when it runs out of budget?
def Term.is_unk(t: Term) -> Bool:
  match t:
    case TUnk{}:
      True{}
    case x:
      False{}

# Does this term hold the term reduction gives back when it runs out of
# budget, anywhere inside it?
#
# A read back that is given a small budget stops where the budget stops and
# leaves this term behind, so the answer is how to tell a term that was read
# back whole from one that was cut off. Out of budget answers yes, which is
# the safe side: a verdict is never read off a term reduction gave up on.
# Two string literals hold the same bytes.
def Term.bytes_same(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xr} Con{y, yr}:
      Bool.and(U32.is_eq(x, y), Term.bytes_same(xr, yr))
    case x y:
      False{}

def Term.is_big(t: Term) -> Bool:
  match t:
    case TBig{ds, nm, zr, sc}:
      True{}
    case o:
      False{}

def Term.big_ds(t: Term) -> List<&2, Nat>:
  match t:
    case TBig{+ds, nm, zr, sc}:
      ds
    case o:
      Nil{}

def Term.is_str(t: Term) -> Bool:
  match t:
    case TStr{sn, bs}:
      True{}
    case TBig{ds, nm, zr, sc}:
      True{}
    case o:
      False{}

def Term.str_name(t: Term) -> Nat:
  match t:
    case TStr{+sn, bs}:
      sn
    case o:
      0n

def Term.str_bytes(t: Term) -> List<&2, U32>:
  match t:
    case TStr{sn, +bs}:
      bs
    case o:
      Nil{}

def Term.any_unk(+fuel: Nat, t: Term) -> Bool:
  match fuel:
    case 0n:
      True{}
    case 1n+(+f):
      match t:
        case TUnk{}:
          True{}
        case TVar{i}:
          False{}
        case TSort{l}:
          False{}
        case TNat{v, nm, zr, sc}:
          False{}
        case TStr{sn, bs}:
          False{}
        case TBig{ds, nm, zr, sc}:
          False{}
        case TConst{n, ls}:
          False{}
        case TRef{i, k, m}:
          False{}
        case TApp{+g, +a}:
          Bool.or(Term.any_unk(f, g), Term.any_unk(f, a))
        case TLam{+ty, +bd}:
          Bool.or(Term.any_unk(f, ty), Term.any_unk(f, bd))
        case TPi{+ty, +bd}:
          Bool.or(Term.any_unk(f, ty), Term.any_unk(f, bd))
        case TLet{+ty, +v, +bd}:
          Bool.or(
            Term.any_unk(f, ty),
            Bool.or(Term.any_unk(f, v), Term.any_unk(f, bd)))
        case TProj{tn, idx, +st}:
          Term.any_unk(f, st)

# How many binders a telescope opens with. The result type of a constructor
# is an application of its inductive and never a pi, so this counts exactly
# the parameters and the fields.
def Term.pi_count(t: Term, +acc: Nat) -> Nat:
  match t:
    case TPi{ty, bd}:
      Term.pi_count(bd, 1n+acc)
    case x:
      acc

# What a telescope reaches after `n` binders, read as syntax and with no
# reduction. The binders are left open: the callers of this ask only whether
# what they reach is a sort, and a sort is closed.
def Term.pi_skip(n: Nat, t: Term) -> Term:
  match n:
    case 0n:
      t
    case 1n+m:
      match t:
        case TPi{ty, bd}:
          Term.pi_skip(m, bd)
        case x:
          x

# Does the constant `n` appear anywhere in this term?
def Term.occurs(t: Term, +n: Nat) -> Bool:
  match t:
    case TConst{m, ls}:
      Nat.is_eq(m, n)
    case TApp{f, a}:
      Bool.or(Term.occurs(f, n), Term.occurs(a, n))
    case TLam{ty, bd}:
      Bool.or(Term.occurs(ty, n), Term.occurs(bd, n))
    case TPi{ty, bd}:
      Bool.or(Term.occurs(ty, n), Term.occurs(bd, n))
    case TLet{ty, v, bd}:
      Bool.or(
        Term.occurs(ty, n),
        Bool.or(Term.occurs(v, n), Term.occurs(bd, n)))
    case TProj{tn, idx, st}:
      Term.occurs(st, n)
    case x:
      False{}

# Does the constant `n` appear in any of these terms?

def Term.occurs_any(ts: List<&2, Term>, +n: Nat) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Term.occurs(h, n), Term.occurs_any(t, n))

# Is every level parameter in this list one of the first `n`?
def Term.pars_ok_levels(ls: List<&2, L.Level>, +n: Nat) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(L.Level.pars_ok(h, n), Term.pars_ok_levels(t, n))

# Is every level parameter in this term one of the first `n`?
#
# A declaration that names a universe it did not declare is rejected by the
# Lean kernel, and `Level.param_pos` leaves a marker for one, so this is where
# the marker is caught.
def Term.pars_ok(t: Term, +n: Nat) -> Bool:
  match t:
    case TVar{i}:
      True{}
    case TSort{l}:
      L.Level.pars_ok(l, n)
    case TConst{m, ls}:
      Term.pars_ok_levels(ls, n)
    case TApp{f, a}:
      Bool.and(Term.pars_ok(f, n), Term.pars_ok(a, n))
    case TLam{ty, bd}:
      Bool.and(Term.pars_ok(ty, n), Term.pars_ok(bd, n))
    case TPi{ty, bd}:
      Bool.and(Term.pars_ok(ty, n), Term.pars_ok(bd, n))
    case TLet{ty, v, bd}:
      Bool.and(
        Bool.and(Term.pars_ok(ty, n), Term.pars_ok(v, n)),
        Term.pars_ok(bd, n))
    case TNat{v, m, z, c}:
      True{}
    case TStr{sn, bs}:
      True{}
    case TBig{ds, nm, zr, sc}:
      True{}
    case TUnk{}:
      True{}
    case TProj{tn, idx, st}:
      Term.pars_ok(st, n)
    case TRef{i, k, m}:
      True{}

# Does this term hold a variable bound `d` binders out or further?
#
# With `d` at zero that asks whether the term is closed. The parser asks it of
# every expression it stores, because a closed and level-free expression is
# one a reference may stand for. A reference answers no, which is sound and is
# what makes the test cost nothing: an entry whose children are references is
# a shallow node.
def Term.has_free(t: Term, +d: Nat) -> Bool:
  match t:
    case TVar{+i}:
      Nat.is_le(d, i)
    case TSort{l}:
      False{}
    case TConst{n, ls}:
      False{}
    case TApp{f, a}:
      Bool.or(Term.has_free(f, d), Term.has_free(a, d))
    case TLam{ty, bd}:
      Bool.or(Term.has_free(ty, d), Term.has_free(bd, 1n+d))
    case TPi{ty, bd}:
      Bool.or(Term.has_free(ty, d), Term.has_free(bd, 1n+d))
    case TLet{ty, v, bd}:
      Bool.or(
        Bool.or(Term.has_free(ty, d), Term.has_free(v, d)),
        Term.has_free(bd, 1n+d))
    case TNat{v, m, z, c}:
      False{}
    case TStr{sn, bs}:
      False{}
    case TBig{ds, nm, zr, sc}:
      False{}
    case TUnk{}:
      False{}
    case TProj{tn, idx, st}:
      Term.has_free(st, d)
    case TRef{i, +k, +m}:
      Bool.and(Nat.is_lt(0n, m), Nat.is_lt(d, Nat.add(k, m)))

# Does this term use the variable bound `d` binders out?
#
# The Lean kernel calls this a loose bound variable. A projection out of a
# proposition needs it: a field before the one projected has to be a proof
# only when the rest of the constructor's telescope uses it.

def Term.has_bvar(t: Term, +d: Nat) -> Bool:
  match t:
    case TVar{+i}:
      Nat.is_eq(i, d)
    case TSort{l}:
      False{}
    case TConst{n, ls}:
      False{}
    case TApp{f, a}:
      Bool.or(Term.has_bvar(f, d), Term.has_bvar(a, d))
    case TLam{ty, bd}:
      Bool.or(Term.has_bvar(ty, d), Term.has_bvar(bd, 1n+d))
    case TPi{ty, bd}:
      Bool.or(Term.has_bvar(ty, d), Term.has_bvar(bd, 1n+d))
    case TLet{ty, v, bd}:
      Bool.or(
        Bool.or(Term.has_bvar(ty, d), Term.has_bvar(v, d)),
        Term.has_bvar(bd, 1n+d))
    case TNat{v, m, z, c}:
      False{}
    case TStr{sn, bs}:
      False{}
    case TBig{ds, nm, zr, sc}:
      False{}
    case TUnk{}:
      False{}
    case TProj{tn, idx, st}:
      Term.has_bvar(st, d)
    case TRef{i, +k, +m}:
      Bool.and(Nat.is_le(k, d), Nat.is_lt(d, Nat.add(k, m)))

def Term.nat_pick(b: Bool, +x: Nat, +y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

# One less, and zero stays zero.
def Term.drop1(+n: Nat) -> Nat:
  Term.nat_pick(Nat.is_eq(n, 0n), 0n, Nat.sub(n, 1n))

# The variables a reference uses are the ones from `k` up to `k + m`, so a
# reference with `m` of zero uses none of them however large `k` is.
def Term.ref_bound(+k: Nat, +m: Nat) -> Nat:
  Term.nat_pick(Nat.is_eq(m, 0n), 0n, Nat.add(k, m))

# One more than the largest free variable, and zero for a closed term.
#
# The parser records this for every expression it stores, because it is what
# a reference to an open expression carries: it says when a lift or a
# substitution may leave the reference alone.
def Term.max_free(t: Term) -> Nat:
  match t:
    case TVar{+i}:
      1n+i
    case TApp{f, a}:
      Nat.max(Term.max_free(f), Term.max_free(a))
    case TLam{ty, bd}:
      Nat.max(Term.max_free(ty), Term.drop1(Term.max_free(bd)))
    case TPi{ty, bd}:
      Nat.max(Term.max_free(ty), Term.drop1(Term.max_free(bd)))
    case TLet{ty, v, bd}:
      Nat.max(
        Nat.max(Term.max_free(ty), Term.max_free(v)),
        Term.drop1(Term.max_free(bd)))
    case TProj{tn, idx, st}:
      Term.max_free(st)
    case TRef{i, +k, +m}:
      Term.ref_bound(k, m)
    case o:
      0n

# What a lift or a substitution does to a reference.
#
# The variables a reference uses are the ones from `k` up to `k + m`. If the
# cutoff falls outside that range, every variable moves the same way and the
# reference answers in one step, which is the whole point of it. If the
# cutoff falls inside, some move and some do not, and no single shift says
# that: the entry has to be read and walked.
type RefAct is Data:
  # No variable of the reference reaches the cutoff.
  RKeep{}
  # Every one does.
  RShift{}
  # Some do and some do not, so the entry has to be read and walked.
  RExpand{}
  # The same, for an entry that needs no shift. A reference the parser wrote
  # carries a shift of zero, so this is the common one, and it saves a walk
  # of the entry that would rebuild it unchanged.
  RHere{}

def Term.act_expand(here: Bool) -> RefAct:
  match here:
    case True{}:
      RHere{}
    case False{}:
      RExpand{}

def Term.act_pick(closed: Bool, above: Bool, below: Bool, here: Bool) -> RefAct:
  match closed:
    case True{}:
      RKeep{}
    case False{}:
      match above:
        case True{}:
          RShift{}
        case False{}:
          match below:
            case True{}:
              RKeep{}
            case False{}:
              Term.act_expand(here)

# A lift moves the variables at the cutoff and above, so `cut` at `k` moves.
def Term.lift_act(+k: Nat, +m: Nat, +cut: Nat) -> RefAct:
  Term.act_pick(
    Nat.is_eq(m, 0n),
    Nat.is_le(cut, k),
    Nat.is_le(Nat.add(k, m), cut),
    Nat.is_eq(k, 0n))

# A substitution replaces the variable at the cutoff, so `cut` at `k` is the
# one being replaced and the reference has to be read.
def Term.subst_act(+k: Nat, +m: Nat, +cut: Nat) -> RefAct:
  Term.act_pick(
    Nat.is_eq(m, 0n),
    Nat.is_lt(cut, k),
    Nat.is_le(Nat.add(k, m), cut),
    Nat.is_eq(k, 0n))

# The answer for a term that is not a reference is never read.
def Term.lift_act_of(t: Term, +cut: Nat) -> RefAct:
  match t:
    case TRef{i, +k, +m}:
      Term.lift_act(k, m, cut)
    case o:
      RKeep{}

def Term.subst_act_of(t: Term, +cut: Nat) -> RefAct:
  match t:
    case TRef{i, +k, +m}:
      Term.subst_act(k, m, cut)
    case o:
      RKeep{}

# The walk a reference may cost. Running out hands back the unknown term,
# which every verdict reads as "do not know" rather than as a no.
def Term.walk_fuel() -> Nat:
  1000000n

# Add `d` to every free variable whose index is at least `cut`.
#
# `act` says what to do when `t` is a reference. It travels as a parameter
# because the decision is a computed value and a Bend match scrutinizes only
# a parameter or a field, so the caller of each step computes the next one.
def Term.lift_go(
  +fuel: Nat, +ex: ETable, t: Term, act: RefAct, +d: Nat, +cut: Nat
) -> Term:
  match fuel:
    case 0n:
      TUnk{}
    case 1n+f:
      match t:
        case TVar{+i}:
          Term.pick(Nat.is_lt(i, cut), TVar{i}, TVar{Nat.add(i, d)})
        case TSort{l}:
          TSort{l}
        case TConst{n, ls}:
          TConst{n, ls}
        case TApp{+g, +a}:
          TApp{
            Term.lift_go(f, ex, g, Term.lift_act_of(g, cut), d, cut),
            Term.lift_go(f, ex, a, Term.lift_act_of(a, cut), d, cut)}
        case TLam{+ty, +bd}:
          TLam{
            Term.lift_go(f, ex, ty, Term.lift_act_of(ty, cut), d, cut),
            Term.lift_go(f, ex, bd, Term.lift_act_of(bd, 1n+cut), d, 1n+cut)}
        case TPi{+ty, +bd}:
          TPi{
            Term.lift_go(f, ex, ty, Term.lift_act_of(ty, cut), d, cut),
            Term.lift_go(f, ex, bd, Term.lift_act_of(bd, 1n+cut), d, 1n+cut)}
        case TLet{+ty, +v, +bd}:
          TLet{
            Term.lift_go(f, ex, ty, Term.lift_act_of(ty, cut), d, cut),
            Term.lift_go(f, ex, v, Term.lift_act_of(v, cut), d, cut),
            Term.lift_go(f, ex, bd, Term.lift_act_of(bd, 1n+cut), d, 1n+cut)}
        case TNat{v, m, z, c}:
          TNat{v, m, z, c}
        case TStr{+sn, +bs}:
          TStr{sn, bs}
        case TBig{+ds, +nm, +zr, +sc}:
          TBig{ds, nm, zr, sc}
        case TUnk{}:
          TUnk{}
        case TProj{+tn, +idx, +st}:
          TProj{tn, idx, Term.lift_go(f, ex, st, Term.lift_act_of(st, cut), d, cut)}
        case TRef{+i, +k, +m}:
          match act:
            case RKeep{}:
              TRef{i, k, m}
            case RShift{}:
              TRef{i, Nat.add(k, d), m}
            case RExpand{}:
              +e : Term = Term.read_ex(ex, i)
              +up : Term = Term.lift_go(f, ex, e, Term.lift_act_of(e, 0n), k, 0n)
              Term.lift_go(f, ex, up, Term.lift_act_of(up, cut), d, cut)
            case RHere{}:
              +h : Term = Term.read_ex(ex, i)
              Term.lift_go(f, ex, h, Term.lift_act_of(h, cut), d, cut)

# The lift the kernel calls where a term may hold a reference.
def Term.lift_at(+ex: ETable, +t: Term, +d: Nat, +cut: Nat) -> Term:
  Term.lift_go(Term.walk_fuel(), ex, t, Term.lift_act_of(t, cut), d, cut)

# A lift by zero is the term itself, and the walk would rebuild the whole of
# it to find that out. Resolving a reference to a closed entry takes this
# path, which is the common one.
def Term.lift_if(no: Bool, +ex: ETable, +t: Term, +d: Nat, +cut: Nat) -> Term:
  match no:
    case True{}:
      t
    case False{}:
      Term.lift_at(ex, t, d, cut)

# The lift for a term that holds no reference, which is every type: a
# declaration's type is stored with its references expanded, because the
# passes that read a type as syntax read a reference as a leaf. An empty
# table resolves a reference to the unknown term, so a reference that
# reached here would be answered "do not know" and never answered wrongly.
def Term.lift(+t: Term, +d: Nat, +cut: Nat) -> Term:
  Term.lift_go(Term.walk_fuel(), ETable.new(), t, Term.lift_act_of(t, cut), d, cut)

# Lift a value into the scope it lands in, unless it lands in the scope it
# was written in. A lift by zero is the value itself, and `Term.lift` would
# walk and rebuild the whole of it to find that out.
def Term.lift_by(at_top: Bool, +ex: ETable, v: Term, +cut: Nat) -> Term:
  match at_top:
    case True{}:
      v
    case False{}:
      Term.lift_at(ex, v, cut, 0n)

# What one variable of the body becomes.
#
# This exists so that the value is walked only at the variable that is being
# replaced. `Term.pick` evaluates both of its branches, because an argument
# evaluates before the match picks an arm, so a lift written there copied the
# whole value at every variable in the body, matching or not. A body with a
# thousand variables copied a thousand values to use one.
def Term.subst_var(
  hit: Bool, +ex: ETable, +i: Nat, +v: Term, +cut: Nat
) -> Term:
  match hit:
    case True{}:
      Term.lift_by(Nat.is_eq(cut, 0n), ex, v, cut)
    case False{}:
      Term.pick(Nat.is_lt(i, cut), TVar{i}, TVar{Nat.sub(i, 1n)})

# Replace the variable at depth `cut` with `v`, and shift the ones above it
# down by one. This is the de Bruijn instantiation a beta step needs.
def Term.subst_go(
  +fuel: Nat, +ex: ETable, t: Term, act: RefAct, +v: Term, +cut: Nat
) -> Term:
  match fuel:
    case 0n:
      TUnk{}
    case 1n+f:
      match t:
        case TVar{+i}:
          Term.subst_var(Nat.is_eq(i, cut), ex, i, v, cut)
        case TSort{l}:
          TSort{l}
        case TConst{n, ls}:
          TConst{n, ls}
        case TApp{+g, +a}:
          TApp{
            Term.subst_go(f, ex, g, Term.subst_act_of(g, cut), v, cut),
            Term.subst_go(f, ex, a, Term.subst_act_of(a, cut), v, cut)}
        case TLam{+ty, +bd}:
          TLam{
            Term.subst_go(f, ex, ty, Term.subst_act_of(ty, cut), v, cut),
            Term.subst_go(f, ex, bd, Term.subst_act_of(bd, 1n+cut), v, 1n+cut)}
        case TPi{+ty, +bd}:
          TPi{
            Term.subst_go(f, ex, ty, Term.subst_act_of(ty, cut), v, cut),
            Term.subst_go(f, ex, bd, Term.subst_act_of(bd, 1n+cut), v, 1n+cut)}
        case TLet{+ty, +vl, +bd}:
          TLet{
            Term.subst_go(f, ex, ty, Term.subst_act_of(ty, cut), v, cut),
            Term.subst_go(f, ex, vl, Term.subst_act_of(vl, cut), v, cut),
            Term.subst_go(f, ex, bd, Term.subst_act_of(bd, 1n+cut), v, 1n+cut)}
        case TNat{n, m, z, c}:
          TNat{n, m, z, c}
        case TStr{+sn, +bs}:
          TStr{sn, bs}
        case TBig{+ds, +nm, +zr, +sc}:
          TBig{ds, nm, zr, sc}
        case TUnk{}:
          TUnk{}
        case TProj{+tn, +idx, +st}:
          TProj{
            tn, idx,
            Term.subst_go(f, ex, st, Term.subst_act_of(st, cut), v, cut)}
        case TRef{+i, +k, +m}:
          match act:
            case RKeep{}:
              TRef{i, k, m}
            case RShift{}:
              TRef{i, Nat.sub(k, 1n), m}
            case RExpand{}:
              +up : Term = Term.lift_at(ex, Term.read_ex(ex, i), k, 0n)
              Term.subst_go(f, ex, up, Term.subst_act_of(up, cut), v, cut)
            case RHere{}:
              +h : Term = Term.read_ex(ex, i)
              Term.subst_go(f, ex, h, Term.subst_act_of(h, cut), v, cut)

# The substitution the kernel calls where a term may hold a reference.
def Term.subst_at(+ex: ETable, +t: Term, +v: Term, +cut: Nat) -> Term:
  Term.subst_go(Term.walk_fuel(), ex, t, Term.subst_act_of(t, cut), v, cut)

# The substitution for a term that holds no reference. See `Term.lift`.
def Term.subst(+t: Term, +v: Term, +cut: Nat) -> Term:
  Term.subst_go(
    Term.walk_fuel(), ETable.new(), t, Term.subst_act_of(t, cut), v, cut)

# Instantiate the body of a binder with `v`, which is the common case of
# `Term.subst` at depth zero.
def Term.inst(bd: Term, +v: Term) -> Term:
  Term.subst(bd, v, 0n)

def Term.inst_at(+ex: ETable, bd: Term, +v: Term) -> Term:
  Term.subst_at(ex, bd, v, 0n)

def Term.subst_level_list(ls: List<&2, L.Level>, +vs: List<&2, L.Level>) -> List<&2, L.Level>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{L.Level.subst(h, vs), Term.subst_level_list(t, vs)}

# Renumber the level parameters in a list of levels.
def Term.remap_level_list(ls: List<&2, L.Level>, +ps: List<&2, Nat>) -> List<&2, L.Level>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{L.Level.remap(h, ps), Term.remap_level_list(t, ps)}

# Renumber every level parameter in a term from name index to position.
def Term.remap_levels(t: Term, +ps: List<&2, Nat>) -> Term:
  match t:
    case TVar{i}:
      TVar{i}
    case TSort{l}:
      TSort{L.Level.remap(l, ps)}
    case TConst{n, ls}:
      TConst{n, Term.remap_level_list(ls, ps)}
    case TApp{f, a}:
      TApp{Term.remap_levels(f, ps), Term.remap_levels(a, ps)}
    case TLam{ty, bd}:
      TLam{Term.remap_levels(ty, ps), Term.remap_levels(bd, ps)}
    case TPi{ty, bd}:
      TPi{Term.remap_levels(ty, ps), Term.remap_levels(bd, ps)}
    case TLet{ty, v, bd}:
      TLet{Term.remap_levels(ty, ps), Term.remap_levels(v, ps), Term.remap_levels(bd, ps)}
    case TNat{v, m, z, c}:
      TNat{v, m, z, c}
    case TStr{sn, bs}:
      TStr{sn, bs}
    case TBig{ds, nm, zr, sc}:
      TBig{ds, nm, zr, sc}
    case TUnk{}:
      TUnk{}
    case TProj{tn, idx, st}:
      TProj{tn, idx, Term.remap_levels(st, ps)}

# Substitute a declaration's level parameters throughout a term.
    case TRef{i, k, m}:
      TRef{i, k, m}

def Term.subst_levels(t: Term, +vs: List<&2, L.Level>) -> Term:
  match t:
    case TVar{i}:
      TVar{i}
    case TSort{l}:
      TSort{L.Level.subst(l, vs)}
    case TConst{n, ls}:
      TConst{n, Term.subst_level_list(ls, vs)}
    case TApp{f, a}:
      TApp{Term.subst_levels(f, vs), Term.subst_levels(a, vs)}
    case TLam{ty, bd}:
      TLam{Term.subst_levels(ty, vs), Term.subst_levels(bd, vs)}
    case TPi{ty, bd}:
      TPi{Term.subst_levels(ty, vs), Term.subst_levels(bd, vs)}
    case TLet{ty, v, bd}:
      TLet{Term.subst_levels(ty, vs), Term.subst_levels(v, vs), Term.subst_levels(bd, vs)}
    case TNat{v, m, z, c}:
      TNat{v, m, z, c}
    case TStr{sn, bs}:
      TStr{sn, bs}
    case TBig{ds, nm, zr, sc}:
      TBig{ds, nm, zr, sc}
    case TUnk{}:
      TUnk{}
    case TProj{tn, idx, st}:
      TProj{tn, idx, Term.subst_levels(st, vs)}
    case TRef{i, k, m}:
      TRef{i, k, m}
