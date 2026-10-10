# Building an environment from an export.
#
# An export assigns indices in three tables: names, levels and expressions.
# Names need no table here, because this kernel identifies a constant by the
# export's own name index rather than by its characters.
#
# The level and expression tables are kept newest first and counted, so adding
# an entry is a cons and costs nothing. Index `i` then sits at position
# `n - 1 - i` from the head. Lookup walks that far, so it is linear, and a
# table of fifty thousand entries would be too slow. That is what `Array` is
# for, and it is the next change. For a file of a few hundred lines a list is
# correct and simple.
#
# The format assigns indices in increasing order with no gaps, so an entry is
# appended in arrival order rather than written at its stated index.

import Base
import ./Bytes.bend as B
import ./Reader.bend as R
import ./Level.bend as L
import ./Term.bend as T
import ./Env.bend as E

# The parser's state: the two tables with their counts, and the declarations
# so far, also newest first.
type PState is Data:
  MkPS{
    nlev: Nat, levs: List<&2, L.Level>,
    nexp: Nat, exps: List<&2, T.Term>,
    decls: List<&2, E.Decl>}

def Parse.fuel() -> Nat:
  1000000n

# Level index 0 is zero and is never written by a line, so the table starts
# with it already in place.
def Parse.start() -> PState:
  MkPS{1n, Con{L.LZero{}, Nil{}}, 0n, Nil{}, Nil{}}

# The i-th level of the table, counting from the head.
def Parse.lev_at(fuel: Nat, xs: List<&2, L.Level>, k: Nat) -> L.Level:
  match fuel:
    case 0n:
      L.LZero{}
    case 1n+f:
      match xs:
        case Nil{}:
          L.LZero{}
        case Con{h, t}:
          match k:
            case 0n:
              h
            case 1n+p:
              Parse.lev_at(f, t, p)

# The level at export index `i`.
def Parse.lev(+levs: List<&2, L.Level>, +n: Nat, +i: Nat) -> L.Level:
  Parse.lev_at(Parse.fuel(), levs, Nat.sub(Nat.sub(n, 1n), i))

# The i-th term of the table, counting from the head.
def Parse.exp_at(fuel: Nat, xs: List<&2, T.Term>, k: Nat) -> T.Term:
  match fuel:
    case 0n:
      T.TSort{L.LZero{}}
    case 1n+f:
      match xs:
        case Nil{}:
          T.TSort{L.LZero{}}
        case Con{h, t}:
          match k:
            case 0n:
              h
            case 1n+p:
              Parse.exp_at(f, t, p)

# The term at export index `i`.
def Parse.exp(+exps: List<&2, T.Term>, +n: Nat, +i: Nat) -> T.Term:
  Parse.exp_at(Parse.fuel(), exps, Nat.sub(Nat.sub(n, 1n), i))

# The i-th number of a list, or zero.
def Parse.nat_at(xs: List<&2, Nat>, i: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      match i:
        case 0n:
          h
        case 1n+p:
          Parse.nat_at(t, p)

# How many numbers are in a list. Short lists only, so a plain count serves.
def Parse.nat_len(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+Parse.nat_len(t)

# The levels named by a list of export indices.
def Parse.levs_of(idxs: List<&2, Nat>, +levs: List<&2, L.Level>, +n: Nat) -> List<&2, L.Level>:
  match idxs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{Parse.lev(levs, n, h), Parse.levs_of(t, levs, n)}

# Levels
# ------
#
# A level line is `{"il":N,"succ":M}` and the like. The key says which kind it
# is, and `Reader.has` is what tells an absent field from a field whose value
# is zero.

def Parse.lvl_imax(h: Bool, +line: List<&2, U32>, +levs: List<&2, L.Level>, +n: Nat) -> L.Level:
  match h:
    case True{}:
      L.LIMax{
        Parse.lev(levs, n, Parse.nat_at(R.Reader.num_list("imax", line), 0n)),
        Parse.lev(levs, n, Parse.nat_at(R.Reader.num_list("imax", line), 1n))}
    case False{}:
      L.LZero{}

def Parse.lvl_max(h: Bool, +line: List<&2, U32>, +levs: List<&2, L.Level>, +n: Nat) -> L.Level:
  match h:
    case True{}:
      L.LMax{
        Parse.lev(levs, n, Parse.nat_at(R.Reader.num_list("max", line), 0n)),
        Parse.lev(levs, n, Parse.nat_at(R.Reader.num_list("max", line), 1n))}
    case False{}:
      Parse.lvl_imax(R.Reader.has("imax", line), line, levs, n)

def Parse.lvl_param(h: Bool, +line: List<&2, U32>, +levs: List<&2, L.Level>, +n: Nat) -> L.Level:
  match h:
    case True{}:
      L.LPar{R.Reader.field("param", line)}
    case False{}:
      Parse.lvl_max(R.Reader.has("max", line), line, levs, n)

def Parse.lvl_succ(h: Bool, +line: List<&2, U32>, +levs: List<&2, L.Level>, +n: Nat) -> L.Level:
  match h:
    case True{}:
      L.LSucc{Parse.lev(levs, n, R.Reader.field("succ", line))}
    case False{}:
      Parse.lvl_param(R.Reader.has("param", line), line, levs, n)

# The level a level line defines.
def Parse.level_of(+line: List<&2, U32>, +levs: List<&2, L.Level>, +n: Nat) -> L.Level:
  Parse.lvl_succ(R.Reader.has("succ", line), line, levs, n)

# Expressions
# -----------
#
# An expression line carries one node key. `"type"` and `"body"` mean the
# binder's type and body inside a `lam`, a `forallE` or a `letE`, and the
# dispatch on the node key is what keeps them apart from a declaration's own
# `"type"`.

def Parse.ex_letE(+st: PState, h: Bool, +line: List<&2, U32>) -> T.Term:
  match st:
    case MkPS{nl, lv, ne, ex, ds}:
      match h:
        case True{}:
          T.TLet{
            Parse.exp(ex, ne, R.Reader.field("type", line)),
            Parse.exp(ex, ne, R.Reader.field("value", line)),
            Parse.exp(ex, ne, R.Reader.field("body", line))}
        case False{}:
          T.TSort{L.LZero{}}

def Parse.ex_forallE(+st: PState, h: Bool, +line: List<&2, U32>) -> T.Term:
  match st:
    case MkPS{nl, lv, ne, ex, ds}:
      match h:
        case True{}:
          T.TPi{
            Parse.exp(ex, ne, R.Reader.field("type", line)),
            Parse.exp(ex, ne, R.Reader.field("body", line))}
        case False{}:
          Parse.ex_letE(MkPS{nl, lv, ne, ex, ds}, R.Reader.has("letE", line), line)

def Parse.ex_lam(+st: PState, h: Bool, +line: List<&2, U32>) -> T.Term:
  match st:
    case MkPS{nl, lv, ne, ex, ds}:
      match h:
        case True{}:
          T.TLam{
            Parse.exp(ex, ne, R.Reader.field("type", line)),
            Parse.exp(ex, ne, R.Reader.field("body", line))}
        case False{}:
          Parse.ex_forallE(MkPS{nl, lv, ne, ex, ds}, R.Reader.has("forallE", line), line)

def Parse.ex_app(+st: PState, h: Bool, +line: List<&2, U32>) -> T.Term:
  match st:
    case MkPS{nl, lv, ne, ex, ds}:
      match h:
        case True{}:
          T.TApp{
            Parse.exp(ex, ne, R.Reader.field("fn", line)),
            Parse.exp(ex, ne, R.Reader.field("arg", line))}
        case False{}:
          Parse.ex_lam(MkPS{nl, lv, ne, ex, ds}, R.Reader.has("lam", line), line)

def Parse.ex_const(+st: PState, h: Bool, +line: List<&2, U32>) -> T.Term:
  match st:
    case MkPS{nl, lv, ne, ex, ds}:
      match h:
        case True{}:
          T.TConst{
            R.Reader.field("name", line),
            Parse.levs_of(R.Reader.num_list("us", line), lv, nl)}
        case False{}:
          Parse.ex_app(MkPS{nl, lv, ne, ex, ds}, R.Reader.has("app", line), line)

def Parse.ex_bvar(+st: PState, h: Bool, +line: List<&2, U32>) -> T.Term:
  match st:
    case MkPS{nl, lv, ne, ex, ds}:
      match h:
        case True{}:
          T.TVar{R.Reader.field("bvar", line)}
        case False{}:
          Parse.ex_const(MkPS{nl, lv, ne, ex, ds}, R.Reader.has("const", line), line)

def Parse.ex_sort(+st: PState, h: Bool, +line: List<&2, U32>) -> T.Term:
  match st:
    case MkPS{nl, lv, ne, ex, ds}:
      match h:
        case True{}:
          T.TSort{Parse.lev(lv, nl, R.Reader.field("sort", line))}
        case False{}:
          Parse.ex_bvar(MkPS{nl, lv, ne, ex, ds}, R.Reader.has("bvar", line), line)

# The term an expression line defines.
def Parse.expr_of(+st: PState, +line: List<&2, U32>) -> T.Term:
  Parse.ex_sort(st, R.Reader.has("sort", line), line)

# Declarations
# ------------
#
# A theorem keeps its own kind, so the kernel can require its type to be a
# Prop. An opaque declaration becomes an axiom: its type is checked and its
# value is not, which is sound but incomplete.

def Parse.decl_of(+st: PState, k: R.LineKind, +line: List<&2, U32>) -> E.Decl:
  match st:
    case MkPS{nl, lv, ne, ex, ds}:
      match k:
        case R.KAxiom{}:
          E.DAxiom{
            R.Reader.field("name", line),
            Parse.nat_len(R.Reader.num_list("levelParams", line)),
            T.Term.remap_levels(
              Parse.exp(ex, ne, R.Reader.field("type", line)),
              R.Reader.num_list("levelParams", line))}
        case R.KDef{}:
          E.DDef{
            R.Reader.field("name", line),
            Parse.nat_len(R.Reader.num_list("levelParams", line)),
            T.Term.remap_levels(
              Parse.exp(ex, ne, R.Reader.field("type", line)),
              R.Reader.num_list("levelParams", line)),
            T.Term.remap_levels(
              Parse.exp(ex, ne, R.Reader.field("value", line)),
              R.Reader.num_list("levelParams", line))}
        case R.KThm{}:
          E.DThm{
            R.Reader.field("name", line),
            Parse.nat_len(R.Reader.num_list("levelParams", line)),
            T.Term.remap_levels(
              Parse.exp(ex, ne, R.Reader.field("type", line)),
              R.Reader.num_list("levelParams", line)),
            T.Term.remap_levels(
              Parse.exp(ex, ne, R.Reader.field("value", line)),
              R.Reader.num_list("levelParams", line))}
        case R.KOpaque{}:
          E.DAxiom{
            R.Reader.field("name", line),
            Parse.nat_len(R.Reader.num_list("levelParams", line)),
            T.Term.remap_levels(
              Parse.exp(ex, ne, R.Reader.field("type", line)),
              R.Reader.num_list("levelParams", line))}
        case R.KMeta{}:
          E.DAxiom{0n, 0n, T.TSort{L.LZero{}}}
        case R.KName{}:
          E.DAxiom{0n, 0n, T.TSort{L.LZero{}}}
        case R.KLevel{}:
          E.DAxiom{0n, 0n, T.TSort{L.LZero{}}}
        case R.KExpr{}:
          E.DAxiom{0n, 0n, T.TSort{L.LZero{}}}
        case R.KInductive{}:
          E.DAxiom{0n, 0n, T.TSort{L.LZero{}}}
        case R.KQuot{}:
          E.DAxiom{0n, 0n, T.TSort{L.LZero{}}}
        case R.KOther{}:
          E.DAxiom{0n, 0n, T.TSort{L.LZero{}}}

# One line
# --------

# Fold one line into the state.
def Parse.step(+st: PState, k: R.LineKind, +line: List<&2, U32>) -> PState:
  match st:
    case MkPS{nl, lv, ne, ex, ds}:
      match k:
        case R.KLevel{}:
          MkPS{
            1n+nl,
            Con{Parse.level_of(line, lv, nl), lv},
            ne, ex, ds}
        case R.KExpr{}:
          MkPS{
            nl, lv,
            1n+ne,
            Con{Parse.expr_of(MkPS{nl, lv, ne, ex, ds}, line), ex},
            ds}
        case R.KAxiom{}:
          MkPS{nl, lv, ne, ex,
            Con{Parse.decl_of(MkPS{nl, lv, ne, ex, ds}, R.KAxiom{}, line), ds}}
        case R.KDef{}:
          MkPS{nl, lv, ne, ex,
            Con{Parse.decl_of(MkPS{nl, lv, ne, ex, ds}, R.KDef{}, line), ds}}
        case R.KThm{}:
          MkPS{nl, lv, ne, ex,
            Con{Parse.decl_of(MkPS{nl, lv, ne, ex, ds}, R.KThm{}, line), ds}}
        case R.KOpaque{}:
          MkPS{nl, lv, ne, ex,
            Con{Parse.decl_of(MkPS{nl, lv, ne, ex, ds}, R.KOpaque{}, line), ds}}
        case R.KMeta{}:
          MkPS{nl, lv, ne, ex, ds}
        case R.KName{}:
          MkPS{nl, lv, ne, ex, ds}
        case R.KInductive{}:
          MkPS{nl, lv, ne, ex, ds}
        case R.KQuot{}:
          MkPS{nl, lv, ne, ex, ds}
        case R.KOther{}:
          MkPS{nl, lv, ne, ex, ds}

# The file
# --------

# Fold every line of the file into the state. `done` carries whether the
# stream is spent, so the recursive call is the whole body.
def Parse.go(fuel: Nat, done: Bool, +st: PState, xs: List<&2, U32>) -> PState:
  match fuel:
    case 0n:
      st
    case 1n+f:
      match done:
        case True{}:
          st
        case False{}:
          +ln = R.Reader.line(R.Reader.line_fuel(), xs)
          Parse.go(
            f,
            B.Bytes.is_empty(R.Reader.line_rest(ln)),
            Parse.step(
              st,
              R.Reader.line_kind(R.Reader.line_bytes(ln)),
              R.Reader.line_bytes(ln)),
            R.Reader.line_rest(ln))

# Reverse the declarations, so they come back in the order the file gave them.
def Parse.rev_decls(fuel: Nat, +acc: List<&2, E.Decl>, xs: List<&2, E.Decl>) -> List<&2, E.Decl>:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      match xs:
        case Nil{}:
          acc
        case Con{h, t}:
          Parse.rev_decls(f, Con{h, acc}, t)

# The declarations an export declares, in order.
def Parse.decls_of(st: PState) -> List<&2, E.Decl>:
  match st:
    case MkPS{nl, lv, ne, ex, ds}:
      Parse.rev_decls(Parse.fuel(), Nil{}, ds)

# Parse a whole export.
def Parse.run(+xs: List<&2, U32>) -> PState:
  Parse.go(Parse.fuel(), B.Bytes.is_empty(xs), Parse.start(), xs)
