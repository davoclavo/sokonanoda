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
import ./Table.bend as Tb

# The parser's state: the two tables with their counts, and the declarations
# so far, also newest first.
type PState is Data:
  MkPS{
    nlev: Nat, levs: Tb.LTable,
    nexp: Nat, exps: Tb.ETable,
    decls: List<&2, E.Decl>,
    # The ids of `Nat`, `Nat.zero` and `Nat.succ`, or zero when not yet seen.
    # A `natVal` node names the real `Nat`, so a literal cannot be read until
    # the name lines that introduce those three have gone by. Zero is a safe
    # sentinel, since name zero is the anonymous name.
    nt: Nat, zr: Nat, sc: Nat,
    # The names of the eight `Nat` definitions the kernel computes itself, in
    # op order, and the names of `Bool`, `Bool.true` and `Bool.false`, which
    # the two rules that compare answer with. Zero where the name has not
    # gone by.
    pm: List<&2, Nat>, bl: Nat, yes: Nat, no: Nat,
    # One for each name whose last component is `rec`. Lean names the
    # eliminator of `I` as `I.rec`, and a recursor under any other name is not
    # the eliminator. The prefix is deliberately not compared: a mutual block
    # of `I1` and `I2` yields `I1.rec` and `I2.rec`, each naming both types,
    # so matching a prefix would reject the second one wrongly.
    rc: Tb.NTable,
    # The id of `Eq`, found the way `Nat` is. The type of `Quot.lift` names
    # it, so the check on a quotient declaration cannot be written without it.
    eqn: Nat}

def Parse.fuel() -> Nat:
  1000000n

# Level index 0 is zero and is never written by a line, so the table starts
# with it already in place.
def Parse.start() -> PState:
  MkPS{
    1n,
    Tb.LTable.new(),
    0n,
    Tb.ETable.new(),
    Nil{}, 0n, 0n, 0n,
    [0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n], 0n, 0n, 0n, Tb.NTable.new(), 0n}

# A line is written at the index its own field states, not at the position it
# arrives in. The two usually agree, and they must not be assumed to: the
# arena's `sparse-name-index` holds one expression numbered four, and a line
# names an expression by that number.

# The level the export calls `i`.
def Parse.lev(+levs: Tb.LTable, +i: Nat) -> L.Level:
  Tb.Table.read_lv(levs, i)

# The expression the export calls `i`.
def Parse.exp(+exps: Tb.ETable, +i: Nat) -> T.Term:
  Tb.Table.read(exps, i)

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
def Parse.levs_of(idxs: List<&2, Nat>, +levs: Tb.LTable) -> List<&2, L.Level>:
  match idxs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{Parse.lev(levs, h), Parse.levs_of(t, levs)}

# Levels
# ------
#
# A level line is `{"il":N,"succ":M}` and the like. The key says which kind it
# is, and `Reader.has` is what tells an absent field from a field whose value
# is zero.

def Parse.lvl_imax(h: Bool, +line: List<&2, U32>, +levs: Tb.LTable) -> L.Level:
  match h:
    case True{}:
      L.LIMax{
        Parse.lev(levs, Parse.nat_at(R.Reader.num_list("imax", line), 0n)),
        Parse.lev(levs, Parse.nat_at(R.Reader.num_list("imax", line), 1n))}
    case False{}:
      L.LZero{}

def Parse.lvl_max(h: Bool, +line: List<&2, U32>, +levs: Tb.LTable) -> L.Level:
  match h:
    case True{}:
      L.LMax{
        Parse.lev(levs, Parse.nat_at(R.Reader.num_list("max", line), 0n)),
        Parse.lev(levs, Parse.nat_at(R.Reader.num_list("max", line), 1n))}
    case False{}:
      Parse.lvl_imax(R.Reader.has("imax", line), line, levs)

def Parse.lvl_param(h: Bool, +line: List<&2, U32>, +levs: Tb.LTable) -> L.Level:
  match h:
    case True{}:
      L.LPar{R.Reader.field("param", line)}
    case False{}:
      Parse.lvl_max(R.Reader.has("max", line), line, levs)

def Parse.lvl_succ(h: Bool, +line: List<&2, U32>, +levs: Tb.LTable) -> L.Level:
  match h:
    case True{}:
      L.LSucc{Parse.lev(levs, R.Reader.field("succ", line))}
    case False{}:
      Parse.lvl_param(R.Reader.has("param", line), line, levs)

# The level a level line defines.
def Parse.level_of(+line: List<&2, U32>, +levs: Tb.LTable) -> L.Level:
  Parse.lvl_succ(R.Reader.has("succ", line), line, levs)

# The names of Nat
# ----------------
#
# A `natVal` node names the real `Nat`, not an index this kernel chose, so a
# literal cannot be read until the three name lines that introduce `Nat`,
# `Nat.zero` and `Nat.succ` have gone by. A name line carries its own last
# component and the id of its prefix, and that is enough: `Nat` is the name
# whose prefix is anonymous and whose component is `Nat`, and the other two
# are the names whose prefix is `Nat`.
#
# Nothing else in this kernel looks at a name's characters.

# The inner object of a name line, holding its prefix and its component.
def Parse.name_part(+line: List<&2, U32>) -> List<&2, U32>:
  R.Reader.inside("str", line)

# Is this name line's last component the given word?
def Parse.name_is(+line: List<&2, U32>, +w: String) -> Bool:
  B.Bytes.is_hit(
    B.Bytes.of_string("\"" ++ w ++ "\""),
    R.Reader.after("str", Parse.name_part(line)))

# The id of this name line's prefix.
def Parse.name_pre(+line: List<&2, U32>) -> Nat:
  R.Reader.field("pre", Parse.name_part(line))

# Keep the old id unless this line is the name being looked for.
def Parse.keep_or(hit: Bool, +line: List<&2, U32>, old: Nat) -> Nat:
  match hit:
    case True{}:
      R.Reader.field("in", line)
    case False{}:
      old

# `Nat` is the name with no prefix and the component `Nat`.
def Parse.upd_nat(+line: List<&2, U32>, +nt: Nat) -> Nat:
  Parse.keep_or(
    Bool.and(Parse.name_is(line, "Nat"), Nat.is_eq(Parse.name_pre(line), 0n)),
    line,
    nt)

# `Nat.zero` and `Nat.succ` are the names whose prefix is `Nat`.
def Parse.upd_under_nat(
  +line: List<&2, U32>, +w: String, +nt: Nat, +old: Nat
) -> Nat:
  Parse.keep_or(
    Bool.and(
      Bool.and(Parse.name_is(line, w), Nat.is_eq(Parse.name_pre(line), nt)),
      Bool.not(Nat.is_eq(nt, 0n))),
    line,
    old)

# Choose between two tables on a computed Bool.
def Parse.pick_tbl(b: Bool, x: Tb.NTable, y: Tb.NTable) -> Tb.NTable:
  match b:
    case True{}:
      x
    case False{}:
      y

# Does this name line's last component begin with the given word?
def Parse.name_starts(+line: List<&2, U32>, +w: String) -> Bool:
  B.Bytes.is_hit(
    B.Bytes.of_string("\"" ++ w),
    R.Reader.after("str", Parse.name_part(line)))

# Record a name whose last component is `rec`, or begins with `rec_`,
# whatever its prefix.
#
# `rec_` is there for a nested inductive. Lean gives such a block more than
# one eliminator and names them `I.rec_1`, `I.rec_2` and so on, and
# `Lean.Syntax.rec_2` in the arena's `init-prelude` is one. Requiring the last
# component to be exactly `rec` rejected it, and that file is one the arena
# expects to accept.
#
# The test is a prefix, so `rec_anything` passes as well. That is looser than
# Lean, which numbers them, and it still refuses the three attacks the rule is
# for: `extra-rec` names its rogue eliminator `False.rogue`, and
# `misnamed_rec_user` and `dup_rec_def2` each name theirs `not_rec`.
def Parse.upd_rec(+line: List<&2, U32>, +rc: Tb.NTable) -> Tb.NTable:
  Parse.pick_tbl(
    Bool.or(
      Parse.name_is(line, "rec"), Parse.name_starts(line, "rec_")),
    Tb.Table.write_nat(rc, R.Reader.field("in", line), 1n),
    rc)

# `Eq` is the name with no prefix and the component `Eq`.
def Parse.upd_eq(+line: List<&2, U32>, +eqn: Nat) -> Nat:
  Parse.keep_or(
    Bool.and(Parse.name_is(line, "Eq"), Nat.is_eq(Parse.name_pre(line), 0n)),
    line,
    eqn)

# `Bool` is the name with no prefix and the component `Bool`.
def Parse.upd_bool(+line: List<&2, U32>, +bl: Nat) -> Nat:
  Parse.keep_or(
    Bool.and(Parse.name_is(line, "Bool"), Nat.is_eq(Parse.name_pre(line), 0n)),
    line,
    bl)

# Choose between two numbers on a computed Bool.
def Parse.pick_nat(b: Bool, x: Nat, y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

# The k-th name of the native table.
def Parse.prim_at(xs: List<&2, Nat>, +k: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      match k:
        case 0n:
          h
        case 1n+p:
          Parse.prim_at(t, p)

# The native table, with this name line folded in. A name line that names one
# of the eight sets that one entry and leaves the rest alone.
def Parse.upd_prims(
  +line: List<&2, U32>, +nt: Nat, +pm: List<&2, Nat>
) -> List<&2, Nat>:
  [Parse.upd_under_nat(line, "add", nt, Parse.prim_at(pm, 0n)),
   Parse.upd_under_nat(line, "sub", nt, Parse.prim_at(pm, 1n)),
   Parse.upd_under_nat(line, "mul", nt, Parse.prim_at(pm, 2n)),
   Parse.upd_under_nat(line, "div", nt, Parse.prim_at(pm, 3n)),
   Parse.upd_under_nat(line, "mod", nt, Parse.prim_at(pm, 4n)),
   Parse.upd_under_nat(line, "beq", nt, Parse.prim_at(pm, 5n)),
   Parse.upd_under_nat(line, "ble", nt, Parse.prim_at(pm, 6n)),
   Parse.upd_under_nat(line, "pow", nt, Parse.prim_at(pm, 7n))]

# Which native rule this name carries, or zero. The table holds the names in
# op order, so the op is the position found, counting from one.
def Parse.prim_op_at(xs: List<&2, Nat>, +id: Nat, +k: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      Parse.pick_nat(
        Bool.and(Nat.is_eq(h, id), Bool.not(Nat.is_eq(id, 0n))),
        1n+k,
        Parse.prim_op_at(t, id, 1n+k))

# The term a literal stands for: that many successors of zero.
#
# The fuel caps how large a literal this kernel will read. Past the cap it
# answers a loose variable, which no inference accepts, so an export with a
# literal beyond the cap is rejected rather than quietly mis-read. The arena
# enables a native `Nat`, where a literal is a primitive and arithmetic on one
# is a rule of the kernel; this is the honest small version of that.
def Parse.nat_term(fuel: Nat, k: Nat, +zr: Nat, +sc: Nat) -> T.Term:
  match fuel:
    case 0n:
      T.TVar{0n}
    case 1n+f:
      match k:
        case 0n:
          T.TConst{zr, []}
        case 1n+p:
          T.TApp{T.TConst{sc, []}, Parse.nat_term(f, p, zr, sc)}

# Expressions
# -----------
#
# An expression line carries one node key. `"type"` and `"body"` mean the
# binder's type and body inside a `lam`, a `forallE` or a `letE`, and the
# dispatch on the node key is what keeps them apart from a declaration's own
# `"type"`.

# A literal, and the end of the chain.
#
# A node this kernel does not read answers the unknown term. It used to
# answer a loose variable, on the reasoning that inference would then fail and
# the declaration would be rejected. That is the wrong answer twice over. A
# rejection is a claim that the declaration is wrong, and a node nobody read
# is no evidence of that. And a loose variable is not even reliably wrong: at
# index zero it names whatever binder happens to be in scope, so a declaration
# could convert and be **accepted** on the strength of a node the kernel never
# looked at.
#
# The unknown term says what is true: this is not known. Every function that
# meets it answers that it does not know, so the file declines.
#
# A sort would be worse than either. An unknown node would pass for `Prop`,
# which is how a `natVal` first went by unnoticed.
#
# The corpus holds ten kinds of expression node and this kernel reads nine.
# The one it does not is `strVal`, a string literal, in 74 places across four
# files.
# A literal, or the unknown term when the number reached the reader's cap.
# A capped number is not the number the export wrote, so nothing may be
# concluded from it, and the unknown term is what says so.
def Parse.lit_term(+v: Nat, +nt: Nat, +zr: Nat, +sc: Nat) -> T.Term:
  T.Term.pick(
    Nat.is_lt(v, B.Bytes.nat_cap()),
    T.TNat{v, nt, zr, sc},
    T.TUnk{})

def Parse.ex_natval(+st: PState, h: Bool, +line: List<&2, U32>) -> T.Term:
  match st:
    case MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}:
      match h:
        case True{}:
          Parse.lit_term(R.Reader.field_q("natVal", line), nt, zr, sc)
        case False{}:
          T.TUnk{}

def Parse.ex_proj(+st: PState, h: Bool, +line: List<&2, U32>) -> T.Term:
  match st:
    case MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}:
      match h:
        case True{}:
          T.TProj{
            R.Reader.field("typeName", line),
            R.Reader.field("idx", line),
            Parse.exp(ex, R.Reader.field("struct", line))}
        case False{}:
          Parse.ex_natval(
            MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn},
            R.Reader.has("natVal", line),
            line)

def Parse.ex_letE(+st: PState, h: Bool, +line: List<&2, U32>) -> T.Term:
  match st:
    case MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}:
      match h:
        case True{}:
          T.TLet{
            Parse.exp(ex, R.Reader.field("type", line)),
            Parse.exp(ex, R.Reader.field("value", line)),
            Parse.exp(ex, R.Reader.field("body", line))}
        case False{}:
          Parse.ex_proj(
            MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn},
            R.Reader.has("typeName", line),
            line)

def Parse.ex_forallE(+st: PState, h: Bool, +line: List<&2, U32>) -> T.Term:
  match st:
    case MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}:
      match h:
        case True{}:
          T.TPi{
            Parse.exp(ex, R.Reader.field("type", line)),
            Parse.exp(ex, R.Reader.field("body", line))}
        case False{}:
          Parse.ex_letE(MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}, R.Reader.has("letE", line), line)

def Parse.ex_lam(+st: PState, h: Bool, +line: List<&2, U32>) -> T.Term:
  match st:
    case MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}:
      match h:
        case True{}:
          T.TLam{
            Parse.exp(ex, R.Reader.field("type", line)),
            Parse.exp(ex, R.Reader.field("body", line))}
        case False{}:
          Parse.ex_forallE(MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}, R.Reader.has("forallE", line), line)

def Parse.ex_app(+st: PState, h: Bool, +line: List<&2, U32>) -> T.Term:
  match st:
    case MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}:
      match h:
        case True{}:
          T.TApp{
            Parse.exp(ex, R.Reader.field("fn", line)),
            Parse.exp(ex, R.Reader.field("arg", line))}
        case False{}:
          Parse.ex_lam(MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}, R.Reader.has("lam", line), line)

def Parse.ex_const(+st: PState, h: Bool, +line: List<&2, U32>) -> T.Term:
  match st:
    case MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}:
      match h:
        case True{}:
          T.TConst{
            R.Reader.field("name", line),
            Parse.levs_of(R.Reader.num_list("us", line), lv)}
        case False{}:
          Parse.ex_app(MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}, R.Reader.has("app", line), line)

def Parse.ex_bvar(+st: PState, h: Bool, +line: List<&2, U32>) -> T.Term:
  match st:
    case MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}:
      match h:
        case True{}:
          T.TVar{R.Reader.field("bvar", line)}
        case False{}:
          Parse.ex_const(MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}, R.Reader.has("const", line), line)

def Parse.ex_sort(+st: PState, h: Bool, +line: List<&2, U32>) -> T.Term:
  match st:
    case MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}:
      match h:
        case True{}:
          T.TSort{Parse.lev(lv, R.Reader.field("sort", line))}
        case False{}:
          Parse.ex_bvar(MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}, R.Reader.has("bvar", line), line)

# The term an expression line defines.
def Parse.expr_of(+st: PState, +line: List<&2, U32>) -> T.Term:
  Parse.ex_sort(st, R.Reader.has("sort", line), line)

# Declarations
# ------------
#
# A theorem keeps its own kind, so the kernel can require its type to be a
# Prop. An opaque declaration becomes an axiom: its type is checked and its
# value is not, which is sound but incomplete.

# Choose between two declarations on a computed Bool.
def Parse.pick_decl(b: Bool, x: E.Decl, y: E.Decl) -> E.Decl:
  match b:
    case True{}:
      x
    case False{}:
      y

def Parse.decl_of(+st: PState, k: R.LineKind, +line: List<&2, U32>) -> E.Decl:
  match st:
    case MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}:
      match k:
        case R.KAxiom{}:
          E.DAxiom{
            R.Reader.field("name", line),
            R.Reader.num_list("levelParams", line),
            T.Term.remap_levels(
              Parse.exp(ex, R.Reader.field("type", line)),
              R.Reader.num_list("levelParams", line))}
        case R.KDef{}:
          # A definition the exporter marks `unsafe` or `partial` is kept as
          # its type and nothing else. Lean's kernel never looks at one, so a
          # kernel that checks it is not stricter but wrong: `unsafe def loop
          # : False := loop` is a file Lean accepts and this used to reject.
          # What makes the omission sound is the rule that a safe declaration
          # may not mention one.
          Parse.pick_decl(
            R.Reader.is_word("safety", "safe", line),
            Parse.pick_decl(
            Nat.is_eq(
              Parse.prim_op_at(pm, R.Reader.field("name", line), 0n), 0n),
            E.DDef{
              R.Reader.field("name", line),
              R.Reader.num_list("levelParams", line),
              T.Term.remap_levels(
                Parse.exp(ex, R.Reader.field("type", line)),
                R.Reader.num_list("levelParams", line)),
              T.Term.remap_levels(
                Parse.exp(ex, R.Reader.field("value", line)),
                R.Reader.num_list("levelParams", line))},
            E.DPrim{
              R.Reader.field("name", line),
              R.Reader.num_list("levelParams", line),
              T.Term.remap_levels(
                Parse.exp(ex, R.Reader.field("type", line)),
                R.Reader.num_list("levelParams", line)),
              T.Term.remap_levels(
                Parse.exp(ex, R.Reader.field("value", line)),
                R.Reader.num_list("levelParams", line)),
              Parse.prim_op_at(pm, R.Reader.field("name", line), 0n),
              yes,
              no}),
            E.DUnsafe{
              R.Reader.field("name", line),
              R.Reader.num_list("levelParams", line),
              T.Term.remap_levels(
                Parse.exp(ex, R.Reader.field("type", line)),
                R.Reader.num_list("levelParams", line))})
        case R.KThm{}:
          E.DThm{
            R.Reader.field("name", line),
            R.Reader.num_list("levelParams", line),
            T.Term.remap_levels(
              Parse.exp(ex, R.Reader.field("type", line)),
              R.Reader.num_list("levelParams", line)),
            T.Term.remap_levels(
              Parse.exp(ex, R.Reader.field("value", line)),
              R.Reader.num_list("levelParams", line))}
        case R.KOpaque{}:
          E.DAxiom{
            R.Reader.field("name", line),
            R.Reader.num_list("levelParams", line),
            T.Term.remap_levels(
              Parse.exp(ex, R.Reader.field("type", line)),
              R.Reader.num_list("levelParams", line))}
        case R.KMeta{}:
          E.DAxiom{0n, [], T.TSort{L.LZero{}}}
        case R.KName{}:
          E.DAxiom{0n, [], T.TSort{L.LZero{}}}
        case R.KLevel{}:
          E.DAxiom{0n, [], T.TSort{L.LZero{}}}
        case R.KExpr{}:
          E.DAxiom{0n, [], T.TSort{L.LZero{}}}
        case R.KInductive{}:
          E.DAxiom{0n, [], T.TSort{L.LZero{}}}
        case R.KQuot{}:
          E.DAxiom{0n, [], T.TSort{L.LZero{}}}
        case R.KOther{}:
          E.DAxiom{0n, [], T.TSort{L.LZero{}}}

# Inductive blocks
# ----------------
#
# One line carries the whole block: the inductive types, their constructors,
# and their recursors with the computation rules. Each is an array of objects,
# and the same key appears in several of them, so `Reader.obj_list` cuts the
# arrays into objects first and a field is read from one object.
#
# Everything is read at the expression table as it stood before the block, so
# a block may not name an expression written after it.

# One computation rule.
#
# The right-hand side is renumbered with the recursor's own level parameters,
# exactly as the recursor's type is. Forgetting that is a silent error: the
# stored side keeps naming its parameters by name index while
# `Term.subst_levels` reads them as positions, so firing the rule produces a
# term at the wrong universe and the conversion that follows fails for no
# visible reason. Only a recursor with a level parameter is affected, which is
# why a hand-written test over `Bool` does not catch it.
def Parse.rule_of(+o: List<&2, U32>, +st: PState, +ps: List<&2, Nat>) -> E.RecRule:
  match st:
    case MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}:
      E.MkRule{
        R.Reader.field("ctor", o),
        R.Reader.field("nfields", o),
        T.Term.remap_levels(
          Parse.exp(ex, R.Reader.field("rhs", o)),
          ps)}

# Every rule of one recursor.
def Parse.rules_of(
  os: List<&2, List<&2, U32>>, +st: PState, +ps: List<&2, Nat>
) -> List<&2, E.RecRule>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, t}:
      Con{Parse.rule_of(o, st, ps), Parse.rules_of(t, st, ps)}

# One inductive type.
def Parse.ind_of(+o: List<&2, U32>, +st: PState) -> E.Decl:
  match st:
    case MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}:
      E.DInd{
        R.Reader.field("name", o),
        R.Reader.num_list("levelParams", o),
        T.Term.remap_levels(
          Parse.exp(ex, R.Reader.field("type", o)),
          R.Reader.num_list("levelParams", o)),
        R.Reader.field("numParams", o),
        R.Reader.field("numIndices", o),
        R.Reader.num_list("ctors", o)}

# One constructor.
def Parse.ctor_of(+o: List<&2, U32>, +st: PState) -> E.Decl:
  match st:
    case MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}:
      E.DCtor{
        R.Reader.field("name", o),
        R.Reader.num_list("levelParams", o),
        T.Term.remap_levels(
          Parse.exp(ex, R.Reader.field("type", o)),
          R.Reader.num_list("levelParams", o)),
        R.Reader.field("induct", o),
        R.Reader.field("cidx", o),
        R.Reader.field("numParams", o),
        R.Reader.field("numFields", o)}

# One recursor.
def Parse.rec_of(+o: List<&2, U32>, +st: PState) -> E.Decl:
  match st:
    case MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}:
      E.DRec{
        R.Reader.field("name", o),
        R.Reader.num_list("levelParams", o),
        T.Term.remap_levels(
          Parse.exp(ex, R.Reader.field("type", o)),
          R.Reader.num_list("levelParams", o)),
        R.Reader.field("numParams", o),
        R.Reader.field("numIndices", o),
        R.Reader.field("numMotives", o),
        R.Reader.field("numMinors", o),
        R.Reader.is_true("k", o),
        Parse.rules_of(
          R.Reader.obj_list("rules", o),
          MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn},
          R.Reader.num_list("levelParams", o)),
        R.Reader.num_list("all", o),
        Nat.is_eq(
          Tb.Table.read_nat(rc, R.Reader.field("name", o)), 1n)}

# Add every object of an array, in order, to the declarations.
def Parse.add_inds(os: List<&2, List<&2, U32>>, +st: PState, +ds: List<&2, E.Decl>) -> List<&2, E.Decl>:
  match os:
    case Nil{}:
      ds
    case Con{o, t}:
      Parse.add_inds(t, st, Con{Parse.ind_of(o, st), ds})

def Parse.add_ctors(os: List<&2, List<&2, U32>>, +st: PState, +ds: List<&2, E.Decl>) -> List<&2, E.Decl>:
  match os:
    case Nil{}:
      ds
    case Con{o, t}:
      Parse.add_ctors(t, st, Con{Parse.ctor_of(o, st), ds})

def Parse.add_recs(os: List<&2, List<&2, U32>>, +st: PState, +ds: List<&2, E.Decl>) -> List<&2, E.Decl>:
  match os:
    case Nil{}:
      ds
    case Con{o, t}:
      Parse.add_recs(t, st, Con{Parse.rec_of(o, st), ds})

# Fold a whole inductive block into the declarations: the types first, then
# the constructors, then the recursors, which is the order a later
# declaration may rely on.
def Parse.block_of(+line: List<&2, U32>, +st: PState) -> List<&2, E.Decl>:
  match st:
    case MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}:
      Parse.add_recs(
        R.Reader.obj_list("recs", line),
        MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn},
        Parse.add_ctors(
          R.Reader.obj_list("ctors", line),
          MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn},
          Parse.add_inds(
            R.Reader.obj_list("types", line),
            MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn},
            ds)))

# Quotients
# ---------
#
# Each of the four is one line with a name, its level parameters and a type,
# which is the shape of an axiom. The `kind` tag says which one it is, and the
# reduction rules for `Quot.lift` and `Quot.ind` are keyed on it.

# Pick the first tag that matched, or 9 for none.
def Parse.pick_nat4(a: Bool, b: Bool, c: Bool, d: Bool) -> Nat:
  match a:
    case True{}:
      0n
    case False{}:
      match b:
        case True{}:
          1n
        case False{}:
          match c:
            case True{}:
              2n
            case False{}:
              match d:
                case True{}:
                  3n
                case False{}:
                  9n

# The tag as a number: 0 for the type, 1 for the constructor, 2 for lift and
# 3 for ind.
def Parse.quot_kind(+line: List<&2, U32>) -> Nat:
  Parse.pick_nat4(
    R.Reader.is_word("kind", "type", line),
    R.Reader.is_word("kind", "ctor", line),
    R.Reader.is_word("kind", "lift", line),
    R.Reader.is_word("kind", "ind", line))

# One quotient declaration.
def Parse.quot_of(+st: PState, +line: List<&2, U32>) -> E.Decl:
  match st:
    case MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}:
      E.DQuot{
        R.Reader.field("name", line),
        R.Reader.num_list("levelParams", line),
        T.Term.remap_levels(
          Parse.exp(ex, R.Reader.field("type", line)),
          R.Reader.num_list("levelParams", line)),
        Parse.quot_kind(line),
        eqn}

# One line
# --------

# Fold one line into the state.
def Parse.step(+st: PState, k: R.LineKind, +line: List<&2, U32>) -> PState:
  match st:
    case MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}:
      match k:
        case R.KLevel{}:
          MkPS{
            1n+nl,
            Tb.Table.write_lv(
              lv, R.Reader.field("il", line), Parse.level_of(line, lv)),
            ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}
        case R.KExpr{}:
          MkPS{
            nl, lv,
            1n+ne,
            Tb.Table.write(
              ex,
              R.Reader.field("ie", line),
              Parse.expr_of(
                MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}, line)),
            ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}
        case R.KAxiom{}:
          MkPS{nl, lv, ne, ex,
            Con{Parse.decl_of(MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}, R.KAxiom{}, line), ds}, nt, zr, sc, pm, bl, yes, no, rc, eqn}
        case R.KDef{}:
          MkPS{nl, lv, ne, ex,
            Con{Parse.decl_of(MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}, R.KDef{}, line), ds}, nt, zr, sc, pm, bl, yes, no, rc, eqn}
        case R.KThm{}:
          MkPS{nl, lv, ne, ex,
            Con{Parse.decl_of(MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}, R.KThm{}, line), ds}, nt, zr, sc, pm, bl, yes, no, rc, eqn}
        case R.KOpaque{}:
          MkPS{nl, lv, ne, ex,
            Con{Parse.decl_of(MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}, R.KOpaque{}, line), ds}, nt, zr, sc, pm, bl, yes, no, rc, eqn}
        case R.KMeta{}:
          MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}
        case R.KName{}:
          MkPS{nl, lv, ne, ex, ds,
            Parse.upd_nat(line, nt),
            Parse.upd_under_nat(line, "zero", nt, zr),
            Parse.upd_under_nat(line, "succ", nt, sc),
            Parse.upd_prims(line, nt, pm),
            Parse.upd_bool(line, bl),
            Parse.upd_under_nat(line, "true", bl, yes),
            Parse.upd_under_nat(line, "false", bl, no),
            Parse.upd_rec(line, rc),
            Parse.upd_eq(line, eqn)}
        case R.KInductive{}:
          MkPS{nl, lv, ne, ex,
            Parse.block_of(line, MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}),
            nt, zr, sc, pm, bl, yes, no, rc, eqn}
        case R.KQuot{}:
          MkPS{nl, lv, ne, ex,
            Con{Parse.quot_of(MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}, line), ds},
            nt, zr, sc, pm, bl, yes, no, rc, eqn}
        case R.KOther{}:
          MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}

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
    case MkPS{nl, lv, ne, ex, ds, nt, zr, sc, pm, bl, yes, no, rc, eqn}:
      Parse.rev_decls(Parse.fuel(), Nil{}, ds)

# Parse a whole export.
def Parse.run(+xs: List<&2, U32>) -> PState:
  Parse.go(Parse.fuel(), B.Bytes.is_empty(xs), Parse.start(), xs)
