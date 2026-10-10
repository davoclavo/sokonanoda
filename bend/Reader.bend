# Reading a Lean export, line by line.
#
# An export is NDJSON: one JSON object per line, each assigning an index in the
# name table, the level table, or the expression table, or declaring a constant.
# A line is short, a file is not, so the walk over the file is tail recursive
# and the work inside a line need not be.
#
# The keys inside an object are not in a fixed order across line kinds. In one
# line `"ie"` comes first and in another it comes last, so a field is found by
# searching the line for its key rather than by position. `Bytes.find` does
# that search.
#
# Every function that walks the file keeps its recursive call in tail position,
# for the reason `Bytes.bend` explains.

import Base
import ./Bytes.bend as B

# A line and the bytes after it.
type Line is Data:
  LLine{line: List<&2, U32>, rest: List<&2, U32>}
  LEnd{}

# What kind of line this is. The reader dispatches on it.
type LineKind is Data:
  KMeta{}
  KName{}
  KLevel{}
  KExpr{}
  KAxiom{}
  KDef{}
  KThm{}
  KInductive{}
  KQuot{}
  KOpaque{}
  KOther{}

# Fuel for one line. A line of an export is well under this.
def Reader.line_fuel() -> Nat:
  65536n

# Peek: is the stream empty, or does it start with a newline?
def Reader.at_stop(+xs: List<&2, U32>) -> Bool:
  Bool.or(B.Bytes.is_empty(xs), B.Bytes.starts_with(xs, B.Bytes.newline()))

# Reverse a list with a tail accumulator. Base's reverse is fine for a line,
# but this keeps the file's one idiom everywhere.
def Reader.rev(fuel: Nat, +acc: List<&2, U32>, xs: List<&2, U32>) -> List<&2, U32>:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      match xs:
        case Nil{}:
          acc
        case Con{c, r}:
          Reader.rev(f, Con{c, acc}, r)

# Drop a leading newline, so the next line starts clean.
def Reader.drop_nl(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{c, r}:
      r

# Finish a line: put its bytes back in order and step past the newline.
def Reader.finish(+acc: List<&2, U32>, xs: List<&2, U32>) -> Line:
  LLine{Reader.rev(Reader.line_fuel(), Nil{}, acc), Reader.drop_nl(xs)}

# Take one line. `stop` says the head ends the line, which the caller
# establishes with `Reader.at_stop`.
def Reader.line_go(fuel: Nat, stop: Bool, +acc: List<&2, U32>, xs: List<&2, U32>) -> Line:
  match fuel:
    case 0n:
      LEnd{}
    case 1n+f:
      match stop:
        case True{}:
          Reader.finish(acc, xs)
        case False{}:
          match xs:
            case Nil{}:
              Reader.finish(acc, Nil{})
            case Con{c, +r}:
              Reader.line_go(f, Reader.at_stop(r), Con{c, acc}, r)

# Choose between the end of the file and one more line.
def Reader.line_pick(done: Bool, fuel: Nat, +xs: List<&2, U32>) -> Line:
  match done:
    case True{}:
      LEnd{}
    case False{}:
      Reader.line_go(fuel, Reader.at_stop(xs), Nil{}, xs)

# Take one line from the stream. An empty stream answers `LEnd`.
def Reader.line(fuel: Nat, +xs: List<&2, U32>) -> Line:
  Reader.line_pick(B.Bytes.is_empty(xs), fuel, xs)

# The bytes of a line, or empty at the end of the file.
def Reader.line_bytes(l: Line) -> List<&2, U32>:
  match l:
    case LLine{line, rest}:
      line
    case LEnd{}:
      Nil{}

# What follows a line, or empty at the end of the file.
def Reader.line_rest(l: Line) -> List<&2, U32>:
  match l:
    case LLine{line, rest}:
      rest
    case LEnd{}:
      Nil{}

# The bytes of a key, as it appears in the file: quoted and followed by a colon.
def Reader.keybytes(+key: String) -> List<&2, U32>:
  B.Bytes.of_string("\"" ++ key ++ "\":")

# Does this line start with the given key, right after the opening brace?
def Reader.heads(+key: String, +line: List<&2, U32>) -> Bool:
  B.Bytes.is_hit(B.Bytes.of_string("{\"" ++ key ++ "\":"), line)

# An expression line opens with `"ie"` or with one of the node keys.
def Reader.line_kind_expr(+line: List<&2, U32>) -> Bool:
  Bool.or(
    Bool.or(
      Bool.or(Reader.heads("ie", line), Reader.heads("app", line)),
      Bool.or(Reader.heads("bvar", line), Reader.heads("const", line))),
    Bool.or(
      Bool.or(Reader.heads("lam", line), Reader.heads("forallE", line)),
      Bool.or(Reader.heads("letE", line), Reader.heads("proj", line))))

# Pick the first kind whose test came back true.

def Reader.line_kind_of(
  meta: Bool, name: Bool, level: Bool, expr: Bool,
  ax: Bool, dfn: Bool, thm: Bool, ind: Bool, quot: Bool, opq: Bool
) -> LineKind:
  match meta:
    case True{}:
      KMeta{}
    case False{}:
      match name:
        case True{}:
          KName{}
        case False{}:
          match level:
            case True{}:
              KLevel{}
            case False{}:
              match expr:
                case True{}:
                  KExpr{}
                case False{}:
                  match ax:
                    case True{}:
                      KAxiom{}
                    case False{}:
                      match dfn:
                        case True{}:
                          KDef{}
                        case False{}:
                          match thm:
                            case True{}:
                              KThm{}
                            case False{}:
                              match ind:
                                case True{}:
                                  KInductive{}
                                case False{}:
                                  match quot:
                                    case True{}:
                                      KQuot{}
                                    case False{}:
                                      match opq:
                                        case True{}:
                                          KOpaque{}
                                        case False{}:
                                          KOther{}

# Classify a line by the key it opens with.
def Reader.line_kind(+line: List<&2, U32>) -> LineKind:
  Reader.line_kind_of(
    Reader.heads("meta", line),
    Reader.heads("in", line),
    Reader.heads("il", line),
    Reader.line_kind_expr(line),
    Reader.heads("axiom", line),
    Reader.heads("def", line),
    Reader.heads("thm", line),
    Reader.heads("inductive", line),
    Reader.heads("quot", line),
    Reader.heads("opaque", line))

# The stream a position left, or empty.
def Reader.pos_of(p: B.Pos) -> List<&2, U32>:
  match p:
    case B.POk{rest}:
      rest
    case B.PBad{}:
      Nil{}

# The number a scan found, or zero.
def Reader.num_of(s: B.Scan) -> Nat:
  match s:
    case B.SOk{v, rest}:
      v
    case B.SBad{}:
      0n

# Is this key present anywhere in the line? A field that is absent and a field
# whose value is zero both read as zero, so the two need telling apart.
def Reader.has(+key: String, +line: List<&2, U32>) -> Bool:
  B.Bytes.pos_ok(
    B.Bytes.find(
      Reader.line_fuel(),
      B.Bytes.is_hit(Reader.keybytes(key), line),
      Reader.keybytes(key),
      line))

# The bytes after `key`, or empty when the key is absent.
def Reader.after(+key: String, +line: List<&2, U32>) -> List<&2, U32>:
  Reader.pos_of(
    B.Bytes.find(
      Reader.line_fuel(),
      B.Bytes.is_hit(Reader.keybytes(key), line),
      Reader.keybytes(key),
      line))

# Take bytes up to, but not including, `b`. `stop` says the head is `b`.
def Reader.upto(fuel: Nat, stop: Bool, +acc: List<&2, U32>, +b: U32, xs: List<&2, U32>) -> List<&2, U32>:
  match fuel:
    case 0n:
      Reader.rev(Reader.line_fuel(), Nil{}, acc)
    case 1n+f:
      match stop:
        case True{}:
          Reader.rev(Reader.line_fuel(), Nil{}, acc)
        case False{}:
          match xs:
            case Nil{}:
              Reader.rev(Reader.line_fuel(), Nil{}, acc)
            case Con{c, +r}:
              Reader.upto(f, B.Bytes.starts_with(r, b), Con{c, acc}, b, r)

# Reverse a list of numbers with a tail accumulator.
def Reader.rev_nats(fuel: Nat, +acc: List<&2, Nat>, xs: List<&2, Nat>) -> List<&2, Nat>:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      match xs:
        case Nil{}:
          acc
        case Con{c, r}:
          Reader.rev_nats(f, Con{c, acc}, r)

# The bytes a scan left behind.
def Reader.rest_of(s: B.Scan) -> List<&2, U32>:
  match s:
    case B.SOk{v, rest}:
      rest
    case B.SBad{}:
      Nil{}

# What follows a number at the head of the stream.
def Reader.skip_num(fuel: Nat, +xs: List<&2, U32>) -> List<&2, U32>:
  Reader.rest_of(B.Bytes.number(fuel, xs))

# Every number in a byte range, in order. Non-digits are skipped, so this reads
# a JSON array of numbers such as `[1,2,3]` once the brackets are stripped.
def Reader.nums(fuel: Nat, dig: Bool, +acc: List<&2, Nat>, +xs: List<&2, U32>) -> List<&2, Nat>:
  match fuel:
    case 0n:
      Reader.rev_nats(Reader.line_fuel(), Nil{}, acc)
    case 1n+f:
      match dig:
        case True{}:
          Reader.nums(
            f,
            B.Bytes.starts_digit(Reader.skip_num(Reader.line_fuel(), xs)),
            Con{Reader.num_of(B.Bytes.number(Reader.line_fuel(), xs)), acc},
            Reader.skip_num(Reader.line_fuel(), xs))
        case False{}:
          match xs:
            case Nil{}:
              Reader.rev_nats(Reader.line_fuel(), Nil{}, acc)
            case Con{c, +r}:
              Reader.nums(f, B.Bytes.starts_digit(r), acc, r)

# Every number in the JSON array that follows `key`.
def Reader.num_list(+key: String, +line: List<&2, U32>) -> List<&2, Nat>:
  Reader.nums(
    Reader.line_fuel(),
    False{},
    Nil{},
    Reader.upto(
      Reader.line_fuel(),
      False{},
      Nil{},
      93,
      Reader.after(key, line)))

# Nested structure
# ----------------
#
# An inductive block nests arrays of objects, and the same key appears in
# several of them: `name` is in the type, in every constructor and in the
# recursor. So a field cannot be found by taking the first occurrence in the
# line. The bytes have to be cut into the array, and the array into its
# objects, before a field is read.
#
# Brackets and braces are counted for that. A line of an export has no string
# that contains a bracket, so counting is enough and no quote tracking is
# needed.

# Is this byte an opening bracket or brace?
def Reader.is_open(+c: U32) -> Bool:
  Bool.or(U32.is_eq(c, 91), U32.is_eq(c, 123))

# Is this byte a closing bracket or brace?
def Reader.is_close(+c: U32) -> Bool:
  Bool.or(U32.is_eq(c, 93), U32.is_eq(c, 125))

# Choose between two numbers on a computed Bool.
def Reader.pick_nat(b: Bool, x: Nat, y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

# The depth after this byte.
def Reader.bump(+d: Nat, +c: U32) -> Nat:
  Reader.pick_nat(
    Reader.is_open(c),
    1n+d,
    Reader.pick_nat(Reader.is_close(c), Nat.sub(d, 1n), d))

# Drop the head of a list.
def Reader.drop1(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{c, r}:
      r

# The bytes inside a bracketed run, with the brackets removed. `xs` must start
# at the opening bracket. `started` is false for that first byte, which is
# consumed but not kept; the run ends when the depth returns to zero, and the
# closing byte was accumulated by then, so the head of the accumulator goes.
def Reader.bal(fuel: Nat, started: Bool, d: Nat, +acc: List<&2, U32>, xs: List<&2, U32>) -> List<&2, U32>:
  match fuel:
    case 0n:
      Reader.rev(Reader.line_fuel(), Nil{}, acc)
    case 1n+f:
      match started:
        case False{}:
          match xs:
            case Nil{}:
              Nil{}
            case Con{+c, r}:
              Reader.bal(f, True{}, Reader.bump(0n, c), acc, r)
        case True{}:
          match d:
            case 0n:
              Reader.rev(Reader.line_fuel(), Nil{}, Reader.drop1(acc))
            case 1n+dd:
              match xs:
                case Nil{}:
                  Reader.rev(Reader.line_fuel(), Nil{}, acc)
                case Con{+c, r}:
                  Reader.bal(f, True{}, Reader.bump(1n+dd, c), Con{c, acc}, r)

# The contents of the array or object that follows `key`.
def Reader.inside(+key: String, +line: List<&2, U32>) -> List<&2, U32>:
  Reader.bal(Reader.line_fuel(), False{}, 0n, Nil{}, Reader.after(key, line))

# One object of a comma-separated list, and what follows it. `d` is the depth
# and `started` says the opening brace has been passed, as in `Reader.bal`.
def Reader.obj(fuel: Nat, started: Bool, d: Nat, +acc: List<&2, U32>, xs: List<&2, U32>) -> Line:
  match fuel:
    case 0n:
      LEnd{}
    case 1n+f:
      match started:
        case False{}:
          match xs:
            case Nil{}:
              LEnd{}
            case Con{+c, r}:
              Reader.obj(f, True{}, Reader.bump(0n, c), acc, r)
        case True{}:
          match d:
            case 0n:
              LLine{
                Reader.rev(Reader.line_fuel(), Nil{}, Reader.drop1(acc)),
                xs}
            case 1n+dd:
              match xs:
                case Nil{}:
                  LLine{Reader.rev(Reader.line_fuel(), Nil{}, acc), Nil{}}
                case Con{+c, r}:
                  Reader.obj(f, True{}, Reader.bump(1n+dd, c), Con{c, acc}, r)

# Peek: is there another object here? The separator is a comma, which is
# skipped before the test.
def Reader.more_objs(+xs: List<&2, U32>) -> Bool:
  Bool.or(
    B.Bytes.starts_with(xs, 123),
    Bool.and(B.Bytes.starts_with(xs, 44), B.Bytes.starts_with(Reader.drop1(xs), 123)))

# Choose between two byte lists on a computed Bool.
def Reader.pick_bytes(b: Bool, x: List<&2, U32>, y: List<&2, U32>) -> List<&2, U32>:
  match b:
    case True{}:
      x
    case False{}:
      y

# Step past a separating comma.
def Reader.skip_comma(+xs: List<&2, U32>) -> List<&2, U32>:
  Reader.pick_bytes(B.Bytes.starts_with(xs, 44), Reader.drop1(xs), xs)

# Reverse a list of objects.
def Reader.rev_objs(
  fuel: Nat, +acc: List<&2, List<&2, U32>>, xs: List<&2, List<&2, U32>>
) -> List<&2, List<&2, U32>>:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      match xs:
        case Nil{}:
          acc
        case Con{h, t}:
          Reader.rev_objs(f, Con{h, acc}, t)

# Split a comma-separated list of objects. `go` says another object follows.
def Reader.objects(
  fuel: Nat, go: Bool, +out: List<&2, List<&2, U32>>, xs: List<&2, U32>
) -> List<&2, List<&2, U32>>:
  match fuel:
    case 0n:
      Reader.rev_objs(Reader.line_fuel(), Nil{}, out)
    case 1n+f:
      match go:
        case False{}:
          Reader.rev_objs(Reader.line_fuel(), Nil{}, out)
        case True{}:
          +o = Reader.obj(Reader.line_fuel(), False{}, 0n, Nil{}, Reader.skip_comma(xs))
          Reader.objects(
            f,
            Reader.more_objs(Reader.line_rest(o)),
            Con{Reader.line_bytes(o), out},
            Reader.line_rest(o))

# The objects of the array that follows `key`.
def Reader.obj_list(+key: String, +line: List<&2, U32>) -> List<&2, List<&2, U32>>:
  +inner = Reader.inside(key, line)
  Reader.objects(Reader.line_fuel(), Reader.more_objs(inner), Nil{}, inner)

# The number that follows `key` in this line, or zero.
def Reader.field(+key: String, +line: List<&2, U32>) -> Nat:
  Reader.num_of(
    B.Bytes.number(
      Reader.line_fuel(),
      Reader.pos_of(
        B.Bytes.find(
          Reader.line_fuel(),
          B.Bytes.is_hit(B.Bytes.of_string("\"" ++ key ++ "\":"), line),
          B.Bytes.of_string("\"" ++ key ++ "\":"),
          line))))
