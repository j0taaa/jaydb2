import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D

# Public API: decode(bytes, B.Number64{high, low}) -> Outcome.
# bytes is the complete BODY (without the eight outer framing bytes).
# The public limit counts body bytes, including tags and lengths.
# Decoded contains exactly D.Value; Input rejects syntax, Unicode,
# names, truncation and extra bytes; Limit means body or declared minimum
# exceeds the limit/u64. Equality with the limit is allowed.
# Reception and framing belong to the caller; there is no physical budget.
# No client counter becomes Nat, an allocation or fuel. The machine
# advances once per byte; emit pops structurally. Therefore there is
# no additional ceiling on depth, quantity or text size.
type Outcome is Data:
  Decoded{value: D.Value}
  Input{}
  Limit{}

def zero64(+n: B.Number64) -> Bool:
  B.Number64{a, b} = n
  U32.is_eq(a, 0) && U32.is_eq(b, 0)

def one64(n: B.Number64) -> Bool:
  B.Number64{a, b} = n
  U32.is_eq(a, 0) && U32.is_eq(b, 1)

def less_equal64(a: B.Number64, b: B.Number64) -> Bool:
  B.Number64{+ah, al} = a
  B.Number64{+bh, bl} = b
  U32.is_lt(ah, bh) || (U32.is_eq(ah, bh) && U32.is_le(al, bl))

def decrease64_cases(low_zero: Bool, high_zero: Bool, a: U32, b: U32) -> B.Number64:
  match low_zero high_zero:
    case False{} _:
      B.Number64{a, (b - 1 : U32)}
    case True{} False{}:
      B.Number64{(a - 1 : U32), 4294967295}
    case True{} True{}:
      B.Number64{0, 0}

# Total at zero; transitions decrement only positive counters.
def decrease64(n: B.Number64) -> B.Number64:
  B.Number64{+a, +b} = n
  decrease64_cases(U32.is_eq(b, 0), U32.is_eq(a, 0), a, b)

def sum64_end(overflow: Bool, high: U32, low: U32) -> Maybe<&2, B.Number64>:
  match overflow:
    case True{}:
      None{}
    case False{}:
      Some{B.Number64{high, low}}

def sum64_transport(carry: Bool, +high: U32, low: U32, overflow: Bool) -> Maybe<&2, B.Number64>:
  match carry:
    case False{}:
      sum64_end(overflow, high, low)
    case True{}:
      sum64_end(overflow || U32.is_eq(high, 4294967295), (high + 1 : U32), low)

def sum64(a: B.Number64, b: B.Number64) -> Maybe<&2, B.Number64>:
  B.Number64{+ah, +al} = a
  B.Number64{bh, bl} = b
  +low = (al + bl : U32)
  +high = (ah + bh : U32)
  sum64_transport(U32.is_lt(low, al), high, low, U32.is_lt(high, ah))

def sum_optional(a: Maybe<&2, B.Number64>, b: Maybe<&2, B.Number64>) -> Maybe<&2, B.Number64>:
  match a b:
    case Some{x} Some{y}:
      sum64(x, y)
    case _ _:
      None{}

def multiply_small(n: Nat, +x: B.Number64) -> Maybe<&2, B.Number64>:
  match n:
    case 0n:
      Some{B.Number64{0, 0}}
    case 1n:
      Some{x}
    case 1n+p:
      sum_optional(Some{x}, multiply_small(p, x))

def sum_pending_cases(empty: Bool, n: B.Number64, factor: Nat, rest: Maybe<&2, B.Number64>) -> Maybe<&2, B.Number64>:
  match empty:
    case True{}:
      rest
    case False{}:
      sum_optional(multiply_small(factor, n), rest)

# Does not multiply/add empty ancestor counters already at the last child.
def sum_pending(+n: B.Number64, factor: Nat, rest: Maybe<&2, B.Number64>) -> Maybe<&2, B.Number64>:
  sum_pending_cases(zero64(n), n, factor, rest)

type Stack is Data:
  Root{}
  ListFrame{last: Bool, remaining: B.Number64, inverted: List<&2, D.Value>, parent: Stack}
  Name{last: Bool, remaining: B.Number64, previous: String, inverted: List<&2, D.Field>, parent: Stack}
  Field{last: Bool, remaining: B.Number64, name: String, inverted: List<&2, D.Field>, parent: Stack}

type Purpose is Data:
  Integer{}
  TextValue{}
  NameText{}
  CountsList{}
  CountsRecord{}

type Unicode is Data:
  Start{}
  Continue{missing: Nat, code: U32, minimum: U32}

type Scalar is Data:
  Character{code: U32}
  Partial{state: Unicode}
  UTFInvalid{}

type Machine is Data:
  Tag{stack: Stack}
  TagName{stack: Stack}
  WordInput{purpose: Purpose, missing: Nat, high: U32, low: U32, stack: Stack}
  Content{name: Bool, last: Bool, remaining: B.Number64, unicode: Unicode, inverted: String, stack: Stack}
  DecodedReady{value: D.Value}
  Invalid{}
  Above{}

def assemble_list(xs: List<&2, D.Value>, acc: D.Value) -> D.Value:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      assemble_list(t, D.VList{h, acc})

def assemble_record(xs: List<&2, D.Field>, acc: D.Value) -> D.Value:
  match xs:
    case Nil{}:
      acc
    case Con{D.Field{n, v}, t}:
      assemble_record(t, D.VRecord{n, v, acc})

# The last child may complete any number of ancestors without reading bytes.
# Recursion descends only through the original stack's parent field.
def emit(stack: Stack, value: D.Value) -> Machine:
  match stack:
    case Root{}:
      DecodedReady{value}
    case ListFrame{True{}, q, xs, parent}:
      emit(parent, assemble_list(Con{value, xs}, D.VListEmpty{}))
    case ListFrame{False{}, +q, xs, parent}:
      Tag{ListFrame{one64(q), decrease64(q), Con{value, xs}, parent}}
    case Field{True{}, q, n, xs, parent}:
      emit(parent, assemble_record(Con{D.Field{n, value}, xs}, D.VRecordEmpty{}))
    case Field{False{}, +q, +n, xs, parent}:
      TagName{Name{one64(q), decrease64(q), n, Con{D.Field{n, value}, xs}, parent}}
    case Name{u, q, n, xs, parent}:
      Invalid{}

# Minimum of pending siblings; the current value has started and is excluded.
# A record pair needs at least 4/u64/one ASCII/tag: eleven bytes.
# During the current pair name, at least one value byte remains.
def minimum_stack(stack: Stack) -> Maybe<&2, B.Number64>:
  match stack:
    case Root{}:
      Some{B.Number64{0, 0}}
    case ListFrame{u, q, xs, parent}:
      sum_pending(q, 1n, minimum_stack(parent))
    case Name{u, q, n, xs, parent}:
      sum_optional(Some{B.Number64{0, 1}}, sum_pending(q, 11n, minimum_stack(parent)))
    case Field{u, q, n, xs, parent}:
      sum_pending(q, 11n, minimum_stack(parent))

type Check is Data:
  Fits{}
  Short{}
  Large{}

def check_cases(fits_limit: Bool, fits_body: Bool) -> Check:
  match fits_limit fits_body:
    case False{} _:
      Large{}
    case True{} False{}:
      Short{}
    case True{} True{}:
      Fits{}

def check(minimum: Maybe<&2, B.Number64>, body: B.Number64, ceiling: B.Number64) -> Check:
  match minimum:
    case None{}:
      Large{}
    case Some{+n}:
      check_cases(less_equal64(n, ceiling), less_equal64(n, body))

def minimum_field(f: Purpose, n: B.Number64) -> Maybe<&2, B.Number64>:
  match f:
    case CountsRecord{}:
      multiply_small(11n, n)
    case _:
      Some{n}

def open_name(fits: Bool, +n: B.Number64, stack: Stack) -> Machine:
  match fits:
    case False{}:
      Invalid{}
    case True{}:
      Content{True{}, one64(n), decrease64(n), Start{}, "", stack}

def open_variable(empty: Bool, f: Purpose, +n: B.Number64, stack: Stack) -> Machine:
  match empty f:
    case True{} TextValue{}:
      emit(stack, D.VText{""})
    case True{} CountsList{}:
      emit(stack, D.VListEmpty{})
    case True{} CountsRecord{}:
      emit(stack, D.VRecordEmpty{})
    case False{} TextValue{}:
      Content{False{}, one64(n), decrease64(n), Start{}, "", stack}
    case False{} NameText{}:
      open_name(less_equal64(n, B.Number64{0, 64}), n, stack)
    case False{} CountsList{}:
      Tag{ListFrame{one64(n), decrease64(n), Nil{}, stack}}
    case False{} CountsRecord{}:
      TagName{Name{one64(n), decrease64(n), "", Nil{}, stack}}
    case _ _:
      Invalid{}

def open_checked(c: Check, f: Purpose, +n: B.Number64, stack: Stack) -> Machine:
  match c:
    case Large{}:
      Above{}
    case Short{}:
      Invalid{}
    case Fits{}:
      open_variable(zero64(n), f, n, stack)

def conclude_word(f: Purpose, +high: U32, +low: U32, +stack: Stack, body: B.Number64, ceiling: B.Number64) -> Machine:
  match f:
    case Integer{}:
      emit(stack, D.VInt{high, low})
    case +other:
      +n = {B.Number64{high, low} : B.Number64}
      open_checked(check(sum_optional(minimum_field(other, n), minimum_stack(stack)), body, ceiling), other, n, stack)

def read_word(missing: Nat, f: Purpose, high: U32, +low: U32, b: U32, stack: Stack, body: B.Number64, ceiling: B.Number64) -> Machine:
  match missing:
    case 0n:
      conclude_word(f, (high * 256 + U32.shrn(low, 24n) : U32), (low * 256 + b : U32), stack, body, ceiling)
    case 1n+p:
      WordInput{f, p, (high * 256 + U32.shrn(low, 24n) : U32), (low * 256 + b : U32), stack}

def start_utf8(ascii: Bool, two: Bool, three: Bool, four: Bool, b: U32) -> Scalar:
  match ascii two three four:
    case True{} _ _ _:
      Character{b}
    case False{} True{} _ _:
      Partial{Continue{1n, (b - 192 : U32), 128}}
    case False{} False{} True{} _:
      Partial{Continue{2n, (b - 224 : U32), 2048}}
    case False{} False{} False{} True{}:
      Partial{Continue{3n, (b - 240 : U32), 65536}}
    case _ _ _ _:
      UTFInvalid{}

def scalar_checked(valid: Bool, cp: U32) -> Scalar:
  match valid:
    case False{}:
      UTFInvalid{}
    case True{}:
      Character{cp}

def complete_utf8(missing: Nat, +cp: U32, minimum: U32) -> Scalar:
  match missing:
    case 0n:
      scalar_checked(U32.is_ge(cp, minimum) && B.code_valid(cp), cp)
    case 1n+p:
      Partial{Continue{1n+p, cp, minimum}}

def resume_utf8(valid: Bool, missing: Nat, cp: U32, minimum: U32, b: U32) -> Scalar:
  match valid:
    case False{}:
      UTFInvalid{}
    case True{}:
      complete_utf8(missing, (cp * 64 + b - 128 : U32), minimum)

def step_utf8(u: Unicode, +b: U32) -> Scalar:
  match u:
    case Start{}:
      start_utf8(U32.is_lt(b, 128), U32.is_ge(b, 194) && U32.is_le(b, 223), U32.is_ge(b, 224) && U32.is_le(b, 239), U32.is_ge(b, 240) && U32.is_le(b, 244), b)
    case Continue{1n+p, cp, minimum}:
      resume_utf8(U32.is_ge(b, 128) && U32.is_le(b, 191), p, cp, minimum, b)
    case Continue{0n, cp, minimum}:
      UTFInvalid{}

def name_checked(valid: Bool, u: Bool, q: B.Number64, name: String, xs: List<&2, D.Field>, parent: Stack) -> Machine:
  match valid:
    case False{}:
      Invalid{}
    case True{}:
      Tag{Field{u, q, name, xs, parent}}

def emit_name(stack: Stack, +name: String) -> Machine:
  match stack:
    case Name{u, q, previous, xs, parent}:
      name_checked(D.name_valid(name) && String.is_lt(previous, name), u, q, name, xs, parent)
    case _:
      Invalid{}

def emit_text(name: Bool, text: String, stack: Stack) -> Machine:
  match name:
    case False{}:
      emit(stack, D.VText{text})
    case True{}:
      emit_name(stack, text)

def store_character(last: Bool, name: Bool, +q: B.Number64, text: String, stack: Stack) -> Machine:
  match last:
    case True{}:
      emit_text(name, String.reverse(text), stack)
    case False{}:
      Content{name, one64(q), decrease64(q), Start{}, text, stack}

def store_partial(last: Bool, name: Bool, +q: B.Number64, u: Unicode, text: String, stack: Stack) -> Machine:
  match last:
    case True{}:
      Invalid{}
    case False{}:
      Content{name, one64(q), decrease64(q), u, text, stack}

def store_scalar(e: Scalar, last: Bool, name: Bool, q: B.Number64, text: String, stack: Stack) -> Machine:
  match e:
    case UTFInvalid{}:
      Invalid{}
    case Character{cp}:
      store_character(last, name, q, SCon{Chr{cp}, text}, stack)
    case Partial{u}:
      store_partial(last, name, q, u, text, stack)

def read_tag(tag: Nat, stack: Stack) -> Machine:
  match tag:
    case 0n:
      emit(stack, D.VAbsent{})
    case 1n:
      emit(stack, D.VBool{False{}})
    case 2n:
      emit(stack, D.VBool{True{}})
    case 3n:
      WordInput{Integer{}, 7n, 0, 0, stack}
    case 4n:
      WordInput{TextValue{}, 7n, 0, 0, stack}
    case 5n:
      WordInput{CountsList{}, 7n, 0, 0, stack}
    case 6n:
      WordInput{CountsRecord{}, 7n, 0, 0, stack}
    case _:
      Invalid{}

def read_tag_name(correct: Bool, stack: Stack) -> Machine:
  match correct:
    case False{}:
      Invalid{}
    case True{}:
      WordInput{NameText{}, 7n, 0, 0, stack}

def step(m: Machine, b: U32, body: B.Number64, ceiling: B.Number64) -> Machine:
  match m:
    case Tag{stack}:
      read_tag(U32.to_nat(b), stack)
    case TagName{stack}:
      read_tag_name(U32.is_eq(b, 4), stack)
    case WordInput{f, n, high, low, stack}:
      read_word(n, f, high, low, b, stack, body, ceiling)
    case Content{name, last, q, u, text, stack}:
      store_scalar(step_utf8(u, b), last, name, q, text, stack)
    case DecodedReady{v}:
      Invalid{}
    case Invalid{}:
      Invalid{}
    case Above{}:
      Above{}

def finalize(m: Machine) -> Outcome:
  match m:
    case DecodedReady{v}:
      Decoded{v}
    case Above{}:
      Limit{}
    case _:
      Input{}

def traverse(bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64, m: Machine) -> Outcome:
  match bs:
    case Nil{}:
      finalize(m)
    case Con{h, t}:
      +rest = decrease64(body)
      +free = decrease64(ceiling)
      traverse(t, rest, free, step(m, h, rest, free))

def decode_octets(all_valid: Bool, bs: List<&2, U32>, body: B.Number64, ceiling: B.Number64) -> Outcome:
  match all_valid:
    case False{}:
      Input{}
    case True{}:
      traverse(bs, body, ceiling, Tag{Root{}})

def decode_size(fits: Bool, +bs: List<&2, U32>, body: B.Number64, ceiling: B.Number64) -> Outcome:
  match fits:
    case False{}:
      Limit{}
    case True{}:
      decode_octets(B.octets_all_valid(bs), bs, body, ceiling)

def decode_measure(n: Maybe<&2, B.Number64>, bs: List<&2, U32>, +ceiling: B.Number64) -> Outcome:
  match n:
    case None{}:
      Limit{}
    case Some{+body}:
      decode_size(less_equal64(body, ceiling), bs, body, ceiling)

def decode(+bytes: List<&2, U32>, limit: B.Number64) -> Outcome:
  decode_measure(B.nat64(B.length(bytes)), bytes, limit)
