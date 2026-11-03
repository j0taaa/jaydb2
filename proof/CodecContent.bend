# Links the UTF-8 transducer to the REAL Content state and a u64 length
# obtained from nat64. Body and ceiling are not used as fuel.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecUTF8.bend as U
import ./CodecCounters.bend as N
import ./CodecTrace.bend as R

def PartialPending(e: C.Scalar) -> Type:
  match e:
    case C.Partial{C.Start{}}:
      Empty
    case C.Partial{C.Continue{0n, cp, minimum}}:
      Empty
    case C.Partial{C.Continue{1n+p, cp, minimum}}:
      Unit
    case C.Character{cp}:
      Unit
    case C.UTFInvalid{}:
      Unit

def checked_pending(ok: Bool, cp: U32) -> PartialPending(C.scalar_checked(ok, cp)):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      Unit{}

law complete_only_leaves_continuation_pending:
  for n: Nat
  for +cp: U32
  for +minimum: U32
  PartialPending(C.complete_utf8(n, cp, minimum))
def complete_only_leaves_continuation_pending(n, cp, minimum):
  match n:
    case 0n:
      checked_pending(U32.is_ge(cp, minimum) && B.code_valid(cp), cp)
    case 1n+p:
      Unit{}

law resume_only_leaves_continuation_pending:
  for ok: Bool
  for n: Nat
  for cp: U32
  for minimum: U32
  for b: U32
  PartialPending(C.resume_utf8(ok, n, cp, minimum, b))
def resume_only_leaves_continuation_pending(ok, n, cp, minimum, b):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      complete_only_leaves_continuation_pending(n, (cp * 64 + b - 128 : U32), minimum)

law start_only_leaves_continuation_pending:
  for ascii: Bool
  for two: Bool
  for three: Bool
  for four: Bool
  for b: U32
  PartialPending(C.start_utf8(ascii, two, three, four, b))
def start_only_leaves_continuation_pending(ascii, two, three, four, b):
  match ascii two three four:
    case True{} _ _ _:
      Unit{}
    case False{} True{} _ _:
      Unit{}
    case False{} False{} True{} _:
      Unit{}
    case False{} False{} False{} True{}:
      Unit{}
    case False{} False{} False{} False{}:
      Unit{}

law step_only_leaves_continuation_pending:
  for u: C.Unicode
  for +b: U32
  PartialPending(C.step_utf8(u, b))
def step_only_leaves_continuation_pending(u, b):
  match u:
    case C.Start{}:
      start_only_leaves_continuation_pending(U32.is_lt(b, 128), U32.is_ge(b, 194) && U32.is_le(b, 223), U32.is_ge(b, 224) && U32.is_le(b, 239), U32.is_ge(b, 240) && U32.is_le(b, 244), b)
    case C.Continue{0n, cp, minimum}:
      Unit{}
    case C.Continue{1n+p, cp, minimum}:
      resume_only_leaves_continuation_pending(U32.is_ge(b, 128) && U32.is_le(b, 191), p, cp, minimum, b)

def conclude_text(name: Bool, stack: C.Stack, t: U.TextValue) -> C.Machine:
  match t:
    case U.TextInvalid{}:
      C.Invalid{}
    case U.Reading{C.Start{}, inverted}:
      C.emit_text(name, String.reverse(inverted), stack)
    case U.Reading{C.Continue{n, cp, minimum}, inverted}:
      C.Invalid{}

law last_scalar_concludes_exactly_o_text:
  for +e: C.Scalar
  for name: Bool
  for q: B.Number64
  for +inverted: String
  for +stack: C.Stack
  for pending: PartialPending(e)
  {C.store_scalar(e, True{}, name, q, inverted, stack) == conclude_text(name, stack, U.join(e, inverted)) : C.Machine}
def last_scalar_concludes_exactly_o_text(e, name, q, inverted, stack, pending):
  match e:
    case C.UTFInvalid{}:
      {==}
    case C.Character{cp}:
      {==}
    case C.Partial{C.Start{}}:
      L.ex_false({C.Invalid{} == C.emit_text(name, String.reverse(inverted), stack) : C.Machine}, pending)
    case C.Partial{C.Continue{0n, cp, minimum}}:
      {==}
    case C.Partial{C.Continue{1n+p, cp, minimum}}:
      {==}

law execute_invalid_remains_invalid:
  for bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  {R.machine(R.execute(bs, R.Frame{body, ceiling, C.Invalid{}})) == C.Invalid{} : C.Machine}
def execute_invalid_remains_invalid(bs, body, ceiling):
  match bs:
    case Nil{}:
      {==}
    case Con{b, t}:
      execute_invalid_remains_invalid(t, C.decrease64(body), C.decrease64(ceiling))

law text_invalid_remains_invalid:
  for bs: List<&2, U32>
  {U.traverse_text(bs, U.TextInvalid{}) == U.TextInvalid{} : U.TextValue}
def text_invalid_remains_invalid(bs):
  match bs:
    case Nil{}:
      {==}
    case Con{b, t}:
      text_invalid_remains_invalid(t)

# Positive quantity; merely a byte-list shape, not canonicity.
def NotEmpty(bs: List<&2, U32>) -> Type:
  match bs:
    case Nil{}:
      Empty
    case Con{h, t}:
      Unit

def process_content(bs: List<&2, U32>, +q: B.Number64,
  body: B.Number64, ceiling: B.Number64, name: Bool, u: C.Unicode,
  inverted: String, stack: C.Stack) -> C.Machine:
  R.machine(R.execute(bs, R.Frame{body, ceiling,
    C.Content{name, C.one64(q), C.decrease64(q), u, inverted, stack}}))

# The callback is the induction hypothesis on the structural TAIL and is
# supplied by the theorem below. It is not a public soundness premise.
def resume_after_scalar(+e: C.Scalar, +bs: List<&2, U32>, +q: B.Number64,
  +body: B.Number64, +ceiling: B.Number64, +name: Bool,
  +inverted: String, +stack: C.Stack,
  resume: @u: C.Unicode -> @text: String ->
    {process_content(bs, q, body, ceiling, name, u, text, stack) ==
      conclude_text(name, stack, U.traverse_text(bs, U.Reading{u, text})) : C.Machine}) ->
  {R.machine(R.execute(bs, R.Frame{body, ceiling, C.store_scalar(e, False{}, name, q, inverted, stack)})) ==
    conclude_text(name, stack, U.traverse_text(bs, U.join(e, inverted))) : C.Machine}:
  match e:
    case C.UTFInvalid{}:
      %Equal.sym(U.TextValue, U.traverse_text(bs, U.TextInvalid{}), U.TextInvalid{}, text_invalid_remains_invalid(bs)) :
        {R.machine(R.execute(bs, R.Frame{body, ceiling, C.Invalid{}})) == conclude_text(name, stack, _) : C.Machine}
      execute_invalid_remains_invalid(bs, body, ceiling)
    case C.Character{cp}:
      resume(C.Start{}, SCon{Chr{cp}, inverted})
    case C.Partial{u}:
      resume(u, inverted)

law content_counted_consume_exactly_o_text:
  for +bs: List<&2, U32>
  for +q: B.Number64
  for +body: B.Number64
  for +ceiling: B.Number64
  for +name: Bool
  for +u: C.Unicode
  for +inverted: String
  for +stack: C.Stack
  for positive: NotEmpty(bs)
  for +measured: {B.nat64(B.length(bs)) == Some{q} : Maybe<&2, B.Number64>}
  {process_content(bs, q, body, ceiling, name, u, inverted, stack) ==
    conclude_text(name, stack, U.traverse_text(bs, U.Reading{u, inverted})) : C.Machine}
def content_counted_consume_exactly_o_text(bs, q, body, ceiling, name, u, inverted, stack, positive, measured):
  match bs:
    case Nil{}:
      L.ex_false({process_content(Nil{}, q, body, ceiling, name, u, inverted, stack) == conclude_text(name, stack, U.Reading{u, inverted}) : C.Machine}, positive)
    case Con{+b, Nil{}}:
      %F.some_injective(B.Number64, B.Number64{0, 1}, q, measured) :
        {process_content(Con{b, Nil{}}, _, body, ceiling, name, u, inverted, stack) == conclude_text(name, stack, U.join(C.step_utf8(u, b), inverted)) : C.Machine}
      last_scalar_concludes_exactly_o_text(C.step_utf8(u, b), name, B.Number64{0, 0}, inverted, stack, step_only_leaves_continuation_pending(u, b))
    case Con{+b, Con{+c, +rest}}:
      +t = {Con{c, rest} : List<&2, U32>}
      %Equal.sym(Bool, C.one64(q), False{}, N.one64_reflects_count_natural(B.length(Con{b, t}), q, measured)) :
        {R.machine(R.execute(t, R.Frame{C.decrease64(body), C.decrease64(ceiling), C.store_scalar(C.step_utf8(u, b), _, name, C.decrease64(q), inverted, stack)})) ==
          conclude_text(name, stack, U.traverse_text(t, U.join(C.step_utf8(u, b), inverted))) : C.Machine}
      resume_after_scalar(C.step_utf8(u, b), t, C.decrease64(q), C.decrease64(body), C.decrease64(ceiling), name, inverted, stack,
        next => text => content_counted_consume_exactly_o_text(t, C.decrease64(q), C.decrease64(body), C.decrease64(ceiling), name, next, text, stack, Unit{},
          N.length_of_tail_and_decrement_of_body(b, t, q, measured)))
