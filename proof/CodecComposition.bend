# Compose segments in the REAL machine, preserving body/ceiling and stack.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecTrace.bend as R
import ./CodecWordsBE64.bend as H
import ./CodecTexts.bend as T
import ./CodecUTF8.bend as U
import ./CodecUTF8Inverse.bend as V
import ./CodecContent.bend as G
import ./CodecCounters.bend as N
import ./CodecSumsMinimum.bend as S
import ./CodecReservations.bend as Z
import ./CodecMinimum.bend as M

def later(+bs: List<&2, U32>, body: B.Number64, ceiling: B.Number64, m: C.Machine) -> R.Frame:
  R.Frame{H.decrease(B.length(bs), body), H.decrease(B.length(bs), ceiling), m}

# Extracting the machine hides no counter effect.
law execution_combined_machine_known_has_counters_exact:
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +m: C.Machine
  for -end: C.Machine
  for machine: {R.machine(R.execute(bs, R.Frame{body, ceiling, m})) == end : C.Machine}
  {R.execute(bs, R.Frame{body, ceiling, m}) == later(bs, body, ceiling, end) : R.Frame}
def execution_combined_machine_known_has_counters_exact(bs, body, ceiling, m, end, machine):
  match bs:
    case Nil{}:
      Equal.cong(C.Machine, R.Frame, x => R.Frame{body, ceiling, x}, m, end, machine)
    case Con{+b, +t}:
      %T.decrease_commutes_combined_iteration(B.length(t), body) :
        {R.execute(t, R.advance(R.Frame{body, ceiling, m}, b)) == R.Frame{_, C.decrease64(H.decrease(B.length(t), ceiling)), end} : R.Frame}
      %T.decrease_commutes_combined_iteration(B.length(t), ceiling) :
        {R.execute(t, R.advance(R.Frame{body, ceiling, m}, b)) == R.Frame{H.decrease(B.length(t), C.decrease64(body)), _, end} : R.Frame}
      execution_combined_machine_known_has_counters_exact(t, C.decrease64(body), C.decrease64(ceiling),
        C.step(m, b, C.decrease64(body), C.decrease64(ceiling)), end, machine)

law decrease_by_concatenation:
  for xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +q: B.Number64
  {H.decrease(B.length(B.concatenate(xs, ys)), q) == H.decrease(B.length(ys), H.decrease(B.length(xs), q)) : B.Number64}
def decrease_by_concatenation(xs, ys, q):
  match xs:
    case Nil{}:
      {==}
    case Con{b, +t}:
      Equal.trans(B.Number64,
        C.decrease64(H.decrease(B.length(B.concatenate(t, ys)), q)),
        H.decrease(B.length(B.concatenate(t, ys)), C.decrease64(q)),
        H.decrease(B.length(ys), C.decrease64(H.decrease(B.length(t), q))),
        Equal.sym(B.Number64, H.decrease(B.length(B.concatenate(t, ys)), C.decrease64(q)), C.decrease64(H.decrease(B.length(B.concatenate(t, ys)), q)), T.decrease_commutes_combined_iteration(B.length(B.concatenate(t, ys)), q)),
        Equal.trans(B.Number64,
          H.decrease(B.length(B.concatenate(t, ys)), C.decrease64(q)),
          H.decrease(B.length(ys), H.decrease(B.length(t), C.decrease64(q))),
          H.decrease(B.length(ys), C.decrease64(H.decrease(B.length(t), q))),
          decrease_by_concatenation(t, ys, C.decrease64(q)),
          Equal.cong(B.Number64, B.Number64, z => H.decrease(B.length(ys), z),
            H.decrease(B.length(t), C.decrease64(q)), C.decrease64(H.decrease(B.length(t), q)), T.decrease_commutes_combined_iteration(B.length(t), q))))

# Name=False and Name=True use the same transducer; the stack may contain
# arbitrary ancestors. emit_name checks name validity/order.
law content_canonical_emits_in_stack_original:
  for +s: String
  for +q: B.Number64
  for +body: B.Number64
  for +ceiling: B.Number64
  for +name: Bool
  for +stack: C.Stack
  for positive: G.NotEmpty(B.utf8(s))
  for valid: {B.text_valid(s) == True{} : Bool}
  for +measured: {B.nat64(B.length(B.utf8(s))) == Some{q} : Maybe<&2, B.Number64>}
  {R.execute(B.utf8(s), R.Frame{body, ceiling, C.Content{name, C.one64(q), C.decrease64(q), C.Start{}, "", stack}}) ==
    later(B.utf8(s), body, ceiling, C.emit_text(name, s, stack)) : R.Frame}
def content_canonical_emits_in_stack_original(s, q, body, ceiling, name, stack, positive, valid, measured):
  execution_combined_machine_known_has_counters_exact(B.utf8(s), body, ceiling,
    C.Content{name, C.one64(q), C.decrease64(q), C.Start{}, "", stack}, C.emit_text(name, s, stack),
    Equal.trans(C.Machine,
      G.process_content(B.utf8(s), q, body, ceiling, name, C.Start{}, "", stack),
      G.conclude_text(name, stack, U.traverse_text(B.utf8(s), U.Reading{C.Start{}, ""})), C.emit_text(name, s, stack),
      G.content_counted_consume_exactly_o_text(B.utf8(s), q, body, ceiling, name, C.Start{}, "", stack, positive, measured),
      T.conclude_transduction_accepts(name, stack, U.traverse_text(B.utf8(s), U.Reading{C.Start{}, ""}), s, V.utf8_text_valid_decodes_exactly(s, valid))))

def opening_textual_machine(+bs: List<&2, U32>, +q: B.Number64, +body: B.Number64, +ceiling: B.Number64,
  +stack: C.Stack, -s: String,
  +measured: {B.nat64(B.length(bs)) == Some{q} : Maybe<&2, B.Number64>},
  accepted: {U.finalize_text(U.traverse_text(bs, U.Reading{C.Start{}, ""})) == Some{s} : Maybe<&2, String>}) ->
  {R.machine(R.execute(bs, R.Frame{body, ceiling, C.open_variable(C.zero64(q), C.TextValue{}, q, stack)})) == C.emit(stack, D.VText{s}) : C.Machine}:
  match bs:
    case Nil{}:
      %F.some_injective(B.Number64, B.Number64{0, 0}, q, measured) :
        {R.machine(R.execute(Nil{}, R.Frame{body, ceiling, C.open_variable(C.zero64(_), C.TextValue{}, q, stack)})) == C.emit(stack, D.VText{s}) : C.Machine}
      Equal.cong(String, C.Machine, text => C.emit(stack, D.VText{text}), "", s, F.some_injective(String, "", s, accepted))
    case Con{+b, +t}:
      %Equal.sym(Bool, C.zero64(q), False{}, N.zero64_reflects_count_natural(B.length(Con{b, t}), q, measured)) :
        {R.machine(R.execute(Con{b, t}, R.Frame{body, ceiling, C.open_variable(_, C.TextValue{}, q, stack)})) == C.emit(stack, D.VText{s}) : C.Machine}
      Equal.trans(C.Machine,
        G.process_content(Con{b, t}, q, body, ceiling, False{}, C.Start{}, "", stack),
        G.conclude_text(False{}, stack, U.traverse_text(Con{b, t}, U.Reading{C.Start{}, ""})), C.emit(stack, D.VText{s}),
        G.content_counted_consume_exactly_o_text(Con{b, t}, q, body, ceiling, False{}, C.Start{}, "", stack, Unit{}, measured),
        T.conclude_transduction_accepts(False{}, stack, U.traverse_text(Con{b, t}, U.Reading{C.Start{}, ""}), s, accepted))

law opening_textual_canonical_emits_in_stack_original:
  for +bs: List<&2, U32>
  for +q: B.Number64
  for +body: B.Number64
  for +ceiling: B.Number64
  for +stack: C.Stack
  for -s: String
  for +measured: {B.nat64(B.length(bs)) == Some{q} : Maybe<&2, B.Number64>}
  for accepted: {U.finalize_text(U.traverse_text(bs, U.Reading{C.Start{}, ""})) == Some{s} : Maybe<&2, String>}
  {R.execute(bs, R.Frame{body, ceiling, C.open_variable(C.zero64(q), C.TextValue{}, q, stack)}) ==
    later(bs, body, ceiling, C.emit(stack, D.VText{s})) : R.Frame}
def opening_textual_canonical_emits_in_stack_original(bs, q, body, ceiling, stack, s, measured, accepted):
  execution_combined_machine_known_has_counters_exact(bs, body, ceiling,
    C.open_variable(C.zero64(q), C.TextValue{}, q, stack), C.emit(stack, D.VText{s}),
    opening_textual_machine(bs, q, body, ceiling, stack, s, measured, accepted))


def tag(f: C.Purpose) -> U32:
  match f:
    case C.Integer{}:
      3
    case C.TextValue{}:
      4
    case C.NameText{}:
      4
    case C.CountsList{}:
      5
    case C.CountsRecord{}:
      6

def start(f: C.Purpose, stack: C.Stack) -> C.Machine:
  match f:
    case C.NameText{}:
      C.TagName{stack}
    case _:
      C.Tag{stack}

def Variable(f: C.Purpose) -> Type:
  match f:
    case C.Integer{}:
      Empty
    case _:
      Unit

law tag_canonical_starts_to_purpose_exact:
  for +f: C.Purpose
  for +stack: C.Stack
  for body: B.Number64
  for ceiling: B.Number64
  {C.step(start(f, stack), tag(f), body, ceiling) == C.WordInput{f, 7n, 0, 0, stack} : C.Machine}
def tag_canonical_starts_to_purpose_exact(f, stack, body, ceiling):
  match f:
    case C.Integer{}:
      {==}
    case C.TextValue{}:
      {==}
    case C.NameText{}:
      {==}
    case C.CountsList{}:
      {==}
    case C.CountsRecord{}:
      {==}

law header_canonical_composed_preserves_all_to_stack:
  for +f: C.Purpose
  for +high: U32
  for +low: U32
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  {R.execute(Con{tag(f), B.be64(high, low)}, R.Frame{body, ceiling, start(f, stack)}) ==
    R.Frame{H.decrease(9n, body), H.decrease(9n, ceiling), C.conclude_word(f, high, low, stack, H.decrease(9n, body), H.decrease(9n, ceiling))} : R.Frame}
def header_canonical_composed_preserves_all_to_stack(f, high, low, stack, body, ceiling):
  %Equal.sym(C.Machine, C.step(start(f, stack), tag(f), C.decrease64(body), C.decrease64(ceiling)), C.WordInput{f, 7n, 0, 0, stack},
    tag_canonical_starts_to_purpose_exact(f, stack, C.decrease64(body), C.decrease64(ceiling))) :
    {R.execute(B.be64(high, low), R.Frame{C.decrease64(body), C.decrease64(ceiling), _}) ==
      R.Frame{H.decrease(9n, body), H.decrease(9n, ceiling), C.conclude_word(f, high, low, stack, H.decrease(9n, body), H.decrease(9n, ceiling))} : R.Frame}
  H.be64_concludes_word(f, high, low, stack, C.decrease64(body), C.decrease64(ceiling))

def conclude_variable_checked(+f: C.Purpose, +high: U32, +low: U32, +stack: C.Stack,
  +body: B.Number64, +ceiling: B.Number64, variable: Variable(f),
  fits: {C.check(C.sum_optional(C.minimum_field(f, B.Number64{high, low}), C.minimum_stack(stack)), body, ceiling) == C.Fits{} : C.Check}) ->
  {C.conclude_word(f, high, low, stack, body, ceiling) == C.open_variable(C.zero64(B.Number64{high, low}), f, B.Number64{high, low}, stack) : C.Machine}:
  match f:
    case C.Integer{}:
      L.ex_false({C.emit(stack, D.VInt{high, low}) == C.open_variable(C.zero64(B.Number64{high, low}), C.Integer{}, B.Number64{high, low}, stack) : C.Machine}, variable)
    case C.TextValue{}:
      Equal.cong(C.Check, C.Machine, c => C.open_checked(c, C.TextValue{}, B.Number64{high, low}, stack),
        C.check(C.sum_optional(C.minimum_field(C.TextValue{}, B.Number64{high, low}), C.minimum_stack(stack)), body, ceiling), C.Fits{}, fits)
    case C.NameText{}:
      Equal.cong(C.Check, C.Machine, c => C.open_checked(c, C.NameText{}, B.Number64{high, low}, stack),
        C.check(C.sum_optional(C.minimum_field(C.NameText{}, B.Number64{high, low}), C.minimum_stack(stack)), body, ceiling), C.Fits{}, fits)
    case C.CountsList{}:
      Equal.cong(C.Check, C.Machine, c => C.open_checked(c, C.CountsList{}, B.Number64{high, low}, stack),
        C.check(C.sum_optional(C.minimum_field(C.CountsList{}, B.Number64{high, low}), C.minimum_stack(stack)), body, ceiling), C.Fits{}, fits)
    case C.CountsRecord{}:
      Equal.cong(C.Check, C.Machine, c => C.open_checked(c, C.CountsRecord{}, B.Number64{high, low}, stack),
        C.check(C.sum_optional(C.minimum_field(C.CountsRecord{}, B.Number64{high, low}), C.minimum_stack(stack)), body, ceiling), C.Fits{}, fits)

# Hypotheses are mathematical measures of pending segments. None
# assumes a successful transition, check or acceptance.
law header_variable_bounded_opens_in_stack_original:
  for +f: C.Purpose
  for +n: Nat
  for +r: Nat
  for +c: Nat
  for +t: Nat
  for +high: U32
  for +low: U32
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  for variable: Variable(f)
  for measured: {B.nat64(n) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
  for parent: {C.minimum_stack(stack) == B.nat64(r) : Maybe<&2, B.Number64>}
  for +mc: {B.nat64(c) == Some{H.decrease(9n, body)} : Maybe<&2, B.Number64>}
  for +mt: {B.nat64(t) == Some{H.decrease(9n, ceiling)} : Maybe<&2, B.Number64>}
  for +lc: {Nat.is_le(Nat.add(S.minimum_field_natural(f, n), r), c) == True{} : Bool}
  for lt: {Nat.is_le(Nat.add(S.minimum_field_natural(f, n), r), t) == True{} : Bool}
  {R.execute(Con{tag(f), B.be64(high, low)}, R.Frame{body, ceiling, start(f, stack)}) ==
    R.Frame{H.decrease(9n, body), H.decrease(9n, ceiling), C.open_variable(C.zero64(B.Number64{high, low}), f, B.Number64{high, low}, stack)} : R.Frame}
def header_variable_bounded_opens_in_stack_original(f, n, r, c, t, high, low, stack, body, ceiling, variable, measured, parent, mc, mt, lc, lt):
  Equal.trans(R.Frame,
    R.execute(Con{tag(f), B.be64(high, low)}, R.Frame{body, ceiling, start(f, stack)}),
    R.Frame{H.decrease(9n, body), H.decrease(9n, ceiling), C.conclude_word(f, high, low, stack, H.decrease(9n, body), H.decrease(9n, ceiling))},
    R.Frame{H.decrease(9n, body), H.decrease(9n, ceiling), C.open_variable(C.zero64(B.Number64{high, low}), f, B.Number64{high, low}, stack)},
    header_canonical_composed_preserves_all_to_stack(f, high, low, stack, body, ceiling),
    Equal.cong(C.Machine, R.Frame, m => R.Frame{H.decrease(9n, body), H.decrease(9n, ceiling), m},
      C.conclude_word(f, high, low, stack, H.decrease(9n, body), H.decrease(9n, ceiling)),
      C.open_variable(C.zero64(B.Number64{high, low}), f, B.Number64{high, low}, stack),
      conclude_variable_checked(f, high, low, stack, H.decrease(9n, body), H.decrease(9n, ceiling), variable,
        S.check_minimum_field_combined_stack_by_limits_nat(f, n, r, c, t, B.Number64{high, low}, stack, H.decrease(9n, body), H.decrease(9n, ceiling), measured, parent, mc, mt, lc, lt))))

law header_variable_combined_body_and_ceiling_u64_arbitrary:
  for +f: C.Purpose
  for +n: Nat
  for +r: Nat
  for +c: Nat
  for +high: U32
  for +low: U32
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  for variable: Variable(f)
  for measured: {B.nat64(n) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
  for parent: {C.minimum_stack(stack) == B.nat64(r) : Maybe<&2, B.Number64>}
  for +mc: {B.nat64(c) == Some{H.decrease(9n, body)} : Maybe<&2, B.Number64>}
  for nc: {Nat.is_le(Nat.add(S.minimum_field_natural(f, n), r), c) == True{} : Bool}
  for ct: {C.less_equal64(body, ceiling) == True{} : Bool}
  {R.execute(Con{tag(f), B.be64(high, low)}, R.Frame{body, ceiling, start(f, stack)}) ==
    R.Frame{H.decrease(9n, body), H.decrease(9n, ceiling), C.open_variable(C.zero64(B.Number64{high, low}), f, B.Number64{high, low}, stack)} : R.Frame}
def header_variable_combined_body_and_ceiling_u64_arbitrary(f, n, r, c, high, low, stack, body, ceiling, variable, measured, parent, mc, nc, ct):
  Equal.trans(R.Frame,
    R.execute(Con{tag(f), B.be64(high, low)}, R.Frame{body, ceiling, start(f, stack)}),
    R.Frame{H.decrease(9n, body), H.decrease(9n, ceiling), C.conclude_word(f, high, low, stack, H.decrease(9n, body), H.decrease(9n, ceiling))},
    R.Frame{H.decrease(9n, body), H.decrease(9n, ceiling), C.open_variable(C.zero64(B.Number64{high, low}), f, B.Number64{high, low}, stack)},
    header_canonical_composed_preserves_all_to_stack(f, high, low, stack, body, ceiling),
    Equal.cong(C.Machine, R.Frame, m => R.Frame{H.decrease(9n, body), H.decrease(9n, ceiling), m},
      C.conclude_word(f, high, low, stack, H.decrease(9n, body), H.decrease(9n, ceiling)),
      C.open_variable(C.zero64(B.Number64{high, low}), f, B.Number64{high, low}, stack),
      conclude_variable_checked(f, high, low, stack, H.decrease(9n, body), H.decrease(9n, ceiling), variable,
        Z.check_minimum_composed_by_body_real(f, n, r, c, B.Number64{high, low}, stack, H.decrease(9n, body), H.decrease(9n, ceiling), measured, parent, mc, nc,
          M.decrease_repeated_preserves_order_of_limits(9n, body, ceiling, ct)))))
