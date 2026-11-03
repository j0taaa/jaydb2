# Name validity supplies the actual NameText opening tests.
# There is no check premise: positivity and limit64 are derived.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecNamesASCII.bend as A
import ./CodecCounters.bend as N
import ./CodecSumsOrder.bend as O
import ./CodecLimitsNames.bend as Z
import ./CodecContent.bend as G
import ./CodecComposition.bend as M
import ./CodecTrace.bend as R

law sixty_and_four_has_measure_exact:
  {B.nat64(64n) == Some{B.Number64{0, 64}} : Maybe<&2, B.Number64>}
def sixty_and_four_has_measure_exact():
  {==}

law name_valid_utf8_has_measure_representable:
  for +s: String
  for valid: {D.name_valid(s) == True{} : Bool}
  O.NumberRepresented<B.nat64(B.length(B.utf8(s)))>
def name_valid_utf8_has_measure_representable(s, valid):
  O.nat64_representability_closed_for_low(B.length(B.utf8(s)), 64n, B.Number64{0, 64},
    sixty_and_four_has_measure_exact(), A.name_valid_utf8_has_until64_octets(s, valid))

law name_valid_measured_respects_limit64:
  for +s: String
  for +q: B.Number64
  for valid: {D.name_valid(s) == True{} : Bool}
  for measured: {B.nat64(B.length(B.utf8(s))) == Some{q} : Maybe<&2, B.Number64>}
  {C.less_equal64(q, B.Number64{0, 64}) == True{} : Bool}
def name_valid_measured_respects_limit64(s, q, valid, measured):
  O.less_equal64_preserves_order_nat(B.length(B.utf8(s)), 64n, q, B.Number64{0, 64},
    measured, sixty_and_four_has_measure_exact(), A.name_valid_utf8_has_until64_octets(s, valid))

law measure_of_bytes_negative_empty_and_positive:
  for +bs: List<&2, U32>
  for -q: B.Number64
  for positive: G.NotEmpty(bs)
  for measured: {B.nat64(B.length(bs)) == Some{q} : Maybe<&2, B.Number64>}
  {C.zero64(q) == False{} : Bool}
def measure_of_bytes_negative_empty_and_positive(bs, q, positive, measured):
  match bs:
    case Nil{}:
      L.ex_false({C.zero64(q) == False{} : Bool}, positive)
    case Con{h, t}:
      N.nat64_successor_never_zero(B.length(t), q, measured)

law name_valid_measured_negative_and_zero:
  for +s: String
  for -q: B.Number64
  for valid: {D.name_valid(s) == True{} : Bool}
  for measured: {B.nat64(B.length(B.utf8(s))) == Some{q} : Maybe<&2, B.Number64>}
  {C.zero64(q) == False{} : Bool}
def name_valid_measured_negative_and_zero(s, q, valid, measured):
  measure_of_bytes_negative_empty_and_positive(B.utf8(s), q,
    Z.text_negative_empty_utf8_negative_empty(s, Z.name_valid_negative_and_empty(s, valid)), measured)

law name_valid_measured_opens_content:
  for +s: String
  for +q: B.Number64
  for +stack: C.Stack
  for +valid: {D.name_valid(s) == True{} : Bool}
  for +measured: {B.nat64(B.length(B.utf8(s))) == Some{q} : Maybe<&2, B.Number64>}
  {C.open_variable(C.zero64(q), C.NameText{}, q, stack) ==
    C.Content{True{}, C.one64(q), C.decrease64(q), C.Start{}, "", stack} : C.Machine}
def name_valid_measured_opens_content(s, q, stack, valid, measured):
  %Equal.sym(Bool, C.zero64(q), False{}, name_valid_measured_negative_and_zero(s, q, valid, measured)) :
    {C.open_variable(_, C.NameText{}, q, stack) ==
      C.Content{True{}, C.one64(q), C.decrease64(q), C.Start{}, "", stack} : C.Machine}
  %Equal.sym(Bool, C.less_equal64(q, B.Number64{0, 64}), True{},
    name_valid_measured_respects_limit64(s, q, valid, measured)) :
    {C.open_name(_, q, stack) ==
      C.Content{True{}, C.one64(q), C.decrease64(q), C.Start{}, "", stack} : C.Machine}
  {==}

# Executes actual name bytes and preserves final stack and counters.
law name_valid_open_emits_in_stack_original:
  for +s: String
  for +q: B.Number64
  for +body: B.Number64
  for +ceiling: B.Number64
  for +stack: C.Stack
  for +valid: {D.name_valid(s) == True{} : Bool}
  for +measured: {B.nat64(B.length(B.utf8(s))) == Some{q} : Maybe<&2, B.Number64>}
  {R.execute(B.utf8(s), R.Frame{body, ceiling, C.open_variable(C.zero64(q), C.NameText{}, q, stack)}) ==
    M.later(B.utf8(s), body, ceiling, C.emit_name(stack, s)) : R.Frame}
def name_valid_open_emits_in_stack_original(s, q, body, ceiling, stack, valid, measured):
  %Equal.sym(C.Machine,
    C.open_variable(C.zero64(q), C.NameText{}, q, stack),
    C.Content{True{}, C.one64(q), C.decrease64(q), C.Start{}, "", stack},
    name_valid_measured_opens_content(s, q, stack, valid, measured)) :
    {R.execute(B.utf8(s), R.Frame{body, ceiling, _}) ==
      M.later(B.utf8(s), body, ceiling, C.emit_name(stack, s)) : R.Frame}
  M.content_canonical_emits_in_stack_original(s, q, body, ceiling, True{}, stack,
    Z.text_negative_empty_utf8_negative_empty(s, Z.name_valid_negative_and_empty(s, valid)),
    A.name_valid_and_text_valid(s, valid), measured)

law name_valid_ordered_open_produces_field:
  for +s: String
  for +q: B.Number64
  for +body: B.Number64
  for +ceiling: B.Number64
  for +last: Bool
  for +remaining: B.Number64
  for +previous: String
  for +fields: List<&2, D.Field>
  for +parent: C.Stack
  for +valid: {D.name_valid(s) == True{} : Bool}
  for measured: {B.nat64(B.length(B.utf8(s))) == Some{q} : Maybe<&2, B.Number64>}
  for order: {String.is_lt(previous, s) == True{} : Bool}
  {R.execute(B.utf8(s), R.Frame{body, ceiling,
      C.open_variable(C.zero64(q), C.NameText{}, q, C.Name{last, remaining, previous, fields, parent})}) ==
    M.later(B.utf8(s), body, ceiling, C.Tag{C.Field{last, remaining, s, fields, parent}}) : R.Frame}
def name_valid_ordered_open_produces_field(s, q, body, ceiling, last, remaining, previous, fields, parent, valid, measured, order):
  Equal.trans(R.Frame,
    R.execute(B.utf8(s), R.Frame{body, ceiling,
      C.open_variable(C.zero64(q), C.NameText{}, q, C.Name{last, remaining, previous, fields, parent})}),
    M.later(B.utf8(s), body, ceiling, C.emit_name(C.Name{last, remaining, previous, fields, parent}, s)),
    M.later(B.utf8(s), body, ceiling, C.Tag{C.Field{last, remaining, s, fields, parent}}),
    name_valid_open_emits_in_stack_original(s, q, body, ceiling,
      C.Name{last, remaining, previous, fields, parent}, valid, measured),
    (%Equal.sym(Bool, D.name_valid(s) && String.is_lt(previous, s), True{},
      F.and_boolean_intro(D.name_valid(s), String.is_lt(previous, s), valid, order)) :
      {M.later(B.utf8(s), body, ceiling, C.name_checked(_, last, remaining, s, fields, parent)) ==
        M.later(B.utf8(s), body, ceiling, C.Tag{C.Field{last, remaining, s, fields, parent}}) : R.Frame}
      {==}))
