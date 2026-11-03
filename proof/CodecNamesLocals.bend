# Complete-name case for the record induction step. All checks
# follow from the original name and suffix reserve.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../src/Codec.bend as C
import ./CodecTrace.bend as R
import ./CodecComposition.bend as X
import ./CodecSequences.bend as S
import ./CodecFields.bend as G
import ./CodecWordsBE64.bend as H
import ./CodecTexts.bend as T
import ./CodecLimitsSequences.bend as K
import ./CodecNamesOpening.bend as N
import ./CodecAssemblyNames.bend as E

law name_canonical_complete_combined_reservation_real:
  for +s: String
  for +high: U32
  for +low: U32
  for +body: B.Number64
  for +ceiling: B.Number64
  for +stack: C.Stack
  for +suffix: List<&2, U32>
  for +r: Nat
  for +valid: {D.name_valid(s) == True{} : Bool}
  for +measure_text: {B.nat64(B.length(B.utf8(s))) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
  for minimum: {C.minimum_stack(stack) == B.nat64(r) : Maybe<&2, B.Number64>}
  for reservation: {Nat.is_le(r, B.length(suffix)) == True{} : Bool}
  for measured: {B.nat64(B.length(B.concatenate(T.bytes_text(high, low, s), suffix))) == Some{body} : Maybe<&2, B.Number64>}
  for +fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  {R.execute(T.bytes_text(high, low, s), R.Frame{body, ceiling, C.TagName{stack}}) ==
    X.later(T.bytes_text(high, low, s), body, ceiling, C.emit_name(stack, s)) : R.Frame}
def name_canonical_complete_combined_reservation_real(s, high, low, body, ceiling, stack, suffix, r, valid, measure_text, minimum, reservation, measured, fits):
  +measure_rest = T.remove_prefix_of_measure(9n, B.length(B.concatenate(B.utf8(s), suffix)), body, measured)
  limit = K.concatenate_segments_preserves_sum_of_limits(B.utf8(s), suffix, B.length(B.utf8(s)), r,
    K.limit_reflexive(B.length(B.utf8(s))), reservation)
  header = X.header_variable_combined_body_and_ceiling_u64_arbitrary(C.NameText{}, B.length(B.utf8(s)), r, B.length(B.concatenate(B.utf8(s), suffix)), high, low, stack, body, ceiling,
    Unit{}, measure_text, minimum, measure_rest, limit, fits)
  S.compose_two_segments_real(Con{4, B.be64(high, low)}, B.utf8(s), body, ceiling, C.TagName{stack},
    C.open_variable(C.zero64(B.Number64{high, low}), C.NameText{}, B.Number64{high, low}, stack), C.emit_name(stack, s), header,
    N.name_valid_open_emits_in_stack_original(s, B.Number64{high, low}, H.decrease(9n, body), H.decrease(9n, ceiling), stack, valid, measure_text))

law name_measured_complete_in_any_context:
  for +s: String
  for +high: U32
  for +low: U32
  for valid: {D.name_valid(s) == True{} : Bool}
  for measure: {B.nat64(B.length(B.utf8(s))) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
  G.NameComplete(s, T.bytes_text(high, low, s))
def name_measured_complete_in_any_context(s, high, low, valid, measure):
  body => ceiling => stack => suffix => r => minimum => reservation => measured => fits =>
    name_canonical_complete_combined_reservation_real(s, high, low, body, ceiling, stack, suffix, r, valid, measure, minimum, reservation, measured, fits)

def apply_name_exposed(+s: String, +bs: List<&2, U32>,
  valid: {D.name_valid(s) == True{} : Bool}, exposed: E.NameExposed<s, bs>) -> G.NameComplete(s, bs):
  match exposed:
    case E.NameExposed{B.Number64{+high, +low}, text_valid, measure, bytes}:
      %Equal.sym(List<&2, U32>, bs, T.bytes_text(high, low, s), bytes) : G.NameComplete(s, _)
      name_measured_complete_in_any_context(s, high, low, valid, measure)

law name_canonical_complete:
  for +s: String
  for +bs: List<&2, U32>
  for valid: {D.name_valid(s) == True{} : Bool}
  for encoded: {P.text(s) == Some{bs} : Maybe<&2, List<&2, U32>>}
  G.NameComplete(s, bs)
def name_canonical_complete(s, bs, valid, encoded):
  apply_name_exposed(s, bs, valid, E.name_canonical_exposes_tag_measure_and_utf8(s, bs, encoded))
