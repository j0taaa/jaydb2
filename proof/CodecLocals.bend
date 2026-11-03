# Completeness induction base cases, strengthened for EVERY stack and
# suffix with sufficient reserve, including ancestors that cascade emissions.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../src/Codec.bend as C
import ./CodecTrace.bend as R
import ./CodecComposition.bend as X
import ./CodecSequences.bend as S
import ./CodecWordsBE64.bend as H
import ./CodecTexts.bend as T
import ./CodecMinimum.bend as M
import ./CodecLimitsSequences.bend as K
import ./CodecUTF8Inverse.bend as V

law absence_complete_in_any_context:
  S.CompleteLocal(D.VAbsent{}, [0])
def absence_complete_in_any_context():
  body => ceiling => stack => suffix => r => minimum => reservation => measured => fits => {==}

def bytes_bool(b: Bool) -> List<&2, U32>:
  match b:
    case False{}:
      [1]
    case True{}:
      [2]

law boolean_complete_in_any_context:
  for +b: Bool
  S.CompleteLocal(D.VBool{b}, bytes_bool(b))
def boolean_complete_in_any_context(b):
  match b:
    case False{}:
      body => ceiling => stack => suffix => r => minimum => reservation => measured => fits => {==}
    case True{}:
      body => ceiling => stack => suffix => r => minimum => reservation => measured => fits => {==}

law integer_complete_in_any_context:
  for +high: U32
  for +low: U32
  S.CompleteLocal(D.VInt{high, low}, Con{3, B.be64(high, low)})
def integer_complete_in_any_context(high, low):
  body => ceiling => stack => suffix => r => minimum => reservation => measured => fits =>
    X.header_canonical_composed_preserves_all_to_stack(C.Integer{}, high, low, stack, body, ceiling)

law text_canonical_complete_combined_reservation_real:
  for +s: String
  for +high: U32
  for +low: U32
  for +body: B.Number64
  for +ceiling: B.Number64
  for +stack: C.Stack
  for +suffix: List<&2, U32>
  for +r: Nat
  for valid: {B.text_valid(s) == True{} : Bool}
  for +measure_text: {B.nat64(B.length(B.utf8(s))) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
  for minimum: {C.minimum_stack(stack) == B.nat64(r) : Maybe<&2, B.Number64>}
  for reservation: {Nat.is_le(r, B.length(suffix)) == True{} : Bool}
  for measured: {B.nat64(B.length(B.concatenate(T.bytes_text(high, low, s), suffix))) == Some{body} : Maybe<&2, B.Number64>}
  for +fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  {R.execute(T.bytes_text(high, low, s), R.Frame{body, ceiling, C.Tag{stack}}) ==
    X.later(T.bytes_text(high, low, s), body, ceiling, C.emit(stack, D.VText{s})) : R.Frame}
def text_canonical_complete_combined_reservation_real(s, high, low, body, ceiling, stack, suffix, r, valid, measure_text, minimum, reservation, measured, fits):
  +measure_rest = T.remove_prefix_of_measure(9n, B.length(B.concatenate(B.utf8(s), suffix)), body, measured)
  limit = K.concatenate_segments_preserves_sum_of_limits(B.utf8(s), suffix, B.length(B.utf8(s)), r,
    K.limit_reflexive(B.length(B.utf8(s))), reservation)
  header = X.header_variable_combined_body_and_ceiling_u64_arbitrary(C.TextValue{}, B.length(B.utf8(s)), r, B.length(B.concatenate(B.utf8(s), suffix)), high, low, stack, body, ceiling,
    Unit{}, measure_text, minimum, measure_rest, limit, fits)
  S.compose_two_segments_real(Con{4, B.be64(high, low)}, B.utf8(s), body, ceiling, C.Tag{stack},
    C.open_variable(C.zero64(B.Number64{high, low}), C.TextValue{}, B.Number64{high, low}, stack), C.emit(stack, D.VText{s}), header,
    X.opening_textual_canonical_emits_in_stack_original(B.utf8(s), B.Number64{high, low}, H.decrease(9n, body), H.decrease(9n, ceiling), stack, s, measure_text, V.utf8_text_valid_decodes_exactly(s, valid)))

law text_complete_in_any_context:
  for +s: String
  for +high: U32
  for +low: U32
  for valid: {B.text_valid(s) == True{} : Bool}
  for measure: {B.nat64(B.length(B.utf8(s))) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
  S.CompleteLocal(D.VText{s}, T.bytes_text(high, low, s))
def text_complete_in_any_context(s, high, low, valid, measure):
  body => ceiling => stack => suffix => r => minimum => reservation => measured => fits =>
    text_canonical_complete_combined_reservation_real(s, high, low, body, ceiling, stack, suffix, r, valid, measure, minimum, reservation, measured, fits)
