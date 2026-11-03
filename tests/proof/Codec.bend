# General theorem application tests; the 222 old cases remain
# a separate regression, not to be confused with these quantifiers.
import Base
import ./CodecCompleteness.bend as Completeness
import ./CodecLaw2.bend as RelationOriginal
import ../../proof/Codec.bend as G
import ../../proof/CodecVerify.bend as All
import ../../proof/CodecTexts.bend as Texts
import ../../proof/CodecTextAccepted.bend as TextAccepted
import ../../proof/CodecUnicode.bend as U
import ../../proof/CodecStructures.bend as E
import ../../proof/CodecCanonical.bend as K
import ../../proof/CodecTrace.bend as R
import ../../proof/CodecIntegers.bend as J
import ../../contract/Bytes.bend as B
import ../../contract/Data.bend as D
import ../../contract/Protocol.bend as P
import ../../contract/Logic.bend as L
import ../../src/Codec.bend as C

# Applies the proof to completely arbitrary inputs, without a supplied
# canonicity, validity, depth, quantity or size witness.
law any_acceptance_has_guarantees_general:
  for +bs: List<&2, U32>
  for +ceiling: B.Number64
  for -v: D.Value
  for accepted: {C.decode(bs, ceiling) == C.Decoded{v} : C.Outcome}
  G.AcceptanceProven<bs, ceiling, v>
def any_acceptance_has_guarantees_general(bs, ceiling, v, accepted):
  G.acceptance_guarantees_validity_limit_and_consumption_integral(bs, ceiling, v, accepted)

law unicode_of_any_transition_and_valid:
  for +u: C.Unicode
  for +b: U32
  U.ScalarValid(C.step_utf8(u, b))
def unicode_of_any_transition_and_valid(u, b):
  U.step_utf8_only_emits_scalars_all_valid(u, b)

law lists_of_width_and_depth_arbitrary:
  for +xs: List<&2, D.Value>
  for all_valid: E.ValuesValid(xs)
  {P.encode(C.assemble_list(xs, D.VListEmpty{})) ==
    P.finalize(K.list_bytes(Nat.add(K.count_values(xs), 0n), P.concatenate_optional(K.content_values(xs), Some{Nil{}}))) : Maybe<&2, List<&2, U32>>}
def lists_of_width_and_depth_arbitrary(xs, all_valid):
  K.list_assembled_has_encoding_exact(xs, all_valid)

law records_of_width_and_depth_arbitrary:
  for +xs: List<&2, D.Field>
  for all_valid: E.FieldsInverted(xs)
  {P.encode(C.assemble_record(xs, D.VRecordEmpty{})) ==
    P.finalize(K.record_bytes(Nat.add(K.count_fields(xs), 0n), P.concatenate_optional(K.content_fields(xs), Some{Nil{}}))) : Maybe<&2, List<&2, U32>>}
def records_of_width_and_depth_arbitrary(xs, all_valid):
  K.record_assembled_has_encoding_exact(xs, all_valid)

law consume_negative_ignores_o_first_octet_extra:
  for b: U32
  for xs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for v: D.Value
  {C.traverse(Con{b, xs}, body, ceiling, C.DecodedReady{v}) == C.Input{} : C.Outcome}
def consume_negative_ignores_o_first_octet_extra(b, xs, body, ceiling, v):
  R.ready_refusal_any_octet_extra(b, xs, body, ceiling, v)

# Nonempty instances exercise invariant composition.
def values() -> List<&2, D.Value>:
  [D.VText{"é𝄞"}, D.VList{D.VInt{4294967295, 4294967295}, D.VListEmpty{}}]

def values_all_valid() -> E.ValuesValid(values()):
  L.Both{{==}, L.Both{{==}, Unit{}}}

law list_composed_negative_loses_unicode_neither_bits:
  {P.encode(C.assemble_list(values(), D.VListEmpty{})) ==
    P.finalize(K.list_bytes(Nat.add(K.count_values(values()), 0n), P.concatenate_optional(K.content_values(values()), Some{Nil{}}))) : Maybe<&2, List<&2, U32>>}
def list_composed_negative_loses_unicode_neither_bits():
  K.list_assembled_has_encoding_exact(values(), values_all_valid())

def fields() -> List<&2, D.Field>:
  [D.Field{"z", D.VText{"𝄞"}}, D.Field{"a", D.VList{D.VAbsent{}, D.VListEmpty{}}}]

def fields_all_valid() -> E.FieldsInverted(fields()):
  L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, Unit{}}}}}}

law record_composed_has_order_canonical:
  {P.encode(C.assemble_record(fields(), D.VRecordEmpty{})) ==
    P.finalize(K.record_bytes(Nat.add(K.count_fields(fields()), 0n), P.concatenate_optional(K.content_fields(fields()), Some{Nil{}}))) : Maybe<&2, List<&2, U32>>}
def record_composed_has_order_canonical():
  K.record_assembled_has_encoding_exact(fields(), fields_all_valid())

law any_tail_accepts_combined_tag_integer_and_canonical:
  for +bs: List<&2, U32>
  for +ceiling: B.Number64
  for -v: D.Value
  for +accepted: {C.decode(Con{3, bs}, ceiling) == C.Decoded{v} : C.Outcome}
  P.Encoding(v, Con{3, bs})
def any_tail_accepts_combined_tag_integer_and_canonical(bs, ceiling, v, accepted):
  J.all_acceptance_started_by_tag_integer_and_canonical(bs, ceiling, v, accepted)

law any_integer_canonical_inside_of_limit_and_accepted:
  for +high: U32
  for +low: U32
  for +ceiling: B.Number64
  for fits: {C.less_equal64(B.Number64{0, 9}, ceiling) == True{} : Bool}
  {C.decode(Con{3, B.be64(high, low)}, ceiling) == C.Decoded{D.VInt{high, low}} : C.Outcome}
def any_integer_canonical_inside_of_limit_and_accepted(high, low, ceiling, fits):
  J.all_integer_canonical_inside_of_limit_and_accepted(high, low, ceiling, fits)

law any_tail_accepts_combined_tag_text_and_canonical:
  for +bs: List<&2, U32>
  for +ceiling: B.Number64
  for -v: D.Value
  for +accepted: {C.decode(Con{4, bs}, ceiling) == C.Decoded{v} : C.Outcome}
  P.Encoding(v, Con{4, bs})
def any_tail_accepts_combined_tag_text_and_canonical(bs, ceiling, v, accepted):
  TextAccepted.all_acceptance_started_by_tag_text_and_canonical(bs, ceiling, v, accepted)

law any_text_canonical_inside_of_limit_and_accepted:
  for +s: String
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +encoded: {P.encode(D.VText{s}) == Some{bs} : Maybe<&2, List<&2, U32>>}
  for measured: {B.nat64(B.length(bs)) == Some{body} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  {C.decode(bs, ceiling) == C.Decoded{D.VText{s}} : C.Outcome}
def any_text_canonical_inside_of_limit_and_accepted(s, bs, body, ceiling, encoded, measured, fits):
  Texts.all_encoding_textual_inside_of_limit_and_accepts(s, bs, body, ceiling, encoded, measured, fits)
