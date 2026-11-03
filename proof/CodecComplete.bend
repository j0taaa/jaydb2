# Codec completeness by STRUCTURAL induction on D.Value.
# The tree stores subvalue capabilities: arbitrary segments
# exposed by the encoder are aligned to it by propositional equality.
# No premise states acceptance or completeness of the entire container.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecSequences.bend as V
import ./CodecRecords.bend as G
import ./CodecLocals.bend as I
import ./CodecTexts.bend as T
import ./CodecArities.bend as A
import ./CodecAssembly.bend as M
import ./CodecAssemblyNames.bend as N
import ./CodecAssemblyExposure.bend as E
import ./CodecAssemblyExposureRecord.bend as R
import ./CodecLimitsSequences.bend as S
import ./CodecLimitsCopy.bend as Q
import ./CodecCompleteStructure.bend as Z
import ./CodecPublic.bend as U

law list_segmented_complete:
  for +xs: List<&2, S.ValueSegmented>
  for +high: U32
  for +low: U32
  for children: V.InductionValues(xs)
  for canonical: S.ValuesCanonical(xs)
  for counted: {B.nat64(S.count_values(xs)) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
  V.CompleteLocal(V.list(xs), V.bytes_list(high, low, xs))
def list_segmented_complete(xs, high, low, children, canonical, counted):
  body => ceiling => parent => suffix => r => minimum => reservation => measured => fits =>
    V.constructor_list_composes_completeness_local(xs, high, low, body, ceiling, parent, suffix, r,
      children, canonical, counted, minimum, reservation, measured, fits)

law record_segmented_complete:
  for +xs: List<&2, S.FieldSegmented>
  for +high: U32
  for +low: U32
  for children: G.InductionFields(xs)
  for ordered: A.FieldsOrdered(S.fields(xs), "")
  for canonical: S.FieldsCanonical(xs)
  for counted: {B.nat64(S.count_fields(xs)) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
  V.CompleteLocal(G.record(xs), G.bytes_record(high, low, xs))
def record_segmented_complete(xs, high, low, children, ordered, canonical, counted):
  body => ceiling => parent => suffix => r => minimum => reservation => measured => fits =>
    G.constructor_record_composes_completeness_local(xs, high, low, body, ceiling, parent, suffix, r,
      children, ordered, canonical, counted, minimum, reservation, measured, fits)

# The first transport consumes only equality of the original value;
# no recursive call is made on segments produced by the encoder.
def apply_list_exposed(+v: D.Value, +bs: List<&2, U32>,
  descendants: Z.Descendants(v), exposed: E.ListExposed<v, bs>) -> V.CompleteLocal(v, bs):
  match exposed:
    case E.ListExposed{+xs, B.Number64{+high, +low}, value, canonical, counted, bytes}:
      +equal = Equal.trans(D.Value, v, A.attach_list(S.values(xs), D.VListEmpty{}), V.list(xs),
        value, Z.attach_values_and_list(xs))
      tree = {(%equal : Z.Descendants(_)
        descendants) : Z.Descendants(V.list(xs))}
      %Equal.sym(D.Value, v, V.list(xs), equal) : V.CompleteLocal(_, bs)
      %Equal.sym(List<&2, U32>, bs, V.bytes_list(high, low, xs), bytes) : V.CompleteLocal(V.list(xs), _)
      F.combined_pair(V.CompleteLocal(V.list(xs), V.bytes_list(high, low, xs)),
        S.ValuesCanonical(xs), S.ValuesCanonical(xs), Q.duplicate_values_canonical(xs, canonical),
        for_children => for_opening => list_segmented_complete(xs, high, low,
          Z.induction_values_of_segments(xs, tree, for_children), for_opening, counted))

def apply_record_exposed(+v: D.Value, +bs: List<&2, U32>,
  descendants: Z.Descendants(v), exposed: R.RecordExposed<v, bs>) -> V.CompleteLocal(v, bs):
  match exposed:
    case R.RecordExposed{+xs, B.Number64{+high, +low}, value, canonical, ordered, names, counted, bytes}:
      +equal = Equal.trans(D.Value, v, A.attach_record(S.fields(xs), D.VRecordEmpty{}), G.record(xs),
        value, Z.attach_fields_and_record(xs))
      tree = {(%equal : Z.Descendants(_)
        descendants) : Z.Descendants(G.record(xs))}
      %Equal.sym(D.Value, v, G.record(xs), equal) : V.CompleteLocal(_, bs)
      %Equal.sym(List<&2, U32>, bs, G.bytes_record(high, low, xs), bytes) : V.CompleteLocal(G.record(xs), _)
      F.combined_pair(V.CompleteLocal(G.record(xs), G.bytes_record(high, low, xs)),
        S.FieldsCanonical(xs), S.FieldsCanonical(xs), Q.duplicate_fields_canonical(xs, canonical),
        for_children => for_opening => record_segmented_complete(xs, high, low,
          Z.induction_fields_of_segments(xs, tree, for_children), ordered, for_opening, counted))

law list_encoded_combined_descendants_and_complete:
  for +v: D.Value
  for +bs: List<&2, U32>
  for descendants: Z.Descendants(v)
  for form: {D.is_list(v) == True{} : Bool}
  for encoded: P.Encoding(v, bs)
  V.CompleteLocal(v, bs)
def list_encoded_combined_descendants_and_complete(v, bs, descendants, form, encoded):
  apply_list_exposed(v, bs, descendants,
    E.list_encoded_exposes_segments_count_and_header(v, bs, form, encoded))

law record_encoded_combined_descendants_and_complete:
  for +v: D.Value
  for +bs: List<&2, U32>
  for descendants: Z.Descendants(v)
  for form: {D.is_record(v) == True{} : Bool}
  for encoded: P.Encoding(v, bs)
  V.CompleteLocal(v, bs)
def record_encoded_combined_descendants_and_complete(v, bs, descendants, form, encoded):
  apply_record_exposed(v, bs, descendants,
    R.record_encoded_exposes_segments_count_and_header(v, bs, form, encoded))

law absence_encoded_and_complete:
  for +bs: List<&2, U32>
  for encoded: P.Encoding(D.VAbsent{}, bs)
  V.CompleteLocal(D.VAbsent{}, bs)
def absence_encoded_and_complete(bs, encoded):
  %F.some_injective(List<&2, U32>, [0], bs, encoded) : V.CompleteLocal(D.VAbsent{}, _)
  I.absence_complete_in_any_context()

law boolean_encoded_and_complete:
  for +b: Bool
  for +bs: List<&2, U32>
  for encoded: P.Encoding(D.VBool{b}, bs)
  V.CompleteLocal(D.VBool{b}, bs)
def boolean_encoded_and_complete(b, bs, encoded):
  match b:
    case False{}:
      %F.some_injective(List<&2, U32>, [1], bs, encoded) : V.CompleteLocal(D.VBool{False{}}, _)
      I.boolean_complete_in_any_context(False{})
    case True{}:
      %F.some_injective(List<&2, U32>, [2], bs, encoded) : V.CompleteLocal(D.VBool{True{}}, _)
      I.boolean_complete_in_any_context(True{})

law integer_encoded_and_complete:
  for +high: U32
  for +low: U32
  for +bs: List<&2, U32>
  for encoded: P.Encoding(D.VInt{high, low}, bs)
  V.CompleteLocal(D.VInt{high, low}, bs)
def integer_encoded_and_complete(high, low, bs, encoded):
  %F.some_injective(List<&2, U32>, Con{3, B.be64(high, low)}, bs, encoded) : V.CompleteLocal(D.VInt{high, low}, _)
  I.integer_complete_in_any_context(high, low)

# The text case exposes only the original encoder result and
# requires no additional measure or text-validity hypothesis.
def apply_text_exposed(+s: String, +bs: List<&2, U32>, exposed: N.NameExposed<s, bs>) -> V.CompleteLocal(D.VText{s}, bs):
  match exposed:
    case N.NameExposed{B.Number64{+high, +low}, valid, measure, bytes}:
      %Equal.sym(List<&2, U32>, bs, T.bytes_text(high, low, s), bytes) : V.CompleteLocal(D.VText{s}, _)
      I.text_complete_in_any_context(s, high, low, valid, measure)

def finalize_atom_optional_exposes_result(result: Maybe<&2, List<&2, U32>>, +bs: List<&2, U32>,
  encoded: {P.finalize(P.atom_optional(result)) == Some{bs} : Maybe<&2, List<&2, U32>>}) ->
  {result == Some{bs} : Maybe<&2, List<&2, U32>>}:
  match result:
    case None{}:
      L.ex_false({None{} == Some{bs} : Maybe<&2, List<&2, U32>>}, F.none_negative_some(List<&2, U32>, bs, encoded))
    case Some{payload}:
      encoded

law text_encoded_exposes_bytes_of_text:
  for +s: String
  for +bs: List<&2, U32>
  for encoded: P.Encoding(D.VText{s}, bs)
  {P.text(s) == Some{bs} : Maybe<&2, List<&2, U32>>}
def text_encoded_exposes_bytes_of_text(s, bs, encoded):
  F.combined_pair({P.text(s) == Some{bs} : Maybe<&2, List<&2, U32>>},
    {D.value_valid(D.VText{s}) == True{} : Bool},
    {P.finalize(P.encode_partial(D.VText{s})) == Some{bs} : Maybe<&2, List<&2, U32>>},
    M.child_canonical_exposes_validity_and_bytes(D.VText{s}, bs, encoded),
    valid => bytes => finalize_atom_optional_exposes_result(P.text(s), bs, bytes))

law text_encoded_and_complete:
  for +s: String
  for +bs: List<&2, U32>
  for encoded: P.Encoding(D.VText{s}, bs)
  V.CompleteLocal(D.VText{s}, bs)
def text_encoded_and_complete(s, bs, encoded):
  apply_text_exposed(s, bs,
    N.name_canonical_exposes_tag_measure_and_utf8(s, bs, text_encoded_exposes_bytes_of_text(s, bs, encoded)))

# Every recursive call receives h or t DIRECTLY from matching v.
# The second construction preserves ancestor capabilities; it
# avoids copying callbacks, which are affine in Bend.
law all_value_has_tree_of_completeness:
  for +v: D.Value
  Z.Structural(v)
def all_value_has_tree_of_completeness(v):
  match v:
    case D.VAbsent{}:
      L.Both{bs => encoded => absence_encoded_and_complete(bs, encoded), Unit{}}
    case D.VBool{+b}:
      L.Both{bs => encoded => boolean_encoded_and_complete(b, bs, encoded), Unit{}}
    case D.VInt{+high, +low}:
      L.Both{bs => encoded => integer_encoded_and_complete(high, low, bs, encoded), Unit{}}
    case D.VText{+s}:
      L.Both{bs => encoded => text_encoded_and_complete(s, bs, encoded), Unit{}}
    case D.VListEmpty{}:
      L.Both{bs => encoded => list_encoded_combined_descendants_and_complete(D.VListEmpty{}, bs, Unit{}, {==}, encoded), Unit{}}
    case D.VList{+h, +t}:
      L.Both{
        bs => encoded => list_encoded_combined_descendants_and_complete(D.VList{h, t}, bs,
          L.Both{all_value_has_tree_of_completeness(h), all_value_has_tree_of_completeness(t)}, {==}, encoded),
        L.Both{all_value_has_tree_of_completeness(h), all_value_has_tree_of_completeness(t)}}
    case D.VRecordEmpty{}:
      L.Both{bs => encoded => record_encoded_combined_descendants_and_complete(D.VRecordEmpty{}, bs, Unit{}, {==}, encoded), Unit{}}
    case D.VRecord{+name, +h, +t}:
      L.Both{
        bs => encoded => record_encoded_combined_descendants_and_complete(D.VRecord{name, h, t}, bs,
          L.Both{all_value_has_tree_of_completeness(h), all_value_has_tree_of_completeness(t)}, {==}, encoded),
        L.Both{all_value_has_tree_of_completeness(h), all_value_has_tree_of_completeness(t)}}

law encoding_canonical_implies_completeness_local:
  for +v: D.Value
  for +bs: List<&2, U32>
  for encoded: P.Encoding(v, bs)
  V.CompleteLocal(v, bs)
def encoding_canonical_implies_completeness_local(v, bs, encoded):
  Z.capacity_of_tree(v, all_value_has_tree_of_completeness(v))(bs, encoded)

# Public API: the only premises beyond canonical encoding are the
# exact body measure and u64 limit actually received by the decoder.
law all_encoding_canonical_representable_and_decoded:
  for +v: D.Value
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for encoded: P.Encoding(v, bs)
  for +measured: {B.nat64(B.length(bs)) == Some{body} : Maybe<&2, B.Number64>}
  for +fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  {C.decode(bs, ceiling) == C.Decoded{v} : C.Outcome}
def all_encoding_canonical_representable_and_decoded(v, bs, body, ceiling, encoded, measured, fits):
  +canonical = {encoded : {P.encode(v) == Some{bs} : Maybe<&2, List<&2, U32>>}}
  U.completeness_local_canonical_implies_acceptance_publish(v, bs, body, ceiling,
    encoding_canonical_implies_completeness_local(v, bs, canonical), canonical, measured, fits)
