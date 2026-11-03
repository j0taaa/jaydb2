# General record-encoder inversion. Segments, order and measure
# follow from the whole encoding, without child premises.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Logic.bend as L
import ./Foundations.bend as F
import ./CodecArities.bend as A
import ./CodecCanonical.bend as K
import ./CodecLimitsSequences.bend as S
import ./CodecAssembly.bend as M
import ./CodecAssemblyExposure.bend as X
import ./CodecAssemblyNames.bend as N

type RecordSegmented<-v: D.Value, -n: Nat, -payload: List<&2, U32>, -previous: String> is Type:
  RecordSegmented{segments: List<&2, S.FieldSegmented>,
    value: {v == A.attach_record(S.fields(segments), D.VRecordEmpty{}) : D.Value},
    canonical: S.FieldsCanonical(segments),
    ordered: A.FieldsOrdered(S.fields(segments), previous),
    count: {S.count_fields(segments) == n : Nat},
    bytes: {S.bytes_fields(segments) == payload : List<&2, U32>}}

def PartialRecord(v: D.Value, p: P.Partial, previous: String) -> Type:
  match p:
    case P.Impossible{}:
      Unit
    case P.Record{n, payload}:
      RecordSegmented<v, n, payload, previous>
    case _:
      Empty

law record_later_requires_form_of_record:
  for +v: D.Value
  for previous: String
  for later: {D.record_later(v, previous) == True{} : Bool}
  {D.is_record(v) == True{} : Bool}
def record_later_requires_form_of_record(v, previous, later):
  match v:
    case D.VRecordEmpty{}:
      {==}
    case D.VRecord{n, x, r}:
      {==}
    case D.VAbsent{}:
      F.absurd_boolean({D.is_record(v) == True{} : Bool}, later)
    case D.VBool{b}:
      F.absurd_boolean({D.is_record(v) == True{} : Bool}, later)
    case D.VInt{a, b}:
      F.absurd_boolean({D.is_record(v) == True{} : Bool}, later)
    case D.VText{s}:
      F.absurd_boolean({D.is_record(v) == True{} : Bool}, later)
    case D.VListEmpty{}:
      F.absurd_boolean({D.is_record(v) == True{} : Bool}, later)
    case D.VList{h, t}:
      F.absurd_boolean({D.is_record(v) == True{} : Bool}, later)

law name_valid_and_later_of_empty:
  for +name: String
  for valid: {D.name_valid(name) == True{} : Bool}
  {String.is_lt("", name) == True{} : Bool}
def name_valid_and_later_of_empty(name, valid):
  match name:
    case SNil{}:
      F.absurd_boolean({String.is_lt("", name) == True{} : Bool}, valid)
    case SCon{h, t}:
      {==}

law record_valid_and_later_of_empty:
  for +v: D.Value
  for valid: {D.value_valid(v) == True{} : Bool}
  for form: {D.is_record(v) == True{} : Bool}
  {D.record_later(v, "") == True{} : Bool}
def record_valid_and_later_of_empty(v, valid, form):
  match v:
    case D.VRecordEmpty{}:
      {==}
    case D.VRecord{+n, +x, +r}:
      name_valid_and_later_of_empty(n,
        F.and_boolean_left(D.name_valid(n), D.value_valid(x),
          F.and_boolean_left(D.name_valid(n) && D.value_valid(x), D.record_later(r, n),
            F.and_boolean_left(D.name_valid(n) && D.value_valid(x) && D.record_later(r, n), D.value_valid(r), valid))))
    case D.VAbsent{}:
      F.absurd_boolean({D.record_later(v, "") == True{} : Bool}, form)
    case D.VBool{b}:
      F.absurd_boolean({D.record_later(v, "") == True{} : Bool}, form)
    case D.VInt{a, b}:
      F.absurd_boolean({D.record_later(v, "") == True{} : Bool}, form)
    case D.VText{s}:
      F.absurd_boolean({D.record_later(v, "") == True{} : Bool}, form)
    case D.VListEmpty{}:
      F.absurd_boolean({D.record_later(v, "") == True{} : Bool}, form)
    case D.VList{h, t}:
      F.absurd_boolean({D.record_later(v, "") == True{} : Bool}, form)

def expose_head_record(+name: String, +v: D.Value, +r: D.Value, +previous: String,
  name_result: Maybe<&2, List<&2, U32>>, value_result: Maybe<&2, List<&2, U32>>, partial: P.Partial,
  +name_valid: {D.name_valid(name) == True{} : Bool},
  value_valid: {D.value_valid(v) == True{} : Bool},
  order: {String.is_lt(previous, name) == True{} : Bool},
  name_bytes: {P.text(name) == name_result : Maybe<&2, List<&2, U32>>},
  value_bytes: {P.finalize(P.encode_partial(v)) == value_result : Maybe<&2, List<&2, U32>>},
  rest: PartialRecord(r, partial, name)) ->
  PartialRecord(D.VRecord{name, v, r}, P.record_cases(name_result, value_result, partial), previous):
  match name_result value_result partial:
    case None{} _ _:
      Unit{}
    case Some{nb} None{} _:
      Unit{}
    case Some{+nb} Some{+vb} P.Record{+n, +payload}:
      match rest:
        case RecordSegmented{+segments, value, canonical, ordered, count, bytes}:
          RecordSegmented{Con{S.FieldSegmented{name, v, nb, vb}, segments},
            Equal.cong(D.Value, D.Value, t => D.VRecord{name, v, t},
              r, A.attach_record(S.fields(segments), D.VRecordEmpty{}), value),
            L.Both{name_valid, L.Both{name_bytes, L.Both{
              Equal.trans(Maybe<&2, List<&2, U32>>, P.encode(v), P.finalize(P.encode_partial(v)), Some{vb},
                K.value_valid_releases_encoding(v, value_valid), value_bytes), canonical}}},
            L.Both{name_valid, L.Both{order, ordered}},
            Equal.cong(Nat, Nat, q => 1n+q, S.count_fields(segments), n, count),
            Equal.trans(List<&2, U32>,
              B.concatenate(B.concatenate(nb, vb), S.bytes_fields(segments)),
              B.concatenate(nb, B.concatenate(vb, S.bytes_fields(segments))),
              B.concatenate(nb, B.concatenate(vb, payload)),
              K.concatenation_associative(nb, vb, S.bytes_fields(segments)),
              Equal.cong(List<&2, U32>, List<&2, U32>, t => B.concatenate(nb, B.concatenate(vb, t)),
                S.bytes_fields(segments), payload, bytes))}
    case Some{nb} Some{vb} P.Impossible{}:
      Unit{}
    case Some{nb} Some{vb} P.Atom{payload}:
      Unit{}
    case Some{nb} Some{vb} P.ListFrame{n, payload}:
      Unit{}

law record_valid_exposes_segmentation_partial:
  for +v: D.Value
  for +previous: String
  for +valid: {D.value_valid(v) == True{} : Bool}
  for form: {D.is_record(v) == True{} : Bool}
  for later: {D.record_later(v, previous) == True{} : Bool}
  PartialRecord(v, P.encode_partial(v), previous)
def record_valid_exposes_segmentation_partial(v, previous, valid, form, later):
  match v:
    case D.VRecordEmpty{}:
      RecordSegmented{Nil{}, {==}, Unit{}, Unit{}, {==}, {==}}
    case D.VRecord{+name, +x, +r}:
      +head_order = F.and_boolean_left(
        D.name_valid(name) && D.value_valid(x) && D.record_later(r, name), D.value_valid(r), valid)
      +head = F.and_boolean_left(D.name_valid(name) && D.value_valid(x), D.record_later(r, name), head_order)
      +order_rest = F.and_boolean_right(D.name_valid(name) && D.value_valid(x), D.record_later(r, name), head_order)
      expose_head_record(name, x, r, previous, P.text(name), P.finalize(P.encode_partial(x)), P.encode_partial(r),
        F.and_boolean_left(D.name_valid(name), D.value_valid(x), head),
        F.and_boolean_right(D.name_valid(name), D.value_valid(x), head), later, {==}, {==},
        record_valid_exposes_segmentation_partial(r, name,
          F.and_boolean_right(D.name_valid(name) && D.value_valid(x) && D.record_later(r, name), D.value_valid(r), valid),
          record_later_requires_form_of_record(r, name, order_rest), order_rest))
    case D.VAbsent{}:
      F.absurd_boolean(PartialRecord(v, P.encode_partial(v), previous), form)
    case D.VBool{b}:
      F.absurd_boolean(PartialRecord(v, P.encode_partial(v), previous), form)
    case D.VInt{a, b}:
      F.absurd_boolean(PartialRecord(v, P.encode_partial(v), previous), form)
    case D.VText{s}:
      F.absurd_boolean(PartialRecord(v, P.encode_partial(v), previous), form)
    case D.VListEmpty{}:
      F.absurd_boolean(PartialRecord(v, P.encode_partial(v), previous), form)
    case D.VList{h, t}:
      F.absurd_boolean(PartialRecord(v, P.encode_partial(v), previous), form)

# Besides the tag6 header, every name exposes its own tag4 and UTF-8 size.
type RecordExposed<-v: D.Value, -bs: List<&2, U32>> is Type:
  RecordExposed{segments: List<&2, S.FieldSegmented>, number: B.Number64,
    value: {v == A.attach_record(S.fields(segments), D.VRecordEmpty{}) : D.Value},
    canonical: S.FieldsCanonical(segments),
    ordered: A.FieldsOrdered(S.fields(segments), ""),
    names: N.NamesExposed(segments),
    measure: {B.nat64(S.count_fields(segments)) == Some{number} : Maybe<&2, B.Number64>},
    bytes: {bs == M.prefix(6, number, S.bytes_fields(segments)) : List<&2, U32>}}

def finalize_record_combined_header(+v: D.Value, +n: Nat, +payload: List<&2, U32>, +bs: List<&2, U32>,
  structure: RecordSegmented<v, n, payload, "">, header: X.Header<6, n, payload, bs>) -> RecordExposed<v, bs>:
  match structure header:
    case RecordSegmented{+segments, value, canonical, ordered, count, bytes} X.Header{+number, measure, bytes_all}:
      F.combined_pair(RecordExposed<v, bs>, S.FieldsCanonical(segments), N.NamesExposed(segments),
        N.fields_canonical_expose_all_os_names(segments, canonical),
        fields => names => RecordExposed{segments, number, value, fields, ordered, names,
          Equal.trans(Maybe<&2, B.Number64>, B.nat64(S.count_fields(segments)), B.nat64(n), Some{number},
            Equal.cong(Nat, Maybe<&2, B.Number64>, k => B.nat64(k), S.count_fields(segments), n, count), measure),
          Equal.trans(List<&2, U32>, bs, M.prefix(6, number, payload), M.prefix(6, number, S.bytes_fields(segments)), bytes_all,
            Equal.cong(List<&2, U32>, List<&2, U32>, p => M.prefix(6, number, p), payload, S.bytes_fields(segments),
              Equal.sym(List<&2, U32>, S.bytes_fields(segments), payload, bytes)))})

def finalize_record_exposed(+v: D.Value, +bs: List<&2, U32>, p: P.Partial,
  structure: PartialRecord(v, p, ""), encoded: {P.finalize(p) == Some{bs} : Maybe<&2, List<&2, U32>>}) -> RecordExposed<v, bs>:
  match p:
    case P.Impossible{}:
      L.ex_false(RecordExposed<v, bs>, F.none_negative_some(List<&2, U32>, bs, encoded))
    case P.Record{+n, +payload}:
      finalize_record_combined_header(v, n, payload, bs, structure,
        X.field_variable_exposes_measure_and_bytes(6, n, payload, bs, encoded))
    case P.Atom{payload}:
      L.ex_false(RecordExposed<v, bs>, structure)
    case P.ListFrame{n, payload}:
      L.ex_false(RecordExposed<v, bs>, structure)

law record_encoded_exposes_segments_count_and_header:
  for +v: D.Value
  for +bs: List<&2, U32>
  for +form: {D.is_record(v) == True{} : Bool}
  for encoded: P.Encoding(v, bs)
  RecordExposed<v, bs>
def record_encoded_exposes_segments_count_and_header(v, bs, form, encoded):
  F.combined_pair(RecordExposed<v, bs>, {D.value_valid(v) == True{} : Bool},
    {P.finalize(P.encode_partial(v)) == Some{bs} : Maybe<&2, List<&2, U32>>},
    M.child_canonical_exposes_validity_and_bytes(v, bs, encoded),
    +valid => partial => finalize_record_exposed(v, bs, P.encode_partial(v),
      record_valid_exposes_segmentation_partial(v, "", valid, form,
        record_valid_and_later_of_empty(v, valid, form)), partial))
