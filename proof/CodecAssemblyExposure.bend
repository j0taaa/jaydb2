# Encoder inversion: the whole encoding yields child segments,
# representable count and exact header, without local premises.
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

type Header<-tag: U32, -n: Nat, -payload: List<&2, U32>, -bs: List<&2, U32>> is Type:
  Header{number: B.Number64,
    measure: {B.nat64(n) == Some{number} : Maybe<&2, B.Number64>},
    bytes: {bs == M.prefix(tag, number, payload) : List<&2, U32>}}

def expose_measure_variable(+tag: U32, +n: Nat, +payload: List<&2, U32>, +bs: List<&2, U32>,
  number: Maybe<&2, B.Number64>,
  measure: {B.nat64(n) == number : Maybe<&2, B.Number64>},
  accepted: {P.prefix_size(tag, B.number64_bytes(number), payload) == Some{bs} : Maybe<&2, List<&2, U32>>}) ->
  Header<tag, n, payload, bs>:
  match number:
    case None{}:
      L.ex_false(Header<tag, n, payload, bs>, F.none_negative_some(List<&2, U32>, bs, accepted))
    case Some{B.Number64{+high, +low}}:
      Header{B.Number64{high, low}, measure,
        Equal.sym(List<&2, U32>, M.prefix(tag, B.Number64{high, low}, payload), bs,
          F.some_injective(List<&2, U32>, M.prefix(tag, B.Number64{high, low}, payload), bs, accepted))}

law field_variable_exposes_measure_and_bytes:
  for +tag: U32
  for +n: Nat
  for +payload: List<&2, U32>
  for +bs: List<&2, U32>
  for accepted: {P.field_variable(tag, n, payload) == Some{bs} : Maybe<&2, List<&2, U32>>}
  Header<tag, n, payload, bs>
def field_variable_exposes_measure_and_bytes(tag, n, payload, bs, accepted):
  expose_measure_variable(tag, n, payload, bs, B.nat64(n), {==}, accepted)

# The partial Impossible form cannot finalize to Some. Its
# Unit witness allows structural induction to preserve this failure.
type ListSegmented<-v: D.Value, -n: Nat, -payload: List<&2, U32>> is Type:
  ListSegmented{segments: List<&2, S.ValueSegmented>,
    value: {v == A.attach_list(S.values(segments), D.VListEmpty{}) : D.Value},
    canonical: S.ValuesCanonical(segments),
    count: {S.count_values(segments) == n : Nat},
    bytes: {S.bytes_values(segments) == payload : List<&2, U32>}}

def PartialList(v: D.Value, p: P.Partial) -> Type:
  match p:
    case P.Impossible{}:
      Unit
    case P.ListFrame{n, payload}:
      ListSegmented<v, n, payload>
    case _:
      Empty

def expose_head_list(+h: D.Value, +t: D.Value,
  head: Maybe<&2, List<&2, U32>>, tail: P.Partial,
  valid: {D.value_valid(h) == True{} : Bool},
  bytes_head: {P.finalize(P.encode_partial(h)) == head : Maybe<&2, List<&2, U32>>},
  rest: PartialList(t, tail)) -> PartialList(D.VList{h, t}, P.list_cases(head, tail)):
  match head tail:
    case None{} _:
      Unit{}
    case Some{+bs} P.ListFrame{+n, +payload}:
      match rest:
        case ListSegmented{+segments, value, canonical, count, bytes}:
          ListSegmented{Con{S.ValueSegmented{h, bs}, segments},
            Equal.cong(D.Value, D.Value, r => D.VList{h, r}, t, A.attach_list(S.values(segments), D.VListEmpty{}), value),
            L.Both{Equal.trans(Maybe<&2, List<&2, U32>>, P.encode(h), P.finalize(P.encode_partial(h)), Some{bs},
              K.value_valid_releases_encoding(h, valid), bytes_head), canonical},
            Equal.cong(Nat, Nat, q => 1n+q, S.count_values(segments), n, count),
            Equal.cong(List<&2, U32>, List<&2, U32>, r => B.concatenate(bs, r), S.bytes_values(segments), payload, bytes)}
    case Some{bs} P.Impossible{}:
      Unit{}
    case Some{bs} P.Atom{payload}:
      Unit{}
    case Some{bs} P.Record{n, payload}:
      Unit{}

law list_is_valid_exposes_segmentation_partial:
  for +v: D.Value
  for +valid: {D.value_valid(v) == True{} : Bool}
  for form: {D.is_list(v) == True{} : Bool}
  PartialList(v, P.encode_partial(v))
def list_is_valid_exposes_segmentation_partial(v, valid, form):
  match v:
    case D.VListEmpty{}:
      ListSegmented{Nil{}, {==}, Unit{}, {==}, {==}}
    case D.VList{+h, +t}:
      +head_form = F.and_boolean_left(D.value_valid(h) && D.is_list(t), D.value_valid(t), valid)
      expose_head_list(h, t, P.finalize(P.encode_partial(h)), P.encode_partial(t),
        F.and_boolean_left(D.value_valid(h), D.is_list(t), head_form), {==},
        list_is_valid_exposes_segmentation_partial(t,
          F.and_boolean_right(D.value_valid(h) && D.is_list(t), D.value_valid(t), valid),
          F.and_boolean_right(D.value_valid(h), D.is_list(t), head_form)))
    case D.VAbsent{}:
      F.absurd_boolean(PartialList(v, P.encode_partial(v)), form)
    case D.VBool{b}:
      F.absurd_boolean(PartialList(v, P.encode_partial(v)), form)
    case D.VInt{a, b}:
      F.absurd_boolean(PartialList(v, P.encode_partial(v)), form)
    case D.VText{s}:
      F.absurd_boolean(PartialList(v, P.encode_partial(v)), form)
    case D.VRecordEmpty{}:
      F.absurd_boolean(PartialList(v, P.encode_partial(v)), form)
    case D.VRecord{n, x, r}:
      F.absurd_boolean(PartialList(v, P.encode_partial(v)), form)

type ListExposed<-v: D.Value, -bs: List<&2, U32>> is Type:
  ListExposed{segments: List<&2, S.ValueSegmented>, number: B.Number64,
    value: {v == A.attach_list(S.values(segments), D.VListEmpty{}) : D.Value},
    canonical: S.ValuesCanonical(segments),
    measure: {B.nat64(S.count_values(segments)) == Some{number} : Maybe<&2, B.Number64>},
    bytes: {bs == M.prefix(5, number, S.bytes_values(segments)) : List<&2, U32>}}

def finalize_list_combined_header(+v: D.Value, +n: Nat, +payload: List<&2, U32>, +bs: List<&2, U32>,
  structure: ListSegmented<v, n, payload>, header: Header<5, n, payload, bs>) -> ListExposed<v, bs>:
  match structure header:
    case ListSegmented{+segments, value, canonical, count, bytes} Header{+number, measure, bytes_all}:
      ListExposed{segments, number, value, canonical,
        Equal.trans(Maybe<&2, B.Number64>, B.nat64(S.count_values(segments)), B.nat64(n), Some{number},
          Equal.cong(Nat, Maybe<&2, B.Number64>, k => B.nat64(k), S.count_values(segments), n, count), measure),
        Equal.trans(List<&2, U32>, bs, M.prefix(5, number, payload), M.prefix(5, number, S.bytes_values(segments)), bytes_all,
          Equal.cong(List<&2, U32>, List<&2, U32>, p => M.prefix(5, number, p), payload, S.bytes_values(segments),
            Equal.sym(List<&2, U32>, S.bytes_values(segments), payload, bytes)))}

def finalize_list_exposed(+v: D.Value, +bs: List<&2, U32>, p: P.Partial,
  structure: PartialList(v, p), encoded: {P.finalize(p) == Some{bs} : Maybe<&2, List<&2, U32>>}) -> ListExposed<v, bs>:
  match p:
    case P.Impossible{}:
      L.ex_false(ListExposed<v, bs>, F.none_negative_some(List<&2, U32>, bs, encoded))
    case P.ListFrame{+n, +payload}:
      finalize_list_combined_header(v, n, payload, bs, structure,
        field_variable_exposes_measure_and_bytes(5, n, payload, bs, encoded))
    case P.Atom{payload}:
      L.ex_false(ListExposed<v, bs>, structure)
    case P.Record{n, payload}:
      L.ex_false(ListExposed<v, bs>, structure)

law list_encoded_exposes_segments_count_and_header:
  for +v: D.Value
  for +bs: List<&2, U32>
  for form: {D.is_list(v) == True{} : Bool}
  for encoded: P.Encoding(v, bs)
  ListExposed<v, bs>
def list_encoded_exposes_segments_count_and_header(v, bs, form, encoded):
  F.combined_pair(ListExposed<v, bs>, {D.value_valid(v) == True{} : Bool},
    {P.finalize(P.encode_partial(v)) == Some{bs} : Maybe<&2, List<&2, U32>>},
    M.child_canonical_exposes_validity_and_bytes(v, bs, encoded),
    valid => partial => finalize_list_exposed(v, bs, P.encode_partial(v),
      list_is_valid_exposes_segmentation_partial(v, valid, form), partial))
