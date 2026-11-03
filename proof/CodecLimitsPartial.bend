# Segment bounds produced by the REAL partial encoder.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Logic.bend as L
import ./Foundations.bend as F
import ./CodecContent.bend as G
import ./CodecSizes.bend as T
import ./CodecLimitsNames.bend as N
import ./CodecLimitsSequences.bend as S

def PartialBounded(p: P.Partial) -> Type:
  match p:
    case P.Impossible{}:
      Unit
    case P.Atom{bs}:
      G.NotEmpty(bs)
    case P.ListFrame{n, bs}:
      {Nat.is_le(n, B.length(bs)) == True{} : Bool}
    case P.Record{n, bs}:
      {Nat.is_le(Nat.mul(11n, n), B.length(bs)) == True{} : Bool}

law finalize_preserves_tag:
  for p: P.Partial
  for tag: T.PartialWithTag(p)
  T.ResultWithTag(P.finalize(p))
def finalize_preserves_tag(p, tag):
  match p:
    case P.Impossible{}:
      Unit{}
    case P.Atom{bs}:
      tag
    case P.ListFrame{n, bs}:
      T.prefix_size_always_inserts_tag(5, B.length64(n), bs)
    case P.Record{n, bs}:
      T.prefix_size_always_inserts_tag(6, B.length64(n), bs)

law atom_optional_bounded:
  for m: Maybe<&2, List<&2, U32>>
  for tag: T.ResultWithTag(m)
  PartialBounded(P.atom_optional(m))
def atom_optional_bounded(m, tag):
  match m:
    case None{}:
      Unit{}
    case Some{bs}:
      tag

law boolean_bounded:
  for b: Bool
  PartialBounded(P.boolean(b))
def boolean_bounded(b):
  match b:
    case False{}:
      Unit{}
    case True{}:
      Unit{}

law list_cases_bounded:
  for h: Maybe<&2, List<&2, U32>>
  for t: P.Partial
  for tag_h: T.ResultWithTag(h)
  for limit_t: PartialBounded(t)
  PartialBounded(P.list_cases(h, t))
def list_cases_bounded(h, t, tag_h, limit_t):
  match h t:
    case None{} _:
      Unit{}
    case Some{bs} P.Impossible{}:
      Unit{}
    case Some{bs} P.Atom{rest}:
      Unit{}
    case Some{+bs} P.ListFrame{+n, +rest}:
      S.concatenate_segments_preserves_sum_of_limits(bs, rest, 1n, n,
        T.bytes_negative_empty_has_by_minus_one_octet(bs, tag_h), limit_t)
    case Some{bs} P.Record{n, rest}:
      Unit{}

law record_cases_bounded:
  for +name: String
  for name_bytes: Maybe<&2, List<&2, U32>>
  for value_bytes: Maybe<&2, List<&2, U32>>
  for r: P.Partial
  for valid: {D.name_valid(name) == True{} : Bool}
  for text: {P.text(name) == name_bytes : Maybe<&2, List<&2, U32>>}
  for tag_value: T.ResultWithTag(value_bytes)
  for limit_r: PartialBounded(r)
  PartialBounded(P.record_cases(name_bytes, value_bytes, r))
def record_cases_bounded(name, name_bytes, value_bytes, r, valid, text, tag_value, limit_r):
  match name_bytes value_bytes r:
    case None{} _ _:
      Unit{}
    case Some{nb} None{} _:
      Unit{}
    case Some{nb} Some{vb} P.Impossible{}:
      Unit{}
    case Some{nb} Some{vb} P.Atom{rest}:
      Unit{}
    case Some{nb} Some{vb} P.ListFrame{n, rest}:
      Unit{}
    case Some{+nb} Some{+vb} P.Record{+n, +rest}:
      %Equal.sym(Nat, Nat.mul(11n, 1n+n), Nat.add(11n, Nat.mul(11n, n)), S.multiply_successor_right(11n, n)) :
        {Nat.is_le(_, B.length(B.concatenate(nb, B.concatenate(vb, rest)))) == True{} : Bool}
      S.concatenate_segments_preserves_sum_of_limits(nb, B.concatenate(vb, rest), 10n, Nat.add(1n, Nat.mul(11n, n)),
        N.name_canonical_requires_ten_octets(name, nb, valid, text),
        S.concatenate_segments_preserves_sum_of_limits(vb, rest, 1n, Nat.mul(11n, n),
          T.bytes_negative_empty_has_by_minus_one_octet(vb, tag_value), limit_r))

law encoding_partial_is_valid_respects_limits:
  for +v: D.Value
  for +valid: {D.value_valid(v) == True{} : Bool}
  PartialBounded(P.encode_partial(v))
def encoding_partial_is_valid_respects_limits(v, valid):
  match v:
    case D.VAbsent{}:
      Unit{}
    case D.VBool{b}:
      boolean_bounded(b)
    case D.VInt{high, low}:
      Unit{}
    case D.VText{+s}:
      atom_optional_bounded(P.text(s), T.text_cases_always_inserts_tag(B.text_valid(s), B.utf8(s)))
    case D.VListEmpty{}:
      {==}
    case D.VList{+h, +t}:
      list_cases_bounded(P.finalize(P.encode_partial(h)), P.encode_partial(t),
        finalize_preserves_tag(P.encode_partial(h), T.encoding_partial_never_loses_tag(h)),
        encoding_partial_is_valid_respects_limits(t,
          F.and_boolean_right(D.value_valid(h) && D.is_list(t), D.value_valid(t), valid)))
    case D.VRecordEmpty{}:
      {==}
    case D.VRecord{+name, +x, +r}:
      record_cases_bounded(name, P.text(name), P.finalize(P.encode_partial(x)), P.encode_partial(r),
        F.and_boolean_left(D.name_valid(name), D.value_valid(x),
          F.and_boolean_left(D.name_valid(name) && D.value_valid(x), D.record_later(r, name),
            F.and_boolean_left(D.name_valid(name) && D.value_valid(x) && D.record_later(r, name), D.value_valid(r), valid))),
        {==}, finalize_preserves_tag(P.encode_partial(x), T.encoding_partial_never_loses_tag(x)),
        encoding_partial_is_valid_respects_limits(r,
          F.and_boolean_right(D.name_valid(name) && D.value_valid(x) && D.record_later(r, name), D.value_valid(r), valid)))

law content_list_canonical_requires_one_octet_by_element:
  for +v: D.Value
  for +n: Nat
  for +content: List<&2, U32>
  for valid: {D.value_valid(v) == True{} : Bool}
  for partial: {P.encode_partial(v) == P.ListFrame{n, content} : P.Partial}
  {Nat.is_le(n, B.length(content)) == True{} : Bool}
def content_list_canonical_requires_one_octet_by_element(v, n, content, valid, partial):
  %partial : PartialBounded(_)
  encoding_partial_is_valid_respects_limits(v, valid)

law content_record_canonical_requires_eleven_octets_by_field:
  for +v: D.Value
  for +n: Nat
  for +content: List<&2, U32>
  for valid: {D.value_valid(v) == True{} : Bool}
  for partial: {P.encode_partial(v) == P.Record{n, content} : P.Partial}
  {Nat.is_le(Nat.mul(11n, n), B.length(content)) == True{} : Bool}
def content_record_canonical_requires_eleven_octets_by_field(v, n, content, valid, partial):
  %partial : PartialBounded(_)
  encoding_partial_is_valid_respects_limits(v, valid)

law encoding_list_requires_header_and_elements:
  for +v: D.Value
  for +n: Nat
  for +content: List<&2, U32>
  for +bs: List<&2, U32>
  for valid: {D.value_valid(v) == True{} : Bool}
  for +partial: {P.encode_partial(v) == P.ListFrame{n, content} : P.Partial}
  for encoded: P.Encoding(v, bs)
  {Nat.is_le(Nat.add(9n, n), B.length(bs)) == True{} : Bool}
def encoding_list_requires_header_and_elements(v, n, content, bs, valid, partial, encoded):
  %Equal.sym(Nat, B.length(bs), Nat.add(9n, B.length(content)),
      N.prefix_number64_has_nine_octets_additional(B.nat64(n), 5, content, bs,
        (%partial :
          {P.finalize(_) == Some{bs} : Maybe<&2, List<&2, U32>>}
          T.cases_accepted_preserve_result(D.value_valid(v), P.finalize(P.encode_partial(v)), bs, encoded)))) :
    {Nat.is_le(Nat.add(9n, n), _) == True{} : Bool}
  N.sum_preserves_limits(9n, n, 9n, B.length(content), {==},
    content_list_canonical_requires_one_octet_by_element(v, n, content, valid, partial))

law encoding_record_requires_header_and_fields:
  for +v: D.Value
  for +n: Nat
  for +content: List<&2, U32>
  for +bs: List<&2, U32>
  for valid: {D.value_valid(v) == True{} : Bool}
  for +partial: {P.encode_partial(v) == P.Record{n, content} : P.Partial}
  for encoded: P.Encoding(v, bs)
  {Nat.is_le(Nat.add(9n, Nat.mul(11n, n)), B.length(bs)) == True{} : Bool}
def encoding_record_requires_header_and_fields(v, n, content, bs, valid, partial, encoded):
  %Equal.sym(Nat, B.length(bs), Nat.add(9n, B.length(content)),
      N.prefix_number64_has_nine_octets_additional(B.nat64(n), 6, content, bs,
        (%partial :
          {P.finalize(_) == Some{bs} : Maybe<&2, List<&2, U32>>}
          T.cases_accepted_preserve_result(D.value_valid(v), P.finalize(P.encode_partial(v)), bs, encoded)))) :
    {Nat.is_le(Nat.add(9n, Nat.mul(11n, n)), _) == True{} : Bool}
  N.sum_preserves_limits(9n, Nat.mul(11n, n), 9n, B.length(content), {==},
    content_record_canonical_requires_eleven_octets_by_field(v, n, content, valid, partial))
