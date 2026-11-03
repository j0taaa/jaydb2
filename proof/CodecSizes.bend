# Lower bounds of canonical segments used by the minima.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecContent.bend as G

def ResultWithTag(m: Maybe<&2, List<&2, U32>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{bs}:
      G.NotEmpty(bs)

def PartialWithTag(p: P.Partial) -> Type:
  match p:
    case P.Atom{bs}:
      G.NotEmpty(bs)
    case P.Impossible{}:
      Unit
    case P.ListFrame{n, bs}:
      Unit
    case P.Record{n, bs}:
      Unit

law prefix_size_always_inserts_tag:
  for tag: U32
  for size: Maybe<&2, List<&2, U32>>
  for content: List<&2, U32>
  ResultWithTag(P.prefix_size(tag, size, content))
def prefix_size_always_inserts_tag(tag, size, content):
  match size:
    case None{}:
      Unit{}
    case Some{header}:
      Unit{}

law text_cases_always_inserts_tag:
  for valid: Bool
  for +bs: List<&2, U32>
  ResultWithTag(P.text_cases(valid, bs))
def text_cases_always_inserts_tag(valid, bs):
  match valid:
    case False{}:
      Unit{}
    case True{}:
      prefix_size_always_inserts_tag(4, B.length64(B.length(bs)), bs)

law atom_optional_preserves_tag:
  for +m: Maybe<&2, List<&2, U32>>
  for tag: ResultWithTag(m)
  PartialWithTag(P.atom_optional(m))
def atom_optional_preserves_tag(m, tag):
  match m:
    case None{}:
      Unit{}
    case Some{bs}:
      tag

law list_cases_has_tag:
  for h: Maybe<&2, List<&2, U32>>
  for t: P.Partial
  PartialWithTag(P.list_cases(h, t))
def list_cases_has_tag(h, t):
  match h t:
    case None{} _:
      Unit{}
    case Some{bs} P.Impossible{}:
      Unit{}
    case Some{bs} P.Atom{xs}:
      Unit{}
    case Some{bs} P.ListFrame{n, xs}:
      Unit{}
    case Some{bs} P.Record{n, xs}:
      Unit{}

law record_cases_has_tag:
  for name: Maybe<&2, List<&2, U32>>
  for v: Maybe<&2, List<&2, U32>>
  for r: P.Partial
  PartialWithTag(P.record_cases(name, v, r))
def record_cases_has_tag(name, v, r):
  match name v r:
    case None{} _ _:
      Unit{}
    case Some{bs} None{} _:
      Unit{}
    case Some{bs} Some{vs} P.Impossible{}:
      Unit{}
    case Some{bs} Some{vs} P.Atom{xs}:
      Unit{}
    case Some{bs} Some{vs} P.ListFrame{n, xs}:
      Unit{}
    case Some{bs} Some{vs} P.Record{n, xs}:
      Unit{}

def boolean_has_tag(b: Bool) -> PartialWithTag(P.boolean(b)):
  match b:
    case False{}:
      Unit{}
    case True{}:
      Unit{}

law encoding_partial_never_loses_tag:
  for v: D.Value
  PartialWithTag(P.encode_partial(v))
def encoding_partial_never_loses_tag(v):
  match v:
    case D.VAbsent{}:
      Unit{}
    case D.VBool{b}:
      boolean_has_tag(b)
    case D.VInt{a, b}:
      Unit{}
    case D.VText{+s}:
      atom_optional_preserves_tag(P.text(s), text_cases_always_inserts_tag(B.text_valid(s), B.utf8(s)))
    case D.VListEmpty{}:
      Unit{}
    case D.VList{h, t}:
      list_cases_has_tag(P.finalize(P.encode_partial(h)), P.encode_partial(t))
    case D.VRecordEmpty{}:
      Unit{}
    case D.VRecord{n, v, r}:
      record_cases_has_tag(P.text(n), P.finalize(P.encode_partial(v)), P.encode_partial(r))

def prefix_accepted_has_tag(tag: U32, size: Maybe<&2, List<&2, U32>>, +content: List<&2, U32>, -bs: List<&2, U32>,
  accepted: {P.prefix_size(tag, size, content) == Some{bs} : Maybe<&2, List<&2, U32>>}) -> G.NotEmpty(bs):
  match size:
    case None{}:
      L.ex_false(G.NotEmpty(bs), F.none_negative_some(List<&2, U32>, bs, accepted))
    case Some{+header}:
      %F.some_injective(List<&2, U32>, Con{tag, B.concatenate(header, content)}, bs, accepted) : G.NotEmpty(_)
      Unit{}

law finalize_partial_combined_tag_never_and_empty:
  for +p: P.Partial
  for -bs: List<&2, U32>
  for tag: PartialWithTag(p)
  for accepted: {P.finalize(p) == Some{bs} : Maybe<&2, List<&2, U32>>}
  G.NotEmpty(bs)
def finalize_partial_combined_tag_never_and_empty(p, bs, tag, accepted):
  match p:
    case P.Impossible{}:
      L.ex_false(G.NotEmpty(bs), F.none_negative_some(List<&2, U32>, bs, accepted))
    case P.Atom{+bytes}:
      %F.some_injective(List<&2, U32>, bytes, bs, accepted) : G.NotEmpty(_)
      tag
    case P.ListFrame{n, +bytes}:
      prefix_accepted_has_tag(5, B.length64(n), bytes, bs, accepted)
    case P.Record{n, +bytes}:
      prefix_accepted_has_tag(6, B.length64(n), bytes, bs, accepted)

def cases_accepted_preserve_result(valid: Bool, -result: Maybe<&2, List<&2, U32>>, -bs: List<&2, U32>,
  accepted: {P.encode_cases(valid, result) == Some{bs} : Maybe<&2, List<&2, U32>>}) -> {result == Some{bs} : Maybe<&2, List<&2, U32>>}:
  match valid:
    case False{}:
      L.ex_false({result == Some{bs} : Maybe<&2, List<&2, U32>>}, F.none_negative_some(List<&2, U32>, bs, accepted))
    case True{}:
      accepted

law none_encoding_canonical_and_empty:
  for +v: D.Value
  for -bs: List<&2, U32>
  for encoded: P.Encoding(v, bs)
  G.NotEmpty(bs)
def none_encoding_canonical_and_empty(v, bs, encoded):
  finalize_partial_combined_tag_never_and_empty(P.encode_partial(v), bs, encoding_partial_never_loses_tag(v),
    cases_accepted_preserve_result(D.value_valid(v), P.finalize(P.encode_partial(v)), bs, encoded))

law zero_natural_negative_greater:
  for n: Nat
  {Nat.is_le(0n, n) == True{} : Bool}
def zero_natural_negative_greater(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

law bytes_negative_empty_has_by_minus_one_octet:
  for +bs: List<&2, U32>
  for positive: G.NotEmpty(bs)
  {Nat.is_le(1n, B.length(bs)) == True{} : Bool}
def bytes_negative_empty_has_by_minus_one_octet(bs, positive):
  match bs:
    case Nil{}:
      L.ex_false({False{} == True{} : Bool}, positive)
    case Con{b, t}:
      zero_natural_negative_greater(B.length(t))

law all_value_canonical_requires_by_minus_one_octet:
  for +v: D.Value
  for +bs: List<&2, U32>
  for encoded: P.Encoding(v, bs)
  {Nat.is_le(1n, B.length(bs)) == True{} : Bool}
def all_value_canonical_requires_by_minus_one_octet(v, bs, encoded):
  bytes_negative_empty_has_by_minus_one_octet(bs, none_encoding_canonical_and_empty(v, bs, encoded))
