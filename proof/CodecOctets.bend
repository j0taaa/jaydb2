# Every ORIGINAL encoder result contains only bytes. Includes failure
# for Unicode, improper shape and unrepresentable counts, without truncation.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Logic.bend as L
import ./Foundations.bend as F
import ./CodecIntegers.bend as J
import ./CodecUTF8InverseOctets.bend as U

def OctetsOptional(m: Maybe<&2, List<&2, U32>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{bs}:
      {B.octets_all_valid(bs) == True{} : Bool}

def PartialOctets(p: P.Partial) -> Type:
  match p:
    case P.Impossible{}:
      Unit
    case P.Atom{bs}:
      {B.octets_all_valid(bs) == True{} : Bool}
    case P.ListFrame{n, bs}:
      {B.octets_all_valid(bs) == True{} : Bool}
    case P.Record{n, bs}:
      {B.octets_all_valid(bs) == True{} : Bool}

law number64_optional_only_emits_octets:
  for n: Maybe<&2, B.Number64>
  OctetsOptional(B.number64_bytes(n))
def number64_optional_only_emits_octets(n):
  match n:
    case None{}:
      Unit{}
    case Some{B.Number64{a, b}}:
      J.be64_only_emits_octets(a, b)

law prefix_preserves_octets:
  for +tag: U32
  for +h: Maybe<&2, List<&2, U32>>
  for +bs: List<&2, U32>
  for vt: {U32.is_le(tag, 255) == True{} : Bool}
  for vh: OctetsOptional(h)
  for vb: {B.octets_all_valid(bs) == True{} : Bool}
  OctetsOptional(P.prefix_size(tag, h, bs))
def prefix_preserves_octets(tag, h, bs, vt, vh, vb):
  match h:
    case None{}:
      Unit{}
    case Some{+header}:
      F.and_boolean_intro(U32.is_le(tag, 255), B.octets_all_valid(B.concatenate(header, bs)), vt,
        J.concatenate_preserves_octets(header, bs, vh, vb))

law finalize_preserves_octets:
  for +p: P.Partial
  for octets: PartialOctets(p)
  OctetsOptional(P.finalize(p))
def finalize_preserves_octets(p, octets):
  match p:
    case P.Impossible{}:
      Unit{}
    case P.Atom{bs}:
      octets
    case P.ListFrame{+n, +bs}:
      prefix_preserves_octets(5, B.length64(n), bs, {==}, number64_optional_only_emits_octets(B.nat64(n)), octets)
    case P.Record{+n, +bs}:
      prefix_preserves_octets(6, B.length64(n), bs, {==}, number64_optional_only_emits_octets(B.nat64(n)), octets)

def text_cases_preserves_octets(valid: Bool, +s: String,
  branch: {B.text_valid(s) == valid : Bool}) -> OctetsOptional(P.text_cases(valid, B.utf8(s))):
  match valid:
    case False{}:
      Unit{}
    case True{}:
      prefix_preserves_octets(4, B.length64(B.length(B.utf8(s))), B.utf8(s), {==},
        number64_optional_only_emits_octets(B.nat64(B.length(B.utf8(s)))), U.utf8_text_valid_emits_octets(s, branch))

law text_only_emits_octets:
  for +s: String
  OctetsOptional(P.text(s))
def text_only_emits_octets(s):
  text_cases_preserves_octets(B.text_valid(s), s, {==})

def atom_optional_preserves_octets(+m: Maybe<&2, List<&2, U32>>,
  octets: OctetsOptional(m)) -> PartialOctets(P.atom_optional(m)):
  match m:
    case None{}:
      Unit{}
    case Some{bs}:
      octets

def list_cases_preserves_octets(+h: Maybe<&2, List<&2, U32>>, +t: P.Partial,
  vh: OctetsOptional(h), vt: PartialOctets(t)) -> PartialOctets(P.list_cases(h, t)):
  match h t:
    case None{} _:
      Unit{}
    case Some{bs} P.Impossible{}:
      Unit{}
    case Some{bs} P.Atom{ts}:
      Unit{}
    case Some{+bs} P.ListFrame{n, +ts}:
      J.concatenate_preserves_octets(bs, ts, vh, vt)
    case Some{bs} P.Record{n, ts}:
      Unit{}

def record_cases_preserves_octets(+name: Maybe<&2, List<&2, U32>>, +v: Maybe<&2, List<&2, U32>>, +r: P.Partial,
  vn: OctetsOptional(name), vv: OctetsOptional(v), vr: PartialOctets(r)) -> PartialOctets(P.record_cases(name, v, r)):
  match name v r:
    case None{} _ _:
      Unit{}
    case Some{bs} None{} _:
      Unit{}
    case Some{bs} Some{vs} P.Impossible{}:
      Unit{}
    case Some{bs} Some{vs} P.Atom{rs}:
      Unit{}
    case Some{bs} Some{vs} P.ListFrame{n, rs}:
      Unit{}
    case Some{+bs} Some{+vs} P.Record{n, +rs}:
      J.concatenate_preserves_octets(bs, B.concatenate(vs, rs), vn, J.concatenate_preserves_octets(vs, rs, vv, vr))

def boolean_only_emits_octets(b: Bool) -> PartialOctets(P.boolean(b)):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law encode_partial_only_emits_octets:
  for +v: D.Value
  PartialOctets(P.encode_partial(v))
def encode_partial_only_emits_octets(v):
  match v:
    case D.VAbsent{}:
      {==}
    case D.VBool{b}:
      boolean_only_emits_octets(b)
    case D.VInt{+a, +b}:
      J.be64_only_emits_octets(a, b)
    case D.VText{+s}:
      atom_optional_preserves_octets(P.text(s), text_only_emits_octets(s))
    case D.VListEmpty{}:
      {==}
    case D.VList{+h, +t}:
      list_cases_preserves_octets(P.finalize(P.encode_partial(h)), P.encode_partial(t),
        finalize_preserves_octets(P.encode_partial(h), encode_partial_only_emits_octets(h)), encode_partial_only_emits_octets(t))
    case D.VRecordEmpty{}:
      {==}
    case D.VRecord{+n, +v, +r}:
      record_cases_preserves_octets(P.text(n), P.finalize(P.encode_partial(v)), P.encode_partial(r), text_only_emits_octets(n),
        finalize_preserves_octets(P.encode_partial(v), encode_partial_only_emits_octets(v)), encode_partial_only_emits_octets(r))

def encode_cases_preserves_octets(valid: Bool, +m: Maybe<&2, List<&2, U32>>, octets: OctetsOptional(m)) -> OctetsOptional(P.encode_cases(valid, m)):
  match valid:
    case False{}:
      Unit{}
    case True{}:
      octets

law encode_only_emits_octets:
  for +v: D.Value
  OctetsOptional(P.encode(v))
def encode_only_emits_octets(v):
  encode_cases_preserves_octets(D.value_valid(v), P.finalize(P.encode_partial(v)),
    finalize_preserves_octets(P.encode_partial(v), encode_partial_only_emits_octets(v)))

def result_accepted_has_octets(+m: Maybe<&2, List<&2, U32>>, -bs: List<&2, U32>,
  octets: OctetsOptional(m), accepted: {m == Some{bs} : Maybe<&2, List<&2, U32>>}) -> {B.octets_all_valid(bs) == True{} : Bool}:
  match m:
    case None{}:
      L.ex_false({B.octets_all_valid(bs) == True{} : Bool}, F.none_negative_some(List<&2, U32>, bs, accepted))
    case Some{+bytes}:
      %F.some_injective(List<&2, U32>, bytes, bs, accepted) : {B.octets_all_valid(_) == True{} : Bool}
      octets

law any_encoding_only_emits_octets:
  for +v: D.Value
  for -bs: List<&2, U32>
  for encoded: P.Encoding(v, bs)
  {B.octets_all_valid(bs) == True{} : Bool}
def any_encoding_only_emits_octets(v, bs, encoded):
  result_accepted_has_octets(P.encode(v), bs, encode_only_emits_octets(v), encoded)
