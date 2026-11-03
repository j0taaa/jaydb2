# Name/field lower bounds derived from the actual encoder.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Logic.bend as L
import ./Foundations.bend as F
import ./CodecContent.bend as G
import ./CodecSizes.bend as T

law length_concatenation:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  {B.length(B.concatenate(a, b)) == Nat.add(B.length(a), B.length(b)) : Nat}
def length_concatenation(a, b):
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, n => 1n+n,
        B.length(B.concatenate(t, b)), Nat.add(B.length(t), B.length(b)),
        length_concatenation(t, b))

law limit_reflexive:
  for n: Nat
  {Nat.is_le(n, n) == True{} : Bool}
def limit_reflexive(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      limit_reflexive(p)

law limit_transitive:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for bc: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_le(a, c) == True{} : Bool}
def limit_transitive(a, b, c, ab, bc):
  match a b c:
    case 0n _ _:
      T.zero_natural_negative_greater(c)
    case 1n+p 0n _:
      F.absurd_boolean({Nat.is_le(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      F.absurd_boolean({False{} == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      limit_transitive(p, q, r, ab, bc)

law increase_limit_right:
  for +a: Nat
  for +b: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(a, 1n+b) == True{} : Bool}
def increase_limit_right(a, b, ab):
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      F.absurd_boolean({Nat.is_le(p, 0n) == True{} : Bool}, ab)
    case 1n+p 1n+q:
      increase_limit_right(p, q, ab)

law sum_preserves_limits:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for ac: {Nat.is_le(a, c) == True{} : Bool}
  for bd: {Nat.is_le(b, d) == True{} : Bool}
  {Nat.is_le(Nat.add(a, b), Nat.add(c, d)) == True{} : Bool}
def sum_preserves_limits(a, b, c, d, ac, bd):
  match a c:
    case 0n 0n:
      bd
    case 0n 1n+r:
      increase_limit_right(b, Nat.add(r, d),
        sum_preserves_limits(0n, b, r, d, T.zero_natural_negative_greater(r), bd))
    case 1n+p 0n:
      F.absurd_boolean({Nat.is_le(Nat.add(1n+p, b), d) == True{} : Bool}, ac)
    case 1n+p 1n+r:
      sum_preserves_limits(p, b, r, d, ac, bd)

def TextNotEmpty(s: String) -> Type:
  match s:
    case SNil{}:
      Empty
    case SCon{h, t}:
      Unit

law concatenate_preserves_negative_empty:
  for +a: List<&2, U32>
  for b: List<&2, U32>
  for positive: G.NotEmpty(a)
  G.NotEmpty(B.concatenate(a, b))
def concatenate_preserves_negative_empty(a, b, positive):
  match a:
    case Nil{}:
      L.ex_false(G.NotEmpty(b), positive)
    case Con{h, t}:
      Unit{}

law utf8_code_emitted_negative_and_empty:
  for cp: U32
  for ascii: Bool
  for two: Bool
  for three: Bool
  G.NotEmpty(B.utf8_code_emit(cp, ascii, two, three))
def utf8_code_emitted_negative_and_empty(cp, ascii, two, three):
  match ascii two three:
    case True{} _ _:
      Unit{}
    case False{} True{} _:
      Unit{}
    case False{} False{} True{}:
      Unit{}
    case False{} False{} False{}:
      Unit{}

law text_negative_empty_utf8_negative_empty:
  for +s: String
  for positive: TextNotEmpty(s)
  G.NotEmpty(B.utf8(s))
def text_negative_empty_utf8_negative_empty(s, positive):
  match s:
    case SNil{}:
      L.ex_false(G.NotEmpty(Nil{}), positive)
    case SCon{Chr{+cp}, t}:
      concatenate_preserves_negative_empty(B.utf8_code(cp), B.utf8(t),
        utf8_code_emitted_negative_and_empty(cp, U32.is_lt(cp, 128), U32.is_lt(cp, 2048), U32.is_lt(cp, 65536)))

law name_valid_negative_and_empty:
  for +name: String
  for valid: {D.name_valid(name) == True{} : Bool}
  TextNotEmpty(name)
def name_valid_negative_and_empty(name, valid):
  match name:
    case SNil{}:
      F.absurd_boolean(Empty, valid)
    case SCon{h, t}:
      Unit{}

law name_valid_utf8_requires_one_octet:
  for +name: String
  for valid: {D.name_valid(name) == True{} : Bool}
  {Nat.is_le(1n, B.length(B.utf8(name))) == True{} : Bool}
def name_valid_utf8_requires_one_octet(name, valid):
  T.bytes_negative_empty_has_by_minus_one_octet(B.utf8(name),
    text_negative_empty_utf8_negative_empty(name, name_valid_negative_and_empty(name, valid)))

# An accepted prefix has a tag and the eight actual u64 bytes.
law prefix_number64_has_nine_octets_additional:
  for x: Maybe<&2, B.Number64>
  for tag: U32
  for +content: List<&2, U32>
  for -bs: List<&2, U32>
  for accepted: {P.prefix_size(tag, B.number64_bytes(x), content) == Some{bs} : Maybe<&2, List<&2, U32>>}
  {B.length(bs) == Nat.add(9n, B.length(content)) : Nat}
def prefix_number64_has_nine_octets_additional(x, tag, content, bs, accepted):
  match x:
    case None{}:
      L.ex_false({B.length(bs) == Nat.add(9n, B.length(content)) : Nat},
        F.none_negative_some(List<&2, U32>, bs, accepted))
    case Some{B.Number64{+high, +low}}:
      %F.some_injective(List<&2, U32>, Con{tag, B.concatenate(B.be64(high, low), content)}, bs, accepted) :
        {B.length(_) == Nat.add(9n, B.length(content)) : Nat}
      {==}

law text_cases_accepted_has_length_exact:
  for valid: Bool
  for +content: List<&2, U32>
  for -bs: List<&2, U32>
  for accepted: {P.text_cases(valid, content) == Some{bs} : Maybe<&2, List<&2, U32>>}
  {B.length(bs) == Nat.add(9n, B.length(content)) : Nat}
def text_cases_accepted_has_length_exact(valid, content, bs, accepted):
  match valid:
    case False{}:
      L.ex_false({B.length(bs) == Nat.add(9n, B.length(content)) : Nat},
        F.none_negative_some(List<&2, U32>, bs, accepted))
    case True{}:
      prefix_number64_has_nine_octets_additional(B.nat64(B.length(content)), 4, content, bs, accepted)

law text_canonical_has_length_exact:
  for +s: String
  for -bs: List<&2, U32>
  for accepted: {P.text(s) == Some{bs} : Maybe<&2, List<&2, U32>>}
  {B.length(bs) == Nat.add(9n, B.length(B.utf8(s))) : Nat}
def text_canonical_has_length_exact(s, bs, accepted):
  text_cases_accepted_has_length_exact(B.text_valid(s), B.utf8(s), bs, accepted)

law name_canonical_requires_ten_octets:
  for +name: String
  for +bs: List<&2, U32>
  for valid: {D.name_valid(name) == True{} : Bool}
  for accepted: {P.text(name) == Some{bs} : Maybe<&2, List<&2, U32>>}
  {Nat.is_le(10n, B.length(bs)) == True{} : Bool}
def name_canonical_requires_ten_octets(name, bs, valid, accepted):
  %Equal.sym(Nat, B.length(bs), Nat.add(9n, B.length(B.utf8(name))),
      text_canonical_has_length_exact(name, bs, accepted)) :
    {Nat.is_le(10n, _) == True{} : Bool}
  sum_preserves_limits(9n, 1n, 9n, B.length(B.utf8(name)), {==}, name_valid_utf8_requires_one_octet(name, valid))

law field_canonical_requires_eleven_octets:
  for +name: String
  for +v: D.Value
  for +nb: List<&2, U32>
  for +vb: List<&2, U32>
  for valid: {D.name_valid(name) == True{} : Bool}
  for accepted_name: {P.text(name) == Some{nb} : Maybe<&2, List<&2, U32>>}
  for encoded: P.Encoding(v, vb)
  {Nat.is_le(11n, B.length(B.concatenate(nb, vb))) == True{} : Bool}
def field_canonical_requires_eleven_octets(name, v, nb, vb, valid, accepted_name, encoded):
  %Equal.sym(Nat, B.length(B.concatenate(nb, vb)), Nat.add(B.length(nb), B.length(vb)),
      length_concatenation(nb, vb)) :
    {Nat.is_le(11n, _) == True{} : Bool}
  sum_preserves_limits(10n, 1n, B.length(nb), B.length(vb),
    name_canonical_requires_ten_octets(name, nb, valid, accepted_name),
    T.all_value_canonical_requires_by_minus_one_octet(v, vb, encoded))
