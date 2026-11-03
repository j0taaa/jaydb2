# Actual segments, in reading order. Premises are contract encodings of
# EACH element, never size inequalities.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Logic.bend as L
import ./Foundations.bend as F
import ./CodecSizes.bend as T
import ./CodecLimitsNames.bend as N
import ./CodecCanonical.bend as K
import ./CodecSums.bend as A

law sum_associative:
  for a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}
def sum_associative(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, r => 1n+r, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), sum_associative(p, b, c))

law sum_commutative:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}
def sum_commutative(a, b):
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, A.nat_sum_zero_right(b))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p),
        Equal.cong(Nat, Nat, r => 1n+r, Nat.add(p, b), Nat.add(b, p), sum_commutative(p, b)),
        Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), K.sum_successor_right(b, p)))

law swap_summands_initial:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}
def swap_summands_initial(a, b, c):
  Equal.trans(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), c), Nat.add(b, Nat.add(a, c)),
    Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), sum_associative(a, b, c)),
    Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(b, a), c), Nat.add(b, Nat.add(a, c)),
      Equal.cong(Nat, Nat, r => Nat.add(r, c), Nat.add(a, b), Nat.add(b, a), sum_commutative(a, b)),
      sum_associative(b, a, c)))

law multiply_successor_right:
  for +k: Nat
  for +n: Nat
  {Nat.mul(k, 1n+n) == Nat.add(k, Nat.mul(k, n)) : Nat}
def multiply_successor_right(k, n):
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, r => 1n+r,
        Nat.add(n, Nat.mul(p, 1n+n)), Nat.add(p, Nat.add(n, Nat.mul(p, n))),
        Equal.trans(Nat, Nat.add(n, Nat.mul(p, 1n+n)), Nat.add(n, Nat.add(p, Nat.mul(p, n))), Nat.add(p, Nat.add(n, Nat.mul(p, n))),
          Equal.cong(Nat, Nat, r => Nat.add(n, r), Nat.mul(p, 1n+n), Nat.add(p, Nat.mul(p, n)), multiply_successor_right(p, n)),
          swap_summands_initial(n, p, Nat.mul(p, n))))

law limit_reflexive:
  for +n: Nat
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

type ValueSegmented is Data:
  ValueSegmented{value: D.Value, bytes: List<&2, U32>}

type FieldSegmented is Data:
  FieldSegmented{name: String, value: D.Value, name_bytes: List<&2, U32>, value_bytes: List<&2, U32>}

def ValuesCanonical(xs: List<&2, ValueSegmented>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{ValueSegmented{v, bs}, t}:
      L.E<P.Encoding(v, bs), ValuesCanonical(t)>

def FieldsCanonical(xs: List<&2, FieldSegmented>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{FieldSegmented{n, v, nb, vb}, t}:
      L.E<{D.name_valid(n) == True{} : Bool},
        L.E<{P.text(n) == Some{nb} : Maybe<&2, List<&2, U32>>},
          L.E<P.Encoding(v, vb), FieldsCanonical(t)>>>

def count_values(xs: List<&2, ValueSegmented>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+count_values(t)

def count_fields(xs: List<&2, FieldSegmented>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+count_fields(t)

def bytes_values(xs: List<&2, ValueSegmented>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{ValueSegmented{v, bs}, t}:
      B.concatenate(bs, bytes_values(t))

def bytes_fields(xs: List<&2, FieldSegmented>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{FieldSegmented{n, v, nb, vb}, t}:
      B.concatenate(B.concatenate(nb, vb), bytes_fields(t))

def values(xs: List<&2, ValueSegmented>) -> List<&2, D.Value>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{ValueSegmented{v, bs}, t}:
      Con{v, values(t)}

def fields(xs: List<&2, FieldSegmented>) -> List<&2, D.Field>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{FieldSegmented{n, v, nb, vb}, t}:
      Con{D.Field{n, v}, fields(t)}

law sequence_of_values_canonical_requires_one_octet_by_value:
  for +xs: List<&2, ValueSegmented>
  for canonical: ValuesCanonical(xs)
  {Nat.is_le(count_values(xs), B.length(bytes_values(xs))) == True{} : Bool}
def sequence_of_values_canonical_requires_one_octet_by_value(xs, canonical):
  match xs:
    case Nil{}:
      {==}
    case Con{ValueSegmented{+v, +bs}, +t}:
      match canonical:
        case L.Both{head, tail}:
          %Equal.sym(Nat, B.length(B.concatenate(bs, bytes_values(t))), Nat.add(B.length(bs), B.length(bytes_values(t))), N.length_concatenation(bs, bytes_values(t))) :
            {Nat.is_le(1n+count_values(t), _) == True{} : Bool}
          N.sum_preserves_limits(1n, count_values(t), B.length(bs), B.length(bytes_values(t)),
            T.all_value_canonical_requires_by_minus_one_octet(v, bs, head),
            sequence_of_values_canonical_requires_one_octet_by_value(t, tail))

law sequence_of_fields_canonical_requires_eleven_octets_by_field:
  for +xs: List<&2, FieldSegmented>
  for canonical: FieldsCanonical(xs)
  {Nat.is_le(Nat.mul(11n, count_fields(xs)), B.length(bytes_fields(xs))) == True{} : Bool}
def sequence_of_fields_canonical_requires_eleven_octets_by_field(xs, canonical):
  match xs:
    case Nil{}:
      {==}
    case Con{FieldSegmented{+n, +v, +nb, +vb}, +t}:
      match canonical:
        case L.Both{name, L.Both{text, L.Both{value, tail}}}:
          %Equal.sym(Nat, Nat.mul(11n, 1n+count_fields(t)), Nat.add(11n, Nat.mul(11n, count_fields(t))), multiply_successor_right(11n, count_fields(t))) :
            {Nat.is_le(_, B.length(bytes_fields(xs))) == True{} : Bool}
          %Equal.sym(Nat, B.length(B.concatenate(B.concatenate(nb, vb), bytes_fields(t))), Nat.add(B.length(B.concatenate(nb, vb)), B.length(bytes_fields(t))), N.length_concatenation(B.concatenate(nb, vb), bytes_fields(t))) :
            {Nat.is_le(Nat.add(11n, Nat.mul(11n, count_fields(t))), _) == True{} : Bool}
          N.sum_preserves_limits(11n, Nat.mul(11n, count_fields(t)), B.length(B.concatenate(nb, vb)), B.length(bytes_fields(t)),
            N.field_canonical_requires_eleven_octets(n, v, nb, vb, name, text, value),
            sequence_of_fields_canonical_requires_eleven_octets_by_field(t, tail))

law concatenate_segments_preserves_sum_of_limits:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +m: Nat
  for +n: Nat
  for ma: {Nat.is_le(m, B.length(a)) == True{} : Bool}
  for nb: {Nat.is_le(n, B.length(b)) == True{} : Bool}
  {Nat.is_le(Nat.add(m, n), B.length(B.concatenate(a, b))) == True{} : Bool}
def concatenate_segments_preserves_sum_of_limits(a, b, m, n, ma, nb):
  %Equal.sym(Nat, B.length(B.concatenate(a, b)), Nat.add(B.length(a), B.length(b)), N.length_concatenation(a, b)) :
    {Nat.is_le(Nat.add(m, n), _) == True{} : Bool}
  N.sum_preserves_limits(m, n, B.length(a), B.length(b), ma, nb)
