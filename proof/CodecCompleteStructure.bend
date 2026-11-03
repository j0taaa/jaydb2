# Subvalue completeness capabilities and their extraction for segments.
# The tree does not assumes acceptance of a container or its bytes.
import Base
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Logic.bend as L
import ./Foundations.bend as F
import ./CodecLimitsSequences.bend as S
import ./CodecSequences.bend as V
import ./CodecRecords.bend as G
import ./CodecArities.bend as A
import ./CodecLimitsCopy.bend as K
import ./CodecSizes.bend as T
import ./CodecNamesLocals.bend as N

def Capacity(+v: D.Value) -> Type:
  @bs: List<&2, U32> -> P.Encoding(v, bs) -> V.CompleteLocal(v, bs)

# A single recursion defines the tree. The second component coincides
# definitionally with Descendants(v) at every D.Value constructor.
def Structural(v: D.Value) -> Type:
  match v:
    case D.VList{h, t}:
      L.E<Capacity(D.VList{h, t}), L.E<Structural(h), Structural(t)>>
    case D.VRecord{n, h, t}:
      L.E<Capacity(D.VRecord{n, h, t}), L.E<Structural(h), Structural(t)>>
    case _:
      L.E<Capacity(v), Unit>

def Descendants(v: D.Value) -> Type:
  match v:
    case D.VList{h, t}:
      L.E<Structural(h), Structural(t)>
    case D.VRecord{n, h, t}:
      L.E<Structural(h), Structural(t)>
    case _:
      Unit

def capacity_of_tree(v: D.Value, tree: Structural(v)) -> Capacity(v):
  match v tree:
    case D.VAbsent{} L.Both{capacity, descendants}:
      capacity
    case D.VBool{b} L.Both{capacity, descendants}:
      capacity
    case D.VInt{high, low} L.Both{capacity, descendants}:
      capacity
    case D.VText{s} L.Both{capacity, descendants}:
      capacity
    case D.VListEmpty{} L.Both{capacity, descendants}:
      capacity
    case D.VList{h, t} L.Both{capacity, descendants}:
      capacity
    case D.VRecordEmpty{} L.Both{capacity, descendants}:
      capacity
    case D.VRecord{n, h, t} L.Both{capacity, descendants}:
      capacity

def descendants_of_tree(v: D.Value, tree: Structural(v)) -> Descendants(v):
  match v tree:
    case D.VAbsent{} L.Both{capacity, descendants}:
      descendants
    case D.VBool{b} L.Both{capacity, descendants}:
      descendants
    case D.VInt{high, low} L.Both{capacity, descendants}:
      descendants
    case D.VText{s} L.Both{capacity, descendants}:
      descendants
    case D.VListEmpty{} L.Both{capacity, descendants}:
      descendants
    case D.VList{h, t} L.Both{capacity, descendants}:
      descendants
    case D.VRecordEmpty{} L.Both{capacity, descendants}:
      descendants
    case D.VRecord{n, h, t} L.Both{capacity, descendants}:
      descendants

law attach_values_and_list:
  for +xs: List<&2, S.ValueSegmented>
  {A.attach_list(S.values(xs), D.VListEmpty{}) == V.list(xs) : D.Value}
def attach_values_and_list(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{S.ValueSegmented{+v, bs}, +t}:
      Equal.cong(D.Value, D.Value, r => D.VList{v, r},
        A.attach_list(S.values(t), D.VListEmpty{}), V.list(t), attach_values_and_list(t))

law attach_fields_and_record:
  for +xs: List<&2, S.FieldSegmented>
  {A.attach_record(S.fields(xs), D.VRecordEmpty{}) == G.record(xs) : D.Value}
def attach_fields_and_record(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{S.FieldSegmented{+n, +v, nb, vb}, +t}:
      Equal.cong(D.Value, D.Value, r => D.VRecord{n, v, r},
        A.attach_record(S.fields(t), D.VRecordEmpty{}), G.record(t), attach_fields_and_record(t))

law induction_values_of_segments:
  for +xs: List<&2, S.ValueSegmented>
  for descendants: Descendants(V.list(xs))
  for canonical: S.ValuesCanonical(xs)
  V.InductionValues(xs)
def induction_values_of_segments(xs, descendants, canonical):
  match xs:
    case Nil{}:
      Unit{}
    case Con{S.ValueSegmented{+v, +bs}, +t}:
      match descendants:
        case L.Both{child, tail}:
          match canonical:
            case L.Both{encoded, rest}:
              F.combined_pair(V.InductionValues(xs), S.ValuesCanonical(t), S.ValuesCanonical(t),
                K.duplicate_values_canonical(t, rest),
                limit => recursion => L.Both{
                  capacity_of_tree(v, child)(bs, encoded),
                  L.Both{
                    S.sequence_of_values_canonical_requires_one_octet_by_value(t, limit),
                    induction_values_of_segments(t, descendants_of_tree(V.list(t), tail), recursion)}})

law induction_fields_of_segments:
  for +xs: List<&2, S.FieldSegmented>
  for descendants: Descendants(G.record(xs))
  for canonical: S.FieldsCanonical(xs)
  G.InductionFields(xs)
def induction_fields_of_segments(xs, descendants, canonical):
  match xs:
    case Nil{}:
      Unit{}
    case Con{S.FieldSegmented{+n, +v, +nb, +vb}, +t}:
      match descendants:
        case L.Both{child, tail}:
          match canonical:
            case L.Both{name_valid, L.Both{name_encoded, L.Both{value_encoded, rest}}}:
              +encoded = {value_encoded : {P.encode(v) == Some{vb} : Maybe<&2, List<&2, U32>>}}
              F.combined_pair(G.InductionFields(xs), S.FieldsCanonical(t), S.FieldsCanonical(t),
                K.duplicate_fields_canonical(t, rest),
                limit => recursion => L.Both{
                  N.name_canonical_complete(n, nb, name_valid, name_encoded),
                  L.Both{
                    capacity_of_tree(v, child)(vb, encoded),
                    L.Both{
                      T.all_value_canonical_requires_by_minus_one_octet(v, vb, encoded),
                      L.Both{
                        S.sequence_of_fields_canonical_requires_eleven_octets_by_field(t, limit),
                        induction_fields_of_segments(t, descendants_of_tree(G.record(t), tail), recursion)}}}})
