# Exposes canonical names: exact tag4, measure and UTF-8.
import Base
import ../contract/Bytes.bend as B
import ../contract/Protocol.bend as P
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Foundations.bend as F
import ./CodecLimitsSequences.bend as S
import ./CodecAssembly.bend as M
import ./CodecAssemblyExposure.bend as X

type NameExposed<-name: String, -bs: List<&2, U32>> is Type:
  NameExposed{number: B.Number64,
    valid: {B.text_valid(name) == True{} : Bool},
    measure: {B.nat64(B.length(B.utf8(name))) == Some{number} : Maybe<&2, B.Number64>},
    bytes: {bs == M.prefix(4, number, B.utf8(name)) : List<&2, U32>}}

def name_combined_header(+name: String, +bs: List<&2, U32>,
  valid: {B.text_valid(name) == True{} : Bool},
  header: X.Header<4, B.length(B.utf8(name)), B.utf8(name), bs>) -> NameExposed<name, bs>:
  match header:
    case X.Header{number, measure, bytes}:
      NameExposed{number, valid, measure, bytes}

def expose_name_cases(valid: Bool, +name: String, +bs: List<&2, U32>,
  test: {B.text_valid(name) == valid : Bool},
  encoded: {P.text_cases(valid, B.utf8(name)) == Some{bs} : Maybe<&2, List<&2, U32>>}) -> NameExposed<name, bs>:
  match valid:
    case False{}:
      L.ex_false(NameExposed<name, bs>, F.none_negative_some(List<&2, U32>, bs, encoded))
    case True{}:
      name_combined_header(name, bs, test,
        X.field_variable_exposes_measure_and_bytes(4, B.length(B.utf8(name)), B.utf8(name), bs, encoded))

law name_canonical_exposes_tag_measure_and_utf8:
  for +name: String
  for +bs: List<&2, U32>
  for encoded: {P.text(name) == Some{bs} : Maybe<&2, List<&2, U32>>}
  NameExposed<name, bs>
def name_canonical_exposes_tag_measure_and_utf8(name, bs, encoded):
  expose_name_cases(B.text_valid(name), name, bs, {==}, encoded)

def NamesExposed(xs: List<&2, S.FieldSegmented>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{S.FieldSegmented{n, v, nb, vb}, t}:
      L.E<NameExposed<n, nb>, NamesExposed(t)>

law fields_canonical_expose_all_os_names:
  for +xs: List<&2, S.FieldSegmented>
  for canonical: S.FieldsCanonical(xs)
  L.E<S.FieldsCanonical(xs), NamesExposed(xs)>
def fields_canonical_expose_all_os_names(xs, canonical):
  match xs:
    case Nil{}:
      L.Both{Unit{}, Unit{}}
    case Con{S.FieldSegmented{+n, +v, +nb, +vb}, +t}:
      match canonical:
        case L.Both{name, L.Both{+text, L.Both{value, tail}}}:
          F.combined_pair(L.E<S.FieldsCanonical(xs), NamesExposed(xs)>, S.FieldsCanonical(t), NamesExposed(t),
            fields_canonical_expose_all_os_names(t, tail),
            fields => names => L.Both{
              L.Both{name, L.Both{text, L.Both{value, fields}}},
              L.Both{name_canonical_exposes_tag_measure_and_utf8(n, nb, text), names}})
