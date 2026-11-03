# Canonical bridge between original child segments and containers.
# Reuses CodecLimitsSequences segments in reading order.
# No hypothesis states the encoding of the entire container.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecArities.bend as A
import ./CodecCanonical.bend as K
import ./CodecLimitsSequences.bend as S

def prefix(tag: U32, q: B.Number64, bs: List<&2, U32>) -> List<&2, U32>:
  B.Number64{high, low} = q
  Con{tag, B.concatenate(B.be64(high, low), bs)}

law count_values_projected:
  for xs: List<&2, S.ValueSegmented>
  {A.count_values(S.values(xs)) == S.count_values(xs) : Nat}
def count_values_projected(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{S.ValueSegmented{v, bs}, t}:
      Equal.cong(Nat, Nat, n => 1n+n,
        A.count_values(S.values(t)), S.count_values(t), count_values_projected(t))

law count_fields_projected:
  for xs: List<&2, S.FieldSegmented>
  {A.count_fields(S.fields(xs)) == S.count_fields(xs) : Nat}
def count_fields_projected(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{S.FieldSegmented{n, v, nb, vb}, t}:
      Equal.cong(Nat, Nat, n => 1n+n,
        A.count_fields(S.fields(t)), S.count_fields(t), count_fields_projected(t))

def separate_encoding(valid: Bool, +result: Maybe<&2, List<&2, U32>>,
  +bs: List<&2, U32>, accepted: {P.encode_cases(valid, result) == Some{bs} : Maybe<&2, List<&2, U32>>}) ->
  L.E<{valid == True{} : Bool}, {result == Some{bs} : Maybe<&2, List<&2, U32>>}>:
  match valid:
    case False{}:
      L.ex_false(L.E<{False{} == True{} : Bool}, {result == Some{bs} : Maybe<&2, List<&2, U32>>}>,
        F.none_negative_some(List<&2, U32>, bs, accepted))
    case True{}:
      L.Both{{==}, accepted}

law child_canonical_exposes_validity_and_bytes:
  for +v: D.Value
  for +bs: List<&2, U32>
  for canonical: P.Encoding(v, bs)
  L.E<{D.value_valid(v) == True{} : Bool},
    {P.finalize(P.encode_partial(v)) == Some{bs} : Maybe<&2, List<&2, U32>>}>
def child_canonical_exposes_validity_and_bytes(v, bs, canonical):
  separate_encoding(D.value_valid(v), P.finalize(P.encode_partial(v)), bs, canonical)

law attach_list_has_form_of_list:
  for xs: List<&2, D.Value>
  {D.is_list(A.attach_list(xs, D.VListEmpty{})) == True{} : Bool}
def attach_list_has_form_of_list(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

law list_segmented_preserves_validity_and_partial:
  for +xs: List<&2, S.ValueSegmented>
  for canonical: S.ValuesCanonical(xs)
  L.E<{D.value_valid(A.attach_list(S.values(xs), D.VListEmpty{})) == True{} : Bool},
    {P.encode_partial(A.attach_list(S.values(xs), D.VListEmpty{})) ==
      P.ListFrame{S.count_values(xs), S.bytes_values(xs)} : P.Partial}>
def list_segmented_preserves_validity_and_partial(xs, canonical):
  match xs:
    case Nil{}:
      L.Both{{==}, {==}}
    case Con{S.ValueSegmented{+h, +bs}, +t}:
      match canonical:
        case L.Both{head, tail}:
          F.combined_pair(
            L.E<{D.value_valid(A.attach_list(S.values(xs), D.VListEmpty{})) == True{} : Bool},
              {P.encode_partial(A.attach_list(S.values(xs), D.VListEmpty{})) == P.ListFrame{S.count_values(xs), S.bytes_values(xs)} : P.Partial}>,
            {D.value_valid(h) == True{} : Bool},
            {P.finalize(P.encode_partial(h)) == Some{bs} : Maybe<&2, List<&2, U32>>},
            child_canonical_exposes_validity_and_bytes(h, bs, head),
            valid => bytes =>
              F.combined_pair(
                L.E<{D.value_valid(A.attach_list(S.values(xs), D.VListEmpty{})) == True{} : Bool},
                  {P.encode_partial(A.attach_list(S.values(xs), D.VListEmpty{})) == P.ListFrame{S.count_values(xs), S.bytes_values(xs)} : P.Partial}>,
                {D.value_valid(A.attach_list(S.values(t), D.VListEmpty{})) == True{} : Bool},
                {P.encode_partial(A.attach_list(S.values(t), D.VListEmpty{})) == P.ListFrame{S.count_values(t), S.bytes_values(t)} : P.Partial},
                list_segmented_preserves_validity_and_partial(t, tail),
                rest_valid => rest_bytes => L.Both{
                  F.and_boolean_intro(D.value_valid(h) && D.is_list(A.attach_list(S.values(t), D.VListEmpty{})),
                    D.value_valid(A.attach_list(S.values(t), D.VListEmpty{})),
                    F.and_boolean_intro(D.value_valid(h), D.is_list(A.attach_list(S.values(t), D.VListEmpty{})),
                      valid, attach_list_has_form_of_list(S.values(t))), rest_valid),
                  (%Equal.sym(Maybe<&2, List<&2, U32>>, P.finalize(P.encode_partial(h)), Some{bs}, bytes) :
                    {P.list_cases(_, P.encode_partial(A.attach_list(S.values(t), D.VListEmpty{}))) == P.ListFrame{S.count_values(xs), S.bytes_values(xs)} : P.Partial}
                    %Equal.sym(P.Partial, P.encode_partial(A.attach_list(S.values(t), D.VListEmpty{})), P.ListFrame{S.count_values(t), S.bytes_values(t)}, rest_bytes) :
                      {P.list_cases(Some{bs}, _) == P.ListFrame{S.count_values(xs), S.bytes_values(xs)} : P.Partial}
                    {==})}))

# The first equality is the strict boundary required by the parent record.
def RecordAssembled(+xs: List<&2, S.FieldSegmented>, previous: String) -> Type:
  L.E<{D.record_later(A.attach_record(S.fields(xs), D.VRecordEmpty{}), previous) == True{} : Bool},
    L.E<{D.value_valid(A.attach_record(S.fields(xs), D.VRecordEmpty{})) == True{} : Bool},
      {P.encode_partial(A.attach_record(S.fields(xs), D.VRecordEmpty{})) ==
        P.Record{S.count_fields(xs), S.bytes_fields(xs)} : P.Partial}>>

def join_head_record(+n: String, +v: D.Value, +nb: List<&2, U32>, +vb: List<&2, U32>,
  +t: List<&2, S.FieldSegmented>, +previous: String,
  name: {D.name_valid(n) == True{} : Bool}, order: {String.is_lt(previous, n) == True{} : Bool},
  name_bytes: {P.text(n) == Some{nb} : Maybe<&2, List<&2, U32>>},
  child: L.E<{D.value_valid(v) == True{} : Bool}, {P.finalize(P.encode_partial(v)) == Some{vb} : Maybe<&2, List<&2, U32>>}>,
  rest: RecordAssembled(t, n)) -> RecordAssembled(Con{S.FieldSegmented{n, v, nb, vb}, t}, previous):
  match child rest:
    case L.Both{valid, bytes} L.Both{boundary, L.Both{rest_valid, rest_bytes}}:
      +xs = {Con{S.FieldSegmented{n, v, nb, vb}, t} : List<&2, S.FieldSegmented>}
      L.Both{order, L.Both{
        F.and_boolean_intro(D.name_valid(n) && D.value_valid(v) && D.record_later(A.attach_record(S.fields(t), D.VRecordEmpty{}), n),
          D.value_valid(A.attach_record(S.fields(t), D.VRecordEmpty{})),
          F.and_boolean_intro(D.name_valid(n) && D.value_valid(v), D.record_later(A.attach_record(S.fields(t), D.VRecordEmpty{}), n),
            F.and_boolean_intro(D.name_valid(n), D.value_valid(v), name, valid), boundary), rest_valid),
        (%Equal.sym(Maybe<&2, List<&2, U32>>, P.text(n), Some{nb}, name_bytes) :
          {P.record_cases(_, P.finalize(P.encode_partial(v)), P.encode_partial(A.attach_record(S.fields(t), D.VRecordEmpty{}))) == P.Record{S.count_fields(xs), S.bytes_fields(xs)} : P.Partial}
          %Equal.sym(Maybe<&2, List<&2, U32>>, P.finalize(P.encode_partial(v)), Some{vb}, bytes) :
            {P.record_cases(Some{nb}, _, P.encode_partial(A.attach_record(S.fields(t), D.VRecordEmpty{}))) == P.Record{S.count_fields(xs), S.bytes_fields(xs)} : P.Partial}
          %Equal.sym(P.Partial, P.encode_partial(A.attach_record(S.fields(t), D.VRecordEmpty{})), P.Record{S.count_fields(t), S.bytes_fields(t)}, rest_bytes) :
            {P.record_cases(Some{nb}, Some{vb}, _) == P.Record{S.count_fields(xs), S.bytes_fields(xs)} : P.Partial}
          Equal.cong(List<&2, U32>, P.Partial, bs => P.Record{1n+S.count_fields(t), bs},
            B.concatenate(nb, B.concatenate(vb, S.bytes_fields(t))), B.concatenate(B.concatenate(nb, vb), S.bytes_fields(t)),
            Equal.sym(List<&2, U32>, B.concatenate(B.concatenate(nb, vb), S.bytes_fields(t)), B.concatenate(nb, B.concatenate(vb, S.bytes_fields(t))),
              K.concatenation_associative(nb, vb, S.bytes_fields(t)))))}}

law record_segmented_preserves_order_validity_and_partial:
  for +xs: List<&2, S.FieldSegmented>
  for +previous: String
  for canonical: S.FieldsCanonical(xs)
  for ordered: A.FieldsOrdered(S.fields(xs), previous)
  RecordAssembled(xs, previous)
def record_segmented_preserves_order_validity_and_partial(xs, previous, canonical, ordered):
  match xs:
    case Nil{}:
      L.Both{{==}, L.Both{{==}, {==}}}
    case Con{S.FieldSegmented{+n, +v, +nb, +vb}, +t}:
      match canonical ordered:
        case L.Both{name, L.Both{name_bytes, L.Both{value, tail}}} L.Both{name2, L.Both{order, order_tail}}:
          join_head_record(n, v, nb, vb, t, previous, name, order, name_bytes,
            child_canonical_exposes_validity_and_bytes(v, vb, value),
            record_segmented_preserves_order_validity_and_partial(t, n, tail, order_tail))

law field_variable_measured_has_prefix_exact:
  for +tag: U32
  for +n: Nat
  for +q: B.Number64
  for +bs: List<&2, U32>
  for measure: {B.nat64(n) == Some{q} : Maybe<&2, B.Number64>}
  {P.field_variable(tag, n, bs) == Some{prefix(tag, q, bs)} : Maybe<&2, List<&2, U32>>}
def field_variable_measured_has_prefix_exact(tag, n, q, bs, measure):
  match q:
    case B.Number64{+high, +low}:
      %Equal.sym(Maybe<&2, B.Number64>, B.nat64(n), Some{B.Number64{high, low}}, measure) :
        {P.prefix_size(tag, B.number64_bytes(_), bs) == Some{prefix(tag, B.Number64{high, low}, bs)} : Maybe<&2, List<&2, U32>>}
      {==}

def finalize_list_segmented(+xs: List<&2, S.ValueSegmented>, +q: B.Number64,
  measure: {B.nat64(S.count_values(xs)) == Some{q} : Maybe<&2, B.Number64>},
  assembled: L.E<{D.value_valid(A.attach_list(S.values(xs), D.VListEmpty{})) == True{} : Bool}, {P.encode_partial(A.attach_list(S.values(xs), D.VListEmpty{})) == P.ListFrame{S.count_values(xs), S.bytes_values(xs)} : P.Partial}>) -> P.Encoding(A.attach_list(S.values(xs), D.VListEmpty{}), prefix(5, q, S.bytes_values(xs))):
  match assembled:
    case L.Both{is_valid, partial}:
      Equal.trans(Maybe<&2, List<&2, U32>>, P.encode(A.attach_list(S.values(xs), D.VListEmpty{})),
        P.finalize(P.encode_partial(A.attach_list(S.values(xs), D.VListEmpty{}))), Some{prefix(5, q, S.bytes_values(xs))},
        K.value_valid_releases_encoding(A.attach_list(S.values(xs), D.VListEmpty{}), is_valid),
        (%Equal.sym(P.Partial, P.encode_partial(A.attach_list(S.values(xs), D.VListEmpty{})), P.ListFrame{S.count_values(xs), S.bytes_values(xs)}, partial) :
          {P.finalize(_) == Some{prefix(5, q, S.bytes_values(xs))} : Maybe<&2, List<&2, U32>>}
          field_variable_measured_has_prefix_exact(5, S.count_values(xs), q, S.bytes_values(xs), measure)))

law list_segmented_has_encoding_canonical:
  for +xs: List<&2, S.ValueSegmented>
  for +q: B.Number64
  for canonical: S.ValuesCanonical(xs)
  for measure: {B.nat64(S.count_values(xs)) == Some{q} : Maybe<&2, B.Number64>}
  P.Encoding(A.attach_list(S.values(xs), D.VListEmpty{}), prefix(5, q, S.bytes_values(xs)))
def list_segmented_has_encoding_canonical(xs, q, canonical, measure):
  finalize_list_segmented(xs, q, measure, list_segmented_preserves_validity_and_partial(xs, canonical))

def finalize_record_segmented(+xs: List<&2, S.FieldSegmented>, +q: B.Number64,
  measure: {B.nat64(S.count_fields(xs)) == Some{q} : Maybe<&2, B.Number64>},
  assembled: RecordAssembled(xs, "")) -> P.Encoding(A.attach_record(S.fields(xs), D.VRecordEmpty{}), prefix(6, q, S.bytes_fields(xs))):
  match assembled:
    case L.Both{boundary, L.Both{is_valid, partial}}:
      Equal.trans(Maybe<&2, List<&2, U32>>, P.encode(A.attach_record(S.fields(xs), D.VRecordEmpty{})),
        P.finalize(P.encode_partial(A.attach_record(S.fields(xs), D.VRecordEmpty{}))), Some{prefix(6, q, S.bytes_fields(xs))},
        K.value_valid_releases_encoding(A.attach_record(S.fields(xs), D.VRecordEmpty{}), is_valid),
        (%Equal.sym(P.Partial, P.encode_partial(A.attach_record(S.fields(xs), D.VRecordEmpty{})), P.Record{S.count_fields(xs), S.bytes_fields(xs)}, partial) :
          {P.finalize(_) == Some{prefix(6, q, S.bytes_fields(xs))} : Maybe<&2, List<&2, U32>>}
          field_variable_measured_has_prefix_exact(6, S.count_fields(xs), q, S.bytes_fields(xs), measure)))

law record_segmented_has_encoding_canonical:
  for +xs: List<&2, S.FieldSegmented>
  for +q: B.Number64
  for canonical: S.FieldsCanonical(xs)
  for ordered: A.FieldsOrdered(S.fields(xs), "")
  for measure: {B.nat64(S.count_fields(xs)) == Some{q} : Maybe<&2, B.Number64>}
  P.Encoding(A.attach_record(S.fields(xs), D.VRecordEmpty{}), prefix(6, q, S.bytes_fields(xs)))
def record_segmented_has_encoding_canonical(xs, q, canonical, ordered, measure):
  finalize_record_segmented(xs, q, measure, record_segmented_preserves_order_validity_and_partial(xs, "", canonical, ordered))

# Every name preserves tag4, u64 measure and original UTF-8 bytes.
law name_measured_has_encoding_textual_exact:
  for +name: String
  for +utf8: List<&2, U32>
  for +q: B.Number64
  for valid: {B.text_valid(name) == True{} : Bool}
  for bytes: {B.utf8(name) == utf8 : List<&2, U32>}
  for measure: {B.nat64(B.length(utf8)) == Some{q} : Maybe<&2, B.Number64>}
  {P.text(name) == Some{prefix(4, q, utf8)} : Maybe<&2, List<&2, U32>>}
def name_measured_has_encoding_textual_exact(name, utf8, q, valid, bytes, measure):
  %Equal.sym(Bool, B.text_valid(name), True{}, valid) :
    {P.text_cases(_, B.utf8(name)) == Some{prefix(4, q, utf8)} : Maybe<&2, List<&2, U32>>}
  %Equal.sym(List<&2, U32>, B.utf8(name), utf8, bytes) :
    {P.field_variable(4, B.length(_), _) == Some{prefix(4, q, utf8)} : Maybe<&2, List<&2, U32>>}
  field_variable_measured_has_prefix_exact(4, B.length(utf8), q, utf8, measure)
