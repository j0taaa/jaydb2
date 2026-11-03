# The REAL closed delivery determines the measure; measure is not a hypothesis.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../contract/Protocol.bend as P
import ../src/Codec.bend as C
import ./CodecArities.bend as A
import ./CodecCounters.bend as N
import ./CodecLimitsSequences.bend as S
import ./CodecAssembly.bend as M
import ./Foundations.bend as F

# Total projection: injectivity of DecodedReady assumes no shape of v.
def value_ready(m: C.Machine) -> D.Value:
  match m:
    case C.DecodedReady{v}:
      v
    case _:
      D.VAbsent{}

law ready_and_injective:
  for -a: D.Value
  for -b: D.Value
  for equal: {C.DecodedReady{a} == C.DecodedReady{b} : C.Machine}
  {a == b : D.Value}
def ready_and_injective(a, b, equal):
  Equal.cong(C.Machine, D.Value, m => value_ready(m), C.DecodedReady{a}, C.DecodedReady{b}, equal)

def measure_list_open_closed(empty: Bool, +xs: List<&2, D.Value>, +q: B.Number64,
  -v: D.Value, zero: {C.zero64(q) == empty : Bool},
  delivery: {A.deliver_values(xs, C.open_variable(empty, C.CountsList{}, q, C.Root{})) == C.DecodedReady{v} : C.Machine}) ->
  {B.nat64(A.count_values(xs)) == Some{q} : Maybe<&2, B.Number64>}:
  match empty:
    case False{}:
      A.list_closed_reconstructs_to_count_canonical_original(xs, q, Nil{}, v, delivery)
    case True{}:
      match xs:
        case Nil{}:
          %Equal.sym(B.Number64, q, B.Number64{0, 0}, N.zero64_only_recognizes_zero(q, zero)) :
            {Some{B.Number64{0, 0}} == Some{_} : Maybe<&2, B.Number64>}
          {==}
        case Con{+h, +t}:
          L.ex_false({B.nat64(A.count_values(Con{h, t})) == Some{q} : Maybe<&2, B.Number64>},
            A.invalid_negative_and_ready(v,
              Equal.trans(C.Machine, C.Invalid{}, A.deliver_values(Con{h, t}, C.DecodedReady{D.VListEmpty{}}), C.DecodedReady{v},
                Equal.sym(C.Machine, A.deliver_values(Con{h, t}, C.DecodedReady{D.VListEmpty{}}), C.Invalid{},
                  A.ready_refusal_value_extra(h, t, D.VListEmpty{})), delivery)))

law opening_of_list_closed_extracts_measure:
  for +xs: List<&2, S.ValueSegmented>
  for +q: B.Number64
  for -v: D.Value
  for delivery: {A.deliver_values(S.values(xs), C.open_variable(C.zero64(q), C.CountsList{}, q, C.Root{})) == C.DecodedReady{v} : C.Machine}
  {B.nat64(S.count_values(xs)) == Some{q} : Maybe<&2, B.Number64>}
def opening_of_list_closed_extracts_measure(xs, q, v, delivery):
  %M.count_values_projected(xs) : {B.nat64(_) == Some{q} : Maybe<&2, B.Number64>}
  measure_list_open_closed(C.zero64(q), S.values(xs), q, v, {==}, delivery)

def measure_record_open_closed(empty: Bool, +xs: List<&2, D.Field>, +q: B.Number64,
  -v: D.Value, zero: {C.zero64(q) == empty : Bool},
  delivery: {A.deliver_fields(xs, C.open_variable(empty, C.CountsRecord{}, q, C.Root{})) == C.DecodedReady{v} : C.Machine}) ->
  {B.nat64(A.count_fields(xs)) == Some{q} : Maybe<&2, B.Number64>}:
  match empty:
    case False{}:
      A.record_closed_reconstructs_to_count_canonical_original(xs, q, "", Nil{}, v, delivery)
    case True{}:
      match xs:
        case Nil{}:
          %Equal.sym(B.Number64, q, B.Number64{0, 0}, N.zero64_only_recognizes_zero(q, zero)) :
            {Some{B.Number64{0, 0}} == Some{_} : Maybe<&2, B.Number64>}
          {==}
        case Con{+h, +t}:
          L.ex_false({B.nat64(A.count_fields(Con{h, t})) == Some{q} : Maybe<&2, B.Number64>},
            A.invalid_negative_and_ready(v,
              Equal.trans(C.Machine, C.Invalid{}, A.deliver_fields(Con{h, t}, C.DecodedReady{D.VRecordEmpty{}}), C.DecodedReady{v},
                Equal.sym(C.Machine, A.deliver_fields(Con{h, t}, C.DecodedReady{D.VRecordEmpty{}}), C.Invalid{},
                  A.ready_refusal_field_extra(h, t, D.VRecordEmpty{})), delivery)))

law opening_of_record_closed_extracts_measure:
  for +xs: List<&2, S.FieldSegmented>
  for +q: B.Number64
  for -v: D.Value
  for delivery: {A.deliver_fields(S.fields(xs), C.open_variable(C.zero64(q), C.CountsRecord{}, q, C.Root{})) == C.DecodedReady{v} : C.Machine}
  {B.nat64(S.count_fields(xs)) == Some{q} : Maybe<&2, B.Number64>}
def opening_of_record_closed_extracts_measure(xs, q, v, delivery):
  %M.count_fields_projected(xs) : {B.nat64(_) == Some{q} : Maybe<&2, B.Number64>}
  measure_record_open_closed(C.zero64(q), S.fields(xs), q, v, {==}, delivery)

# The extracted measure is reused when opening A to reconstruct v.
# Segment bytes enter only through the individual encoding of S.
law list_closed_has_measure_and_encoding_canonical:
  for +xs: List<&2, S.ValueSegmented>
  for +q: B.Number64
  for -v: D.Value
  for canonical: S.ValuesCanonical(xs)
  for +delivery: {A.deliver_values(S.values(xs), C.open_variable(C.zero64(q), C.CountsList{}, q, C.Root{})) == C.DecodedReady{v} : C.Machine}
  L.E<{B.nat64(S.count_values(xs)) == Some{q} : Maybe<&2, B.Number64>},
    P.Encoding(v, M.prefix(5, q, S.bytes_values(xs)))>
def list_closed_has_measure_and_encoding_canonical(xs, q, v, canonical, delivery):
  +measure = opening_of_list_closed_extracts_measure(xs, q, v, delivery)
  measure_projected = {(%Equal.sym(Nat, A.count_values(S.values(xs)), S.count_values(xs), M.count_values_projected(xs)) :
    {B.nat64(_) == Some{q} : Maybe<&2, B.Number64>}
    measure) : {B.nat64(A.count_values(S.values(xs))) == Some{q} : Maybe<&2, B.Number64>}}
  value = ready_and_injective(A.attach_list(S.values(xs), D.VListEmpty{}), v,
    Equal.trans(C.Machine,
      C.DecodedReady{A.attach_list(S.values(xs), D.VListEmpty{})},
      A.deliver_values(S.values(xs), C.open_variable(C.zero64(q), C.CountsList{}, q, C.Root{})), C.DecodedReady{v},
      Equal.sym(C.Machine,
        A.deliver_values(S.values(xs), C.open_variable(C.zero64(q), C.CountsList{}, q, C.Root{})),
        C.DecodedReady{A.attach_list(S.values(xs), D.VListEmpty{})},
        A.opening_of_list_counted_preserves_arity_and_order(S.values(xs), q, C.Root{}, measure_projected)), delivery))
  L.Both{measure,
    (%value : P.Encoding(_, M.prefix(5, q, S.bytes_values(xs)))
      M.list_segmented_has_encoding_canonical(xs, q, canonical, measure))}

# FieldsOrdered is Type: its conjunctions are reconstructed by induction.
law duplicate_fields_ordered:
  for +xs: List<&2, D.Field>
  for +previous: String
  for ordered: A.FieldsOrdered(xs, previous)
  L.E<A.FieldsOrdered(xs, previous), A.FieldsOrdered(xs, previous)>
def duplicate_fields_ordered(xs, previous, ordered):
  match xs:
    case Nil{}:
      L.Both{Unit{}, Unit{}}
    case Con{D.Field{+name, +v}, +t}:
      match ordered:
        case L.Both{+valid, L.Both{+order, tail}}:
          F.combined_pair(L.E<A.FieldsOrdered(xs, previous), A.FieldsOrdered(xs, previous)>,
            A.FieldsOrdered(t, name), A.FieldsOrdered(t, name), duplicate_fields_ordered(t, name, tail),
            left => right => L.Both{
              L.Both{valid, L.Both{order, left}},
              L.Both{valid, L.Both{order, right}}})

def conclude_record_closed(+xs: List<&2, S.FieldSegmented>, +q: B.Number64, -v: D.Value,
  canonical: S.FieldsCanonical(xs),
  order_reconstruction: A.FieldsOrdered(S.fields(xs), ""),
  order_encoding: A.FieldsOrdered(S.fields(xs), ""),
  delivery: {A.deliver_fields(S.fields(xs), C.open_variable(C.zero64(q), C.CountsRecord{}, q, C.Root{})) == C.DecodedReady{v} : C.Machine},
  +measure: {B.nat64(S.count_fields(xs)) == Some{q} : Maybe<&2, B.Number64>}) ->
  L.E<{B.nat64(S.count_fields(xs)) == Some{q} : Maybe<&2, B.Number64>},
    P.Encoding(v, M.prefix(6, q, S.bytes_fields(xs)))>:
  measure_projected = {(%Equal.sym(Nat, A.count_fields(S.fields(xs)), S.count_fields(xs), M.count_fields_projected(xs)) :
    {B.nat64(_) == Some{q} : Maybe<&2, B.Number64>}
    measure) : {B.nat64(A.count_fields(S.fields(xs))) == Some{q} : Maybe<&2, B.Number64>}}
  value = ready_and_injective(A.attach_record(S.fields(xs), D.VRecordEmpty{}), v,
    Equal.trans(C.Machine,
      C.DecodedReady{A.attach_record(S.fields(xs), D.VRecordEmpty{})},
      A.deliver_fields(S.fields(xs), C.open_variable(C.zero64(q), C.CountsRecord{}, q, C.Root{})), C.DecodedReady{v},
      Equal.sym(C.Machine,
        A.deliver_fields(S.fields(xs), C.open_variable(C.zero64(q), C.CountsRecord{}, q, C.Root{})),
        C.DecodedReady{A.attach_record(S.fields(xs), D.VRecordEmpty{})},
        A.opening_of_record_counted_preserves_arity_and_order(S.fields(xs), q, C.Root{}, order_reconstruction, measure_projected)), delivery))
  L.Both{measure,
    (%value : P.Encoding(_, M.prefix(6, q, S.bytes_fields(xs)))
      M.record_segmented_has_encoding_canonical(xs, q, canonical, order_encoding, measure))}

law record_closed_has_measure_and_encoding_canonical:
  for +xs: List<&2, S.FieldSegmented>
  for +q: B.Number64
  for -v: D.Value
  for canonical: S.FieldsCanonical(xs)
  for ordered: A.FieldsOrdered(S.fields(xs), "")
  for +delivery: {A.deliver_fields(S.fields(xs), C.open_variable(C.zero64(q), C.CountsRecord{}, q, C.Root{})) == C.DecodedReady{v} : C.Machine}
  L.E<{B.nat64(S.count_fields(xs)) == Some{q} : Maybe<&2, B.Number64>},
    P.Encoding(v, M.prefix(6, q, S.bytes_fields(xs)))>
def record_closed_has_measure_and_encoding_canonical(xs, q, v, canonical, ordered, delivery):
  +measure = opening_of_record_closed_extracts_measure(xs, q, v, delivery)
  F.combined_pair(L.E<{B.nat64(S.count_fields(xs)) == Some{q} : Maybe<&2, B.Number64>},
      P.Encoding(v, M.prefix(6, q, S.bytes_fields(xs)))>,
    A.FieldsOrdered(S.fields(xs), ""), A.FieldsOrdered(S.fields(xs), ""),
    duplicate_fields_ordered(S.fields(xs), "", ordered),
    order_reconstruction => order_encoding =>
      conclude_record_closed(xs, q, v, canonical, order_reconstruction, order_encoding, delivery, measure))
