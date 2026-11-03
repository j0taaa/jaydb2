# Strict order also follows from ACTUAL delivery: a rejected name
# invalidates the machine, and no field suffix recovers it.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecArities.bend as A
import ./CodecLimitsSequences.bend as S
import ./CodecAssembly.bend as M
import ./CodecAssemblyClosed.bend as E

def fields_after_ready_has_order(xs: List<&2, D.Field>, +ready: D.Value, -v: D.Value, +previous: String,
  delivery: {A.deliver_fields(xs, C.DecodedReady{ready}) == C.DecodedReady{v} : C.Machine}) -> A.FieldsOrdered(xs, previous):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+h, +t}:
      L.ex_false(A.FieldsOrdered(Con{h, t}, previous), A.invalid_negative_and_ready(v,
        Equal.trans(C.Machine, C.Invalid{}, A.deliver_fields(Con{h, t}, C.DecodedReady{ready}), C.DecodedReady{v},
          Equal.sym(C.Machine, A.deliver_fields(Con{h, t}, C.DecodedReady{ready}), C.Invalid{},
            A.ready_refusal_field_extra(h, t, ready)), delivery)))

def check_name_and_order_closed(ok: Bool, last: Bool, +q: B.Number64,
  +previous: String, +name: String, +value: D.Value, +t: List<&2, D.Field>,
  +inverted: List<&2, D.Field>, -v: D.Value,
  +test: {D.name_valid(name) && String.is_lt(previous, name) == ok : Bool},
  delivery: {A.deliver_fields(t, A.next_value(C.name_checked(ok, last, C.decrease64(q), name, inverted, C.Root{}), value)) == C.DecodedReady{v} : C.Machine},
  resume: {A.deliver_fields(t, C.TagName{C.Name{C.one64(C.decrease64(q)), C.decrease64(C.decrease64(q)), name, Con{D.Field{name, value}, inverted}, C.Root{}}}) == C.DecodedReady{v} : C.Machine} ->
    A.FieldsOrdered(t, name)) -> A.FieldsOrdered(Con{D.Field{name, value}, t}, previous):
  match ok last:
    case False{} _:
      L.ex_false(A.FieldsOrdered(Con{D.Field{name, value}, t}, previous), A.invalid_negative_and_ready(v,
        Equal.trans(C.Machine, C.Invalid{}, A.deliver_fields(t, C.Invalid{}), C.DecodedReady{v},
          Equal.sym(C.Machine, A.deliver_fields(t, C.Invalid{}), C.Invalid{}, A.fields_negative_recover_machine_invalid(t)), delivery)))
    case True{} False{}:
      L.Both{F.and_boolean_left(D.name_valid(name), String.is_lt(previous, name), test),
        L.Both{F.and_boolean_right(D.name_valid(name), String.is_lt(previous, name), test), resume(delivery)}}
    case True{} True{}:
      L.Both{F.and_boolean_left(D.name_valid(name), String.is_lt(previous, name), test),
        L.Both{F.and_boolean_right(D.name_valid(name), String.is_lt(previous, name), test),
          fields_after_ready_has_order(t, C.assemble_record(Con{D.Field{name, value}, inverted}, D.VRecordEmpty{}), v, name, delivery)}}

law record_closed_checked_all_os_names_and_order:
  for +xs: List<&2, D.Field>
  for +q: B.Number64
  for +previous: String
  for +inverted: List<&2, D.Field>
  for -v: D.Value
  for delivery: {A.deliver_fields(xs, C.TagName{C.Name{C.one64(q), C.decrease64(q), previous, inverted, C.Root{}}}) == C.DecodedReady{v} : C.Machine}
  A.FieldsOrdered(xs, previous)
def record_closed_checked_all_os_names_and_order(xs, q, previous, inverted, v, delivery):
  match xs:
    case Nil{}:
      Unit{}
    case Con{D.Field{+name, +value}, +t}:
      check_name_and_order_closed(D.name_valid(name) && String.is_lt(previous, name), C.one64(q), q, previous, name, value, t, inverted, v,
        {==}, delivery, e => record_closed_checked_all_os_names_and_order(t, C.decrease64(q), name, Con{D.Field{name, value}, inverted}, v, e))

def order_opening_closed(empty: Bool, +xs: List<&2, D.Field>, +q: B.Number64, -v: D.Value,
  delivery: {A.deliver_fields(xs, C.open_variable(empty, C.CountsRecord{}, q, C.Root{})) == C.DecodedReady{v} : C.Machine}) -> A.FieldsOrdered(xs, ""):
  match empty:
    case True{}:
      fields_after_ready_has_order(xs, D.VRecordEmpty{}, v, "", delivery)
    case False{}:
      record_closed_checked_all_os_names_and_order(xs, q, "", Nil{}, v, delivery)

law opening_of_record_closed_extracts_order:
  for +xs: List<&2, S.FieldSegmented>
  for +q: B.Number64
  for -v: D.Value
  for delivery: {A.deliver_fields(S.fields(xs), C.open_variable(C.zero64(q), C.CountsRecord{}, q, C.Root{})) == C.DecodedReady{v} : C.Machine}
  A.FieldsOrdered(S.fields(xs), "")
def opening_of_record_closed_extracts_order(xs, q, v, delivery):
  order_opening_closed(C.zero64(q), S.fields(xs), q, v, delivery)

def combine_closing_combined_order(+xs: List<&2, S.FieldSegmented>, +q: B.Number64, -v: D.Value,
  ordered: A.FieldsOrdered(S.fields(xs), ""),
  closed: L.E<{B.nat64(S.count_fields(xs)) == Some{q} : Maybe<&2, B.Number64>}, P.Encoding(v, M.prefix(6, q, S.bytes_fields(xs)))>) ->
  L.E<{B.nat64(S.count_fields(xs)) == Some{q} : Maybe<&2, B.Number64>},
    L.E<A.FieldsOrdered(S.fields(xs), ""), P.Encoding(v, M.prefix(6, q, S.bytes_fields(xs)))>>:
  match closed:
    case L.Both{measure, bytes}:
      L.Both{measure, L.Both{ordered, bytes}}

# Only individual segments and closed delivery are premises;
# count, strict order and record encoding are conclusions.
law record_closed_extracts_measure_order_and_encoding_canonical:
  for +xs: List<&2, S.FieldSegmented>
  for +q: B.Number64
  for -v: D.Value
  for canonical: S.FieldsCanonical(xs)
  for +delivery: {A.deliver_fields(S.fields(xs), C.open_variable(C.zero64(q), C.CountsRecord{}, q, C.Root{})) == C.DecodedReady{v} : C.Machine}
  L.E<{B.nat64(S.count_fields(xs)) == Some{q} : Maybe<&2, B.Number64>},
    L.E<A.FieldsOrdered(S.fields(xs), ""), P.Encoding(v, M.prefix(6, q, S.bytes_fields(xs)))>>
def record_closed_extracts_measure_order_and_encoding_canonical(xs, q, v, canonical, delivery):
  F.combined_pair(
    L.E<{B.nat64(S.count_fields(xs)) == Some{q} : Maybe<&2, B.Number64>},
      L.E<A.FieldsOrdered(S.fields(xs), ""), P.Encoding(v, M.prefix(6, q, S.bytes_fields(xs)))>>,
    A.FieldsOrdered(S.fields(xs), ""), A.FieldsOrdered(S.fields(xs), ""),
    E.duplicate_fields_ordered(S.fields(xs), "", opening_of_record_closed_extracts_order(xs, q, v, delivery)),
    order => order2 => combine_closing_combined_order(xs, q, v, order,
      E.record_closed_has_measure_and_encoding_canonical(xs, q, v, canonical, order2, delivery)))
