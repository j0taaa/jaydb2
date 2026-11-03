# General record induction step: segmented names and values execute
# in the actual machine, preserving order, count and all ancestors.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecTrace.bend as R
import ./CodecComposition.bend as X
import ./CodecSequences.bend as V
import ./CodecFields.bend as G
import ./CodecCounters.bend as N
import ./CodecWordsBE64.bend as H
import ./CodecTexts.bend as T
import ./CodecMinimum.bend as M
import ./CodecMinimumStack.bend as A
import ./CodecCanonical.bend as K
import ./CodecLimitsSequences.bend as S
import ./CodecArities.bend as E

def record(xs: List<&2, S.FieldSegmented>) -> D.Value:
  match xs:
    case Nil{}:
      D.VRecordEmpty{}
    case Con{S.FieldSegmented{n, v, nb, vb}, t}:
      D.VRecord{n, v, record(t)}

def InductionFields(xs: List<&2, S.FieldSegmented>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{S.FieldSegmented{n, v, nb, vb}, t}:
      L.E<G.NameComplete(n, nb), L.E<V.CompleteLocal(v, vb),
        L.E<{Nat.is_le(1n, B.length(vb)) == True{} : Bool},
          L.E<{Nat.is_le(Nat.mul(11n, S.count_fields(t)), B.length(S.bytes_fields(t))) == True{} : Bool}, InductionFields(t)>>>>

def NotEmpty(xs: List<&2, S.FieldSegmented>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case Con{h, t}:
      Unit

def minimum_frame_field(+u: Bool, +q: B.Number64, -name: String, -xs: List<&2, D.Field>, +parent: C.Stack,
  +n: Nat, +r: Nat,
  measured: {B.nat64(n) == Some{q} : Maybe<&2, B.Number64>},
  minimum: {C.minimum_stack(parent) == B.nat64(r) : Maybe<&2, B.Number64>}) ->
  {C.minimum_stack(C.Field{u, q, name, xs, parent}) == B.nat64(Nat.add(Nat.mul(11n, n), r)) : Maybe<&2, B.Number64>}:
  %Equal.sym(Maybe<&2, B.Number64>, C.minimum_stack(parent), B.nat64(r), minimum) :
    {C.sum_pending(q, 11n, _) == B.nat64(Nat.add(Nat.mul(11n, n), r)) : Maybe<&2, B.Number64>}
  A.sum_pending_nat64_exact(n, q, 11n, r, measured)

def compose_tail_record(+t: List<&2, S.FieldSegmented>, +q: B.Number64, +name: String, +v: D.Value, +bs: List<&2, U32>,
  +previous: String, +inverted: List<&2, D.Field>, +parent: C.Stack, +suffix: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64,
  +counted: {B.nat64(1n+S.count_fields(t)) == Some{q} : Maybe<&2, B.Number64>},
  +input: {B.nat64(B.length(B.concatenate(bs, B.concatenate(S.bytes_fields(t), suffix)))) == Some{body} : Maybe<&2, B.Number64>},
  fits: {C.less_equal64(body, ceiling) == True{} : Bool},
  step: {R.execute(bs, R.Frame{body, ceiling, C.TagName{C.Name{C.one64(q), C.decrease64(q), previous, inverted, parent}}}) ==
    X.later(bs, body, ceiling, C.emit(C.Field{C.one64(q), C.decrease64(q), name, inverted, parent}, v)) : R.Frame},
  resume: NotEmpty(t) ->
    {B.nat64(B.length(B.concatenate(S.bytes_fields(t), suffix))) == Some{H.decrease(B.length(bs), body)} : Maybe<&2, B.Number64>} ->
    {C.less_equal64(H.decrease(B.length(bs), body), H.decrease(B.length(bs), ceiling)) == True{} : Bool} ->
    {R.execute(S.bytes_fields(t), R.Frame{H.decrease(B.length(bs), body), H.decrease(B.length(bs), ceiling),
        C.TagName{C.Name{C.one64(C.decrease64(q)), C.decrease64(C.decrease64(q)), name, Con{D.Field{name, v}, inverted}, parent}}}) ==
      X.later(S.bytes_fields(t), H.decrease(B.length(bs), body), H.decrease(B.length(bs), ceiling), C.emit(parent, C.assemble_record(Con{D.Field{name, v}, inverted}, record(t)))) : R.Frame}) ->
  {R.execute(B.concatenate(bs, S.bytes_fields(t)), R.Frame{body, ceiling, C.TagName{C.Name{C.one64(q), C.decrease64(q), previous, inverted, parent}}}) ==
    X.later(B.concatenate(bs, S.bytes_fields(t)), body, ceiling, C.emit(parent, C.assemble_record(inverted, D.VRecord{name, v, record(t)}))) : R.Frame}:
  match t:
    case Nil{}:
      +last = N.one64_reflects_count_natural(1n, q, counted)
      +emission = {(%Equal.sym(Bool, C.one64(q), True{}, last) :
        {C.emit(C.Field{_, C.decrease64(q), name, inverted, parent}, v) == C.emit(parent, C.assemble_record(inverted, D.VRecord{name, v, D.VRecordEmpty{}})) : C.Machine}
        {==}) : {C.emit(C.Field{C.one64(q), C.decrease64(q), name, inverted, parent}, v) == C.emit(parent, C.assemble_record(inverted, D.VRecord{name, v, D.VRecordEmpty{}})) : C.Machine}}
      V.compose_two_segments_real(bs, Nil{}, body, ceiling, C.TagName{C.Name{C.one64(q), C.decrease64(q), previous, inverted, parent}},
        C.emit(C.Field{C.one64(q), C.decrease64(q), name, inverted, parent}, v), C.emit(parent, C.assemble_record(inverted, D.VRecord{name, v, D.VRecordEmpty{}})), step,
        Equal.cong(C.Machine, R.Frame, m => X.later(bs, body, ceiling, m),
          C.emit(C.Field{C.one64(q), C.decrease64(q), name, inverted, parent}, v), C.emit(parent, C.assemble_record(inverted, D.VRecord{name, v, D.VRecordEmpty{}})), emission))
    case Con{+h, +rest}:
      +last = N.one64_reflects_count_natural(2n+S.count_fields(rest), q, counted)
      +emission = {(%Equal.sym(Bool, C.one64(q), False{}, last) :
        {C.emit(C.Field{_, C.decrease64(q), name, inverted, parent}, v) == C.TagName{C.Name{C.one64(C.decrease64(q)), C.decrease64(C.decrease64(q)), name, Con{D.Field{name, v}, inverted}, parent}} : C.Machine}
        {==}) : {C.emit(C.Field{C.one64(q), C.decrease64(q), name, inverted, parent}, v) == C.TagName{C.Name{C.one64(C.decrease64(q)), C.decrease64(C.decrease64(q)), name, Con{D.Field{name, v}, inverted}, parent}} : C.Machine}}
      V.compose_two_segments_real(bs, S.bytes_fields(Con{h, rest}), body, ceiling, C.TagName{C.Name{C.one64(q), C.decrease64(q), previous, inverted, parent}},
        C.TagName{C.Name{C.one64(C.decrease64(q)), C.decrease64(C.decrease64(q)), name, Con{D.Field{name, v}, inverted}, parent}}, C.emit(parent, C.assemble_record(Con{D.Field{name, v}, inverted}, record(Con{h, rest}))),
        Equal.trans(R.Frame,
          R.execute(bs, R.Frame{body, ceiling, C.TagName{C.Name{C.one64(q), C.decrease64(q), previous, inverted, parent}}}),
          X.later(bs, body, ceiling, C.emit(C.Field{C.one64(q), C.decrease64(q), name, inverted, parent}, v)),
          X.later(bs, body, ceiling, C.TagName{C.Name{C.one64(C.decrease64(q)), C.decrease64(C.decrease64(q)), name, Con{D.Field{name, v}, inverted}, parent}}), step,
          Equal.cong(C.Machine, R.Frame, m => X.later(bs, body, ceiling, m),
            C.emit(C.Field{C.one64(q), C.decrease64(q), name, inverted, parent}, v), C.TagName{C.Name{C.one64(C.decrease64(q)), C.decrease64(C.decrease64(q)), name, Con{D.Field{name, v}, inverted}, parent}}, emission)),
        resume(Unit{}, V.measure_after_segment(bs, B.concatenate(S.bytes_fields(Con{h, rest}), suffix), body, input), M.decrease_repeated_preserves_order_of_limits(B.length(bs), body, ceiling, fits)))

law record_of_segments_composes_execution_real_of_fields:
  for +xs: List<&2, S.FieldSegmented>
  for +q: B.Number64
  for +previous: String
  for +inverted: List<&2, D.Field>
  for +parent: C.Stack
  for +suffix: List<&2, U32>
  for +r: Nat
  for +body: B.Number64
  for +ceiling: B.Number64
  for positive: NotEmpty(xs)
  for children: InductionFields(xs)
  for ordered: E.FieldsOrdered(S.fields(xs), previous)
  for +counted: {B.nat64(S.count_fields(xs)) == Some{q} : Maybe<&2, B.Number64>}
  for +minimum: {C.minimum_stack(parent) == B.nat64(r) : Maybe<&2, B.Number64>}
  for +reservation: {Nat.is_le(r, B.length(suffix)) == True{} : Bool}
  for +measured: {B.nat64(B.length(B.concatenate(S.bytes_fields(xs), suffix))) == Some{body} : Maybe<&2, B.Number64>}
  for +fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  {R.execute(S.bytes_fields(xs), R.Frame{body, ceiling, C.TagName{C.Name{C.one64(q), C.decrease64(q), previous, inverted, parent}}}) ==
    X.later(S.bytes_fields(xs), body, ceiling, C.emit(parent, C.assemble_record(inverted, record(xs)))) : R.Frame}
def record_of_segments_composes_execution_real_of_fields(xs, q, previous, inverted, parent, suffix, r, body, ceiling, positive, children, ordered, counted, minimum, reservation, measured, fits):
  match xs:
    case Nil{}:
      L.ex_false({R.Frame{body, ceiling, C.TagName{C.Name{C.one64(q), C.decrease64(q), previous, inverted, parent}}} == R.Frame{body, ceiling, C.emit(parent, C.assemble_record(inverted, D.VRecordEmpty{}))} : R.Frame}, positive)
    case Con{S.FieldSegmented{+name, +v, +nb, +vb}, +t}:
      match children ordered:
        case L.Both{name_complete, L.Both{value_complete, L.Both{positive_v, L.Both{+size, tail}}}} L.Both{valid, L.Both{order, ordered_tail}}:
          +bs = B.concatenate(nb, vb)
          +remaining = N.measure_decremented(S.count_fields(t), q, N.nat64_successor_has_predecessor_exact(S.count_fields(t), q, counted))
          +reservation_child = S.concatenate_segments_preserves_sum_of_limits(S.bytes_fields(t), suffix, Nat.mul(11n, S.count_fields(t)), r, size, reservation)
          +input_child = {(%K.concatenation_associative(bs, S.bytes_fields(t), suffix) :
              {B.nat64(B.length(_)) == Some{body} : Maybe<&2, B.Number64>}
              measured) : {B.nat64(B.length(B.concatenate(bs, B.concatenate(S.bytes_fields(t), suffix)))) == Some{body} : Maybe<&2, B.Number64>}}
          minimum_field = minimum_frame_field(C.one64(q), C.decrease64(q), name, inverted, parent, S.count_fields(t), r, remaining, minimum)
          step = G.name_and_value_segmented_compose_field_real(name, v, nb, vb, C.one64(q), C.decrease64(q), previous, inverted, parent,
            B.concatenate(S.bytes_fields(t), suffix), Nat.add(Nat.mul(11n, S.count_fields(t)), r), body, ceiling,
            name_complete, value_complete, valid, order, positive_v, minimum_field, reservation_child, input_child, fits)
          compose_tail_record(t, q, name, v, bs, previous, inverted, parent, suffix, body, ceiling, counted, input_child, fits, step,
            positive => measure_tail => fits_tail =>
              record_of_segments_composes_execution_real_of_fields(t, C.decrease64(q), name, Con{D.Field{name, v}, inverted}, parent, suffix, r,
                H.decrease(B.length(bs), body), H.decrease(B.length(bs), ceiling), positive, tail, ordered_tail, remaining, minimum, reservation, measure_tail, fits_tail))

law record_open_composes_all_os_segments:
  for +xs: List<&2, S.FieldSegmented>
  for +q: B.Number64
  for +parent: C.Stack
  for +suffix: List<&2, U32>
  for +r: Nat
  for +body: B.Number64
  for +ceiling: B.Number64
  for children: InductionFields(xs)
  for ordered: E.FieldsOrdered(S.fields(xs), "")
  for +counted: {B.nat64(S.count_fields(xs)) == Some{q} : Maybe<&2, B.Number64>}
  for +minimum: {C.minimum_stack(parent) == B.nat64(r) : Maybe<&2, B.Number64>}
  for +reservation: {Nat.is_le(r, B.length(suffix)) == True{} : Bool}
  for +measured: {B.nat64(B.length(B.concatenate(S.bytes_fields(xs), suffix))) == Some{body} : Maybe<&2, B.Number64>}
  for +fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  {R.execute(S.bytes_fields(xs), R.Frame{body, ceiling, C.open_variable(C.zero64(q), C.CountsRecord{}, q, parent)}) ==
    X.later(S.bytes_fields(xs), body, ceiling, C.emit(parent, record(xs))) : R.Frame}
def record_open_composes_all_os_segments(xs, q, parent, suffix, r, body, ceiling, children, ordered, counted, minimum, reservation, measured, fits):
  match xs:
    case Nil{}:
      %F.some_injective(B.Number64, B.Number64{0, 0}, q, counted) :
        {R.Frame{body, ceiling, C.open_variable(C.zero64(_), C.CountsRecord{}, q, parent)} == X.later(Nil{}, body, ceiling, C.emit(parent, D.VRecordEmpty{})) : R.Frame}
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, C.zero64(q), False{}, N.zero64_reflects_count_natural(S.count_fields(Con{h, t}), q, counted)) :
        {R.execute(S.bytes_fields(Con{h, t}), R.Frame{body, ceiling, C.open_variable(_, C.CountsRecord{}, q, parent)}) == X.later(S.bytes_fields(Con{h, t}), body, ceiling, C.emit(parent, record(Con{h, t}))) : R.Frame}
      record_of_segments_composes_execution_real_of_fields(Con{h, t}, q, "", Nil{}, parent, suffix, r, body, ceiling, Unit{}, children, ordered, counted, minimum, reservation, measured, fits)

def bytes_record(high: U32, low: U32, xs: List<&2, S.FieldSegmented>) -> List<&2, U32>:
  Con{6, B.concatenate(B.be64(high, low), S.bytes_fields(xs))}

# This is the record constructor's INDUCTION STEP. All child values are
# arbitrary; the hypothesis applies only to each smaller subvalue.
# The sole limit is the actual body/ceiling, without depth or arity quotas.
law constructor_record_composes_completeness_local:
  for +xs: List<&2, S.FieldSegmented>
  for +high: U32
  for +low: U32
  for +body: B.Number64
  for +ceiling: B.Number64
  for +parent: C.Stack
  for +suffix: List<&2, U32>
  for +r: Nat
  for children: InductionFields(xs)
  for ordered: E.FieldsOrdered(S.fields(xs), "")
  for canonical: S.FieldsCanonical(xs)
  for +counted: {B.nat64(S.count_fields(xs)) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
  for +minimum: {C.minimum_stack(parent) == B.nat64(r) : Maybe<&2, B.Number64>}
  for +reservation: {Nat.is_le(r, B.length(suffix)) == True{} : Bool}
  for +measured: {B.nat64(B.length(B.concatenate(bytes_record(high, low, xs), suffix))) == Some{body} : Maybe<&2, B.Number64>}
  for +fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  {R.execute(bytes_record(high, low, xs), R.Frame{body, ceiling, C.Tag{parent}}) ==
    X.later(bytes_record(high, low, xs), body, ceiling, C.emit(parent, record(xs))) : R.Frame}
def constructor_record_composes_completeness_local(xs, high, low, body, ceiling, parent, suffix, r, children, ordered, canonical, counted, minimum, reservation, measured, fits):
  +measure_tail = T.remove_prefix_of_measure(9n, B.length(B.concatenate(S.bytes_fields(xs), suffix)), body, measured)
  +limit_minimum = S.concatenate_segments_preserves_sum_of_limits(S.bytes_fields(xs), suffix, Nat.mul(11n, S.count_fields(xs)), r,
    S.sequence_of_fields_canonical_requires_eleven_octets_by_field(xs, canonical), reservation)
  +opening = X.header_variable_combined_body_and_ceiling_u64_arbitrary(C.CountsRecord{}, S.count_fields(xs), r, B.length(B.concatenate(S.bytes_fields(xs), suffix)), high, low, parent, body, ceiling, Unit{}, counted, minimum, measure_tail, limit_minimum, fits)
  V.compose_two_segments_real(Con{6, B.be64(high, low)}, S.bytes_fields(xs), body, ceiling, C.Tag{parent},
    C.open_variable(C.zero64(B.Number64{high, low}), C.CountsRecord{}, B.Number64{high, low}, parent), C.emit(parent, record(xs)), opening,
    record_open_composes_all_os_segments(xs, B.Number64{high, low}, parent, suffix, r, H.decrease(9n, body), H.decrease(9n, ceiling), children, ordered, counted, minimum, reservation, measure_tail,
      M.decrease_repeated_preserves_order_of_limits(9n, body, ceiling, fits)))
