# Actual composition of field name and value with an ancestor stack.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecTrace.bend as R
import ./CodecComposition.bend as X
import ./CodecSequences.bend as S
import ./CodecWordsBE64.bend as H
import ./CodecMinimum.bend as M
import ./CodecSums.bend as A
import ./CodecLimitsSequences.bend as K
import ./CodecCanonical.bend as J

def NameComplete(name: String, +bs: List<&2, U32>) -> Type:
  @body: B.Number64 -> @ceiling: B.Number64 -> @stack: C.Stack ->
  @suffix: List<&2, U32> -> @r: Nat ->
  {C.minimum_stack(stack) == B.nat64(r) : Maybe<&2, B.Number64>} ->
  {Nat.is_le(r, B.length(suffix)) == True{} : Bool} ->
  {B.nat64(B.length(B.concatenate(bs, suffix))) == Some{body} : Maybe<&2, B.Number64>} ->
  {C.less_equal64(body, ceiling) == True{} : Bool} ->
  {R.execute(bs, R.Frame{body, ceiling, C.TagName{stack}}) == X.later(bs, body, ceiling, C.emit_name(stack, name)) : R.Frame}

law minimum_name_includes_exactly_value_current:
  for +u: Bool
  for +q: B.Number64
  for +previous: String
  for +name: String
  for +xs: List<&2, D.Field>
  for +parent: C.Stack
  for +r: Nat
  for minimum: {C.minimum_stack(C.Field{u, q, name, xs, parent}) == B.nat64(r) : Maybe<&2, B.Number64>}
  {C.minimum_stack(C.Name{u, q, previous, xs, parent}) == B.nat64(1n+r) : Maybe<&2, B.Number64>}
def minimum_name_includes_exactly_value_current(u, q, previous, name, xs, parent, r, minimum):
  %Equal.sym(Maybe<&2, B.Number64>, C.minimum_stack(C.Field{u, q, name, xs, parent}), B.nat64(r), minimum) :
    {C.sum_optional(Some{B.Number64{0, 1}}, _) == B.nat64(1n+r) : Maybe<&2, B.Number64>}
  A.sum_optional_nat64_exact(1n, r)

law name_ordered_prepares_o_value_correct:
  for +u: Bool
  for +q: B.Number64
  for +previous: String
  for +name: String
  for +xs: List<&2, D.Field>
  for +parent: C.Stack
  for valid: {D.name_valid(name) == True{} : Bool}
  for order: {String.is_lt(previous, name) == True{} : Bool}
  {C.emit_name(C.Name{u, q, previous, xs, parent}, name) == C.Tag{C.Field{u, q, name, xs, parent}} : C.Machine}
def name_ordered_prepares_o_value_correct(u, q, previous, name, xs, parent, valid, order):
  %Equal.sym(Bool, D.name_valid(name) && String.is_lt(previous, name), True{}, F.and_boolean_intro(D.name_valid(name), String.is_lt(previous, name), valid, order)) :
    {C.name_checked(_, u, q, name, xs, parent) == C.Tag{C.Field{u, q, name, xs, parent}} : C.Machine}
  {==}

# Both callbacks are induction cases: name and SUBVALUE, not the record.
# All limits of the two Name/Field states follow from the reserve.
law name_and_value_segmented_compose_field_real:
  for +name: String
  for +v: D.Value
  for +nb: List<&2, U32>
  for +vb: List<&2, U32>
  for +u: Bool
  for +q: B.Number64
  for +previous: String
  for +xs: List<&2, D.Field>
  for +parent: C.Stack
  for +suffix: List<&2, U32>
  for +r: Nat
  for +body: B.Number64
  for +ceiling: B.Number64
  for name_complete: NameComplete(name, nb)
  for value_complete: S.CompleteLocal(v, vb)
  for valid: {D.name_valid(name) == True{} : Bool}
  for order: {String.is_lt(previous, name) == True{} : Bool}
  for positive: {Nat.is_le(1n, B.length(vb)) == True{} : Bool}
  for +minimum: {C.minimum_stack(C.Field{u, q, name, xs, parent}) == B.nat64(r) : Maybe<&2, B.Number64>}
  for +reservation: {Nat.is_le(r, B.length(suffix)) == True{} : Bool}
  for +measured: {B.nat64(B.length(B.concatenate(B.concatenate(nb, vb), suffix))) == Some{body} : Maybe<&2, B.Number64>}
  for +fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  {R.execute(B.concatenate(nb, vb), R.Frame{body, ceiling, C.TagName{C.Name{u, q, previous, xs, parent}}}) ==
    X.later(B.concatenate(nb, vb), body, ceiling, C.emit(C.Field{u, q, name, xs, parent}, v)) : R.Frame}
def name_and_value_segmented_compose_field_real(name, v, nb, vb, u, q, previous, xs, parent, suffix, r, body, ceiling, name_complete, value_complete, valid, order, positive, minimum, reservation, measured, fits):
  +measure_name = {(%J.concatenation_associative(nb, vb, suffix) :
      {B.nat64(B.length(_)) == Some{body} : Maybe<&2, B.Number64>}
      measured) : {B.nat64(B.length(B.concatenate(nb, B.concatenate(vb, suffix)))) == Some{body} : Maybe<&2, B.Number64>}}
  step_name = name_complete(body, ceiling, C.Name{u, q, previous, xs, parent}, B.concatenate(vb, suffix), 1n+r,
    minimum_name_includes_exactly_value_current(u, q, previous, name, xs, parent, r, minimum),
    K.concatenate_segments_preserves_sum_of_limits(vb, suffix, 1n, r, positive, reservation), measure_name, fits)
  emission_name = name_ordered_prepares_o_value_correct(u, q, previous, name, xs, parent, valid, order)
  S.compose_two_segments_real(nb, vb, body, ceiling, C.TagName{C.Name{u, q, previous, xs, parent}}, C.Tag{C.Field{u, q, name, xs, parent}}, C.emit(C.Field{u, q, name, xs, parent}, v),
    Equal.trans(R.Frame,
      R.execute(nb, R.Frame{body, ceiling, C.TagName{C.Name{u, q, previous, xs, parent}}}),
      X.later(nb, body, ceiling, C.emit_name(C.Name{u, q, previous, xs, parent}, name)), X.later(nb, body, ceiling, C.Tag{C.Field{u, q, name, xs, parent}}), step_name,
      Equal.cong(C.Machine, R.Frame, m => X.later(nb, body, ceiling, m), C.emit_name(C.Name{u, q, previous, xs, parent}, name), C.Tag{C.Field{u, q, name, xs, parent}}, emission_name)),
    value_complete(H.decrease(B.length(nb), body), H.decrease(B.length(nb), ceiling), C.Field{u, q, name, xs, parent}, suffix, r, minimum, reservation,
      S.measure_after_segment(nb, B.concatenate(vb, suffix), body, measure_name), M.decrease_repeated_preserves_order_of_limits(B.length(nb), body, ceiling, fits)))
