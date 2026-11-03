# Exact structural reconstruction of declared arities. The Nat parameter
# is mathematical child-sequence length, without an additional limit.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecCounters.bend as N

def next_value(m: C.Machine, v: D.Value) -> C.Machine:
  match m:
    case C.Tag{stack}:
      C.emit(stack, v)
    case _:
      C.Invalid{}

def deliver_values(xs: List<&2, D.Value>, m: C.Machine) -> C.Machine:
  match xs:
    case Nil{}:
      m
    case Con{v, t}:
      deliver_values(t, next_value(m, v))

def count_values(xs: List<&2, D.Value>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+count_values(t)

def attach_list(xs: List<&2, D.Value>, acc: D.Value) -> D.Value:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      D.VList{h, attach_list(t, acc)}

def ValuesNotEmpty(xs: List<&2, D.Value>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case Con{h, t}:
      Unit

law list_counted_reconstructs_exactly_all_os_children:
  for +xs: List<&2, D.Value>
  for +q: B.Number64
  for +inverted: List<&2, D.Value>
  for +parent: C.Stack
  for positive: ValuesNotEmpty(xs)
  for +measured: {B.nat64(count_values(xs)) == Some{q} : Maybe<&2, B.Number64>}
  {deliver_values(xs, C.Tag{C.ListFrame{C.one64(q), C.decrease64(q), inverted, parent}}) ==
    C.emit(parent, C.assemble_list(inverted, attach_list(xs, D.VListEmpty{}))) : C.Machine}
def list_counted_reconstructs_exactly_all_os_children(xs, q, inverted, parent, positive, measured):
  match xs:
    case Nil{}:
      L.ex_false({C.Tag{C.ListFrame{C.one64(q), C.decrease64(q), inverted, parent}} == C.emit(parent, C.assemble_list(inverted, D.VListEmpty{})) : C.Machine}, positive)
    case Con{+h, Nil{}}:
      %F.some_injective(B.Number64, B.Number64{0, 1}, q, measured) :
        {deliver_values(Con{h, Nil{}}, C.Tag{C.ListFrame{C.one64(_), C.decrease64(q), inverted, parent}}) ==
          C.emit(parent, C.assemble_list(inverted, D.VList{h, D.VListEmpty{}})) : C.Machine}
      {==}
    case Con{+h, Con{+v, +rest}}:
      +t = {Con{v, rest} : List<&2, D.Value>}
      %Equal.sym(Bool, C.one64(q), False{}, N.one64_reflects_count_natural(count_values(Con{h, t}), q, measured)) :
        {deliver_values(t, C.emit(C.ListFrame{_, C.decrease64(q), inverted, parent}, h)) ==
          C.emit(parent, C.assemble_list(inverted, D.VList{h, attach_list(t, D.VListEmpty{})})) : C.Machine}
      list_counted_reconstructs_exactly_all_os_children(t, C.decrease64(q), Con{h, inverted}, parent, Unit{},
        N.measure_decremented(count_values(t), q, N.nat64_successor_has_predecessor_exact(count_values(t), q, measured)))

law opening_of_list_counted_preserves_arity_and_order:
  for +xs: List<&2, D.Value>
  for +q: B.Number64
  for +parent: C.Stack
  for +measured: {B.nat64(count_values(xs)) == Some{q} : Maybe<&2, B.Number64>}
  {deliver_values(xs, C.open_variable(C.zero64(q), C.CountsList{}, q, parent)) ==
    C.emit(parent, attach_list(xs, D.VListEmpty{})) : C.Machine}
def opening_of_list_counted_preserves_arity_and_order(xs, q, parent, measured):
  match xs:
    case Nil{}:
      %F.some_injective(B.Number64, B.Number64{0, 0}, q, measured) :
        {C.open_variable(C.zero64(_), C.CountsList{}, q, parent) == C.emit(parent, D.VListEmpty{}) : C.Machine}
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, C.zero64(q), False{}, N.zero64_reflects_count_natural(count_values(Con{h, t}), q, measured)) :
        {deliver_values(Con{h, t}, C.open_variable(_, C.CountsList{}, q, parent)) == C.emit(parent, attach_list(Con{h, t}, D.VListEmpty{})) : C.Machine}
      list_counted_reconstructs_exactly_all_os_children(Con{h, t}, q, Nil{}, parent, Unit{}, measured)

# Fields are delivered in reading order. Strict order and the actual
# contract name predicate are checked before inserting each value.
def FieldsOrdered(xs: List<&2, D.Field>, previous: String) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{D.Field{n, v}, t}:
      L.E<{D.name_valid(n) == True{} : Bool},
        L.E<{String.is_lt(previous, n) == True{} : Bool}, FieldsOrdered(t, n)>>

def count_fields(xs: List<&2, D.Field>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+count_fields(t)

def attach_record(xs: List<&2, D.Field>, acc: D.Value) -> D.Value:
  match xs:
    case Nil{}:
      acc
    case Con{D.Field{n, v}, t}:
      D.VRecord{n, v, attach_record(t, acc)}

def deliver_field(m: C.Machine, field: D.Field) -> C.Machine:
  match m field:
    case C.TagName{stack} D.Field{n, v}:
      next_value(C.emit_name(stack, n), v)
    case _ _:
      C.Invalid{}

def deliver_fields(xs: List<&2, D.Field>, m: C.Machine) -> C.Machine:
  match xs:
    case Nil{}:
      m
    case Con{h, t}:
      deliver_fields(t, deliver_field(m, h))

def FieldsNotEmpty(xs: List<&2, D.Field>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case Con{h, t}:
      Unit

law field_ordered_and_delivered_without_swap:
  for +last: Bool
  for +q: B.Number64
  for +previous: String
  for +name: String
  for +v: D.Value
  for +inverted: List<&2, D.Field>
  for +parent: C.Stack
  for name_valid: {D.name_valid(name) == True{} : Bool}
  for order: {String.is_lt(previous, name) == True{} : Bool}
  {deliver_field(C.TagName{C.Name{last, q, previous, inverted, parent}}, D.Field{name, v}) ==
    C.emit(C.Field{last, q, name, inverted, parent}, v) : C.Machine}
def field_ordered_and_delivered_without_swap(last, q, previous, name, v, inverted, parent, name_valid, order):
  %Equal.sym(Bool, D.name_valid(name) && String.is_lt(previous, name), True{},
    F.and_boolean_intro(D.name_valid(name), String.is_lt(previous, name), name_valid, order)) :
    {next_value(C.name_checked(_, last, q, name, inverted, parent), v) == C.emit(C.Field{last, q, name, inverted, parent}, v) : C.Machine}
  {==}

# The induction hypothesis is applied after checking the current field name.
def resume_fields(+xs: List<&2, D.Field>, +q: B.Number64,
  +previous: String, +name: String, +v: D.Value,
  +inverted: List<&2, D.Field>, +parent: C.Stack,
  name_valid: {D.name_valid(name) == True{} : Bool},
  order: {String.is_lt(previous, name) == True{} : Bool},
  last: Bool) ->
  {deliver_fields(xs, deliver_field(C.TagName{C.Name{last, q, previous, inverted, parent}}, D.Field{name, v})) ==
    deliver_fields(xs, C.emit(C.Field{last, q, name, inverted, parent}, v)) : C.Machine}:
  Equal.cong(C.Machine, C.Machine, m => deliver_fields(xs, m),
    deliver_field(C.TagName{C.Name{last, q, previous, inverted, parent}}, D.Field{name, v}),
    C.emit(C.Field{last, q, name, inverted, parent}, v),
    field_ordered_and_delivered_without_swap(last, q, previous, name, v, inverted, parent, name_valid, order))

law record_counted_reconstructs_exactly_all_os_fields:
  for +xs: List<&2, D.Field>
  for +q: B.Number64
  for +previous: String
  for +inverted: List<&2, D.Field>
  for +parent: C.Stack
  for positive: FieldsNotEmpty(xs)
  for ordered: FieldsOrdered(xs, previous)
  for +measured: {B.nat64(count_fields(xs)) == Some{q} : Maybe<&2, B.Number64>}
  {deliver_fields(xs, C.TagName{C.Name{C.one64(q), C.decrease64(q), previous, inverted, parent}}) ==
    C.emit(parent, C.assemble_record(inverted, attach_record(xs, D.VRecordEmpty{}))) : C.Machine}
def record_counted_reconstructs_exactly_all_os_fields(xs, q, previous, inverted, parent, positive, ordered, measured):
  match xs:
    case Nil{}:
      L.ex_false({C.TagName{C.Name{C.one64(q), C.decrease64(q), previous, inverted, parent}} == C.emit(parent, C.assemble_record(inverted, D.VRecordEmpty{})) : C.Machine}, positive)
    case Con{D.Field{+name, +v}, Nil{}}:
      match ordered:
        case L.Both{name_valid, L.Both{order, tail}}:
          %F.some_injective(B.Number64, B.Number64{0, 1}, q, measured) :
            {deliver_field(C.TagName{C.Name{C.one64(_), C.decrease64(q), previous, inverted, parent}}, D.Field{name, v}) ==
              C.emit(parent, C.assemble_record(inverted, D.VRecord{name, v, D.VRecordEmpty{}})) : C.Machine}
          field_ordered_and_delivered_without_swap(True{}, C.decrease64(q), previous, name, v, inverted, parent, name_valid, order)
    case Con{D.Field{+name, +v}, Con{+field, +rest}}:
      match ordered:
        case L.Both{name_valid, L.Both{order, tail}}:
          +t = {Con{field, rest} : List<&2, D.Field>}
          %Equal.sym(Bool, C.one64(q), False{}, N.one64_reflects_count_natural(count_fields(xs), q, measured)) :
            {deliver_fields(t, deliver_field(C.TagName{C.Name{_, C.decrease64(q), previous, inverted, parent}}, D.Field{name, v})) ==
              C.emit(parent, C.assemble_record(inverted, D.VRecord{name, v, attach_record(t, D.VRecordEmpty{})})) : C.Machine}
          Equal.trans(C.Machine,
            deliver_fields(t, deliver_field(C.TagName{C.Name{False{}, C.decrease64(q), previous, inverted, parent}}, D.Field{name, v})),
            deliver_fields(t, C.emit(C.Field{False{}, C.decrease64(q), name, inverted, parent}, v)),
            C.emit(parent, C.assemble_record(inverted, D.VRecord{name, v, attach_record(t, D.VRecordEmpty{})})),
            resume_fields(t, C.decrease64(q), previous, name, v, inverted, parent, name_valid, order, False{}),
            record_counted_reconstructs_exactly_all_os_fields(t, C.decrease64(q), name, Con{D.Field{name, v}, inverted}, parent, Unit{}, tail,
              N.measure_decremented(count_fields(t), q, N.nat64_successor_has_predecessor_exact(count_fields(t), q, measured))))

law opening_of_record_counted_preserves_arity_and_order:
  for +xs: List<&2, D.Field>
  for +q: B.Number64
  for +parent: C.Stack
  for ordered: FieldsOrdered(xs, "")
  for +measured: {B.nat64(count_fields(xs)) == Some{q} : Maybe<&2, B.Number64>}
  {deliver_fields(xs, C.open_variable(C.zero64(q), C.CountsRecord{}, q, parent)) ==
    C.emit(parent, attach_record(xs, D.VRecordEmpty{})) : C.Machine}
def opening_of_record_counted_preserves_arity_and_order(xs, q, parent, ordered, measured):
  match xs:
    case Nil{}:
      %F.some_injective(B.Number64, B.Number64{0, 0}, q, measured) :
        {C.open_variable(C.zero64(_), C.CountsRecord{}, q, parent) == C.emit(parent, D.VRecordEmpty{}) : C.Machine}
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, C.zero64(q), False{}, N.zero64_reflects_count_natural(count_fields(Con{h, t}), q, measured)) :
        {deliver_fields(Con{h, t}, C.open_variable(_, C.CountsRecord{}, q, parent)) == C.emit(parent, attach_record(Con{h, t}, D.VRecordEmpty{})) : C.Machine}
      record_counted_reconstructs_exactly_all_os_fields(Con{h, t}, q, "", Nil{}, parent, Unit{}, ordered, measured)

def ready(m: C.Machine) -> Bool:
  match m:
    case C.DecodedReady{v}:
      True{}
    case _:
      False{}

law tag_negative_and_ready:
  for -stack: C.Stack
  for -v: D.Value
  for e: {C.Tag{stack} == C.DecodedReady{v} : C.Machine}
  Empty
def tag_negative_and_ready(stack, v, e):
  F.false_negative_true(Equal.cong(C.Machine, Bool, m => ready(m), C.Tag{stack}, C.DecodedReady{v}, e))

law invalid_negative_and_ready:
  for -v: D.Value
  for e: {C.Invalid{} == C.DecodedReady{v} : C.Machine}
  Empty
def invalid_negative_and_ready(v, e):
  F.false_negative_true(Equal.cong(C.Machine, Bool, m => ready(m), C.Invalid{}, C.DecodedReady{v}, e))

law values_negative_recover_machine_invalid:
  for xs: List<&2, D.Value>
  {deliver_values(xs, C.Invalid{}) == C.Invalid{} : C.Machine}
def values_negative_recover_machine_invalid(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      values_negative_recover_machine_invalid(t)

law ready_refusal_value_extra:
  for h: D.Value
  for xs: List<&2, D.Value>
  for v: D.Value
  {deliver_values(Con{h, xs}, C.DecodedReady{v}) == C.Invalid{} : C.Machine}
def ready_refusal_value_extra(h, xs, v):
  values_negative_recover_machine_invalid(xs)

def check_child_unique(last: Bool, +q: B.Number64, +h: D.Value,
  +inverted: List<&2, D.Value>, -v: D.Value,
  accepted: {C.emit(C.ListFrame{last, C.decrease64(q), inverted, C.Root{}}, h) == C.DecodedReady{v} : C.Machine}) ->
  {last == True{} : Bool}:
  match last:
    case True{}:
      {==}
    case False{}:
      L.ex_false({False{} == True{} : Bool},
        tag_negative_and_ready(C.ListFrame{C.one64(C.decrease64(q)), C.decrease64(C.decrease64(q)), Con{h, inverted}, C.Root{}}, v, accepted))

# Structural hypothesis on the tail supplied by the induction below.
def check_children_remaining(last: Bool, +q: B.Number64, +h: D.Value,
  +x: D.Value, +xs: List<&2, D.Value>, +inverted: List<&2, D.Value>, -v: D.Value,
  accepted: {deliver_values(Con{x, xs}, C.emit(C.ListFrame{last, C.decrease64(q), inverted, C.Root{}}, h)) == C.DecodedReady{v} : C.Machine},
  resume: {deliver_values(Con{x, xs}, C.Tag{C.ListFrame{C.one64(C.decrease64(q)), C.decrease64(C.decrease64(q)), Con{h, inverted}, C.Root{}}}) == C.DecodedReady{v} : C.Machine} ->
    {N.last(count_values(Con{x, xs}), C.decrease64(q)) == True{} : Bool}) ->
  {Bool.not(last) && N.last(count_values(Con{x, xs}), C.decrease64(q)) == True{} : Bool}:
  match last:
    case False{}:
      resume(accepted)
    case True{}:
      L.ex_false({False{} == True{} : Bool}, invalid_negative_and_ready(v,
        Equal.trans(C.Machine, C.Invalid{}, deliver_values(Con{x, xs}, C.DecodedReady{C.assemble_list(Con{h, inverted}, D.VListEmpty{})}), C.DecodedReady{v},
          Equal.sym(C.Machine, deliver_values(Con{x, xs}, C.DecodedReady{C.assemble_list(Con{h, inverted}, D.VListEmpty{})}), C.Invalid{},
            ready_refusal_value_extra(x, xs, C.assemble_list(Con{h, inverted}, D.VListEmpty{}))), accepted)))

law list_closed_checked_exactly_all_os_last:
  for +xs: List<&2, D.Value>
  for +q: B.Number64
  for +inverted: List<&2, D.Value>
  for -v: D.Value
  for accepted: {deliver_values(xs, C.Tag{C.ListFrame{C.one64(q), C.decrease64(q), inverted, C.Root{}}}) == C.DecodedReady{v} : C.Machine}
  {N.last(count_values(xs), q) == True{} : Bool}
def list_closed_checked_exactly_all_os_last(xs, q, inverted, v, accepted):
  match xs:
    case Nil{}:
      L.ex_false({False{} == True{} : Bool}, tag_negative_and_ready(C.ListFrame{C.one64(q), C.decrease64(q), inverted, C.Root{}}, v, accepted))
    case Con{h, Nil{}}:
      check_child_unique(C.one64(q), q, h, inverted, v, accepted)
    case Con{+h, Con{+x, +rest}}:
      check_children_remaining(C.one64(q), q, h, x, rest, inverted, v, accepted,
        e => list_closed_checked_exactly_all_os_last(Con{x, rest}, C.decrease64(q), Con{h, inverted}, v, e))

law list_closed_reconstructs_to_count_canonical_original:
  for +xs: List<&2, D.Value>
  for +q: B.Number64
  for +inverted: List<&2, D.Value>
  for -v: D.Value
  for accepted: {deliver_values(xs, C.Tag{C.ListFrame{C.one64(q), C.decrease64(q), inverted, C.Root{}}}) == C.DecodedReady{v} : C.Machine}
  {B.nat64(count_values(xs)) == Some{q} : Maybe<&2, B.Number64>}
def list_closed_reconstructs_to_count_canonical_original(xs, q, inverted, v, accepted):
  N.last_accepted_reconstruct_to_count_original(count_values(xs), q,
    list_closed_checked_exactly_all_os_last(xs, q, inverted, v, accepted))

law tag_name_negative_and_ready:
  for -stack: C.Stack
  for -v: D.Value
  for e: {C.TagName{stack} == C.DecodedReady{v} : C.Machine}
  Empty
def tag_name_negative_and_ready(stack, v, e):
  F.false_negative_true(Equal.cong(C.Machine, Bool, m => ready(m), C.TagName{stack}, C.DecodedReady{v}, e))

law fields_negative_recover_machine_invalid:
  for xs: List<&2, D.Field>
  {deliver_fields(xs, C.Invalid{}) == C.Invalid{} : C.Machine}
def fields_negative_recover_machine_invalid(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      fields_negative_recover_machine_invalid(t)

law ready_refusal_field_extra:
  for h: D.Field
  for xs: List<&2, D.Field>
  for v: D.Value
  {deliver_fields(Con{h, xs}, C.DecodedReady{v}) == C.Invalid{} : C.Machine}
def ready_refusal_field_extra(h, xs, v):
  fields_negative_recover_machine_invalid(xs)

def field_unique_checks_last(ok: Bool, last: Bool, +q: B.Number64,
  +name: String, +value: D.Value, +inverted: List<&2, D.Field>, -v: D.Value,
  accepted: {next_value(C.name_checked(ok, last, C.decrease64(q), name, inverted, C.Root{}), value) == C.DecodedReady{v} : C.Machine}) ->
  {last == True{} : Bool}:
  match ok last:
    case False{} _:
      L.ex_false({last == True{} : Bool}, invalid_negative_and_ready(v, accepted))
    case True{} True{}:
      {==}
    case True{} False{}:
      L.ex_false({False{} == True{} : Bool}, tag_name_negative_and_ready(C.Name{C.one64(C.decrease64(q)), C.decrease64(C.decrease64(q)), name, Con{D.Field{name, value}, inverted}, C.Root{}}, v, accepted))

def fields_remaining_check_last(ok: Bool, last: Bool, +q: B.Number64,
  +name: String, +value: D.Value, +h: D.Field, +xs: List<&2, D.Field>, +inverted: List<&2, D.Field>, -v: D.Value,
  accepted: {deliver_fields(Con{h, xs}, next_value(C.name_checked(ok, last, C.decrease64(q), name, inverted, C.Root{}), value)) == C.DecodedReady{v} : C.Machine},
  resume: {deliver_fields(Con{h, xs}, C.TagName{C.Name{C.one64(C.decrease64(q)), C.decrease64(C.decrease64(q)), name, Con{D.Field{name, value}, inverted}, C.Root{}}}) == C.DecodedReady{v} : C.Machine} ->
    {N.last(count_fields(Con{h, xs}), C.decrease64(q)) == True{} : Bool}) ->
  {Bool.not(last) && N.last(count_fields(Con{h, xs}), C.decrease64(q)) == True{} : Bool}:
  match ok last:
    case False{} _:
      L.ex_false({Bool.not(last) && N.last(count_fields(Con{h, xs}), C.decrease64(q)) == True{} : Bool}, invalid_negative_and_ready(v,
        Equal.trans(C.Machine, C.Invalid{}, deliver_fields(Con{h, xs}, C.Invalid{}), C.DecodedReady{v},
          Equal.sym(C.Machine, deliver_fields(Con{h, xs}, C.Invalid{}), C.Invalid{}, fields_negative_recover_machine_invalid(Con{h, xs})), accepted)))
    case True{} False{}:
      resume(accepted)
    case True{} True{}:
      L.ex_false({False{} == True{} : Bool}, invalid_negative_and_ready(v,
        Equal.trans(C.Machine, C.Invalid{}, deliver_fields(Con{h, xs}, C.DecodedReady{C.assemble_record(Con{D.Field{name, value}, inverted}, D.VRecordEmpty{})}), C.DecodedReady{v},
          Equal.sym(C.Machine, deliver_fields(Con{h, xs}, C.DecodedReady{C.assemble_record(Con{D.Field{name, value}, inverted}, D.VRecordEmpty{})}), C.Invalid{},
            ready_refusal_field_extra(h, xs, C.assemble_record(Con{D.Field{name, value}, inverted}, D.VRecordEmpty{}))), accepted)))

law record_closed_checked_exactly_all_os_last:
  for +xs: List<&2, D.Field>
  for +q: B.Number64
  for +previous: String
  for +inverted: List<&2, D.Field>
  for -v: D.Value
  for accepted: {deliver_fields(xs, C.TagName{C.Name{C.one64(q), C.decrease64(q), previous, inverted, C.Root{}}}) == C.DecodedReady{v} : C.Machine}
  {N.last(count_fields(xs), q) == True{} : Bool}
def record_closed_checked_exactly_all_os_last(xs, q, previous, inverted, v, accepted):
  match xs:
    case Nil{}:
      L.ex_false({False{} == True{} : Bool}, tag_name_negative_and_ready(C.Name{C.one64(q), C.decrease64(q), previous, inverted, C.Root{}}, v, accepted))
    case Con{D.Field{+name, +value}, Nil{}}:
      field_unique_checks_last(D.name_valid(name) && String.is_lt(previous, name), C.one64(q), q, name, value, inverted, v, accepted)
    case Con{D.Field{+name, +value}, Con{+h, +t}}:
      fields_remaining_check_last(D.name_valid(name) && String.is_lt(previous, name), C.one64(q), q, name, value, h, t, inverted, v, accepted,
        e => record_closed_checked_exactly_all_os_last(Con{h, t}, C.decrease64(q), name, Con{D.Field{name, value}, inverted}, v, e))

law record_closed_reconstructs_to_count_canonical_original:
  for +xs: List<&2, D.Field>
  for +q: B.Number64
  for +previous: String
  for +inverted: List<&2, D.Field>
  for -v: D.Value
  for accepted: {deliver_fields(xs, C.TagName{C.Name{C.one64(q), C.decrease64(q), previous, inverted, C.Root{}}}) == C.DecodedReady{v} : C.Machine}
  {B.nat64(count_fields(xs)) == Some{q} : Maybe<&2, B.Number64>}
def record_closed_reconstructs_to_count_canonical_original(xs, q, previous, inverted, v, accepted):
  N.last_accepted_reconstruct_to_count_original(count_fields(xs), q,
    record_closed_checked_exactly_all_os_last(xs, q, previous, inverted, v, accepted))
