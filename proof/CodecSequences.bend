# Induction steps on children AND THEIR ACTUAL byte segments.
# Induction hypotheses are strictly per child, under any stack and
# suffix with numeric reserve; they do not assumes whole-list acceptance.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecTrace.bend as R
import ./CodecComposition.bend as X
import ./CodecCounters.bend as N
import ./CodecWordsBE64.bend as H
import ./CodecTexts.bend as T
import ./CodecMinimum.bend as M
import ./CodecMinimumStack.bend as A
import ./CodecCanonical.bend as K
import ./CodecLimitsSequences.bend as S
import ./CodecLimitsNames.bend as W
import ./CodecSumsMinimum.bend as J

# The reserve refers to sibling/ancestor bytes that ACTUALLY follow the
# segment. It is not a premise about the decoder result or check.
def CompleteLocal(v: D.Value, +bs: List<&2, U32>) -> Type:
  @body: B.Number64 -> @ceiling: B.Number64 -> @stack: C.Stack ->
  @suffix: List<&2, U32> -> @r: Nat ->
  {C.minimum_stack(stack) == B.nat64(r) : Maybe<&2, B.Number64>} ->
  {Nat.is_le(r, B.length(suffix)) == True{} : Bool} ->
  {B.nat64(B.length(B.concatenate(bs, suffix))) == Some{body} : Maybe<&2, B.Number64>} ->
  {C.less_equal64(body, ceiling) == True{} : Bool} ->
  {R.execute(bs, R.Frame{body, ceiling, C.Tag{stack}}) == X.later(bs, body, ceiling, C.emit(stack, v)) : R.Frame}

def values(xs: List<&2, S.ValueSegmented>) -> List<&2, D.Value>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{S.ValueSegmented{v, bs}, t}:
      Con{v, values(t)}

def list(xs: List<&2, S.ValueSegmented>) -> D.Value:
  match xs:
    case Nil{}:
      D.VListEmpty{}
    case Con{S.ValueSegmented{v, bs}, t}:
      D.VList{v, list(t)}

# Bounds for all tails are independent results of
# CodecLimitsSequences. The callback is the hypothesis on the current SUBVALUE.
def InductionValues(xs: List<&2, S.ValueSegmented>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{S.ValueSegmented{v, bs}, t}:
      L.E<CompleteLocal(v, bs),
        L.E<{Nat.is_le(S.count_values(t), B.length(S.bytes_values(t))) == True{} : Bool}, InductionValues(t)>>

law measure_after_segment:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +body: B.Number64
  for measured: {B.nat64(B.length(B.concatenate(a, b))) == Some{body} : Maybe<&2, B.Number64>}
  {B.nat64(B.length(b)) == Some{H.decrease(B.length(a), body)} : Maybe<&2, B.Number64>}
def measure_after_segment(a, b, body, measured):
  T.remove_prefix_of_measure(B.length(a), B.length(b), body,
    (%W.length_concatenation(a, b) : {B.nat64(_) == Some{body} : Maybe<&2, B.Number64>}
      measured))

law later_of_segments_concatenated:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +m: C.Machine
  {X.later(b, H.decrease(B.length(a), body), H.decrease(B.length(a), ceiling), m) == X.later(B.concatenate(a, b), body, ceiling, m) : R.Frame}
def later_of_segments_concatenated(a, b, body, ceiling, m):
  %Equal.sym(B.Number64, H.decrease(B.length(B.concatenate(a, b)), body), H.decrease(B.length(b), H.decrease(B.length(a), body)), X.decrease_by_concatenation(a, b, body)) :
    {R.Frame{H.decrease(B.length(b), H.decrease(B.length(a), body)), H.decrease(B.length(b), H.decrease(B.length(a), ceiling)), m} == R.Frame{_, H.decrease(B.length(B.concatenate(a, b)), ceiling), m} : R.Frame}
  %Equal.sym(B.Number64, H.decrease(B.length(B.concatenate(a, b)), ceiling), H.decrease(B.length(b), H.decrease(B.length(a), ceiling)), X.decrease_by_concatenation(a, b, ceiling)) :
    {R.Frame{H.decrease(B.length(b), H.decrease(B.length(a), body)), H.decrease(B.length(b), H.decrease(B.length(a), ceiling)), m} == R.Frame{H.decrease(B.length(b), H.decrease(B.length(a), body)), _, m} : R.Frame}
  {==}

def NotEmpty(xs: List<&2, S.ValueSegmented>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case Con{h, t}:
      Unit

def sum_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 0n), p, sum_zero(p))

def minimum_frame_list(+u: Bool, +q: B.Number64, -xs: List<&2, D.Value>, +parent: C.Stack,
  +n: Nat, +r: Nat,
  measured: {B.nat64(n) == Some{q} : Maybe<&2, B.Number64>},
  minimum: {C.minimum_stack(parent) == B.nat64(r) : Maybe<&2, B.Number64>}) ->
  {C.minimum_stack(C.ListFrame{u, q, xs, parent}) == B.nat64(Nat.add(n, r)) : Maybe<&2, B.Number64>}:
  %Equal.sym(Maybe<&2, B.Number64>, C.minimum_stack(parent), B.nat64(r), minimum) :
    {C.sum_pending(q, 1n, _) == B.nat64(Nat.add(n, r)) : Maybe<&2, B.Number64>}
  %sum_zero(n) :
    {C.sum_pending(q, 1n, B.nat64(r)) == B.nat64(Nat.add(_, r)) : Maybe<&2, B.Number64>}
  A.sum_pending_nat64_exact(n, q, 1n, r, measured)


law compose_two_segments_real:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +m: C.Machine
  for +n: C.Machine
  for +end: C.Machine
  for first: {R.execute(a, R.Frame{body, ceiling, m}) == X.later(a, body, ceiling, n) : R.Frame}
  for second: {R.execute(b, X.later(a, body, ceiling, n)) == X.later(b, H.decrease(B.length(a), body), H.decrease(B.length(a), ceiling), end) : R.Frame}
  {R.execute(B.concatenate(a, b), R.Frame{body, ceiling, m}) == X.later(B.concatenate(a, b), body, ceiling, end) : R.Frame}
def compose_two_segments_real(a, b, body, ceiling, m, n, end, first, second):
  Equal.trans(R.Frame,
    R.execute(B.concatenate(a, b), R.Frame{body, ceiling, m}),
    R.execute(b, R.execute(a, R.Frame{body, ceiling, m})),
    X.later(B.concatenate(a, b), body, ceiling, end),
    R.execution_of_concatenation(a, b, R.Frame{body, ceiling, m}),
    Equal.trans(R.Frame,
      R.execute(b, R.execute(a, R.Frame{body, ceiling, m})), R.execute(b, X.later(a, body, ceiling, n)),
      X.later(B.concatenate(a, b), body, ceiling, end),
      Equal.cong(R.Frame, R.Frame, q => R.execute(b, q), R.execute(a, R.Frame{body, ceiling, m}), X.later(a, body, ceiling, n), first),
      Equal.trans(R.Frame, R.execute(b, X.later(a, body, ceiling, n)),
        X.later(b, H.decrease(B.length(a), body), H.decrease(B.length(a), ceiling), end),
        X.later(B.concatenate(a, b), body, ceiling, end), second, later_of_segments_concatenated(a, b, body, ceiling, end))))

def compose_tail_list(+t: List<&2, S.ValueSegmented>, +q: B.Number64, +v: D.Value, +bs: List<&2, U32>,
  +inverted: List<&2, D.Value>, +parent: C.Stack, +suffix: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64,
  +counted: {B.nat64(1n+S.count_values(t)) == Some{q} : Maybe<&2, B.Number64>},
  +input: {B.nat64(B.length(B.concatenate(bs, B.concatenate(S.bytes_values(t), suffix)))) == Some{body} : Maybe<&2, B.Number64>},
  fits: {C.less_equal64(body, ceiling) == True{} : Bool},
  step: {R.execute(bs, R.Frame{body, ceiling, C.Tag{C.ListFrame{C.one64(q), C.decrease64(q), inverted, parent}}}) ==
    X.later(bs, body, ceiling, C.emit(C.ListFrame{C.one64(q), C.decrease64(q), inverted, parent}, v)) : R.Frame},
  resume: NotEmpty(t) ->
    {B.nat64(B.length(B.concatenate(S.bytes_values(t), suffix))) == Some{H.decrease(B.length(bs), body)} : Maybe<&2, B.Number64>} ->
    {C.less_equal64(H.decrease(B.length(bs), body), H.decrease(B.length(bs), ceiling)) == True{} : Bool} ->
    {R.execute(S.bytes_values(t), R.Frame{H.decrease(B.length(bs), body), H.decrease(B.length(bs), ceiling),
        C.Tag{C.ListFrame{C.one64(C.decrease64(q)), C.decrease64(C.decrease64(q)), Con{v, inverted}, parent}}}) ==
      X.later(S.bytes_values(t), H.decrease(B.length(bs), body), H.decrease(B.length(bs), ceiling), C.emit(parent, C.assemble_list(Con{v, inverted}, list(t)))) : R.Frame}) ->
  {R.execute(B.concatenate(bs, S.bytes_values(t)), R.Frame{body, ceiling, C.Tag{C.ListFrame{C.one64(q), C.decrease64(q), inverted, parent}}}) ==
    X.later(B.concatenate(bs, S.bytes_values(t)), body, ceiling, C.emit(parent, C.assemble_list(inverted, D.VList{v, list(t)}))) : R.Frame}:
  match t:
    case Nil{}:
      +last = N.one64_reflects_count_natural(1n, q, counted)
      +emission = {(%Equal.sym(Bool, C.one64(q), True{}, last) :
        {C.emit(C.ListFrame{_, C.decrease64(q), inverted, parent}, v) == C.emit(parent, C.assemble_list(inverted, D.VList{v, D.VListEmpty{}})) : C.Machine}
        {==}) : {C.emit(C.ListFrame{C.one64(q), C.decrease64(q), inverted, parent}, v) == C.emit(parent, C.assemble_list(inverted, D.VList{v, D.VListEmpty{}})) : C.Machine}}
      compose_two_segments_real(bs, Nil{}, body, ceiling, C.Tag{C.ListFrame{C.one64(q), C.decrease64(q), inverted, parent}},
        C.emit(C.ListFrame{C.one64(q), C.decrease64(q), inverted, parent}, v), C.emit(parent, C.assemble_list(inverted, D.VList{v, D.VListEmpty{}})), step,
        Equal.cong(C.Machine, R.Frame, m => X.later(bs, body, ceiling, m),
          C.emit(C.ListFrame{C.one64(q), C.decrease64(q), inverted, parent}, v), C.emit(parent, C.assemble_list(inverted, D.VList{v, D.VListEmpty{}})), emission))
    case Con{+h, +rest}:
      +last = N.one64_reflects_count_natural(2n+S.count_values(rest), q, counted)
      +emission = {(%Equal.sym(Bool, C.one64(q), False{}, last) :
        {C.emit(C.ListFrame{_, C.decrease64(q), inverted, parent}, v) == C.Tag{C.ListFrame{C.one64(C.decrease64(q)), C.decrease64(C.decrease64(q)), Con{v, inverted}, parent}} : C.Machine}
        {==}) : {C.emit(C.ListFrame{C.one64(q), C.decrease64(q), inverted, parent}, v) == C.Tag{C.ListFrame{C.one64(C.decrease64(q)), C.decrease64(C.decrease64(q)), Con{v, inverted}, parent}} : C.Machine}}
      compose_two_segments_real(bs, S.bytes_values(Con{h, rest}), body, ceiling, C.Tag{C.ListFrame{C.one64(q), C.decrease64(q), inverted, parent}},
        C.Tag{C.ListFrame{C.one64(C.decrease64(q)), C.decrease64(C.decrease64(q)), Con{v, inverted}, parent}}, C.emit(parent, C.assemble_list(Con{v, inverted}, list(Con{h, rest}))),
        Equal.trans(R.Frame,
          R.execute(bs, R.Frame{body, ceiling, C.Tag{C.ListFrame{C.one64(q), C.decrease64(q), inverted, parent}}}),
          X.later(bs, body, ceiling, C.emit(C.ListFrame{C.one64(q), C.decrease64(q), inverted, parent}, v)),
          X.later(bs, body, ceiling, C.Tag{C.ListFrame{C.one64(C.decrease64(q)), C.decrease64(C.decrease64(q)), Con{v, inverted}, parent}}), step,
          Equal.cong(C.Machine, R.Frame, m => X.later(bs, body, ceiling, m),
            C.emit(C.ListFrame{C.one64(q), C.decrease64(q), inverted, parent}, v), C.Tag{C.ListFrame{C.one64(C.decrease64(q)), C.decrease64(C.decrease64(q)), Con{v, inverted}, parent}}, emission)),
        resume(Unit{}, measure_after_segment(bs, B.concatenate(S.bytes_values(Con{h, rest}), suffix), body, input), M.decrease_repeated_preserves_order_of_limits(B.length(bs), body, ceiling, fits)))

# The code below inducts on the TAIL of segments, not the declared
# count. The u64 counter is reconstructed/decremented through nat64.
law list_of_segments_composes_execution_real_of_children:
  for +xs: List<&2, S.ValueSegmented>
  for +q: B.Number64
  for +inverted: List<&2, D.Value>
  for +parent: C.Stack
  for +suffix: List<&2, U32>
  for +r: Nat
  for +body: B.Number64
  for +ceiling: B.Number64
  for positive: NotEmpty(xs)
  for children: InductionValues(xs)
  for +counted: {B.nat64(S.count_values(xs)) == Some{q} : Maybe<&2, B.Number64>}
  for +minimum: {C.minimum_stack(parent) == B.nat64(r) : Maybe<&2, B.Number64>}
  for +reservation: {Nat.is_le(r, B.length(suffix)) == True{} : Bool}
  for +measured: {B.nat64(B.length(B.concatenate(S.bytes_values(xs), suffix))) == Some{body} : Maybe<&2, B.Number64>}
  for +fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  {R.execute(S.bytes_values(xs), R.Frame{body, ceiling, C.Tag{C.ListFrame{C.one64(q), C.decrease64(q), inverted, parent}}}) ==
    X.later(S.bytes_values(xs), body, ceiling, C.emit(parent, C.assemble_list(inverted, list(xs)))) : R.Frame}
def list_of_segments_composes_execution_real_of_children(xs, q, inverted, parent, suffix, r, body, ceiling, positive, children, counted, minimum, reservation, measured, fits):
  match xs:
    case Nil{}:
      L.ex_false({R.Frame{body, ceiling, C.Tag{C.ListFrame{C.one64(q), C.decrease64(q), inverted, parent}}} == R.Frame{body, ceiling, C.emit(parent, C.assemble_list(inverted, D.VListEmpty{}))} : R.Frame}, positive)
    case Con{S.ValueSegmented{+v, +bs}, +t}:
      match children:
        case L.Both{current, L.Both{+size, tail}}:
          +remaining = N.measure_decremented(S.count_values(t), q, N.nat64_successor_has_predecessor_exact(S.count_values(t), q, counted))
          # minimum_field(CountsList,q)=q, and minimum_stack(ListFrame)=q+parent.
          +reservation_child = S.concatenate_segments_preserves_sum_of_limits(S.bytes_values(t), suffix, S.count_values(t), r, size, reservation)
          +input_child = {(%K.concatenation_associative(bs, S.bytes_values(t), suffix) :
              {B.nat64(B.length(_)) == Some{body} : Maybe<&2, B.Number64>}
              measured) : {B.nat64(B.length(B.concatenate(bs, B.concatenate(S.bytes_values(t), suffix)))) == Some{body} : Maybe<&2, B.Number64>}}
          # sum_pending may skip q=0; this equality is proved by the
          # arithmetic lemma, without assuming representability.
          +minimum_list = minimum_frame_list(C.one64(q), C.decrease64(q), inverted, parent, S.count_values(t), r, remaining, minimum)
          +step = current(body, ceiling, C.ListFrame{C.one64(q), C.decrease64(q), inverted, parent}, B.concatenate(S.bytes_values(t), suffix), Nat.add(S.count_values(t), r), minimum_list, reservation_child, input_child, fits)
          compose_tail_list(t, q, v, bs, inverted, parent, suffix, body, ceiling, counted, input_child, fits, step,
            positive => measure_tail => fits_tail =>
              list_of_segments_composes_execution_real_of_children(t, C.decrease64(q), Con{v, inverted}, parent, suffix, r,
                H.decrease(B.length(bs), body), H.decrease(B.length(bs), ceiling), positive, tail, remaining, minimum, reservation, measure_tail, fits_tail))

law list_open_composes_all_os_segments:
  for +xs: List<&2, S.ValueSegmented>
  for +q: B.Number64
  for +parent: C.Stack
  for +suffix: List<&2, U32>
  for +r: Nat
  for +body: B.Number64
  for +ceiling: B.Number64
  for children: InductionValues(xs)
  for +counted: {B.nat64(S.count_values(xs)) == Some{q} : Maybe<&2, B.Number64>}
  for +minimum: {C.minimum_stack(parent) == B.nat64(r) : Maybe<&2, B.Number64>}
  for +reservation: {Nat.is_le(r, B.length(suffix)) == True{} : Bool}
  for +measured: {B.nat64(B.length(B.concatenate(S.bytes_values(xs), suffix))) == Some{body} : Maybe<&2, B.Number64>}
  for +fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  {R.execute(S.bytes_values(xs), R.Frame{body, ceiling, C.open_variable(C.zero64(q), C.CountsList{}, q, parent)}) ==
    X.later(S.bytes_values(xs), body, ceiling, C.emit(parent, list(xs))) : R.Frame}
def list_open_composes_all_os_segments(xs, q, parent, suffix, r, body, ceiling, children, counted, minimum, reservation, measured, fits):
  match xs:
    case Nil{}:
      %F.some_injective(B.Number64, B.Number64{0, 0}, q, counted) :
        {R.Frame{body, ceiling, C.open_variable(C.zero64(_), C.CountsList{}, q, parent)} == X.later(Nil{}, body, ceiling, C.emit(parent, D.VListEmpty{})) : R.Frame}
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, C.zero64(q), False{}, N.zero64_reflects_count_natural(S.count_values(Con{h, t}), q, counted)) :
        {R.execute(S.bytes_values(Con{h, t}), R.Frame{body, ceiling, C.open_variable(_, C.CountsList{}, q, parent)}) == X.later(S.bytes_values(Con{h, t}), body, ceiling, C.emit(parent, list(Con{h, t}))) : R.Frame}
      list_of_segments_composes_execution_real_of_children(Con{h, t}, q, Nil{}, parent, suffix, r, body, ceiling, Unit{}, children, counted, minimum, reservation, measured, fits)

def bytes_list(high: U32, low: U32, xs: List<&2, S.ValueSegmented>) -> List<&2, U32>:
  Con{5, B.concatenate(B.be64(high, low), S.bytes_values(xs))}

# This is the list constructor's INDUCTION STEP. All values of the
# arbitrary; the hypothesis applies only to each smaller subvalue.
# The sole limit is the actual body/ceiling, without depth or arity quotas.
law constructor_list_composes_completeness_local:
  for +xs: List<&2, S.ValueSegmented>
  for +high: U32
  for +low: U32
  for +body: B.Number64
  for +ceiling: B.Number64
  for +parent: C.Stack
  for +suffix: List<&2, U32>
  for +r: Nat
  for children: InductionValues(xs)
  for canonical: S.ValuesCanonical(xs)
  for +counted: {B.nat64(S.count_values(xs)) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
  for +minimum: {C.minimum_stack(parent) == B.nat64(r) : Maybe<&2, B.Number64>}
  for +reservation: {Nat.is_le(r, B.length(suffix)) == True{} : Bool}
  for +measured: {B.nat64(B.length(B.concatenate(bytes_list(high, low, xs), suffix))) == Some{body} : Maybe<&2, B.Number64>}
  for +fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  {R.execute(bytes_list(high, low, xs), R.Frame{body, ceiling, C.Tag{parent}}) ==
    X.later(bytes_list(high, low, xs), body, ceiling, C.emit(parent, list(xs))) : R.Frame}
def constructor_list_composes_completeness_local(xs, high, low, body, ceiling, parent, suffix, r, children, canonical, counted, minimum, reservation, measured, fits):
  +measure_tail = T.remove_prefix_of_measure(9n, B.length(B.concatenate(S.bytes_values(xs), suffix)), body, measured)
  +limit_minimum = S.concatenate_segments_preserves_sum_of_limits(S.bytes_values(xs), suffix, S.count_values(xs), r,
    S.sequence_of_values_canonical_requires_one_octet_by_value(xs, canonical), reservation)
  +opening = X.header_variable_combined_body_and_ceiling_u64_arbitrary(C.CountsList{}, S.count_values(xs), r, B.length(B.concatenate(S.bytes_values(xs), suffix)), high, low, parent, body, ceiling, Unit{}, counted, minimum, measure_tail, limit_minimum, fits)
  compose_two_segments_real(Con{5, B.be64(high, low)}, S.bytes_values(xs), body, ceiling, C.Tag{parent},
    C.open_variable(C.zero64(B.Number64{high, low}), C.CountsList{}, B.Number64{high, low}, parent), C.emit(parent, list(xs)), opening,
    list_open_composes_all_os_segments(xs, B.Number64{high, low}, parent, suffix, r, H.decrease(9n, body), H.decrease(9n, ceiling), children, counted, minimum, reservation, measure_tail,
      M.decrease_repeated_preserves_order_of_limits(9n, body, ceiling, fits)))
