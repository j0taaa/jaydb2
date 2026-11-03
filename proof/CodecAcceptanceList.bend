# Complete segmentation of the ACTUAL payload of an accepted list.
# Fuel is only a mathematical upper bound on remaining length.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecTrace.bend as R
import ./CodecArities.bend as A
import ./CodecLimitsSequences.bend as S
import ./CodecAcceptancePrefix.bend as X
import ./CodecAcceptanceChildren.bend as H

type Segmentation<-bs: List<&2, U32>, -start: C.Machine, -v: D.Value, -max: Nat> is Type:
  Segmentation{xs: List<&2, S.ValueSegmented>,
    bytes: {bs == S.bytes_values(xs) : List<&2, U32>},
    delivery: {A.deliver_values(S.values(xs), start) == C.DecodedReady{v} : C.Machine},
    children: H.ChildrenRead(xs, max)}

# Emission in a root list preserves exactly these two states.
type StateList is Data:
  Reading{last: Bool, remaining: B.Number64, inverted: List<&2, D.Value>}
  Terminated{value: D.Value}

def machine_list(e: StateList) -> C.Machine:
  match e:
    case Reading{u, q, xs}:
      C.Tag{C.ListFrame{u, q, xs, C.Root{}}}
    case Terminated{v}:
      C.DecodedReady{v}

def ready_combined_suffix_impossible(+b: U32, +bs: List<&2, U32>,
  +body: B.Number64, +ceiling: B.Number64, +w: D.Value, -v: D.Value,
  accepted: {R.machine(R.execute(Con{b, bs}, R.Frame{body, ceiling, C.DecodedReady{w}})) == C.DecodedReady{v} : C.Machine}) -> Empty:
  R.input_negative_decoded(v,
    Equal.trans(C.Outcome, C.Input{}, R.finalize_frame(R.execute(Con{b, bs}, R.Frame{body, ceiling, C.DecodedReady{w}})), C.Decoded{v},
      Equal.trans(C.Outcome, C.Input{}, C.traverse(Con{b, bs}, body, ceiling, C.DecodedReady{w}),
        R.finalize_frame(R.execute(Con{b, bs}, R.Frame{body, ceiling, C.DecodedReady{w}})),
        Equal.sym(C.Outcome, C.traverse(Con{b, bs}, body, ceiling, C.DecodedReady{w}), C.Input{},
          R.ready_refusal_any_octet_extra(b, bs, body, ceiling, w)),
        R.execution_trace_and_execution_integral(Con{b, bs}, R.Frame{body, ceiling, C.DecodedReady{w}})),
      Equal.cong(C.Machine, C.Outcome, m => C.finalize(m),
        R.machine(R.execute(Con{b, bs}, R.Frame{body, ceiling, C.DecodedReady{w}})), C.DecodedReady{v}, accepted)))

def attach_child_read(+bs: List<&2, U32>, +pre: List<&2, U32>, +suf: List<&2, U32>,
  +outside: C.Stack, +h: D.Value, -v: D.Value, +max: Nat,
  bytes: {bs == B.concatenate(pre, suf) : List<&2, U32>},
  child: H.ChildRead<h, pre, max>,
  tail: Segmentation<suf, C.emit(outside, h), v, max>) ->
  Segmentation<bs, C.Tag{outside}, v, max>:
  match tail:
    case Segmentation{+xs, rest_bytes, delivery, children}:
      Segmentation{Con{S.ValueSegmented{h, pre}, xs},
        Equal.trans(List<&2, U32>, bs, B.concatenate(pre, suf), B.concatenate(pre, S.bytes_values(xs)), bytes,
          Equal.cong(List<&2, U32>, List<&2, U32>, t => B.concatenate(pre, t), suf, S.bytes_values(xs), rest_bytes)),
        delivery, L.Both{child, children}}

def resume_cut_list(+n: Nat, +bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64,
  +last: Bool, +q: B.Number64, +inverted: List<&2, D.Value>, -v: D.Value, +max: Nat,
  limit_n: {Nat.is_le(B.length(bs), 1n+n) == True{} : Bool},
  limit_max: {Nat.is_le(B.length(bs), max) == True{} : Bool},
  cut: X.Cut<bs, body, ceiling, C.Tag{C.Root{}}, C.ListFrame{last, q, inverted, C.Root{}}, v>,
  resume: @suf: List<&2, U32> -> @cf: B.Number64 -> @tf: B.Number64 -> @state: StateList ->
    {Nat.is_le(B.length(suf), n) == True{} : Bool} ->
    {Nat.is_le(B.length(suf), max) == True{} : Bool} ->
    {R.machine(R.execute(suf, R.Frame{cf, tf, machine_list(state)})) == C.DecodedReady{v} : C.Machine} ->
    Segmentation<suf, machine_list(state), v, max>) ->
  Segmentation<bs, C.Tag{C.ListFrame{last, q, inverted, C.Root{}}}, v, max>:
  match last cut:
    case True{} X.Cut{+pre, +suf, +h, +cf, +tf, +bytes, local, real, remaining}:
      +outside = {C.ListFrame{True{}, q, inverted, C.Root{}} : C.Stack}
      +local_accepted = Equal.cong(R.Frame, C.Machine, frame => R.machine(frame),
        X.execute_local(pre, outside, R.Frame{body, ceiling, C.Tag{C.Root{}}}), R.Frame{cf, tf, C.DecodedReady{h}}, local)
      +cut_max = H.limit_of_bytes_equal(bs, B.concatenate(pre, suf), max, bytes, limit_max)
      attach_child_read(bs, pre, suf, outside, h, v, max, bytes,
        H.ChildRead{body, ceiling, outside, local_accepted, H.limit_prefix(pre, suf, max, cut_max)},
        resume(suf, cf, tf,
          Terminated{C.assemble_list(Con{h, inverted}, D.VListEmpty{})},
          H.suffix_after_prefix_positive(pre, suf, n,
            H.tag_root_local_accepted_has_bytes(pre, outside, body, ceiling, h, local_accepted),
            H.limit_of_bytes_equal(bs, B.concatenate(pre, suf), 1n+n, bytes, limit_n)),
          H.limit_suffix(pre, suf, max, cut_max), remaining))
    case False{} X.Cut{+pre, +suf, +h, +cf, +tf, +bytes, local, real, remaining}:
      +outside = {C.ListFrame{False{}, q, inverted, C.Root{}} : C.Stack}
      +local_accepted = Equal.cong(R.Frame, C.Machine, frame => R.machine(frame),
        X.execute_local(pre, outside, R.Frame{body, ceiling, C.Tag{C.Root{}}}), R.Frame{cf, tf, C.DecodedReady{h}}, local)
      +cut_max = H.limit_of_bytes_equal(bs, B.concatenate(pre, suf), max, bytes, limit_max)
      attach_child_read(bs, pre, suf, outside, h, v, max, bytes,
        H.ChildRead{body, ceiling, outside, local_accepted, H.limit_prefix(pre, suf, max, cut_max)},
        resume(suf, cf, tf,
          Reading{C.one64(q), C.decrease64(q), Con{h, inverted}},
          H.suffix_after_prefix_positive(pre, suf, n,
            H.tag_root_local_accepted_has_bytes(pre, outside, body, ceiling, h, local_accepted),
            H.limit_of_bytes_equal(bs, B.concatenate(pre, suf), 1n+n, bytes, limit_n)),
          H.limit_suffix(pre, suf, max, cut_max), remaining))

law extract_list_by_fuel:
  for n: Nat
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +state: StateList
  for -v: D.Value
  for +max: Nat
  for limit_n: {Nat.is_le(B.length(bs), n) == True{} : Bool}
  for limit_max: {Nat.is_le(B.length(bs), max) == True{} : Bool}
  for accepted: {R.machine(R.execute(bs, R.Frame{body, ceiling, machine_list(state)})) == C.DecodedReady{v} : C.Machine}
  Segmentation<bs, machine_list(state), v, max>
def extract_list_by_fuel(n, bs, body, ceiling, state, v, max, limit_n, limit_max, accepted):
  match n bs state:
    case _ Nil{} Reading{u, q, xs}:
      L.ex_false(Segmentation<Nil{}, machine_list(state), v, max>,
        F.false_negative_true(Equal.cong(C.Machine, Bool, m => X.and_ready(m), machine_list(state), C.DecodedReady{v}, accepted)))
    case _ Nil{} Terminated{w}:
      Segmentation{Nil{}, {==}, accepted, Unit{}}
    case 0n Con{b, t} _:
      F.absurd_boolean(Segmentation<bs, machine_list(state), v, max>, limit_n)
    case 1n+ +less Con{b, t} Terminated{+w}:
      L.ex_false(Segmentation<bs, C.DecodedReady{w}, v, max>, ready_combined_suffix_impossible(b, t, body, ceiling, w, v, accepted))
    case 1n+ +less Con{b, t} Reading{+u, +q, +inverted}:
      resume_cut_list(less, bs, body, ceiling, u, q, inverted, v, max, limit_n, limit_max,
        X.execution_real_accepts_extracts_to_first_emission(bs, body, ceiling, C.Tag{C.Root{}},
          C.ListFrame{u, q, inverted, C.Root{}}, v, Unit{}, accepted),
        suf => cf => tf => next => ln => lm => accepted_rest =>
          extract_list_by_fuel(less, suf, cf, tf, next, v, max, ln, lm, accepted_rest))

def extract_opening_list(empty: Bool, +bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64,
  +q: B.Number64, -v: D.Value,
  accepted: {R.machine(R.execute(bs, R.Frame{body, ceiling, C.open_variable(empty, C.CountsList{}, q, C.Root{})})) == C.DecodedReady{v} : C.Machine}) ->
  Segmentation<bs, C.open_variable(empty, C.CountsList{}, q, C.Root{}), v, B.length(bs)>:
  match empty:
    case True{}:
      extract_list_by_fuel(B.length(bs), bs, body, ceiling, Terminated{D.VListEmpty{}}, v, B.length(bs),
        S.limit_reflexive(B.length(bs)), S.limit_reflexive(B.length(bs)), accepted)
    case False{}:
      extract_list_by_fuel(B.length(bs), bs, body, ceiling, Reading{C.one64(q), C.decrease64(q), Nil{}}, v, B.length(bs),
        S.limit_reflexive(B.length(bs)), S.limit_reflexive(B.length(bs)), accepted)

law list_accepts_extracts_all_os_children:
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +q: B.Number64
  for -v: D.Value
  for accepted: {R.machine(R.execute(bs, R.Frame{body, ceiling, C.open_variable(C.zero64(q), C.CountsList{}, q, C.Root{})})) == C.DecodedReady{v} : C.Machine}
  Segmentation<bs, C.open_variable(C.zero64(q), C.CountsList{}, q, C.Root{}), v, B.length(bs)>
def list_accepts_extracts_all_os_children(bs, body, ceiling, q, v, accepted):
  extract_opening_list(C.zero64(q), bs, body, ceiling, q, v, accepted)
