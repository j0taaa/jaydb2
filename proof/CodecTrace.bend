# Complete consumption and inversion of actual parser prechecks.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F

def accepts(r: C.Outcome) -> Bool:
  match r:
    case C.Decoded{v}:
      True{}
    case _:
      False{}

law input_negative_decoded:
  for -v: D.Value
  for e: {C.Input{} == C.Decoded{v} : C.Outcome}
  Empty
def input_negative_decoded(v, e):
  F.false_negative_true(Equal.cong(C.Outcome, Bool, r => accepts(r), C.Input{}, C.Decoded{v}, e))

law limit_negative_decoded:
  for -v: D.Value
  for e: {C.Limit{} == C.Decoded{v} : C.Outcome}
  Empty
def limit_negative_decoded(v, e):
  F.false_negative_true(Equal.cong(C.Outcome, Bool, r => accepts(r), C.Limit{}, C.Decoded{v}, e))

def TraceAccepted(-bs: List<&2, U32>, -body: B.Number64, -ceiling: B.Number64, -v: D.Value) -> Type:
  {C.traverse(bs, body, ceiling, C.Tag{C.Root{}}) == C.Decoded{v} : C.Outcome}

law octets_accepted_were_checked:
  for all_valid: Bool
  for -bs: List<&2, U32>
  for -body: B.Number64
  for -ceiling: B.Number64
  for -v: D.Value
  for accepted: {C.decode_octets(all_valid, bs, body, ceiling) == C.Decoded{v} : C.Outcome}
  L.E<{all_valid == True{} : Bool}, TraceAccepted(bs, body, ceiling, v)>
def octets_accepted_were_checked(all_valid, bs, body, ceiling, v, accepted):
  match all_valid:
    case False{}:
      L.ex_false(L.E<{False{} == True{} : Bool}, TraceAccepted(bs, body, ceiling, v)>, input_negative_decoded(v, accepted))
    case True{}:
      L.Both{{==}, accepted}

law size_accepted_was_checked:
  for fits: Bool
  for +bs: List<&2, U32>
  for -body: B.Number64
  for -ceiling: B.Number64
  for -v: D.Value
  for accepted: {C.decode_size(fits, bs, body, ceiling) == C.Decoded{v} : C.Outcome}
  L.E<{fits == True{} : Bool},
    L.E<{B.octets_all_valid(bs) == True{} : Bool}, TraceAccepted(bs, body, ceiling, v)>>
def size_accepted_was_checked(fits, bs, body, ceiling, v, accepted):
  match fits:
    case False{}:
      L.ex_false(L.E<{False{} == True{} : Bool}, L.E<{B.octets_all_valid(bs) == True{} : Bool}, TraceAccepted(bs, body, ceiling, v)>>, limit_negative_decoded(v, accepted))
    case True{}:
      L.Both{{==}, octets_accepted_were_checked(B.octets_all_valid(bs), bs, body, ceiling, v, accepted)}

# The body is not supplied as a premise: it follows from the accepted measure.
type InputChecked<-n: Maybe<&2, B.Number64>, -bs: List<&2, U32>, -ceiling: B.Number64, -v: D.Value> is Type:
  Checked{body: B.Number64,
    measure: {n == Some{body} : Maybe<&2, B.Number64>},
    fits: {C.less_equal64(body, ceiling) == True{} : Bool},
    octets: {B.octets_all_valid(bs) == True{} : Bool},
    execution_trace: TraceAccepted(bs, body, ceiling, v)}

def assemble_checked(-n: Maybe<&2, B.Number64>, -bs: List<&2, U32>,
  -ceiling: B.Number64, -v: D.Value, +body: B.Number64,
  measure: {n == Some{body} : Maybe<&2, B.Number64>},
  proofs: L.E<{C.less_equal64(body, ceiling) == True{} : Bool},
    L.E<{B.octets_all_valid(bs) == True{} : Bool}, TraceAccepted(bs, body, ceiling, v)>>) ->
  InputChecked<n, bs, ceiling, v>:
  match proofs:
    case L.Both{fits, L.Both{octets, execution_trace}}:
      Checked{body, measure, fits, octets, execution_trace}

law measure_accepts_was_checked:
  for n: Maybe<&2, B.Number64>
  for +bs: List<&2, U32>
  for +ceiling: B.Number64
  for -v: D.Value
  for accepted: {C.decode_measure(n, bs, ceiling) == C.Decoded{v} : C.Outcome}
  InputChecked<n, bs, ceiling, v>
def measure_accepts_was_checked(n, bs, ceiling, v, accepted):
  match n:
    case None{}:
      L.ex_false(InputChecked<None{}, bs, ceiling, v>, limit_negative_decoded(v, accepted))
    case Some{+body}:
      assemble_checked(Some{body}, bs, ceiling, v, body, {==},
        size_accepted_was_checked(C.less_equal64(body, ceiling), bs, body, ceiling, v, accepted))

law acceptance_requires_body_representable_octets_and_limit:
  for +bs: List<&2, U32>
  for +ceiling: B.Number64
  for -v: D.Value
  for accepted: {C.decode(bs, ceiling) == C.Decoded{v} : C.Outcome}
  InputChecked<B.nat64(B.length(bs)), bs, ceiling, v>
def acceptance_requires_body_representable_octets_and_limit(bs, ceiling, v, accepted):
  measure_accepts_was_checked(B.nat64(B.length(bs)), bs, ceiling, v, accepted)

# This helper machine returns the final state of the SAME path, including
# both counters. The proof below links it to C.traverse by induction.
type Frame is Data:
  Frame{body: B.Number64, ceiling: B.Number64, machine: C.Machine}

def advance(q: Frame, b: U32) -> Frame:
  Frame{body, ceiling, m} = q
  +rest = C.decrease64(body)
  +free = C.decrease64(ceiling)
  Frame{rest, free, C.step(m, b, rest, free)}

def execute(bs: List<&2, U32>, q: Frame) -> Frame:
  match bs:
    case Nil{}:
      q
    case Con{b, t}:
      execute(t, advance(q, b))

def machine(q: Frame) -> C.Machine:
  Frame{body, ceiling, m} = q
  m

def finalize_frame(q: Frame) -> C.Outcome:
  C.finalize(machine(q))

def traverse_frame(bs: List<&2, U32>, q: Frame) -> C.Outcome:
  Frame{body, ceiling, m} = q
  C.traverse(bs, body, ceiling, m)

law execution_trace_and_execution_integral:
  for +bs: List<&2, U32>
  for +q: Frame
  {traverse_frame(bs, q) == finalize_frame(execute(bs, q)) : C.Outcome}
def execution_trace_and_execution_integral(bs, q):
  match bs q:
    case Nil{} Frame{body, ceiling, m}:
      {==}
    case Con{+b, +t} Frame{+body, +ceiling, +m}:
      execution_trace_and_execution_integral(t, advance(Frame{body, ceiling, m}, b))

law execution_of_concatenation:
  for xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +q: Frame
  {execute(B.concatenate(xs, ys), q) == execute(ys, execute(xs, q)) : Frame}
def execution_of_concatenation(xs, ys, q):
  match xs:
    case Nil{}:
      {==}
    case Con{b, t}:
      execution_of_concatenation(t, ys, advance(q, b))

def ready_result(r: C.Outcome) -> C.Machine:
  match r:
    case C.Decoded{value}:
      C.DecodedReady{value}
    case _:
      C.Invalid{}

law finalize_accepts_only_ready:
  for +m: C.Machine
  for -v: D.Value
  for accepted: {C.finalize(m) == C.Decoded{v} : C.Outcome}
  {m == C.DecodedReady{v} : C.Machine}
def finalize_accepts_only_ready(m, v, accepted):
  match m:
    case C.Tag{stack}:
      L.ex_false({C.Tag{stack} == C.DecodedReady{v} : C.Machine}, input_negative_decoded(v, accepted))
    case C.TagName{stack}:
      L.ex_false({C.TagName{stack} == C.DecodedReady{v} : C.Machine}, input_negative_decoded(v, accepted))
    case C.WordInput{f, n, a, b, stack}:
      L.ex_false({C.WordInput{f, n, a, b, stack} == C.DecodedReady{v} : C.Machine}, input_negative_decoded(v, accepted))
    case C.Content{name, last, q, u, text, stack}:
      L.ex_false({C.Content{name, last, q, u, text, stack} == C.DecodedReady{v} : C.Machine}, input_negative_decoded(v, accepted))
    case C.DecodedReady{+x}:
      Equal.cong(C.Outcome, C.Machine, r => ready_result(r), C.Decoded{x}, C.Decoded{v}, accepted)
    case C.Invalid{}:
      L.ex_false({C.Invalid{} == C.DecodedReady{v} : C.Machine}, input_negative_decoded(v, accepted))
    case C.Above{}:
      L.ex_false({C.Above{} == C.DecodedReady{v} : C.Machine}, limit_negative_decoded(v, accepted))

law execution_trace_accepted_terminates_ready:
  for +bs: List<&2, U32>
  for +q: Frame
  for -v: D.Value
  for accepted: {traverse_frame(bs, q) == C.Decoded{v} : C.Outcome}
  {machine(execute(bs, q)) == C.DecodedReady{v} : C.Machine}
def execution_trace_accepted_terminates_ready(bs, q, v, accepted):
  finalize_accepts_only_ready(machine(execute(bs, q)), v,
    Equal.trans(C.Outcome, finalize_frame(execute(bs, q)), traverse_frame(bs, q), C.Decoded{v},
      Equal.sym(C.Outcome, traverse_frame(bs, q), finalize_frame(execute(bs, q)), execution_trace_and_execution_integral(bs, q)), accepted))

law invalid_absorbs_all_suffix:
  for bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  {C.traverse(bs, body, ceiling, C.Invalid{}) == C.Input{} : C.Outcome}
def invalid_absorbs_all_suffix(bs, body, ceiling):
  match bs:
    case Nil{}:
      {==}
    case Con{b, t}:
      invalid_absorbs_all_suffix(t, C.decrease64(body), C.decrease64(ceiling))

law above_absorbs_all_suffix:
  for bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  {C.traverse(bs, body, ceiling, C.Above{}) == C.Limit{} : C.Outcome}
def above_absorbs_all_suffix(bs, body, ceiling):
  match bs:
    case Nil{}:
      {==}
    case Con{b, t}:
      above_absorbs_all_suffix(t, C.decrease64(body), C.decrease64(ceiling))

law ready_refusal_any_octet_extra:
  for b: U32
  for bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for v: D.Value
  {C.traverse(Con{b, bs}, body, ceiling, C.DecodedReady{v}) == C.Input{} : C.Outcome}
def ready_refusal_any_octet_extra(b, bs, body, ceiling, v):
  invalid_absorbs_all_suffix(bs, C.decrease64(body), C.decrease64(ceiling))

law execution_trace_of_concatenation:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +q: Frame
  {traverse_frame(B.concatenate(xs, ys), q) == traverse_frame(ys, execute(xs, q)) : C.Outcome}
def execution_trace_of_concatenation(xs, ys, q):
  Equal.trans(C.Outcome, traverse_frame(B.concatenate(xs, ys), q), finalize_frame(execute(B.concatenate(xs, ys), q)), traverse_frame(ys, execute(xs, q)),
    execution_trace_and_execution_integral(B.concatenate(xs, ys), q),
    Equal.trans(C.Outcome, finalize_frame(execute(B.concatenate(xs, ys), q)), finalize_frame(execute(ys, execute(xs, q))), traverse_frame(ys, execute(xs, q)),
      Equal.cong(Frame, C.Outcome, r => finalize_frame(r), execute(B.concatenate(xs, ys), q), execute(ys, execute(xs, q)), execution_of_concatenation(xs, ys, q)),
      Equal.sym(C.Outcome, traverse_frame(ys, execute(xs, q)), finalize_frame(execute(ys, execute(xs, q))), execution_trace_and_execution_integral(ys, execute(xs, q)))))
