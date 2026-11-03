# Removing the outer stack from an accepted LOCAL execution preserves exactly
# all states and counters. Only WordInput guards may differ;
# their acceptance follows from the suffix; the smaller minimum is proved separately.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecTrace.bend as R
import ./CodecAcceptanceStack.bend as J
import ./CodecAcceptancePrefix.bend as P
import ./CodecRelaxArithmetic.bend as A

law error_local_invalid_absorbing:
  for bs: List<&2, U32>
  for +outside: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  {R.machine(P.execute_local(bs, outside, R.Frame{body, ceiling, C.Invalid{}})) == C.Invalid{} : C.Machine}
def error_local_invalid_absorbing(bs, outside, body, ceiling):
  match bs:
    case Nil{}:
      {==}
    case Con{b, t}:
      error_local_invalid_absorbing(t, outside, C.decrease64(body), C.decrease64(ceiling))

law error_local_above_absorbing:
  for bs: List<&2, U32>
  for +outside: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  {R.machine(P.execute_local(bs, outside, R.Frame{body, ceiling, C.Above{}})) == C.Above{} : C.Machine}
def error_local_above_absorbing(bs, outside, body, ceiling):
  match bs:
    case Nil{}:
      {==}
    case Con{b, t}:
      error_local_above_absorbing(t, outside, C.decrease64(body), C.decrease64(ceiling))

law check_local_accepts_requires_fits:
  for c: C.Check
  for +bs: List<&2, U32>
  for +outside: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  for +f: C.Purpose
  for +q: B.Number64
  for +p: C.Stack
  for -v: D.Value
  for accepted: {R.machine(P.execute_local(bs, outside, R.Frame{body, ceiling, C.open_checked(c, f, q, p)})) == C.DecodedReady{v} : C.Machine}
  {c == C.Fits{} : C.Check}
def check_local_accepts_requires_fits(c, bs, outside, body, ceiling, f, q, p, v, accepted):
  match c:
    case C.Fits{}:
      {==}
    case C.Short{}:
      L.ex_false({C.Short{} == C.Fits{} : C.Check}, R.input_negative_decoded(v,
        Equal.cong(C.Machine, C.Outcome, m => C.finalize(m), C.Invalid{}, C.DecodedReady{v},
          Equal.trans(C.Machine, C.Invalid{}, R.machine(P.execute_local(bs, outside, R.Frame{body, ceiling, C.Invalid{}})), C.DecodedReady{v},
            Equal.sym(C.Machine, R.machine(P.execute_local(bs, outside, R.Frame{body, ceiling, C.Invalid{}})), C.Invalid{}, error_local_invalid_absorbing(bs, outside, body, ceiling)), accepted))))
    case C.Large{}:
      L.ex_false({C.Large{} == C.Fits{} : C.Check}, R.limit_negative_decoded(v,
        Equal.cong(C.Machine, C.Outcome, m => C.finalize(m), C.Above{}, C.DecodedReady{v},
          Equal.trans(C.Machine, C.Above{}, R.machine(P.execute_local(bs, outside, R.Frame{body, ceiling, C.Above{}})), C.DecodedReady{v},
            Equal.sym(C.Machine, R.machine(P.execute_local(bs, outside, R.Frame{body, ceiling, C.Above{}})), C.Above{}, error_local_above_absorbing(bs, outside, body, ceiling)), accepted))))

def check_complete(+f: C.Purpose, +q: B.Number64, +p: C.Stack, +outside: C.Stack,
  body: B.Number64, ceiling: B.Number64) -> C.Check:
  C.check(C.sum_optional(C.minimum_field(f, q), C.minimum_stack(J.link_stack(p, outside))), body, ceiling)

def remove_guard_accepted(+f: C.Purpose, +q: B.Number64, +p: C.Stack, +outside: C.Stack,
  +body: B.Number64, +ceiling: B.Number64, +bs: List<&2, U32>, -v: D.Value,
  accepted: {R.machine(P.execute_local(bs, outside, R.Frame{body, ceiling, C.open_checked(check_complete(f, q, p, outside, body, ceiling), f, q, p)})) == C.DecodedReady{v} : C.Machine}) ->
  {C.open_checked(C.check(C.sum_optional(C.minimum_field(f, q), C.minimum_stack(p)), body, ceiling), f, q, p) ==
    C.open_checked(check_complete(f, q, p, outside, body, ceiling), f, q, p) : C.Machine}:
  +fits_outside = check_local_accepts_requires_fits(check_complete(f, q, p, outside, body, ceiling), bs, outside, body, ceiling, f, q, p, v, accepted)
  fits_root = A.check_without_stack_external(f, q, p, outside, body, ceiling, fits_outside)
  Equal.trans(C.Machine,
    C.open_checked(C.check(C.sum_optional(C.minimum_field(f, q), C.minimum_stack(p)), body, ceiling), f, q, p),
    C.open_checked(C.Fits{}, f, q, p), C.open_checked(check_complete(f, q, p, outside, body, ceiling), f, q, p),
    Equal.cong(C.Check, C.Machine, c => C.open_checked(c, f, q, p), C.check(C.sum_optional(C.minimum_field(f, q), C.minimum_stack(p)), body, ceiling), C.Fits{}, fits_root),
    Equal.cong(C.Check, C.Machine, c => C.open_checked(c, f, q, p), C.Fits{}, check_complete(f, q, p, outside, body, ceiling),
      Equal.sym(C.Check, check_complete(f, q, p, outside, body, ceiling), C.Fits{}, fits_outside)))

def conclude_local_remove_outside(+f: C.Purpose, +high: U32, +low: U32, +p: C.Stack, +outside: C.Stack,
  +body: B.Number64, +ceiling: B.Number64, +bs: List<&2, U32>, -v: D.Value,
  accepted: {R.machine(P.execute_local(bs, outside, R.Frame{body, ceiling, J.conclude_local(f, high, low, p, outside, body, ceiling)})) == C.DecodedReady{v} : C.Machine}) ->
  {C.conclude_word(f, high, low, p, body, ceiling) == J.conclude_local(f, high, low, p, outside, body, ceiling) : C.Machine}:
  match f:
    case C.Integer{}:
      {==}
    case C.TextValue{}:
      remove_guard_accepted(C.TextValue{}, B.Number64{high, low}, p, outside, body, ceiling, bs, v, accepted)
    case C.NameText{}:
      remove_guard_accepted(C.NameText{}, B.Number64{high, low}, p, outside, body, ceiling, bs, v, accepted)
    case C.CountsList{}:
      remove_guard_accepted(C.CountsList{}, B.Number64{high, low}, p, outside, body, ceiling, bs, v, accepted)
    case C.CountsRecord{}:
      remove_guard_accepted(C.CountsRecord{}, B.Number64{high, low}, p, outside, body, ceiling, bs, v, accepted)

law step_local_accepted_and_step_real_without_stack_external:
  for +m: C.Machine
  for +outside: C.Stack
  for +b: U32
  for +body: B.Number64
  for +ceiling: B.Number64
  for +bs: List<&2, U32>
  for -v: D.Value
  for accepted: {R.machine(P.execute_local(bs, outside, R.Frame{body, ceiling, J.step_local(m, outside, b, body, ceiling)})) == C.DecodedReady{v} : C.Machine}
  {C.step(m, b, body, ceiling) == J.step_local(m, outside, b, body, ceiling) : C.Machine}
def step_local_accepted_and_step_real_without_stack_external(m, outside, b, body, ceiling, bs, v, accepted):
  match m:
    case C.Tag{p}:
      {==}
    case C.TagName{p}:
      {==}
    case C.WordInput{+f, 0n, +high, +low, +p}:
      conclude_local_remove_outside(f, (high * 256 + U32.shrn(low, 24n) : U32), (low * 256 + b : U32), p, outside, body, ceiling, bs, v, accepted)
    case C.WordInput{f, 1n+n, high, low, p}:
      {==}
    case C.Content{name, last, q, u, s, p}:
      {==}
    case C.DecodedReady{w}:
      {==}
    case C.Invalid{}:
      {==}
    case C.Above{}:
      {==}

law execution_local_accepts_coincides_combined_execution_real:
  for +bs: List<&2, U32>
  for +outside: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  for +m: C.Machine
  for -v: D.Value
  for +accepted: {R.machine(P.execute_local(bs, outside, R.Frame{body, ceiling, m})) == C.DecodedReady{v} : C.Machine}
  {R.execute(bs, R.Frame{body, ceiling, m}) == P.execute_local(bs, outside, R.Frame{body, ceiling, m}) : R.Frame}
def execution_local_accepts_coincides_combined_execution_real(bs, outside, body, ceiling, m, v, accepted):
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      +rest = C.decrease64(body)
      +free = C.decrease64(ceiling)
      %Equal.sym(C.Machine, C.step(m, b, rest, free), J.step_local(m, outside, b, rest, free),
        step_local_accepted_and_step_real_without_stack_external(m, outside, b, rest, free, t, v, accepted)) :
        {R.execute(t, R.Frame{rest, free, _}) == P.execute_local(t, outside, R.Frame{rest, free, J.step_local(m, outside, b, rest, free)}) : R.Frame}
      execution_local_accepts_coincides_combined_execution_real(t, outside, rest, free, J.step_local(m, outside, b, rest, free), v, accepted)

law execution_local_accepts_continues_accepts_without_stack_external:
  for +bs: List<&2, U32>
  for +outside: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  for +m: C.Machine
  for -v: D.Value
  for +accepted: {R.machine(P.execute_local(bs, outside, R.Frame{body, ceiling, m})) == C.DecodedReady{v} : C.Machine}
  {R.machine(R.execute(bs, R.Frame{body, ceiling, m})) == C.DecodedReady{v} : C.Machine}
def execution_local_accepts_continues_accepts_without_stack_external(bs, outside, body, ceiling, m, v, accepted):
  Equal.trans(C.Machine,
    R.machine(R.execute(bs, R.Frame{body, ceiling, m})), R.machine(P.execute_local(bs, outside, R.Frame{body, ceiling, m})), C.DecodedReady{v},
    Equal.cong(R.Frame, C.Machine, q => R.machine(q), R.execute(bs, R.Frame{body, ceiling, m}), P.execute_local(bs, outside, R.Frame{body, ceiling, m}),
      execution_local_accepts_coincides_combined_execution_real(bs, outside, body, ceiling, m, v, accepted)), accepted)
