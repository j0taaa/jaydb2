# Removing an outer stack relaxes the actual Codec guard for every u64.
# Minima may overflow; their representability follows only from Fits.
import Base
import ../contract/Bytes.bend as B
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./CodecAcceptanceStack.bend as J
import ./CodecMinimumStack.bend as M
import ./CodecRelaxArithmeticWord.bend as W
import ./CodecRelaxArithmeticNat.bend as A

def measure_counter(-q: B.Number64, measure: W.NumberMeasured<q>) -> M.CounterMeasured<q>:
  match measure:
    case W.NumberMeasured{n, measured}:
      M.CounterMeasured{n, measured}

def measure_stack(+p: C.Stack) -> M.MeasuresStack(p):
  match p:
    case C.Root{}:
      Unit{}
    case C.ListFrame{u, +q, xs, +parent}:
      L.Both{measure_counter(q, W.measure_number(q)), measure_stack(parent)}
    case C.Field{u, +q, name, xs, +parent}:
      L.Both{measure_counter(q, W.measure_number(q)), measure_stack(parent)}
    case C.Name{u, +q, previous, xs, +parent}:
      L.Both{measure_counter(q, W.measure_number(q)), measure_stack(parent)}

def minimum_field_linked(+f: C.Purpose, +q: B.Number64, +p: C.Stack, +outside: C.Stack,
  measure: W.NumberMeasured<q>) ->
  A.OrderNatural<C.sum_optional(C.minimum_field(f, q), C.minimum_stack(p)),
    C.sum_optional(C.minimum_field(f, q), C.minimum_stack(J.link_stack(p, outside)))>:
  match measure:
    case W.NumberMeasured{+n, measured}:
      A.sum_to_order(C.minimum_field(f, q), Nat.mul(M.factor_field(f), n),
        C.minimum_stack(p), C.minimum_stack(J.link_stack(p, outside)),
        M.all_os_minimum_of_field_measured_are_exact(f, n, q, measured),
        A.minimum_linked_naturals(p, outside, measure_stack(p), measure_stack(outside)))

def check_order_measure(+a: Maybe<&2, B.Number64>, +b: Maybe<&2, B.Number64>,
  +body: B.Number64, +ceiling: B.Number64, h: A.OrderNatural<a, b>,
  measure_body: W.NumberMeasured<body>, measure_ceiling: W.NumberMeasured<ceiling>,
  fits: {C.check(b, body, ceiling) == C.Fits{} : C.Check}) ->
  {C.check(a, body, ceiling) == C.Fits{} : C.Check}:
  match h measure_body measure_ceiling:
    case A.OrderNatural{+n, +m, ea, eb, reads} W.NumberMeasured{+c, mc} W.NumberMeasured{+t, mt}:
      %Equal.sym(Maybe<&2, B.Number64>, a, B.nat64(n), ea) :
        {C.check(_, body, ceiling) == C.Fits{} : C.Check}
      A.check_natural_less(n, m, c, t, body, ceiling, mc, mt, reads,
        (%eb : {C.check(_, body, ceiling) == C.Fits{} : C.Check}
          fits))

# Interface without additional measures or representability hypotheses.
law check_without_stack_external:
  for +f: C.Purpose
  for +q: B.Number64
  for +p: C.Stack
  for +outside: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  for fits: {C.check(C.sum_optional(C.minimum_field(f, q), C.minimum_stack(J.link_stack(p, outside))), body, ceiling) == C.Fits{} : C.Check}
  {C.check(C.sum_optional(C.minimum_field(f, q), C.minimum_stack(p)), body, ceiling) == C.Fits{} : C.Check}
def check_without_stack_external(f, q, p, outside, body, ceiling, fits):
  check_order_measure(C.sum_optional(C.minimum_field(f, q), C.minimum_stack(p)),
    C.sum_optional(C.minimum_field(f, q), C.minimum_stack(J.link_stack(p, outside))), body, ceiling,
    minimum_field_linked(f, q, p, outside, W.measure_number(q)),
    W.measure_number(body), W.measure_number(ceiling), fits)
