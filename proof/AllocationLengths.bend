# Invert the REAL guards before opening a variable Codec field.
# Applies to prefixes that may still fail later, without requiring final acceptance.
# Asserts no host facts; ordering of actual facts belongs to the runtime.
import Base
import ../contract/Bytes.bend as B
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecRelaxArithmetic.bend as A
import ./CodecRelaxArithmeticNat.bend as N
import ./CodecRelaxArithmeticWord.bend as W
import ./CodecMinimumStack.bend as M
import ./CodecSumsMinimum.bend as S
import ./CodecLimitsSequences.bend as Q

def in_construction(m: C.Machine) -> Bool:
  match m:
    case C.Invalid{}:
      False{}
    case C.Above{}:
      False{}
    case _:
      True{}

law opening_in_construction_requires_check_real:
  for +c: C.Check
  for +f: C.Purpose
  for +q: B.Number64
  for +stack: C.Stack
  for opened: {in_construction(C.open_checked(c, f, q, stack)) == True{} : Bool}
  {c == C.Fits{} : C.Check}
def opening_in_construction_requires_check_real(c, f, q, stack, opened):
  match c:
    case C.Fits{}:
      {==}
    case C.Short{}:
      F.absurd_boolean({C.Short{} == C.Fits{} : C.Check}, opened)
    case C.Large{}:
      F.absurd_boolean({C.Large{} == C.Fits{} : C.Check}, opened)

law summand_negative_exceeds_sum:
  for +n: Nat
  for +r: Nat
  {Nat.is_le(n, Nat.add(n, r)) == True{} : Bool}
def summand_negative_exceeds_sum(n, r):
  match n:
    case 0n:
      N.zero_negative_greater(r)
    case 1n+p:
      summand_negative_exceeds_sum(p, r)

law count_negative_exceeds_minimum_of_field:
  for +f: C.Purpose
  for +n: Nat
  {Nat.is_le(n, S.minimum_field_natural(f, n)) == True{} : Bool}
def count_negative_exceeds_minimum_of_field(f, n):
  match f:
    case C.CountsRecord{}:
      summand_negative_exceeds_sum(n, Nat.mul(10n, n))
    case C.Integer{}:
      Q.limit_reflexive(n)
    case C.TextValue{}:
      Q.limit_reflexive(n)
    case C.NameText{}:
      Q.limit_reflexive(n)
    case C.CountsList{}:
      Q.limit_reflexive(n)

def count_less_that_reservation(+f: C.Purpose, +q: B.Number64, +stack: C.Stack,
  count: W.NumberMeasured<q>, reservation: M.MinimumExact<stack>) ->
  N.OrderNatural<Some{q}, C.sum_optional(C.minimum_field(f, q), C.minimum_stack(stack))>:
  match count reservation:
    case W.NumberMeasured{+n, +measured} M.MinimumExact{+r, exact}:
      N.OrderNatural{n, Nat.add(S.minimum_field_natural(f, n), r),
        Equal.sym(Maybe<&2, B.Number64>, B.nat64(n), Some{q}, measured),
        S.minimum_field_combined_stack_nat64_exact(f, n, r, q, stack, measured, exact),
        N.order_transitive(n, S.minimum_field_natural(f, n), Nat.add(S.minimum_field_natural(f, n), r),
          count_negative_exceeds_minimum_of_field(f, n), summand_negative_exceeds_sum(S.minimum_field_natural(f, n), r))}

# No Nat measure or minimum representability is an external premise.
# They follow from all real u64 values and frames, including overflow.
law check_composed_limits_to_count_declared:
  for +f: C.Purpose
  for +q: B.Number64
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  for fits: {C.check(C.sum_optional(C.minimum_field(f, q), C.minimum_stack(stack)), body, ceiling) == C.Fits{} : C.Check}
  {C.check(Some{q}, body, ceiling) == C.Fits{} : C.Check}
def check_composed_limits_to_count_declared(f, q, stack, body, ceiling, fits):
  A.check_order_measure(Some{q}, C.sum_optional(C.minimum_field(f, q), C.minimum_stack(stack)), body, ceiling,
    count_less_that_reservation(f, q, stack, W.measure_number(q),
      M.all_os_minimum_of_stack_measure_are_exact(stack, A.measure_stack(stack))),
    W.measure_number(body), W.measure_number(ceiling), fits)

def invert_limits(-q: B.Number64, -body: B.Number64, -ceiling: B.Number64,
  limits: L.E<{C.less_equal64(q, ceiling) == True{} : Bool}, {C.less_equal64(q, body) == True{} : Bool}>) ->
  L.E<{C.less_equal64(q, body) == True{} : Bool}, {C.less_equal64(q, ceiling) == True{} : Bool}>:
  match limits:
    case L.Both{lt, lc}:
      L.Both{lc, lt}

law check_composed_requires_both_limits:
  for +f: C.Purpose
  for +q: B.Number64
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  for fits: {C.check(C.sum_optional(C.minimum_field(f, q), C.minimum_stack(stack)), body, ceiling) == C.Fits{} : C.Check}
  L.E<{C.less_equal64(q, body) == True{} : Bool}, {C.less_equal64(q, ceiling) == True{} : Bool}>
def check_composed_requires_both_limits(f, q, stack, body, ceiling, fits):
  invert_limits(q, body, ceiling,
    N.check_cases_requires_limits(C.less_equal64(q, ceiling), C.less_equal64(q, body),
      check_composed_limits_to_count_declared(f, q, stack, body, ceiling, fits)))

# Excludes only the Integer branch, which uses eight fixed bytes and no u64 arity.
def Variable(f: C.Purpose) -> Type:
  match f:
    case C.Integer{}:
      Empty
    case _:
      Unit

law conclude_word_variable_in_construction_was_checked:
  for +f: C.Purpose
  for +high: U32
  for +low: U32
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  for variable: Variable(f)
  for opened: {in_construction(C.conclude_word(f, high, low, stack, body, ceiling)) == True{} : Bool}
  {C.check(C.sum_optional(C.minimum_field(f, B.Number64{high, low}), C.minimum_stack(stack)), body, ceiling) == C.Fits{} : C.Check}
def conclude_word_variable_in_construction_was_checked(f, high, low, stack, body, ceiling, variable, opened):
  match f:
    case C.Integer{}:
      L.ex_false({C.check(C.sum_optional(C.minimum_field(C.Integer{}, B.Number64{high, low}), C.minimum_stack(stack)), body, ceiling) == C.Fits{} : C.Check}, variable)
    case C.TextValue{}:
      opening_in_construction_requires_check_real(C.check(C.sum_optional(C.minimum_field(C.TextValue{}, B.Number64{high, low}), C.minimum_stack(stack)), body, ceiling), C.TextValue{}, B.Number64{high, low}, stack, opened)
    case C.NameText{}:
      opening_in_construction_requires_check_real(C.check(C.sum_optional(C.minimum_field(C.NameText{}, B.Number64{high, low}), C.minimum_stack(stack)), body, ceiling), C.NameText{}, B.Number64{high, low}, stack, opened)
    case C.CountsList{}:
      opening_in_construction_requires_check_real(C.check(C.sum_optional(C.minimum_field(C.CountsList{}, B.Number64{high, low}), C.minimum_stack(stack)), body, ceiling), C.CountsList{}, B.Number64{high, low}, stack, opened)
    case C.CountsRecord{}:
      opening_in_construction_requires_check_real(C.check(C.sum_optional(C.minimum_field(C.CountsRecord{}, B.Number64{high, low}), C.minimum_stack(stack)), body, ceiling), C.CountsRecord{}, B.Number64{high, low}, stack, opened)

law opening_variable_real_respects_body_and_ceiling:
  for +f: C.Purpose
  for +high: U32
  for +low: U32
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  for variable: Variable(f)
  for opened: {in_construction(C.conclude_word(f, high, low, stack, body, ceiling)) == True{} : Bool}
  L.E<{C.less_equal64(B.Number64{high, low}, body) == True{} : Bool},
    {C.less_equal64(B.Number64{high, low}, ceiling) == True{} : Bool}>
def opening_variable_real_respects_body_and_ceiling(f, high, low, stack, body, ceiling, variable, opened):
  check_composed_requires_both_limits(f, B.Number64{high, low}, stack, body, ceiling,
    conclude_word_variable_in_construction_was_checked(f, high, low, stack, body, ceiling, variable, opened))
