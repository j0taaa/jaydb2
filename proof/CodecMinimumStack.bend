# EXACT mathematical minima of every stack whose counters are measured.
# Includes None on overflow; does not assumes sums fit.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecCounters.bend as N
import ./CodecSums.bend as S

law multiply_by_zero_right:
  for k: Nat
  {Nat.mul(k, 0n) == 0n : Nat}
def multiply_by_zero_right(k):
  match k:
    case 0n:
      {==}
    case 1n+p:
      multiply_by_zero_right(p)

law sum_pending_nat64_exact:
  for +n: Nat
  for +q: B.Number64
  for +factor: Nat
  for +rest: Nat
  for +measured: {B.nat64(n) == Some{q} : Maybe<&2, B.Number64>}
  {C.sum_pending(q, factor, B.nat64(rest)) == B.nat64(Nat.add(Nat.mul(factor, n), rest)) : Maybe<&2, B.Number64>}
def sum_pending_nat64_exact(n, q, factor, rest, measured):
  match n:
    case 0n:
      %F.some_injective(B.Number64, B.Number64{0, 0}, q, measured) :
        {C.sum_pending(_, factor, B.nat64(rest)) == B.nat64(Nat.add(Nat.mul(factor, 0n), rest)) : Maybe<&2, B.Number64>}
      %Equal.sym(Nat, Nat.mul(factor, 0n), 0n, multiply_by_zero_right(factor)) :
        {B.nat64(rest) == B.nat64(Nat.add(_, rest)) : Maybe<&2, B.Number64>}
      {==}
    case 1n+p:
      %Equal.sym(Bool, C.zero64(q), False{}, N.zero64_reflects_count_natural(1n+p, q, measured)) :
        {C.sum_pending_cases(_, q, factor, B.nat64(rest)) == B.nat64(Nat.add(Nat.mul(factor, 1n+p), rest)) : Maybe<&2, B.Number64>}
      %Equal.sym(Maybe<&2, B.Number64>, C.multiply_small(factor, q), B.nat64(Nat.mul(factor, 1n+p)), S.multiply_small_nat64_exact(factor, 1n+p, q, measured)) :
        {C.sum_optional(_, B.nat64(rest)) == B.nat64(Nat.add(Nat.mul(factor, 1n+p), rest)) : Maybe<&2, B.Number64>}
      S.sum_optional_nat64_exact(Nat.mul(factor, 1n+p), rest)

type CounterMeasured<-q: B.Number64> is Type:
  CounterMeasured{natural: Nat, measure: {B.nat64(natural) == Some{q} : Maybe<&2, B.Number64>}}

# Only natural counts of each frame. There is no minimum-size,
# decoder-canonicity or check-correctness premise.
def MeasuresStack(stack: C.Stack) -> Type:
  match stack:
    case C.Root{}:
      Unit
    case C.ListFrame{u, q, xs, parent}:
      L.E<CounterMeasured<q>, MeasuresStack(parent)>
    case C.Name{u, q, previous, xs, parent}:
      L.E<CounterMeasured<q>, MeasuresStack(parent)>
    case C.Field{u, q, name, xs, parent}:
      L.E<CounterMeasured<q>, MeasuresStack(parent)>

type MinimumExact<-stack: C.Stack> is Type:
  MinimumExact{natural: Nat, exact: {C.minimum_stack(stack) == B.nat64(natural) : Maybe<&2, B.Number64>}}

def minimum_list(+u: Bool, +q: B.Number64, -xs: List<&2, D.Value>, +parent: C.Stack,
  +n: Nat, measured: {B.nat64(n) == Some{q} : Maybe<&2, B.Number64>},
  minimum_parent: MinimumExact<parent>) -> MinimumExact<C.ListFrame{u, q, xs, parent}>:
  match minimum_parent:
    case MinimumExact{+rest, exact}:
      MinimumExact{Nat.add(Nat.mul(1n, n), rest),
        (%Equal.sym(Maybe<&2, B.Number64>, C.minimum_stack(parent), B.nat64(rest), exact) :
          {C.sum_pending(q, 1n, _) == B.nat64(Nat.add(Nat.mul(1n, n), rest)) : Maybe<&2, B.Number64>}
          sum_pending_nat64_exact(n, q, 1n, rest, measured))}

def minimum_field(+u: Bool, +q: B.Number64, -name: String, -xs: List<&2, D.Field>, +parent: C.Stack,
  +n: Nat, measured: {B.nat64(n) == Some{q} : Maybe<&2, B.Number64>},
  minimum_parent: MinimumExact<parent>) -> MinimumExact<C.Field{u, q, name, xs, parent}>:
  match minimum_parent:
    case MinimumExact{+rest, exact}:
      MinimumExact{Nat.add(Nat.mul(11n, n), rest),
        (%Equal.sym(Maybe<&2, B.Number64>, C.minimum_stack(parent), B.nat64(rest), exact) :
          {C.sum_pending(q, 11n, _) == B.nat64(Nat.add(Nat.mul(11n, n), rest)) : Maybe<&2, B.Number64>}
          sum_pending_nat64_exact(n, q, 11n, rest, measured))}

def minimum_name(+u: Bool, +q: B.Number64, -previous: String, -xs: List<&2, D.Field>, +parent: C.Stack,
  +n: Nat, measured: {B.nat64(n) == Some{q} : Maybe<&2, B.Number64>},
  minimum_parent: MinimumExact<parent>) -> MinimumExact<C.Name{u, q, previous, xs, parent}>:
  match minimum_parent:
    case MinimumExact{+rest, exact}:
      MinimumExact{1n+Nat.add(Nat.mul(11n, n), rest),
        (%Equal.sym(Maybe<&2, B.Number64>, C.minimum_stack(parent), B.nat64(rest), exact) :
          {C.sum_optional(Some{B.Number64{0, 1}}, C.sum_pending(q, 11n, _)) == B.nat64(1n+Nat.add(Nat.mul(11n, n), rest)) : Maybe<&2, B.Number64>}
          %Equal.sym(Maybe<&2, B.Number64>, C.sum_pending(q, 11n, B.nat64(rest)), B.nat64(Nat.add(Nat.mul(11n, n), rest)), sum_pending_nat64_exact(n, q, 11n, rest, measured)) :
            {C.sum_optional(B.nat64(1n), _) == B.nat64(1n+Nat.add(Nat.mul(11n, n), rest)) : Maybe<&2, B.Number64>}
          S.sum_optional_nat64_exact(1n, Nat.add(Nat.mul(11n, n), rest)))}

law all_os_minimum_of_stack_measure_are_exact:
  for +stack: C.Stack
  for measures: MeasuresStack(stack)
  MinimumExact<stack>
def all_os_minimum_of_stack_measure_are_exact(stack, measures):
  match stack:
    case C.Root{}:
      MinimumExact{0n, {==}}
    case C.ListFrame{+u, +q, xs, +parent}:
      match measures:
        case L.Both{CounterMeasured{n, measured}, above}:
          minimum_list(u, q, xs, parent, n, measured, all_os_minimum_of_stack_measure_are_exact(parent, above))
    case C.Field{+u, +q, name, xs, +parent}:
      match measures:
        case L.Both{CounterMeasured{n, measured}, above}:
          minimum_field(u, q, name, xs, parent, n, measured, all_os_minimum_of_stack_measure_are_exact(parent, above))
    case C.Name{+u, +q, previous, xs, +parent}:
      match measures:
        case L.Both{CounterMeasured{n, measured}, above}:
          minimum_name(u, q, previous, xs, parent, n, measured, all_os_minimum_of_stack_measure_are_exact(parent, above))

def factor_field(f: C.Purpose) -> Nat:
  match f:
    case C.CountsRecord{}:
      11n
    case _:
      1n

def minimum_unit(+n: Nat, -q: B.Number64,
  measured: {B.nat64(n) == Some{q} : Maybe<&2, B.Number64>}) ->
  {Some{q} == B.nat64(Nat.mul(1n, n)) : Maybe<&2, B.Number64>}:
  %Equal.sym(Nat, Nat.add(n, 0n), n, S.nat_sum_zero_right(n)) :
    {Some{q} == B.nat64(_) : Maybe<&2, B.Number64>}
  Equal.sym(Maybe<&2, B.Number64>, B.nat64(n), Some{q}, measured)

law all_os_minimum_of_field_measured_are_exact:
  for +f: C.Purpose
  for +n: Nat
  for +q: B.Number64
  for measured: {B.nat64(n) == Some{q} : Maybe<&2, B.Number64>}
  {C.minimum_field(f, q) == B.nat64(Nat.mul(factor_field(f), n)) : Maybe<&2, B.Number64>}
def all_os_minimum_of_field_measured_are_exact(f, n, q, measured):
  match f:
    case C.CountsRecord{}:
      S.multiply_small_nat64_exact(11n, n, q, measured)
    case C.Integer{}:
      minimum_unit(n, q, measured)
    case C.TextValue{}:
      minimum_unit(n, q, measured)
    case C.NameText{}:
      minimum_unit(n, q, measured)
    case C.CountsList{}:
      minimum_unit(n, q, measured)

law minimum_of_field_and_stack_measured_and_exact:
  for +f: C.Purpose
  for +n: Nat
  for +q: B.Number64
  for +stack: C.Stack
  for +m: Nat
  for measured: {B.nat64(n) == Some{q} : Maybe<&2, B.Number64>}
  for minimum: {C.minimum_stack(stack) == B.nat64(m) : Maybe<&2, B.Number64>}
  {C.sum_optional(C.minimum_field(f, q), C.minimum_stack(stack)) == B.nat64(Nat.add(Nat.mul(factor_field(f), n), m)) : Maybe<&2, B.Number64>}
def minimum_of_field_and_stack_measured_and_exact(f, n, q, stack, m, measured, minimum):
  %Equal.sym(Maybe<&2, B.Number64>, C.minimum_field(f, q), B.nat64(Nat.mul(factor_field(f), n)), all_os_minimum_of_field_measured_are_exact(f, n, q, measured)) :
    {C.sum_optional(_, C.minimum_stack(stack)) == B.nat64(Nat.add(Nat.mul(factor_field(f), n), m)) : Maybe<&2, B.Number64>}
  %Equal.sym(Maybe<&2, B.Number64>, C.minimum_stack(stack), B.nat64(m), minimum) :
    {C.sum_optional(B.nat64(Nat.mul(factor_field(f), n)), _) == B.nat64(Nat.add(Nat.mul(factor_field(f), n), m)) : Maybe<&2, B.Number64>}
  S.sum_optional_nat64_exact(Nat.mul(factor_field(f), n), m)
