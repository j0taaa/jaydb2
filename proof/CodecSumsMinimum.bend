# Applications of general theorems to actual codec minima.
import Base
import ../contract/Bytes.bend as B
import ../src/Codec.bend as C
import ./CodecCounters.bend as N
import ./CodecSums.bend as A
import ./CodecSumsOrder.bend as O

law nat_multiply_zero_right:
  for +k: Nat
  {Nat.mul(k, 0n) == 0n : Nat}
def nat_multiply_zero_right(k):
  match k:
    case 0n:
      {==}
    case 1n+p:
      nat_multiply_zero_right(p)

# The empty-pending shortcut preserves exactly the mathematical sum,
# including when the remainder or product is unrepresentable.
law sum_pending_nat64_exact:
  for +n: Nat
  for +factor: Nat
  for +r: Nat
  for +q: B.Number64
  for +measured: {B.nat64(n) == Some{q} : Maybe<&2, B.Number64>}
  {C.sum_pending(q, factor, B.nat64(r)) == B.nat64(Nat.add(Nat.mul(factor, n), r)) : Maybe<&2, B.Number64>}
def sum_pending_nat64_exact(n, factor, r, q, measured):
  match n:
    case 0n:
      %Equal.sym(Bool, C.zero64(q), True{}, N.zero64_reflects_count_natural(0n, q, measured)) :
        {C.sum_pending_cases(_, q, factor, B.nat64(r)) == B.nat64(Nat.add(Nat.mul(factor, 0n), r)) : Maybe<&2, B.Number64>}
      %Equal.sym(Nat, Nat.mul(factor, 0n), 0n, nat_multiply_zero_right(factor)) :
        {B.nat64(r) == B.nat64(Nat.add(_, r)) : Maybe<&2, B.Number64>}
      {==}
    case 1n+p:
      %Equal.sym(Bool, C.zero64(q), False{}, N.zero64_reflects_count_natural(1n+p, q, measured)) :
        {C.sum_pending_cases(_, q, factor, B.nat64(r)) == B.nat64(Nat.add(Nat.mul(factor, 1n+p), r)) : Maybe<&2, B.Number64>}
      %Equal.sym(Maybe<&2, B.Number64>, C.multiply_small(factor, q), B.nat64(Nat.mul(factor, 1n+p)), A.multiply_small_nat64_exact(factor, 1n+p, q, measured)) :
        {C.sum_optional(_, B.nat64(r)) == B.nat64(Nat.add(Nat.mul(factor, 1n+p), r)) : Maybe<&2, B.Number64>}
      A.sum_optional_nat64_exact(Nat.mul(factor, 1n+p), r)

def minimum_field_natural(f: C.Purpose, n: Nat) -> Nat:
  match f:
    case C.CountsRecord{}:
      Nat.mul(11n, n)
    case _:
      n

law minimum_field_nat64_exact:
  for +f: C.Purpose
  for +n: Nat
  for +q: B.Number64
  for measured: {B.nat64(n) == Some{q} : Maybe<&2, B.Number64>}
  {C.minimum_field(f, q) == B.nat64(minimum_field_natural(f, n)) : Maybe<&2, B.Number64>}
def minimum_field_nat64_exact(f, n, q, measured):
  match f:
    case C.CountsRecord{}:
      A.multiply_small_nat64_exact(11n, n, q, measured)
    case C.Integer{}:
      Equal.sym(Maybe<&2, B.Number64>, B.nat64(n), Some{q}, measured)
    case C.TextValue{}:
      Equal.sym(Maybe<&2, B.Number64>, B.nat64(n), Some{q}, measured)
    case C.NameText{}:
      Equal.sym(Maybe<&2, B.Number64>, B.nat64(n), Some{q}, measured)
    case C.CountsList{}:
      Equal.sym(Maybe<&2, B.Number64>, B.nat64(n), Some{q}, measured)

# Local parent-stack hypothesis: permits the theorem as an induction
# step without assuming correctness of the compound check.
law minimum_field_combined_stack_nat64_exact:
  for +f: C.Purpose
  for +n: Nat
  for +r: Nat
  for +q: B.Number64
  for +stack: C.Stack
  for measured: {B.nat64(n) == Some{q} : Maybe<&2, B.Number64>}
  for parent: {C.minimum_stack(stack) == B.nat64(r) : Maybe<&2, B.Number64>}
  {C.sum_optional(C.minimum_field(f, q), C.minimum_stack(stack)) ==
    B.nat64(Nat.add(minimum_field_natural(f, n), r)) : Maybe<&2, B.Number64>}
def minimum_field_combined_stack_nat64_exact(f, n, r, q, stack, measured, parent):
  %Equal.sym(Maybe<&2, B.Number64>, C.minimum_field(f, q), B.nat64(minimum_field_natural(f, n)), minimum_field_nat64_exact(f, n, q, measured)) :
    {C.sum_optional(_, C.minimum_stack(stack)) == B.nat64(Nat.add(minimum_field_natural(f, n), r)) : Maybe<&2, B.Number64>}
  %Equal.sym(Maybe<&2, B.Number64>, C.minimum_stack(stack), B.nat64(r), parent) :
    {C.sum_optional(B.nat64(minimum_field_natural(f, n)), _) == B.nat64(Nat.add(minimum_field_natural(f, n), r)) : Maybe<&2, B.Number64>}
  A.sum_optional_nat64_exact(minimum_field_natural(f, n), r)

# Direct application to actual bounds: the compound minimum does not
# need a hypothesis that its u64 conversion was accepted.
law check_minimum_field_combined_stack_by_limits_nat:
  for +f: C.Purpose
  for +n: Nat
  for +r: Nat
  for +c: Nat
  for +t: Nat
  for +q: B.Number64
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  for measured: {B.nat64(n) == Some{q} : Maybe<&2, B.Number64>}
  for parent: {C.minimum_stack(stack) == B.nat64(r) : Maybe<&2, B.Number64>}
  for +mc: {B.nat64(c) == Some{body} : Maybe<&2, B.Number64>}
  for +mt: {B.nat64(t) == Some{ceiling} : Maybe<&2, B.Number64>}
  for +lc: {Nat.is_le(Nat.add(minimum_field_natural(f, n), r), c) == True{} : Bool}
  for lt: {Nat.is_le(Nat.add(minimum_field_natural(f, n), r), t) == True{} : Bool}
  {C.check(C.sum_optional(C.minimum_field(f, q), C.minimum_stack(stack)), body, ceiling) == C.Fits{} : C.Check}
def check_minimum_field_combined_stack_by_limits_nat(f, n, r, c, t, q, stack, body, ceiling, measured, parent, mc, mt, lc, lt):
  %Equal.sym(Maybe<&2, B.Number64>,
    C.sum_optional(C.minimum_field(f, q), C.minimum_stack(stack)),
    B.nat64(Nat.add(minimum_field_natural(f, n), r)),
    minimum_field_combined_stack_nat64_exact(f, n, r, q, stack, measured, parent)) :
    {C.check(_, body, ceiling) == C.Fits{} : C.Check}
  O.check_natural_bounded(Nat.add(minimum_field_natural(f, n), r), c, t, body, ceiling, mc, mt, lc, lt)
