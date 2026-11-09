# Euclidean uniqueness for ordinary unbounded natural arithmetic. There is no
# division algorithm or assumed uniqueness fact in the premises. The proof
# cancels one whole divisor from both positive quotients, and derives a strict
# remainder contradiction when exactly one quotient reaches zero.
import Base
import ../contract/Logic.bend as L
import ../proof/Foundations.bend as F
import ./Int64Proofs.bend as A
import ./Int64NatProduct.bend as P

law zero_quotient_value:
  for +d: Nat
  for +r: Nat
  {Nat.add(Nat.mul(d, 0n), r) == r : Nat}
def zero_quotient_value(d, r):
  Equal.cong(Nat, Nat, value => Nat.add(value, r), Nat.mul(d, 0n), 0n, P.mul_zero_right(d))

law successor_quotient_expansion:
  for +d: Nat
  for +q: Nat
  for +r: Nat
  {Nat.add(Nat.mul(d, 1n+q), r) == Nat.add(d, Nat.add(Nat.mul(d, q), r)) : Nat}
def successor_quotient_expansion(d, q, r):
  Equal.trans(Nat, Nat.add(Nat.mul(d, 1n+q), r), Nat.add(Nat.add(d, Nat.mul(d, q)), r),
    Nat.add(d, Nat.add(Nat.mul(d, q), r)),
    Equal.cong(Nat, Nat, value => Nat.add(value, r), Nat.mul(d, 1n+q), Nat.add(d, Nat.mul(d, q)), P.mul_successor_right(d, q)),
    A.add_associative(d, Nat.mul(d, q), r))

law sum_is_never_strictly_below_its_first_summand:
  for +prefix: Nat
  for +tail: Nat
  {Nat.is_lt(Nat.add(prefix, tail), prefix) == False{} : Bool}
def sum_is_never_strictly_below_its_first_summand(prefix, tail):
  match prefix tail:
    case 0n 0n: {==}
    case 0n 1n+rest: {==}
    case 1n+rest tail: sum_is_never_strictly_below_its_first_summand(rest, tail)

law a_strict_remainder_cannot_contain_a_whole_divisor:
  for +d: Nat
  for +r: Nat
  for +tail: Nat
  for small: {Nat.is_lt(r, d) == True{} : Bool}
  for same: {r == Nat.add(d, tail) : Nat}
  Empty
def a_strict_remainder_cannot_contain_a_whole_divisor(d, r, tail, small, same):
  F.absurd_boolean(Empty,
    Equal.trans(Bool, False{}, Nat.is_lt(Nat.add(d, tail), d), True{},
      Equal.sym(Bool, Nat.is_lt(Nat.add(d, tail), d), False{}, sum_is_never_strictly_below_its_first_summand(d, tail)),
      Equal.trans(Bool, Nat.is_lt(Nat.add(d, tail), d), Nat.is_lt(r, d), True{},
        Equal.cong(Nat, Bool, value => Nat.is_lt(value, d), Nat.add(d, tail), r,
          Equal.sym(Nat, r, Nat.add(d, tail), same)), small)))

law cancel_common_divisor_from_positive_quotients:
  for +d: Nat
  for +q: Nat
  for +r: Nat
  for +q2: Nat
  for +r2: Nat
  for same: {Nat.add(Nat.mul(d, 1n+q), r) == Nat.add(Nat.mul(d, 1n+q2), r2) : Nat}
  {Nat.add(Nat.mul(d, q), r) == Nat.add(Nat.mul(d, q2), r2) : Nat}
def cancel_common_divisor_from_positive_quotients(d, q, r, q2, r2, same):
  A.add_left_cancel(d, Nat.add(Nat.mul(d, q), r), Nat.add(Nat.mul(d, q2), r2),
    Equal.trans(Nat, Nat.add(d, Nat.add(Nat.mul(d, q), r)), Nat.add(Nat.mul(d, 1n+q), r),
      Nat.add(d, Nat.add(Nat.mul(d, q2), r2)),
      Equal.sym(Nat, Nat.add(Nat.mul(d, 1n+q), r), Nat.add(d, Nat.add(Nat.mul(d, q), r)), successor_quotient_expansion(d, q, r)),
      Equal.trans(Nat, Nat.add(Nat.mul(d, 1n+q), r), Nat.add(Nat.mul(d, 1n+q2), r2), Nat.add(d, Nat.add(Nat.mul(d, q2), r2)),
        same, successor_quotient_expansion(d, q2, r2))))

def lift_quotient_equality(-q: Nat, -r: Nat, -q2: Nat, -r2: Nat,
  pair: L.E<{q == q2 : Nat}, {r == r2 : Nat}>) -> L.E<{1n+q == 1n+q2 : Nat}, {r == r2 : Nat}>:
  L.Both{quotient, remainder} = pair
  L.Both{Equal.cong(Nat, Nat, value => 1n+value, q, q2, quotient), remainder}

# The strict remainder bounds already entail d>0; this stronger core theorem
# needs no separate positivity argument. Its only shared-value premise is the
# literal multiplication/addition equality of the two representations.
law strict_euclidean_representations_are_unique:
  for +d: Nat
  for +q: Nat
  for +r: Nat
  for +q2: Nat
  for +r2: Nat
  for small: {Nat.is_lt(r, d) == True{} : Bool}
  for small2: {Nat.is_lt(r2, d) == True{} : Bool}
  for same: {Nat.add(Nat.mul(d, q), r) == Nat.add(Nat.mul(d, q2), r2) : Nat}
  L.E<{q == q2 : Nat}, {r == r2 : Nat}>
def strict_euclidean_representations_are_unique(d, q, r, q2, r2, small, small2, same):
  match q q2:
    case 0n 0n:
      L.Both{{==}, Equal.trans(Nat, r, Nat.add(Nat.mul(d, 0n), r), r2,
        Equal.sym(Nat, Nat.add(Nat.mul(d, 0n), r), r, zero_quotient_value(d, r)),
        Equal.trans(Nat, Nat.add(Nat.mul(d, 0n), r), Nat.add(Nat.mul(d, 0n), r2), r2, same, zero_quotient_value(d, r2)))}
    case 0n 1n+q2:
      L.ex_false(L.E<{0n == 1n+q2 : Nat}, {r == r2 : Nat}>,
        a_strict_remainder_cannot_contain_a_whole_divisor(d, r, Nat.add(Nat.mul(d, q2), r2), small,
          Equal.trans(Nat, r, Nat.add(Nat.mul(d, 0n), r), Nat.add(d, Nat.add(Nat.mul(d, q2), r2)),
            Equal.sym(Nat, Nat.add(Nat.mul(d, 0n), r), r, zero_quotient_value(d, r)),
            Equal.trans(Nat, Nat.add(Nat.mul(d, 0n), r), Nat.add(Nat.mul(d, 1n+q2), r2), Nat.add(d, Nat.add(Nat.mul(d, q2), r2)),
              same, successor_quotient_expansion(d, q2, r2)))))
    case 1n+q 0n:
      L.ex_false(L.E<{1n+q == 0n : Nat}, {r == r2 : Nat}>,
        a_strict_remainder_cannot_contain_a_whole_divisor(d, r2, Nat.add(Nat.mul(d, q), r), small2,
          Equal.trans(Nat, r2, Nat.add(Nat.mul(d, 0n), r2), Nat.add(d, Nat.add(Nat.mul(d, q), r)),
            Equal.sym(Nat, Nat.add(Nat.mul(d, 0n), r2), r2, zero_quotient_value(d, r2)),
            Equal.trans(Nat, Nat.add(Nat.mul(d, 0n), r2), Nat.add(Nat.mul(d, 1n+q), r), Nat.add(d, Nat.add(Nat.mul(d, q), r)),
              Equal.sym(Nat, Nat.add(Nat.mul(d, 1n+q), r), Nat.add(Nat.mul(d, 0n), r2), same), successor_quotient_expansion(d, q, r)))))
    case 1n+ +q 1n+ +q2:
      lift_quotient_equality(q, r, q2, r2,
        strict_euclidean_representations_are_unique(d, q, r, q2, r2, small, small2,
          cancel_common_divisor_from_positive_quotients(d, q, r, q2, r2, same)))

law natural_euclidean_quotient_and_remainder_are_unique:
  for +a: Nat
  for +d: Nat
  for +q: Nat
  for +r: Nat
  for +q2: Nat
  for +r2: Nat
  for positive: {Nat.is_lt(0n, d) == True{} : Bool}
  for first: {a == Nat.add(Nat.mul(d, q), r) : Nat}
  for r_small: {Nat.is_lt(r, d) == True{} : Bool}
  for second: {a == Nat.add(Nat.mul(d, q2), r2) : Nat}
  for r2_small: {Nat.is_lt(r2, d) == True{} : Bool}
  L.E<{q == q2 : Nat}, {r == r2 : Nat}>
def natural_euclidean_quotient_and_remainder_are_unique(a, d, q, r, q2, r2, positive, first, r_small, second, r2_small):
  strict_euclidean_representations_are_unique(d, q, r, q2, r2, r_small, r2_small,
    Equal.trans(Nat, Nat.add(Nat.mul(d, q), r), a, Nat.add(Nat.mul(d, q2), r2),
      Equal.sym(Nat, a, Nat.add(Nat.mul(d, q), r), first), second))

law natural_euclidean_quotient_and_remainder_are_unique_right_product:
  for +a: Nat
  for +d: Nat
  for +q: Nat
  for +r: Nat
  for +q2: Nat
  for +r2: Nat
  for positive: {Nat.is_lt(0n, d) == True{} : Bool}
  for first: {a == Nat.add(Nat.mul(q, d), r) : Nat}
  for r_small: {Nat.is_lt(r, d) == True{} : Bool}
  for second: {a == Nat.add(Nat.mul(q2, d), r2) : Nat}
  for r2_small: {Nat.is_lt(r2, d) == True{} : Bool}
  L.E<{q == q2 : Nat}, {r == r2 : Nat}>
def natural_euclidean_quotient_and_remainder_are_unique_right_product(a, d, q, r, q2, r2, positive, first, r_small, second, r2_small):
  natural_euclidean_quotient_and_remainder_are_unique(a, d, q, r, q2, r2, positive,
    Equal.trans(Nat, a, Nat.add(Nat.mul(q, d), r), Nat.add(Nat.mul(d, q), r), first,
      Equal.cong(Nat, Nat, value => Nat.add(value, r), Nat.mul(q, d), Nat.mul(d, q), P.mul_commutative(q, d))), r_small,
    Equal.trans(Nat, a, Nat.add(Nat.mul(q2, d), r2), Nat.add(Nat.mul(d, q2), r2), second,
      Equal.cong(Nat, Nat, value => Nat.add(value, r2), Nat.mul(q2, d), Nat.mul(d, q2), P.mul_commutative(q2, d))), r2_small)
