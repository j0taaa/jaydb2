# Ordinary addition in the independent Nat-difference integer model.
import Base
import ./Int64Proofs.bend as A
import ./Int64NatProduct.bend as N
import ./Int64IntegerProduct.bend as P

def add(a: A.Integer, b: A.Integer) -> A.Integer:
  A.Integer{ap, an} = a
  A.Integer{bp, bn} = b
  A.Integer{Nat.add(ap, bp), Nat.add(an, bn)}

law addition_respects_integer_equalities:
  for +a: A.Integer
  for +b: A.Integer
  for +c: A.Integer
  for +d: A.Integer
  for ac: P.IntegerEqual(a, c)
  for bd: P.IntegerEqual(b, d)
  P.IntegerEqual(add(a, b), add(c, d))
def addition_respects_integer_equalities(a, b, c, d, ac, bd):
  match a b c d:
    case A.Integer{+ap, +an} A.Integer{+bp, +bn} A.Integer{+cp, +cn} A.Integer{+dp, +dn}:
      Equal.trans(Nat, Nat.add(Nat.add(ap, bp), Nat.add(cn, dn)), Nat.add(Nat.add(ap, cn), Nat.add(bp, dn)), Nat.add(Nat.add(cp, dp), Nat.add(an, bn)),
        N.four_sum(ap, bp, cn, dn),
        Equal.trans(Nat, Nat.add(Nat.add(ap, cn), Nat.add(bp, dn)), Nat.add(Nat.add(cp, an), Nat.add(dp, bn)), Nat.add(Nat.add(cp, dp), Nat.add(an, bn)),
          P.sum_congruence(Nat.add(ap, cn), Nat.add(bp, dn), Nat.add(cp, an), Nat.add(dp, bn), ac, bd), N.four_sum(cp, an, dp, bn)))

law same_sign_adds_magnitudes:
  for sign: Bool
  for +a: Nat
  for +b: Nat
  {add(P.sign_integer(sign, a), P.sign_integer(sign, b)) == P.sign_integer(sign, Nat.add(a, b)) : A.Integer}
def same_sign_adds_magnitudes(sign, a, b):
  match sign:
    case False{}: {==}
    case True{}: {==}
