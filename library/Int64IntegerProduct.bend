# Integers are equivalence classes of Nat differences. This specification uses
# ordinary distributive multiplication, independently of shift-and-add.
import Base
import ./Int64NatProduct.bend as N
import ../proof/Foundations.bend as F
import ./Int64Proofs.bend as A

def IntegerEqual(a: A.Integer,b: A.Integer) -> Type:
  A.Integer{ap,an}=a
  A.Integer{bp,bn}=b
  {Nat.add(ap,bn) == Nat.add(bp,an) : Nat}

def product(+a: A.Integer,+b: A.Integer) -> A.Integer:
  A.Integer{+ap,+an}=a
  A.Integer{+bp,+bn}=b
  A.Integer{Nat.add(Nat.mul(ap,bp),Nat.mul(an,bn)),Nat.add(Nat.mul(ap,bn),Nat.mul(an,bp))}

def sign_integer(negative: Bool,+magnitude: Nat) -> A.Integer:
  match negative:
    case False{}: A.Integer{magnitude,0n}
    case True{}: A.Integer{0n,magnitude}

law integer_equal_reflexive:
  for +a: A.Integer
  IntegerEqual(a,a)
def integer_equal_reflexive(a):
  match a:
    case A.Integer{p,n}: {==}

law integer_equal_symmetric:
  for +a: A.Integer
  for +b: A.Integer
  for same: IntegerEqual(a,b)
  IntegerEqual(b,a)
def integer_equal_symmetric(a,b,same):
  match a b:
    case A.Integer{+ap,+an} A.Integer{+bp,+bn}:
      Equal.sym(Nat,Nat.add(ap,bn),Nat.add(bp,an),same)

law exchange_tail:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a,b),c) == Nat.add(Nat.add(a,c),b) : Nat}
def exchange_tail(a,b,c):
  Equal.trans(Nat,Nat.add(Nat.add(a,b),c),Nat.add(a,Nat.add(b,c)),Nat.add(Nat.add(a,c),b),A.add_associative(a,b,c),
    Equal.trans(Nat,Nat.add(a,Nat.add(b,c)),Nat.add(a,Nat.add(c,b)),Nat.add(Nat.add(a,c),b),
      Equal.cong(Nat,Nat,n => Nat.add(a,n),Nat.add(b,c),Nat.add(c,b),A.add_commutative(b,c)),
      Equal.sym(Nat,Nat.add(Nat.add(a,c),b),Nat.add(a,Nat.add(c,b)),A.add_associative(a,c,b))))

law integer_equal_transitive:
  for +a: A.Integer
  for +b: A.Integer
  for +c: A.Integer
  for ab: IntegerEqual(a,b)
  for bc: IntegerEqual(b,c)
  IntegerEqual(a,c)
def integer_equal_transitive(a,b,c,ab,bc):
  match a b c:
    case A.Integer{+ap,+an} A.Integer{+bp,+bn} A.Integer{+cp,+cn}:
      A.add_right_cancel(bn,Nat.add(ap,cn),Nat.add(cp,an),
        Equal.trans(Nat,Nat.add(Nat.add(ap,cn),bn),Nat.add(Nat.add(ap,bn),cn),Nat.add(Nat.add(cp,an),bn),exchange_tail(ap,cn,bn),
          Equal.trans(Nat,Nat.add(Nat.add(ap,bn),cn),Nat.add(Nat.add(bp,an),cn),Nat.add(Nat.add(cp,an),bn),
            Equal.cong(Nat,Nat,n => Nat.add(n,cn),Nat.add(ap,bn),Nat.add(bp,an),ab),
            Equal.trans(Nat,Nat.add(Nat.add(bp,an),cn),Nat.add(Nat.add(bp,cn),an),Nat.add(Nat.add(cp,an),bn),exchange_tail(bp,an,cn),
              Equal.trans(Nat,Nat.add(Nat.add(bp,cn),an),Nat.add(Nat.add(cp,bn),an),Nat.add(Nat.add(cp,an),bn),
                Equal.cong(Nat,Nat,n => Nat.add(n,an),Nat.add(bp,cn),Nat.add(cp,bn),bc),exchange_tail(cp,bn,an))))))

law cross_sum:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {Nat.add(Nat.add(a,b),Nat.add(c,d)) == Nat.add(Nat.add(a,d),Nat.add(c,b)) : Nat}
def cross_sum(a,b,c,d):
  Equal.trans(Nat,Nat.add(Nat.add(a,b),Nat.add(c,d)),Nat.add(Nat.add(a,b),Nat.add(d,c)),Nat.add(Nat.add(a,d),Nat.add(c,b)),
    Equal.cong(Nat,Nat,n => Nat.add(Nat.add(a,b),n),Nat.add(c,d),Nat.add(d,c),A.add_commutative(c,d)),
    Equal.trans(Nat,Nat.add(Nat.add(a,b),Nat.add(d,c)),Nat.add(Nat.add(a,d),Nat.add(b,c)),Nat.add(Nat.add(a,d),Nat.add(c,b)),N.four_sum(a,b,d,c),
      Equal.cong(Nat,Nat,n => Nat.add(Nat.add(a,d),n),Nat.add(b,c),Nat.add(c,b),A.add_commutative(b,c))))

law multiply_sum_equality:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for +factor: Nat
  for same: {Nat.add(a,b) == Nat.add(c,d) : Nat}
  {Nat.add(Nat.mul(a,factor),Nat.mul(b,factor)) == Nat.add(Nat.mul(c,factor),Nat.mul(d,factor)) : Nat}
def multiply_sum_equality(a,b,c,d,factor,same):
  Equal.trans(Nat,Nat.add(Nat.mul(a,factor),Nat.mul(b,factor)),Nat.mul(Nat.add(a,b),factor),Nat.add(Nat.mul(c,factor),Nat.mul(d,factor)),
    Equal.sym(Nat,Nat.mul(Nat.add(a,b),factor),Nat.add(Nat.mul(a,factor),Nat.mul(b,factor)),N.mul_add_left(a,b,factor)),
    Equal.trans(Nat,Nat.mul(Nat.add(a,b),factor),Nat.mul(Nat.add(c,d),factor),Nat.add(Nat.mul(c,factor),Nat.mul(d,factor)),
      Equal.cong(Nat,Nat,n => Nat.mul(n,factor),Nat.add(a,b),Nat.add(c,d),same),N.mul_add_left(c,d,factor)))

# The source equality is direct equality data and can be copied into its two
# independent distributive consequences (positive and negative multiplier).
law product_equality_terms:
  for +ap: Nat
  for +an: Nat
  for +op: Nat
  for +on: Nat
  for +bp: Nat
  for +bn: Nat
  for +same: {Nat.add(ap,on) == Nat.add(op,an) : Nat}
  {Nat.add(Nat.add(Nat.mul(ap,bp),Nat.mul(an,bn)),Nat.add(Nat.mul(op,bn),Nat.mul(on,bp))) == Nat.add(Nat.add(Nat.mul(op,bp),Nat.mul(on,bn)),Nat.add(Nat.mul(ap,bn),Nat.mul(an,bp))) : Nat}
def product_equality_terms(ap,an,op,on,bp,bn,same):
  Equal.trans(Nat,Nat.add(Nat.add(Nat.mul(ap,bp),Nat.mul(an,bn)),Nat.add(Nat.mul(op,bn),Nat.mul(on,bp))),Nat.add(Nat.add(Nat.mul(ap,bp),Nat.mul(on,bp)),Nat.add(Nat.mul(op,bn),Nat.mul(an,bn))),Nat.add(Nat.add(Nat.mul(op,bp),Nat.mul(on,bn)),Nat.add(Nat.mul(ap,bn),Nat.mul(an,bp))),
    cross_sum(Nat.mul(ap,bp),Nat.mul(an,bn),Nat.mul(op,bn),Nat.mul(on,bp)),
    Equal.trans(Nat,Nat.add(Nat.add(Nat.mul(ap,bp),Nat.mul(on,bp)),Nat.add(Nat.mul(op,bn),Nat.mul(an,bn))),Nat.add(Nat.add(Nat.mul(op,bp),Nat.mul(an,bp)),Nat.add(Nat.mul(op,bn),Nat.mul(an,bn))),Nat.add(Nat.add(Nat.mul(op,bp),Nat.mul(on,bn)),Nat.add(Nat.mul(ap,bn),Nat.mul(an,bp))),
      Equal.cong(Nat,Nat,n => Nat.add(n,Nat.add(Nat.mul(op,bn),Nat.mul(an,bn))),Nat.add(Nat.mul(ap,bp),Nat.mul(on,bp)),Nat.add(Nat.mul(op,bp),Nat.mul(an,bp)),multiply_sum_equality(ap,on,op,an,bp,same)),
      Equal.trans(Nat,Nat.add(Nat.add(Nat.mul(op,bp),Nat.mul(an,bp)),Nat.add(Nat.mul(op,bn),Nat.mul(an,bn))),Nat.add(Nat.add(Nat.mul(op,bp),Nat.mul(an,bp)),Nat.add(Nat.mul(ap,bn),Nat.mul(on,bn))),Nat.add(Nat.add(Nat.mul(op,bp),Nat.mul(on,bn)),Nat.add(Nat.mul(ap,bn),Nat.mul(an,bp))),
        Equal.cong(Nat,Nat,n => Nat.add(Nat.add(Nat.mul(op,bp),Nat.mul(an,bp)),n),Nat.add(Nat.mul(op,bn),Nat.mul(an,bn)),Nat.add(Nat.mul(ap,bn),Nat.mul(on,bn)),multiply_sum_equality(op,an,ap,on,bn,Equal.sym(Nat,Nat.add(ap,on),Nat.add(op,an),same))),
        cross_sum(Nat.mul(op,bp),Nat.mul(an,bp),Nat.mul(ap,bn),Nat.mul(on,bn)))))

law product_respects_left_equality:
  for +a: A.Integer
  for +other: A.Integer
  for +b: A.Integer
  for same: IntegerEqual(a,other)
  IntegerEqual(product(a,b),product(other,b))
def product_respects_left_equality(a,other,b,same):
  match a other b:
    case A.Integer{+ap,+an} A.Integer{+op,+on} A.Integer{+bp,+bn}:
      product_equality_terms(ap,an,op,on,bp,bn,same)

law sum_congruence:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for ac: {a == c : Nat}
  for bd: {b == d : Nat}
  {Nat.add(a,b) == Nat.add(c,d) : Nat}
def sum_congruence(a,b,c,d,ac,bd):
  Equal.trans(Nat,Nat.add(a,b),Nat.add(c,b),Nat.add(c,d),Equal.cong(Nat,Nat,n => Nat.add(n,b),a,c,ac),Equal.cong(Nat,Nat,n => Nat.add(c,n),b,d,bd))

law pair_congruence:
  for +ap: Nat
  for +an: Nat
  for +bp: Nat
  for +bn: Nat
  for positive: {ap == bp : Nat}
  for negative: {an == bn : Nat}
  {A.Integer{ap,an} == A.Integer{bp,bn} : A.Integer}
def pair_congruence(ap,an,bp,bn,positive,negative):
  Equal.trans(A.Integer,A.Integer{ap,an},A.Integer{bp,an},A.Integer{bp,bn},
    Equal.cong(Nat,A.Integer,n => A.Integer{n,an},ap,bp,positive),Equal.cong(Nat,A.Integer,n => A.Integer{bp,n},an,bn,negative))

law product_commutes:
  for +a: A.Integer
  for +b: A.Integer
  {product(a,b) == product(b,a) : A.Integer}
def product_commutes(a,b):
  match a b:
    case A.Integer{+ap,+an} A.Integer{+bp,+bn}:
      pair_congruence(Nat.add(Nat.mul(ap,bp),Nat.mul(an,bn)),Nat.add(Nat.mul(ap,bn),Nat.mul(an,bp)),Nat.add(Nat.mul(bp,ap),Nat.mul(bn,an)),Nat.add(Nat.mul(bp,an),Nat.mul(bn,ap)),
        sum_congruence(Nat.mul(ap,bp),Nat.mul(an,bn),Nat.mul(bp,ap),Nat.mul(bn,an),N.mul_commutative(ap,bp),N.mul_commutative(an,bn)),
        Equal.trans(Nat,Nat.add(Nat.mul(ap,bn),Nat.mul(an,bp)),Nat.add(Nat.mul(an,bp),Nat.mul(ap,bn)),Nat.add(Nat.mul(bp,an),Nat.mul(bn,ap)),A.add_commutative(Nat.mul(ap,bn),Nat.mul(an,bp)),
          sum_congruence(Nat.mul(an,bp),Nat.mul(ap,bn),Nat.mul(bp,an),Nat.mul(bn,ap),N.mul_commutative(an,bp),N.mul_commutative(ap,bn))))

law product_respects_right_equality:
  for +a: A.Integer
  for +b: A.Integer
  for +other: A.Integer
  for same: IntegerEqual(b,other)
  IntegerEqual(product(a,b),product(a,other))
def product_respects_right_equality(a,b,other,same):
  %Equal.sym(A.Integer,product(a,b),product(b,a),product_commutes(a,b)) : IntegerEqual(_,product(a,other))
  %Equal.sym(A.Integer,product(a,other),product(other,a),product_commutes(a,other)) : IntegerEqual(product(b,a),_)
  product_respects_left_equality(b,other,a,same)

law product_respects_equalities:
  for +a: A.Integer
  for +b: A.Integer
  for +c: A.Integer
  for +d: A.Integer
  for ac: IntegerEqual(a,c)
  for bd: IntegerEqual(b,d)
  IntegerEqual(product(a,b),product(c,d))
def product_respects_equalities(a,b,c,d,ac,bd):
  integer_equal_transitive(product(a,b),product(c,b),product(c,d),product_respects_left_equality(a,c,b,ac),product_respects_right_equality(c,b,d,bd))

law product_of_signed_magnitudes:
  for +sa: Bool
  for +sb: Bool
  for +a: Nat
  for +b: Nat
  {product(sign_integer(sa,a),sign_integer(sb,b)) == sign_integer(Bool.xor(sa,sb),Nat.mul(a,b)) : A.Integer}
def product_of_signed_magnitudes(sa,sb,a,b):
  match sa sb:
    case False{} False{}:
      pair_congruence(Nat.add(Nat.mul(a,b),0n),Nat.add(Nat.mul(a,0n),0n),Nat.mul(a,b),0n,A.add_zero_right(Nat.mul(a,b)),
        Equal.trans(Nat,Nat.add(Nat.mul(a,0n),0n),Nat.mul(a,0n),0n,A.add_zero_right(Nat.mul(a,0n)),N.mul_zero_right(a)))
    case False{} True{}:
      pair_congruence(Nat.add(Nat.mul(a,0n),0n),Nat.add(Nat.mul(a,b),0n),0n,Nat.mul(a,b),
        Equal.trans(Nat,Nat.add(Nat.mul(a,0n),0n),Nat.mul(a,0n),0n,A.add_zero_right(Nat.mul(a,0n)),N.mul_zero_right(a)),A.add_zero_right(Nat.mul(a,b)))
    case True{} False{}:
      pair_congruence(Nat.mul(a,0n),Nat.mul(a,b),0n,Nat.mul(a,b),N.mul_zero_right(a),{==})
    case True{} True{}:
      pair_congruence(Nat.mul(a,b),Nat.mul(a,0n),Nat.mul(a,b),0n,{==},N.mul_zero_right(a))

law product_of_signed_magnitudes_reversed:
  for +sa: Bool
  for +sb: Bool
  for +a: Nat
  for +b: Nat
  {product(sign_integer(sa,a),sign_integer(sb,b)) == sign_integer(Bool.xor(sa,sb),Nat.mul(b,a)) : A.Integer}
def product_of_signed_magnitudes_reversed(sa,sb,a,b):
  Equal.trans(A.Integer,product(sign_integer(sa,a),sign_integer(sb,b)),sign_integer(Bool.xor(sa,sb),Nat.mul(a,b)),sign_integer(Bool.xor(sa,sb),Nat.mul(b,a)),product_of_signed_magnitudes(sa,sb,a,b),
    Equal.cong(Nat,A.Integer,n => sign_integer(Bool.xor(sa,sb),n),Nat.mul(a,b),Nat.mul(b,a),N.mul_commutative(a,b)))

law zero_sum_makes_equal:
  for +a: Nat
  for +b: Nat
  for zero: {Nat.add(a,b) == 0n : Nat}
  {a == b : Nat}
def zero_sum_makes_equal(a,b,zero):
  match a b:
    case 0n 0n: {==}
    case 0n 1n+p:
      F.absurd_boolean({0n == 1n+p : Nat},Equal.cong(Nat,Bool,n => Nat.is_eq(n,0n),1n+p,0n,zero))
    case 1n+p _:
      F.absurd_boolean({1n+p == b : Nat},Equal.cong(Nat,Bool,n => Nat.is_eq(n,0n),1n+Nat.add(p,b),0n,zero))

# Absolute magnitude is unique even if a signed-zero representation chooses a
# different sign. No positivity or matching-sign hypothesis is needed.
law equal_signed_integers_have_equal_magnitudes:
  for +sa: Bool
  for +sb: Bool
  for +a: Nat
  for +b: Nat
  for same: IntegerEqual(sign_integer(sa,a),sign_integer(sb,b))
  {a == b : Nat}
def equal_signed_integers_have_equal_magnitudes(sa,sb,a,b,same):
  match sa sb:
    case False{} False{}: A.add_right_cancel(0n,a,b,same)
    case False{} True{}: zero_sum_makes_equal(a,b,same)
    case True{} False{}:
      Equal.sym(Nat,b,a,zero_sum_makes_equal(b,a,Equal.sym(Nat,0n,Nat.add(b,a),same)))
    case True{} True{}: Equal.sym(Nat,b,a,same)
