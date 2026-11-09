# Reuse complete scalar addition through independent integer equality.
import Base
import ./AggregateModel.bend as M
import ./Value.bend as V
import ./Int64Proofs.bend as A
import ./Int64IntegerProduct.bend as P
import ./Int64IntegerAddition.bend as Add

law sum_equation_to_product_equality:
  for +a: A.Integer
  for +b: A.Integer
  for +r: A.Integer
  for exact: A.IntegerSum(a,b,r)
  P.IntegerEqual(Add.add(a,b),r)
def sum_equation_to_product_equality(a,b,r,exact):
  match a b r:
    case A.Integer{ap,an} A.Integer{bp,bn} A.Integer{rp,rn}: exact

law product_equality_to_sum_equation:
  for +a: A.Integer
  for +b: A.Integer
  for +r: A.Integer
  for exact: P.IntegerEqual(Add.add(a,b),r)
  A.IntegerSum(a,b,r)
def product_equality_to_sum_equation(a,b,r,exact):
  match a b r:
    case A.Integer{ap,an} A.Integer{bp,bn} A.Integer{rp,rn}: exact

law added_word_has_exact_mathematical_sum:
  for +x: V.Int64
  for +tail: V.Int64
  for +expected_tail: A.Integer
  for +r: V.Int64
  for tail_exact: M.EqualInteger(A.integer(tail),expected_tail)
  for added: A.IntegerSum(A.integer(x),A.integer(tail),A.integer(r))
  M.EqualInteger(A.integer(r),Add.add(A.integer(x),expected_tail))
def added_word_has_exact_mathematical_sum(x,tail,expected_tail,r,tail_exact,added):
  M.equality_from_integer_product_model(A.integer(r),Add.add(A.integer(x),expected_tail),
    P.integer_equal_transitive(A.integer(r),Add.add(A.integer(x),A.integer(tail)),Add.add(A.integer(x),expected_tail),
      P.integer_equal_symmetric(Add.add(A.integer(x),A.integer(tail)),A.integer(r),sum_equation_to_product_equality(A.integer(x),A.integer(tail),A.integer(r),added)),
      Add.addition_respects_integer_equalities(A.integer(x),A.integer(tail),A.integer(x),expected_tail,P.integer_equal_reflexive(A.integer(x)),M.equality_to_integer_product_model(A.integer(tail),expected_tail,tail_exact))))

law mathematical_sum_candidate_is_scalar_addition_candidate:
  for +x: V.Int64
  for +tail: V.Int64
  for +expected_tail: A.Integer
  for +r: V.Int64
  for tail_exact: M.EqualInteger(A.integer(tail),expected_tail)
  for candidate: M.EqualInteger(A.integer(r),Add.add(A.integer(x),expected_tail))
  A.IntegerSum(A.integer(x),A.integer(tail),A.integer(r))
def mathematical_sum_candidate_is_scalar_addition_candidate(x,tail,expected_tail,r,tail_exact,candidate):
  product_equality_to_sum_equation(A.integer(x),A.integer(tail),A.integer(r),
    P.integer_equal_transitive(Add.add(A.integer(x),A.integer(tail)),Add.add(A.integer(x),expected_tail),A.integer(r),
      Add.addition_respects_integer_equalities(A.integer(x),A.integer(tail),A.integer(x),expected_tail,P.integer_equal_reflexive(A.integer(x)),M.equality_to_integer_product_model(A.integer(tail),expected_tail,tail_exact)),
      P.integer_equal_symmetric(A.integer(r),Add.add(A.integer(x),expected_tail),M.equality_to_integer_product_model(A.integer(r),Add.add(A.integer(x),expected_tail),candidate))))
