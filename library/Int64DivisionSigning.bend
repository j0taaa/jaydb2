# The actual signed_division postprocessor preserves complete Euclidean meaning.
# Its unsigned equations and bound are derived by the separate restoring-loop
# theorem; they are not premises of the eventual public divmod theorem.
import Base
import ../contract/Logic.bend as L
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ./Int64IntegerProduct.bend as P
import ./Int64ProductInterpretation.bend as Product
import ./Int64SignedMagnitude.bend as Signed
import ./Int64DivisionUnique.bend as Unique
import ./Int64RemainderRange.bend as Range
import ./Int64DivisionEquation.bend as Equation
import ./Int64DivisionSpec.bend as S

# Reopen only a named pure theorem, then use the same actual DATA result
# equality. No captured arbitrary certificate or invariant is duplicated.
def chosen_quotient_is_correct(+negative: Bool, +uq: V.Int64, +result: Maybe<&2, V.Int64>,
  actual: {I.signed(negative, uq) == result : Maybe<&2, V.Int64>}) -> Signed.SignedResult(negative, uq, result):
  %actual : Signed.SignedResult(negative, uq, _)
  Signed.actual_signed_is_integer_magnitude(negative, uq)

law signed_remainder_has_original_unsigned_magnitude:
  for +negative: Bool
  for +ur: V.Int64
  for +b: V.Int64
  for proper: {I.unsigned_lt(ur, I.magnitude(b)) == True{} : Bool}
  {S.absolute(I.signed_word(negative, ur)) == A.unsigned(ur) : Nat}
def signed_remainder_has_original_unsigned_magnitude(negative, ur, b, proper):
  Product.candidate_magnitude(I.signed_word(negative, ur), negative, A.unsigned(ur), Range.actual_remainder_signing_has_exact_integer_value(negative, ur, b, proper))

def unsigned_equation_transfers_to_signed_results(+a: V.Int64, +b: V.Int64, +q: V.Int64, +r: V.Int64, +uq: V.Int64, +ur: V.Int64,
  equation: {S.absolute(a) == Nat.add(Nat.mul(S.absolute(b), A.unsigned(uq)), A.unsigned(ur)) : Nat},
  qmag: {S.absolute(q) == A.unsigned(uq) : Nat}, rmag: {S.absolute(r) == A.unsigned(ur) : Nat}) ->
  {S.absolute(a) == Nat.add(Nat.mul(S.absolute(b), S.absolute(q)), S.absolute(r)) : Nat}:
  Equal.trans(Nat, S.absolute(a), Nat.add(Nat.mul(S.absolute(b), A.unsigned(uq)), A.unsigned(ur)),
    Nat.add(Nat.mul(S.absolute(b), S.absolute(q)), S.absolute(r)), equation,
    Equal.trans(Nat, Nat.add(Nat.mul(S.absolute(b), A.unsigned(uq)), A.unsigned(ur)), Nat.add(Nat.mul(S.absolute(b), S.absolute(q)), A.unsigned(ur)),
      Nat.add(Nat.mul(S.absolute(b), S.absolute(q)), S.absolute(r)),
      Equal.cong(Nat, Nat, magnitude => Nat.add(Nat.mul(S.absolute(b), magnitude), A.unsigned(ur)), A.unsigned(uq), S.absolute(q),
        Equal.sym(Nat, S.absolute(q), A.unsigned(uq), qmag)),
      Equal.cong(Nat, Nat, magnitude => Nat.add(Nat.mul(S.absolute(b), S.absolute(q)), magnitude), A.unsigned(ur), S.absolute(r),
        Equal.sym(Nat, S.absolute(r), A.unsigned(ur), rmag))))

def accepted_quotient_sign(+a: V.Int64, +b: V.Int64, +uq: V.Int64, +q: V.Int64,
  actual: {I.signed(S.quotient_sign(a, b), uq) == Some{q} : Maybe<&2, V.Int64>},
  qmag: {S.absolute(q) == A.unsigned(uq) : Nat}) ->
  P.IntegerEqual(A.integer(q), P.sign_integer(S.quotient_sign(a, b), S.absolute(q))):
  %Equal.sym(Nat, S.absolute(q), A.unsigned(uq), qmag) : P.IntegerEqual(A.integer(q), P.sign_integer(S.quotient_sign(a, b), _))
  chosen_quotient_is_correct(S.quotient_sign(a, b), uq, Some{q}, actual)

def accepted_remainder_sign(+a: V.Int64, +b: V.Int64, +ur: V.Int64,
  proper: {I.unsigned_lt(ur, I.magnitude(b)) == True{} : Bool},
  rmag: {S.absolute(I.signed_word(I.negative(a), ur)) == A.unsigned(ur) : Nat}) ->
  P.IntegerEqual(A.integer(I.signed_word(I.negative(a), ur)), P.sign_integer(I.negative(a), S.absolute(I.signed_word(I.negative(a), ur)))):
  %Equal.sym(Nat, S.absolute(I.signed_word(I.negative(a), ur)), A.unsigned(ur), rmag) :
    P.IntegerEqual(A.integer(I.signed_word(I.negative(a), ur)), P.sign_integer(I.negative(a), _))
  Range.actual_remainder_signing_has_exact_integer_value(I.negative(a), ur, b, proper)

def accepted_unsigned_result_has_signed_meaning(+a: V.Int64, +b: V.Int64, +uq: V.Int64, +ur: V.Int64, +q: V.Int64,
  +actual: {I.signed(S.quotient_sign(a, b), uq) == Some{q} : Maybe<&2, V.Int64>},
  nonzero: {I.zero(b) == False{} : Bool},
  +equation: {S.absolute(a) == Nat.add(Nat.mul(S.absolute(b), A.unsigned(uq)), A.unsigned(ur)) : Nat},
  small: {Nat.is_lt(A.unsigned(ur), S.absolute(b)) == True{} : Bool},
  +proper: {I.unsigned_lt(ur, I.magnitude(b)) == True{} : Bool}) ->
  S.Meaning<a, b, q, I.signed_word(I.negative(a), ur)>:
  +qmag = Product.candidate_magnitude(q, S.quotient_sign(a, b), A.unsigned(uq), chosen_quotient_is_correct(S.quotient_sign(a, b), uq, Some{q}, actual))
  +rmag = signed_remainder_has_original_unsigned_magnitude(I.negative(a), ur, b, proper)
  S.Meaning{nonzero,
    unsigned_equation_transfers_to_signed_results(a, b, q, I.signed_word(I.negative(a), ur), uq, ur, equation, qmag, rmag),
    (Equal.trans(Bool, Nat.is_lt(S.absolute(I.signed_word(I.negative(a), ur)), S.absolute(b)), Nat.is_lt(A.unsigned(ur), S.absolute(b)), True{},
      Equal.cong(Nat, Bool, magnitude => Nat.is_lt(magnitude, S.absolute(b)), S.absolute(I.signed_word(I.negative(a), ur)), A.unsigned(ur), rmag), small)),
    accepted_quotient_sign(a, b, uq, q, actual, qmag), accepted_remainder_sign(a, b, ur, proper, rmag),
    Equation.signed_quotient_and_remainder_satisfy_the_integer_equation(a, b, q, I.signed_word(I.negative(a), ur), uq, ur, equation,
      chosen_quotient_is_correct(S.quotient_sign(a, b), uq, Some{q}, actual), Range.actual_remainder_signing_has_exact_integer_value(I.negative(a), ur, b, proper))}

def reject_from_unique_quotient(+a: V.Int64, +b: V.Int64, +uq: V.Int64, +ur: V.Int64, +q: V.Int64, +r: V.Int64,
  actual: {I.signed(S.quotient_sign(a, b), uq) == None{} : Maybe<&2, V.Int64>},
  quotient: P.IntegerEqual(A.integer(q), P.sign_integer(S.quotient_sign(a, b), S.absolute(q))),
  unique: L.E<{A.unsigned(uq) == S.absolute(q) : Nat}, {A.unsigned(ur) == S.absolute(r) : Nat}>) -> Empty:
  match unique:
    case L.Both{same_quotient, same_remainder}:
      chosen_quotient_is_correct(S.quotient_sign(a, b), uq, None{}, actual)(q,
        (%Equal.sym(Nat, A.unsigned(uq), S.absolute(q), same_quotient) : P.IntegerEqual(A.integer(q), P.sign_integer(S.quotient_sign(a, b), _))
          quotient))

def rejected_unsigned_result_excludes_signed_meaning(+a: V.Int64, +b: V.Int64, +uq: V.Int64, +ur: V.Int64,
  actual: {I.signed(S.quotient_sign(a, b), uq) == None{} : Maybe<&2, V.Int64>},
  equation: {S.absolute(a) == Nat.add(Nat.mul(S.absolute(b), A.unsigned(uq)), A.unsigned(ur)) : Nat},
  small: {Nat.is_lt(A.unsigned(ur), S.absolute(b)) == True{} : Bool}, +q: V.Int64, +r: V.Int64, candidate: S.Meaning<a, b, q, r>) -> Empty:
  match candidate:
    case S.Meaning{nonzero, other, smaller, quotient, remainder, integer}:
      reject_from_unique_quotient(a, b, uq, ur, q, r, actual, quotient,
        Unique.strict_euclidean_representations_are_unique(S.absolute(b), A.unsigned(uq), A.unsigned(ur), S.absolute(q), S.absolute(r), small, smaller,
          Equal.trans(Nat, Nat.add(Nat.mul(S.absolute(b), A.unsigned(uq)), A.unsigned(ur)), S.absolute(a), Nat.add(Nat.mul(S.absolute(b), S.absolute(q)), S.absolute(r)),
            Equal.sym(Nat, S.absolute(a), Nat.add(Nat.mul(S.absolute(b), A.unsigned(uq)), A.unsigned(ur)), equation), other)))

def actual_signing_result(+a: V.Int64, +b: V.Int64, +uq: V.Int64, +ur: V.Int64, result: Maybe<&2, V.Int64>,
  actual: {I.signed(S.quotient_sign(a, b), uq) == result : Maybe<&2, V.Int64>}, nonzero: {I.zero(b) == False{} : Bool},
  equation: {S.absolute(a) == Nat.add(Nat.mul(S.absolute(b), A.unsigned(uq)), A.unsigned(ur)) : Nat},
  small: {Nat.is_lt(A.unsigned(ur), S.absolute(b)) == True{} : Bool}, proper: {I.unsigned_lt(ur, I.magnitude(b)) == True{} : Bool}) ->
  S.DivisionCorrect(a, b, I.division_quotient(result, I.signed_word(I.negative(a), ur))):
  match result:
    case Some{q}: accepted_unsigned_result_has_signed_meaning(a, b, uq, ur, q, actual, nonzero, equation, small, proper)
    case None{}: +q => +r => candidate => rejected_unsigned_result_excludes_signed_meaning(a, b, uq, ur, actual, equation, small, q, r, candidate)

law actual_unsigned_division_signing_preserves_complete_euclidean_meaning:
  for +a: V.Int64
  for +b: V.Int64
  for +uq: V.Int64
  for +ur: V.Int64
  for nonzero: {I.zero(b) == False{} : Bool}
  for equation: {S.absolute(a) == Nat.add(Nat.mul(S.absolute(b), A.unsigned(uq)), A.unsigned(ur)) : Nat}
  for small: {Nat.is_lt(A.unsigned(ur), S.absolute(b)) == True{} : Bool}
  for proper: {I.unsigned_lt(ur, I.magnitude(b)) == True{} : Bool}
  S.DivisionCorrect(a, b, I.signed_division(S.quotient_sign(a, b), I.negative(a), I.Division{uq, ur}))
def actual_unsigned_division_signing_preserves_complete_euclidean_meaning(a, b, uq, ur, nonzero, equation, small, proper):
  actual_signing_result(a, b, uq, ur, I.signed(S.quotient_sign(a, b), uq), {==}, nonzero, equation, small, proper)
