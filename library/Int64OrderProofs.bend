# Ordinary strict/non-strict order of independent Nat-difference integers.
# The public strict comparison equality holds for every pair of signed words.
import Base
import ./Int64WordIntegerOrder.bend as W
import ./Int64OrderBinding.bend as Binding
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ./ComparisonProofs.bend as Comparison
import ../proof/Orders.bend as O
import ../proof/Foundations.bend as F

def compare(a: A.Integer,b: A.Integer) -> Cmp:
  A.Integer{ap,an}=a
  A.Integer{bp,bn}=b
  Nat.cmp(Nat.add(ap,bn),Nat.add(bp,an))

def less(a: A.Integer,b: A.Integer) -> Bool:
  Cmp.is_lt(compare(a,b))

def LessEqual(a: V.Int64,b: V.Int64) -> Data:
  {Cmp.is_le(compare(A.integer(a),A.integer(b))) == True{} : Bool}

law actual_rank_is_independent_integer_comparison:
  for +a: V.Int64
  for +b: V.Int64
  {Comparison.rank_order(a,b) == compare(A.integer(a),A.integer(b)) : Cmp}
def actual_rank_is_independent_integer_comparison(a,b):
  Equal.trans(Cmp,Comparison.rank_order(a,b),Word.cmp(64n,W.flip_sign(64n,A.bits(a)),W.flip_sign(64n,A.bits(b))),compare(A.integer(a),A.integer(b)),Binding.actual_rank_is_full_flipped_word_comparison(a,b),
    Equal.sym(Cmp,compare(A.integer(a),A.integer(b)),Word.cmp(64n,W.flip_sign(64n,A.bits(a)),W.flip_sign(64n,A.bits(b))),W.flipped_comparison_is_signed_cross_sum_comparison(64n,A.bits(a),A.bits(b))))

law actual_lt_is_strict_independent_integer_order:
  for +a: V.Int64
  for +b: V.Int64
  {I.lt(a,b) == less(A.integer(a),A.integer(b)) : Bool}
def actual_lt_is_strict_independent_integer_order(a,b):
  Equal.trans(Bool,I.lt(a,b),Cmp.is_lt(Comparison.rank_order(a,b)),less(A.integer(a),A.integer(b)),Equal.sym(Bool,Cmp.is_lt(Comparison.rank_order(a,b)),I.lt(a,b),Comparison.rank_matches_lt(a,b)),Equal.cong(Cmp,Bool,Cmp.is_lt,Comparison.rank_order(a,b),compare(A.integer(a),A.integer(b)),actual_rank_is_independent_integer_comparison(a,b)))

law mathematical_nonstrict_order_is_reflexive:
  for +a: V.Int64
  LessEqual(a,a)
def mathematical_nonstrict_order_is_reflexive(a):
  Equal.cong(Cmp,Bool,Cmp.is_le,compare(A.integer(a),A.integer(a)),EQ{},Equal.trans(Cmp,compare(A.integer(a),A.integer(a)),Comparison.rank_order(a,a),EQ{},Equal.sym(Cmp,Comparison.rank_order(a,a),compare(A.integer(a),A.integer(a)),actual_rank_is_independent_integer_comparison(a,a)),Comparison.rank_reflexive(a)))

def le_after_strict(c: Cmp,strict: {Cmp.is_lt(c) == True{} : Bool}) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}: {==}
    case EQ{}: F.absurd_boolean({True{} == True{} : Bool},strict)
    case GT{}: F.absurd_boolean({False{} == True{} : Bool},strict)

law actual_strict_comparison_entails_mathematical_nonstrict_order:
  for +a: V.Int64
  for +b: V.Int64
  for strict: {I.lt(a,b) == True{} : Bool}
  LessEqual(a,b)
def actual_strict_comparison_entails_mathematical_nonstrict_order(a,b,strict):
  le_after_strict(compare(A.integer(a),A.integer(b)),Equal.trans(Bool,less(A.integer(a),A.integer(b)),I.lt(a,b),True{},Equal.sym(Bool,I.lt(a,b),less(A.integer(a),A.integer(b)),actual_lt_is_strict_independent_integer_order(a,b)),strict))

def le_if_reverse_not_strict(c: Cmp,no: {Cmp.is_lt(Comparison.reverse_cmp(c)) == False{} : Bool}) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: F.absurd_boolean({False{} == True{} : Bool},Equal.sym(Bool,True{},False{},no))

law actual_reverse_not_less_entails_mathematical_nonstrict_order:
  for +a: V.Int64
  for +b: V.Int64
  for no: {I.lt(b,a) == False{} : Bool}
  LessEqual(a,b)
def actual_reverse_not_less_entails_mathematical_nonstrict_order(a,b,no):
  %actual_rank_is_independent_integer_comparison(a,b) : {Cmp.is_le(_) == True{} : Bool}
  le_if_reverse_not_strict(Comparison.rank_order(a,b),Equal.trans(Bool,Cmp.is_lt(Comparison.reverse_cmp(Comparison.rank_order(a,b))),Cmp.is_lt(Comparison.rank_order(b,a)),False{},
    Equal.cong(Cmp,Bool,Cmp.is_lt,Comparison.reverse_cmp(Comparison.rank_order(a,b)),Comparison.rank_order(b,a),Equal.sym(Cmp,Comparison.rank_order(b,a),Comparison.reverse_cmp(Comparison.rank_order(a,b)),Comparison.rank_reverse(a,b))),Equal.trans(Bool,Cmp.is_lt(Comparison.rank_order(b,a)),I.lt(b,a),False{},Comparison.rank_matches_lt(b,a),no)))

def compose_nonstrict(ab: Cmp,bc: Cmp,+ac: Cmp,first: {Cmp.is_le(ab) == True{} : Bool},second: {Cmp.is_le(bc) == True{} : Bool},coherent: O.Coherent(ab,bc,ac)) -> {Cmp.is_le(ac) == True{} : Bool}:
  match ab bc:
    case EQ{} LT{}: Equal.cong(Cmp,Bool,Cmp.is_le,ac,LT{},coherent)
    case EQ{} EQ{}: Equal.cong(Cmp,Bool,Cmp.is_le,ac,EQ{},coherent)
    case EQ{} GT{}: F.absurd_boolean({Cmp.is_le(ac) == True{} : Bool},second)
    case LT{} EQ{}: Equal.cong(Cmp,Bool,Cmp.is_le,ac,LT{},coherent)
    case LT{} LT{}: Equal.cong(Cmp,Bool,Cmp.is_le,ac,LT{},coherent)
    case LT{} GT{}: F.absurd_boolean({Cmp.is_le(ac) == True{} : Bool},second)
    case GT{} bc: F.absurd_boolean({Cmp.is_le(ac) == True{} : Bool},first)

law mathematical_nonstrict_order_is_transitive:
  for +a: V.Int64
  for +b: V.Int64
  for +c: V.Int64
  for ab: LessEqual(a,b)
  for bc: LessEqual(b,c)
  LessEqual(a,c)
def mathematical_nonstrict_order_is_transitive(a,b,c,ab,bc):
  %actual_rank_is_independent_integer_comparison(a,c) : {Cmp.is_le(_) == True{} : Bool}
  compose_nonstrict(Comparison.rank_order(a,b),Comparison.rank_order(b,c),Comparison.rank_order(a,c),
    (%Equal.sym(Cmp,Comparison.rank_order(a,b),compare(A.integer(a),A.integer(b)),actual_rank_is_independent_integer_comparison(a,b)) : {Cmp.is_le(_) == True{} : Bool} ab),
    (%Equal.sym(Cmp,Comparison.rank_order(b,c),compare(A.integer(b),A.integer(c)),actual_rank_is_independent_integer_comparison(b,c)) : {Cmp.is_le(_) == True{} : Bool} bc),Comparison.rank_coherent(a,b,c))
