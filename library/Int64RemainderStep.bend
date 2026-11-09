# Actual restoring step: the inserted dividend bit fits, subtraction is exact,
# and the next remainder is strictly smaller than the positive divisor.
import Base
import ./Int64BitInsert.bend as B
import ./Int64DivisionNoLoss.bend as NoLoss
import ./Int64DivisionNaturalStep.bend as N
import ./Int64UnsignedSubtract.bend as Sub
import ./Int64NaturalOrder.bend as O
import ./Int64Proofs.bend as A
import ./Int64.bend as I
import ./Value.bend as V
import ../contract/Logic.bend as L
import ../proof/Foundations.bend as F

def after_subtract(+flag: Bool,+next: V.Int64,+d: V.Int64) -> V.Int64:
  Bool.pick(V.Int64,flag,I.wrapping_sub(next,d),next)

def decision(+next: V.Int64,+d: V.Int64) -> Bool:
  Bool.not(I.unsigned_lt(next,d))

def StepData(+flag: Bool,+r: V.Int64,+d: V.Int64,+next: V.Int64,+bit: Bool) -> Type:
  L.E<{A.unsigned(next) == A.place(bit,A.unsigned(r)) : Nat},
    L.E<{A.unsigned(next) == Bool.pick(Nat,flag,Nat.add(A.unsigned(d),A.unsigned(after_subtract(flag,next,d))),A.unsigned(after_subtract(flag,next,d))) : Nat},
      {I.unsigned_lt(after_subtract(flag,next,d),d) == True{} : Bool}>>

law not_false_implies_true:
  for +b: Bool
  for evidence: {Bool.not(b) == False{} : Bool}
  {b == True{} : Bool}
def not_false_implies_true(b,evidence):
  match b:
    case True{}: {==}
    case False{}: F.absurd_boolean({False{} == True{} : Bool},Equal.sym(Bool,True{},False{},evidence))

law actual_less_is_natural_less:
  for +r: V.Int64
  for +d: V.Int64
  for small: {I.unsigned_lt(r,d) == True{} : Bool}
  {Nat.is_lt(A.unsigned(r),A.unsigned(d)) == True{} : Bool}
def actual_less_is_natural_less(r,d,small):
  Equal.trans(Bool,Nat.is_lt(A.unsigned(r),A.unsigned(d)),I.unsigned_lt(r,d),True{},Equal.sym(Bool,I.unsigned_lt(r,d),Nat.is_lt(A.unsigned(r),A.unsigned(d)),O.actual_unsigned_lt_is_natural_order(r,d)),small)

def step_by_flag(flag: Bool,+r: V.Int64,+d: V.Int64,+next: V.Int64,+bit: Bool,
  +formed: {A.unsigned(next) == A.place(bit,A.unsigned(r)) : Nat},
  small: {I.unsigned_lt(r,d) == True{} : Bool},
  actual: {decision(next,d) == flag : Bool}) -> StepData(flag,r,d,next,bit):
  match flag:
    case False{}:
      L.Both{formed,L.Both{{==},not_false_implies_true(I.unsigned_lt(next,d),actual)}}
    case True{}:
      +difference = Sub.actual_unsigned_subtract_is_natural_difference(next,d,F.negation_true(I.unsigned_lt(next,d),actual))
      smaller = N.subtraction_restores_strict_remainder(bit,A.unsigned(r),A.unsigned(d),A.unsigned(next),A.unsigned(I.wrapping_sub(next,d)),actual_less_is_natural_less(r,d,small),formed,difference)
      L.Both{formed,L.Both{difference,Equal.trans(Bool,I.unsigned_lt(I.wrapping_sub(next,d),d),Nat.is_lt(A.unsigned(I.wrapping_sub(next,d)),A.unsigned(d)),True{},O.actual_unsigned_lt_is_natural_order(I.wrapping_sub(next,d),d),smaller)}}

law actual_remainder_step:
  for +r: V.Int64
  for +input: V.Int64
  for +d: V.Int64
  for +small: {I.unsigned_lt(r,d) == True{} : Bool}
  for bound: {Cmp.is_le(Word.cmp(64n,A.bits(d),A.sign_threshold(63n))) == True{} : Bool}
  StepData(decision(B.insert(r,I.negative(input)),d),r,d,B.insert(r,I.negative(input)),I.negative(input))
def actual_remainder_step(r,input,d,small,bound):
  step_by_flag(decision(B.insert(r,I.negative(input)),d),r,d,B.insert(r,I.negative(input)),I.negative(input),B.actual_insert_without_loss(r,I.negative(input),NoLoss.remainder_high_bit_is_clear(r,d,small,bound)),small,{==})
