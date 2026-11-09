# Exhaustive mathematical reasons for rejection. The final constructor means
# no representable quotient/remainder satisfies signed Euclidean division with
# the exact total and the nonzero exact length; it assumes no algorithm result.
import Base
import ./AggregateAverageSpec.bend as Average
import ./AggregateCountMeaning.bend as C
import ./AggregateModel.bend as M
import ./AggregateCountProofs.bend as Count
import ./AggregateSumProofs.bend as Sum
import ./AggregateNonnegative.bend as N
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ./Int64Flags.bend as Flags
import ./Int64DivisionSpec.bend as Division
import ./Int64DivisionProofs.bend as Divide
import ./Aggregate.bend as Aggregate
import ../proof/Foundations.bend as F

law zero_length_is_exactly_the_empty_list:
  for +xs: List<&2,V.Int64>
  for zero: {M.length(xs) == 0n : Nat}
  {xs == Nil{} : List<&2,V.Int64>}
def zero_length_is_exactly_the_empty_list(xs,zero):
  match xs:
    case Nil{}: {==}
    case Con{x,tail}:
      F.absurd_boolean({Con{x,tail} == Nil{} : List<&2,V.Int64>},Equal.cong(Nat,Bool,A.nat_zero,1n+M.length(tail),0n,zero))

law zero_count_forces_empty_input:
  for +xs: List<&2,V.Int64>
  for +count: V.Int64
  for exact: M.EqualInteger(A.integer(count),Count.positive_length(xs))
  for zero: {I.zero(count) == True{} : Bool}
  {xs == Nil{} : List<&2,V.Int64>}
def zero_count_forces_empty_input(xs,count,exact,zero):
  zero_length_is_exactly_the_empty_list(xs,Equal.trans(Nat,M.length(xs),A.unsigned(count),0n,
    Equal.sym(Nat,A.unsigned(count),M.length(xs),N.nonnegative_word_has_exact_unsigned_value(count,M.length(xs),exact)),
    Equal.cong(V.Int64,Nat,A.unsigned,count,V.Int64{0,0},Flags.zero_guard_is_sound(count,zero))))

type Rejection<-xs: List<&2,V.Int64>> is Type:
  EmptyInput{empty: {xs == Nil{} : List<&2,V.Int64>}}
  SuffixOverflow{unfit: M.SuffixSumsFit(xs) -> Empty}
  CountOverflow{unfit: M.Representable<Count.positive_length(xs)> -> Empty}
  DivisionOverflow{total: V.Int64,count: V.Int64,
    total_exact: M.EqualInteger(A.integer(total),M.sum(xs)),
    count_exact: M.EqualInteger(A.integer(count),Count.positive_length(xs)),
    suffixes: M.SuffixSumsFit(xs),nonzero: {I.zero(count) == False{} : Bool},
    impossible: @q: V.Int64 -> @r: V.Int64 -> Division.Meaning<total,count,q,r> -> Empty}

def Outcome(+xs: List<&2,V.Int64>,result: Maybe<&2,V.Int64>) -> Type:
  match result:
    case Some{q}: Average.Meaning<xs,q>
    case None{}: Rejection<xs>

def rejected_division_case(zero: Bool,+xs: List<&2,V.Int64>,+s: V.Int64,+n: V.Int64,
  sum_exact: M.EqualInteger(A.integer(s),M.sum(xs)),+count_exact: M.EqualInteger(A.integer(n),Count.positive_length(xs)),
  suffixes: M.SuffixSumsFit(xs),actual: {I.zero(n) == zero : Bool},
  impossible: @q: V.Int64 -> @r: V.Int64 -> Division.Meaning<s,n,q,r> -> Empty) -> Rejection<xs>:
  match zero:
    case True{}: EmptyInput{zero_count_forces_empty_input(xs,n,count_exact,actual)}
    case False{}: DivisionOverflow{s,n,sum_exact,count_exact,suffixes,actual,impossible}

def division_case(+xs: List<&2,V.Int64>,+s: V.Int64,+n: V.Int64,
  sum_exact: M.EqualInteger(A.integer(s),M.sum(xs)),+count_exact: M.EqualInteger(A.integer(n),Count.positive_length(xs)),
  suffixes: M.SuffixSumsFit(xs),result: Maybe<&2,I.Division>,correct: Division.DivisionCorrect(s,n,result)) ->
  Outcome(xs,Aggregate.quotient(result)):
  match result:
    case Some{I.Division{q,r}}: Average.Meaning{s,n,r,sum_exact,count_exact,suffixes,correct}
    case None{}: rejected_division_case(I.zero(n),xs,s,n,sum_exact,count_exact,suffixes,{==},correct)

def input_case(+xs: List<&2,V.Int64>,total: Maybe<&2,V.Int64>,count: Maybe<&2,V.Int64>,sum_correct: Sum.SumCorrect(xs,total),count_correct: C.CountCorrect(xs,count)) -> Outcome(xs,Aggregate.average_result(total,count)):
  match total count:
    case None{} None{}: SuffixOverflow{sum_correct}
    case None{} Some{n}: SuffixOverflow{sum_correct}
    case Some{s} None{}: CountOverflow{count_correct}
    case Some{+s} Some{+n}:
      match sum_correct:
        case M.Both{exact,suffixes}: division_case(xs,s,n,exact,count_correct,suffixes,I.divmod(s,n),Divide.checked_divmod_is_truncating_integer_division(s,n))

law checked_average_has_exact_success_or_classified_failure:
  for +xs: List<&2,V.Int64>
  Outcome(xs,Aggregate.average(xs))
def checked_average_has_exact_success_or_classified_failure(xs):
  input_case(xs,Aggregate.sum(xs),Aggregate.count(xs),Sum.checked_sum_is_right_fold_integer_addition(xs),C.count_is_exact_positive_integer_length(xs))

# Independent reason constructors actually exclude every mathematical result.
# This converse rules out a permissive, vacuous rejection classification.
def empty_has_no_meaning(+q: V.Int64,candidate: Average.Meaning<Nil{},q>) -> Empty:
  match candidate:
    case Average.Meaning{total,+count,remainder,total_exact,count_exact,suffixes,Division.Meaning{nonzero,equation,small,quotient_sign,remainder_sign,ordinary}}:
      F.false_negative_true(Equal.trans(Bool,False{},I.zero(count),True{},Equal.sym(Bool,I.zero(count),False{},nonzero),
        Flags.unsigned_zero_forces_zero_guard(count,N.nonnegative_word_has_exact_unsigned_value(count,0n,count_exact))))

law every_classified_rejection_excludes_every_mathematical_average:
  for +xs: List<&2,V.Int64>
  for rejection: Rejection<xs>
  for +q: V.Int64
  for candidate: Average.Meaning<xs,q>
  Empty
def every_classified_rejection_excludes_every_mathematical_average(xs,rejection,q,candidate):
  match rejection:
    case EmptyInput{empty}: empty_has_no_meaning(q,(%empty : Average.Meaning<_,q> candidate))
    case SuffixOverflow{impossible}: Average.rejected_sum_refutes_independent_average(xs,impossible,q,candidate)
    case CountOverflow{impossible}: Average.rejected_count_refutes_independent_average(xs,impossible,q,candidate)
    case DivisionOverflow{+s,+n,sum_exact,count_exact,suffixes,nonzero,impossible}:
      Average.rejected_division_refutes_independent_average(xs,s,n,sum_exact,count_exact,impossible,q,candidate)
