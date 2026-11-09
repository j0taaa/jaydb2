# The complete admissibility condition is mathematical: nonempty input,
# representable length, and every right suffix sum representable. A positive
# count rules out the scalar division-overflow case altogether.
import Base
import ./AggregateAverageSpec.bend as Average
import ./AggregateAverageFailure.bend as Failure
import ./Int64PositiveDivision.bend as Positive
import ./SummaryProofs.bend as Summary
import ./AggregateModel.bend as M
import ./AggregateCountProofs.bend as Count
import ./AggregateNonnegative.bend as N
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ./Int64Flags.bend as Flags
import ./Int64DivisionSpec.bend as Division
import ./Aggregate.bend as Aggregate
import ../contract/Logic.bend as L
import ../proof/Foundations.bend as F

def Nonempty(xs: List<&2,V.Int64>) -> Data:
  match xs:
    case Nil{}: {False{} == True{} : Bool}
    case Con{x,tail}: Unit

def Ready(+xs: List<&2,V.Int64>) -> Data:
  M.Both<Nonempty(xs),Summary.InputsFit(xs)>

type Rejection<-xs: List<&2,V.Int64>> is Type:
  EmptyInput{empty: {xs == Nil{} : List<&2,V.Int64>}}
  SuffixOverflow{unfit: M.SuffixSumsFit(xs) -> Empty}
  CountOverflow{unfit: M.Representable<Count.positive_length(xs)> -> Empty}

def Outcome(+xs: List<&2,V.Int64>,result: Maybe<&2,V.Int64>) -> Type:
  match result:
    case Some{q}: Average.Meaning<xs,q>
    case None{}: Rejection<xs>

def impossible_positive_division(+s: V.Int64,+n: V.Int64,possible: Positive.DivisionWitness<s,n>,impossible: @q: V.Int64 -> @r: V.Int64 -> Division.Meaning<s,n,q,r> -> Empty) -> Empty:
  match possible:
    case Positive.DivisionWitness{q,r,meaning}: impossible(q,r,meaning)

law division_overflow_is_impossible_for_any_representable_nonzero_count:
  for +xs: List<&2,V.Int64>
  for +s: V.Int64
  for +n: V.Int64
  for exact: M.EqualInteger(A.integer(n),Count.positive_length(xs))
  for nonzero: {I.zero(n) == False{} : Bool}
  for impossible: @q: V.Int64 -> @r: V.Int64 -> Division.Meaning<s,n,q,r> -> Empty
  Empty
def division_overflow_is_impossible_for_any_representable_nonzero_count(xs,s,n,exact,nonzero,impossible):
  impossible_positive_division(s,n,Positive.every_positive_divisor_has_a_representable_truncating_division(s,n,N.nonnegative_word_has_clear_sign(n,M.length(xs),exact),nonzero),impossible)

def refine_rejection(+xs: List<&2,V.Int64>,reason: Failure.Rejection<xs>) -> Rejection<xs>:
  match reason:
    case Failure.EmptyInput{empty}: EmptyInput{empty}
    case Failure.SuffixOverflow{unfit}: SuffixOverflow{unfit}
    case Failure.CountOverflow{unfit}: CountOverflow{unfit}
    case Failure.DivisionOverflow{+s,+n,total_exact,count_exact,suffixes,nonzero,impossible}:
      L.ex_false(Rejection<xs>,division_overflow_is_impossible_for_any_representable_nonzero_count(xs,s,n,count_exact,nonzero,impossible))

def refine_outcome(+xs: List<&2,V.Int64>,result: Maybe<&2,V.Int64>,correct: Failure.Outcome(xs,result)) -> Outcome(xs,result):
  match result:
    case Some{q}: correct
    case None{}: refine_rejection(xs,correct)

law checked_average_succeeds_exactly_on_admissible_nonempty_lists:
  for +xs: List<&2,V.Int64>
  Outcome(xs,Aggregate.average(xs))
def checked_average_succeeds_exactly_on_admissible_nonempty_lists(xs):
  refine_outcome(xs,Aggregate.average(xs),Failure.checked_average_has_exact_success_or_classified_failure(xs))

def reject_ready(+xs: List<&2,V.Int64>,reason: Rejection<xs>,ready: Ready(xs)) -> Empty:
  match reason ready:
    case EmptyInput{empty} M.Both{nonempty,fit}: F.false_negative_true((%empty : Nonempty(_) nonempty))
    case SuffixOverflow{unfit} M.Both{nonempty,M.Both{suffixes,length}}: unfit(suffixes)
    case CountOverflow{unfit} M.Both{nonempty,M.Both{suffixes,length}}: unfit(length)

def HasResult(result: Maybe<&2,V.Int64>) -> Type:
  match result:
    case Some{q}: Unit
    case None{}: Empty

def ready_result_case(+xs: List<&2,V.Int64>,result: Maybe<&2,V.Int64>,correct: Outcome(xs,result),ready: Ready(xs)) -> HasResult(result):
  match result:
    case Some{q}: Unit{}
    case None{}: reject_ready(xs,correct,ready)

law admissible_nonempty_lists_are_always_accepted:
  for +xs: List<&2,V.Int64>
  for ready: Ready(xs)
  HasResult(Aggregate.average(xs))
def admissible_nonempty_lists_are_always_accepted(xs,ready):
  ready_result_case(xs,Aggregate.average(xs),checked_average_succeeds_exactly_on_admissible_nonempty_lists(xs),ready)

def nonzero_exact_count_forces_nonempty(+xs: List<&2,V.Int64>,+n: V.Int64,exact: M.EqualInteger(A.integer(n),Count.positive_length(xs)),nonzero: {I.zero(n) == False{} : Bool}) -> Nonempty(xs):
  match xs:
    case Con{x,tail}: Unit{}
    case Nil{}:
      Equal.trans(Bool,False{},I.zero(n),True{},Equal.sym(Bool,I.zero(n),False{},nonzero),Flags.unsigned_zero_forces_zero_guard(n,N.nonnegative_word_has_exact_unsigned_value(n,0n,exact)))

law mathematical_average_results_require_exactly_the_input_admissibility_conditions:
  for +xs: List<&2,V.Int64>
  for +q: V.Int64
  for meaning: Average.Meaning<xs,q>
  Ready(xs)
def mathematical_average_results_require_exactly_the_input_admissibility_conditions(xs,q,meaning):
  match meaning:
    case Average.Meaning{total,+n,remainder,total_exact,+count_exact,suffixes,Division.Meaning{nonzero,equation,small,quotient_sign,remainder_sign,ordinary}}:
      M.Both{nonzero_exact_count_forces_nonempty(xs,n,count_exact,nonzero),M.Both{suffixes,M.Representable{n,count_exact}}}
