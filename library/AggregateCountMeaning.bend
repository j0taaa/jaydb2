# Count expressed directly in the independent integer model, for composition.
import Base
import ./AggregateModel.bend as M
import ./AggregateSumProofs.bend as Sum
import ./AggregateCountProofs.bend as Count
import ./Value.bend as V
import ./Int64Proofs.bend as A
import ./Aggregate.bend as Aggregate

def CountCorrect(+xs: List<&2,V.Int64>,result: Maybe<&2,V.Int64>) -> Type:
  match result:
    case Some{n}: M.EqualInteger(A.integer(n),Count.positive_length(xs))
    case None{}: M.Representable<Count.positive_length(xs)> -> Empty

def sum_case(+xs: List<&2,V.Int64>,result: Maybe<&2,V.Int64>,correct: Sum.SumCorrect(Count.ones(xs),result)) -> CountCorrect(xs,result):
  match result:
    case Some{n}:
      match correct:
        case M.Both{exact,suffixes}:
          %Count.sum_of_ones_is_positive_length(xs) : M.EqualInteger(A.integer(n),_)
          exact
    case None{}: representation => correct(Count.representable_length_implies_all_suffix_counts_fit(xs,representation))

law count_is_exact_positive_integer_length:
  for +xs: List<&2,V.Int64>
  CountCorrect(xs,Aggregate.count(xs))
def count_is_exact_positive_integer_length(xs):
  %Equal.sym(Maybe<&2,V.Int64>,Aggregate.count(xs),Aggregate.sum(Count.ones(xs)),Count.count_is_actual_sum_of_ones(xs)) : CountCorrect(xs,_)
  sum_case(xs,Aggregate.sum(Count.ones(xs)),Sum.checked_sum_is_right_fold_integer_addition(Count.ones(xs)))
