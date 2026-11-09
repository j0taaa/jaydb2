# Summary success means exact independent count and total. Rejection is exactly
# the impossibility of simultaneously representing length and every right sum.
import Base
import ./AggregateWords.bend as W
import ./AggregateCountMeaning.bend as C
import ./AggregateModel.bend as M
import ./AggregateCountProofs.bend as Count
import ./AggregateSumProofs.bend as Sum
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ./Aggregate.bend as Aggregate
import ./Summary.bend as Summary

def no_total(count: Maybe<&2,V.Int64>) -> {Summary.added_count(count,None{}) == None{} : Maybe<&2,Summary.Stats>}:
  match count:
    case None{}: {==}
    case Some{n}: {==}

def pack_step(+x: V.Int64,count: Maybe<&2,V.Int64>,total: Maybe<&2,V.Int64>) ->
  {Summary.add(x,Summary.added_count(count,total)) == Summary.added_count(Aggregate.plus(V.Int64{0,1},count),Aggregate.plus(x,total)) : Maybe<&2,Summary.Stats>}:
  match count total:
    case None{} None{}: {==}
    case None{} Some{s}: {==}
    case Some{+n} None{}: Equal.sym(Maybe<&2,Summary.Stats>,Summary.added_count(I.add(V.Int64{0,1},n),None{}),None{},no_total(I.add(V.Int64{0,1},n)))
    case Some{+n} Some{+s}:
      Equal.cong(Maybe<&2,V.Int64>,Maybe<&2,Summary.Stats>,next => Summary.added_count(next,I.add(x,s)),I.increment(n),I.add(V.Int64{0,1},n),W.actual_checked_add_commutes(n,V.Int64{0,1}))

law actual_summary_is_packed_count_and_sum:
  for +xs: List<&2,V.Int64>
  {Summary.compute(xs) == Summary.added_count(Aggregate.count(xs),Aggregate.sum(xs)) : Maybe<&2,Summary.Stats>}
def actual_summary_is_packed_count_and_sum(xs):
  match xs:
    case Nil{}: {==}
    case Con{+x,+tail}:
      Equal.trans(Maybe<&2,Summary.Stats>,Summary.compute(Con{x,tail}),Summary.add(x,Summary.added_count(Aggregate.count(tail),Aggregate.sum(tail))),Summary.added_count(Aggregate.count(Con{x,tail}),Aggregate.sum(Con{x,tail})),
        Equal.cong(Maybe<&2,Summary.Stats>,Maybe<&2,Summary.Stats>,previous => Summary.add(x,previous),Summary.compute(tail),Summary.added_count(Aggregate.count(tail),Aggregate.sum(tail)),actual_summary_is_packed_count_and_sum(tail)),
        pack_step(x,Aggregate.count(tail),Aggregate.sum(tail)))

def InputsFit(+xs: List<&2,V.Int64>) -> Data:
  M.Both<M.SuffixSumsFit(xs),M.Representable<Count.positive_length(xs)>>

type Meaning<-xs: List<&2,V.Int64>,-count: V.Int64,-total: V.Int64> is Data:
  Meaning{count: M.EqualInteger(A.integer(count),Count.positive_length(xs)),total: M.EqualInteger(A.integer(total),M.sum(xs)),suffixes: M.SuffixSumsFit(xs)}

def SummaryCorrect(+xs: List<&2,V.Int64>,result: Maybe<&2,Summary.Stats>) -> Type:
  match result:
    case Some{Summary.Stats{count,total}}: Meaning<xs,count,total>
    case None{}: InputsFit(xs) -> Empty

def reject_unrepresentable_count(+xs: List<&2,V.Int64>,impossible: M.Representable<Count.positive_length(xs)> -> Empty,fit: InputsFit(xs)) -> Empty:
  match fit:
    case M.Both{suffixes,length}: impossible(length)

def reject_unrepresentable_sum(+xs: List<&2,V.Int64>,impossible: M.SuffixSumsFit(xs) -> Empty,fit: InputsFit(xs)) -> Empty:
  match fit:
    case M.Both{suffixes,length}: impossible(suffixes)

def packed_case(+xs: List<&2,V.Int64>,count: Maybe<&2,V.Int64>,total: Maybe<&2,V.Int64>,count_correct: C.CountCorrect(xs,count),total_correct: Sum.SumCorrect(xs,total)) -> SummaryCorrect(xs,Summary.added_count(count,total)):
  match count total:
    case None{} None{}: fit => reject_unrepresentable_count(xs,count_correct,fit)
    case None{} Some{s}: fit => reject_unrepresentable_count(xs,count_correct,fit)
    case Some{n} None{}: fit => reject_unrepresentable_sum(xs,total_correct,fit)
    case Some{n} Some{s}:
      match total_correct:
        case M.Both{exact,suffixes}: Meaning{count_correct,exact,suffixes}

law checked_summary_is_exact_count_and_right_fold_sum:
  for +xs: List<&2,V.Int64>
  SummaryCorrect(xs,Summary.compute(xs))
def checked_summary_is_exact_count_and_right_fold_sum(xs):
  %Equal.sym(Maybe<&2,Summary.Stats>,Summary.compute(xs),Summary.added_count(Aggregate.count(xs),Aggregate.sum(xs)),actual_summary_is_packed_count_and_sum(xs)) : SummaryCorrect(xs,_)
  packed_case(xs,Aggregate.count(xs),Aggregate.sum(xs),C.count_is_exact_positive_integer_length(xs),Sum.checked_sum_is_right_fold_integer_addition(xs))

def HasResult(result: Maybe<&2,Summary.Stats>) -> Type:
  match result:
    case Some{stats}: Unit
    case None{}: Empty

def fitted_result_case(+xs: List<&2,V.Int64>,result: Maybe<&2,Summary.Stats>,correct: SummaryCorrect(xs,result),fit: InputsFit(xs)) -> HasResult(result):
  match result:
    case Some{stats}: Unit{}
    case None{}: correct(fit)

law admissible_lists_are_always_summarized:
  for +xs: List<&2,V.Int64>
  for fit: InputsFit(xs)
  HasResult(Summary.compute(xs))
def admissible_lists_are_always_summarized(xs,fit):
  fitted_result_case(xs,Summary.compute(xs),checked_summary_is_exact_count_and_right_fold_sum(xs),fit)

law mathematical_summary_results_require_exactly_the_input_admissibility_conditions:
  for +xs: List<&2,V.Int64>
  for +count: V.Int64
  for +total: V.Int64
  for meaning: Meaning<xs,count,total>
  InputsFit(xs)
def mathematical_summary_results_require_exactly_the_input_admissibility_conditions(xs,count,total,meaning):
  match meaning:
    case Meaning{count_exact,total_exact,suffixes}: M.Both{suffixes,M.Representable{count,count_exact}}
