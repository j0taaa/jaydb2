# Average uses exact mathematical total/length witnesses and the independently
# proved signed Euclidean meaning, including truncation toward zero. Neither
# an actual intermediate output nor an overflow/invariant premise is required.
import Base
import ./AggregateWords.bend as W
import ./AggregateCountMeaning.bend as C
import ./AggregateModel.bend as M
import ./AggregateSumProofs.bend as Sum
import ./AggregateCountProofs.bend as Count
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ./Int64IntegerProduct.bend as P
import ./Int64DivisionSpec.bend as Division
import ./Int64DivisionProofs.bend as Divide
import ./Aggregate.bend as Aggregate

type Meaning<-xs: List<&2,V.Int64>,-q: V.Int64> is Type:
  Meaning{total: V.Int64,count: V.Int64,remainder: V.Int64,
    total_exact: M.EqualInteger(A.integer(total),M.sum(xs)),
    count_exact: M.EqualInteger(A.integer(count),Count.positive_length(xs)),
    suffixes: M.SuffixSumsFit(xs),
    division: Division.Meaning<total,count,q,remainder>}

def AverageCorrect(+xs: List<&2,V.Int64>,result: Maybe<&2,V.Int64>) -> Type:
  match result:
    case Some{q}: Meaning<xs,q>
    case None{}: @q: V.Int64 -> Meaning<xs,q> -> Empty

law independently_equal_representations_are_the_same_word:
  for +a: V.Int64
  for +b: V.Int64
  for +integer: A.Integer
  for a_exact: M.EqualInteger(A.integer(a),integer)
  for b_exact: M.EqualInteger(A.integer(b),integer)
  {a == b : V.Int64}
def independently_equal_representations_are_the_same_word(a,b,integer,a_exact,b_exact):
  W.integer_interpretation_is_injective(a,b,M.equality_from_integer_product_model(A.integer(a),A.integer(b),
    P.integer_equal_transitive(A.integer(a),integer,A.integer(b),M.equality_to_integer_product_model(A.integer(a),integer,a_exact),
      P.integer_equal_symmetric(A.integer(b),integer,M.equality_to_integer_product_model(A.integer(b),integer,b_exact)))))

def transport_division_inputs(+a: V.Int64,+b: V.Int64,+a2: V.Int64,+b2: V.Int64,+q: V.Int64,+r: V.Int64,
  same_a: {a == a2 : V.Int64},same_b: {b == b2 : V.Int64},meaning: Division.Meaning<a,b,q,r>) -> Division.Meaning<a2,b2,q,r>:
  %same_b : Division.Meaning<a2,_,q,r>
  %same_a : Division.Meaning<_,b,q,r>
  meaning

def rejected_division_refutes_independent_average(+xs: List<&2,V.Int64>,+s: V.Int64,+n: V.Int64,
  sum_exact: M.EqualInteger(A.integer(s),M.sum(xs)),count_exact: M.EqualInteger(A.integer(n),Count.positive_length(xs)),
  impossible: @q: V.Int64 -> @r: V.Int64 -> Division.Meaning<s,n,q,r> -> Empty,
  +q: V.Int64,candidate: Meaning<xs,q>) -> Empty:
  match candidate:
    case Meaning{+total,+count,+remainder,total_exact,candidate_count,suffixes,division}:
      impossible(q,remainder,transport_division_inputs(total,count,s,n,q,remainder,
        independently_equal_representations_are_the_same_word(total,s,M.sum(xs),total_exact,sum_exact),
        independently_equal_representations_are_the_same_word(count,n,Count.positive_length(xs),candidate_count,count_exact),division))

def division_case(+xs: List<&2,V.Int64>,+s: V.Int64,+n: V.Int64,
  sum_exact: M.EqualInteger(A.integer(s),M.sum(xs)),count_exact: M.EqualInteger(A.integer(n),Count.positive_length(xs)),
  suffixes: M.SuffixSumsFit(xs),result: Maybe<&2,I.Division>,correct: Division.DivisionCorrect(s,n,result)) ->
  AverageCorrect(xs,Aggregate.quotient(result)):
  match result:
    case Some{I.Division{q,r}}: Meaning{s,n,r,sum_exact,count_exact,suffixes,correct}
    case None{}: q => candidate => rejected_division_refutes_independent_average(xs,s,n,sum_exact,count_exact,correct,q,candidate)

def rejected_sum_refutes_independent_average(+xs: List<&2,V.Int64>,impossible: M.SuffixSumsFit(xs) -> Empty,+q: V.Int64,candidate: Meaning<xs,q>) -> Empty:
  match candidate:
    case Meaning{total,count,remainder,total_exact,count_exact,suffixes,division}: impossible(suffixes)

def rejected_count_refutes_independent_average(+xs: List<&2,V.Int64>,impossible: M.Representable<Count.positive_length(xs)> -> Empty,+q: V.Int64,candidate: Meaning<xs,q>) -> Empty:
  match candidate:
    case Meaning{total,+count,remainder,total_exact,count_exact,suffixes,division}: impossible(M.Representable{count,count_exact})

def input_case(+xs: List<&2,V.Int64>,total: Maybe<&2,V.Int64>,count: Maybe<&2,V.Int64>,sum_correct: Sum.SumCorrect(xs,total),count_correct: C.CountCorrect(xs,count)) -> AverageCorrect(xs,Aggregate.average_result(total,count)):
  match total count:
    case None{} None{}: q => candidate => rejected_sum_refutes_independent_average(xs,sum_correct,q,candidate)
    case None{} Some{n}: q => candidate => rejected_sum_refutes_independent_average(xs,sum_correct,q,candidate)
    case Some{s} None{}: q => candidate => rejected_count_refutes_independent_average(xs,count_correct,q,candidate)
    case Some{+s} Some{+n}:
      match sum_correct:
        case M.Both{exact,suffixes}: division_case(xs,s,n,exact,count_correct,suffixes,I.divmod(s,n),Divide.checked_divmod_is_truncating_integer_division(s,n))

law checked_average_is_exact_truncating_integer_mean:
  for +xs: List<&2,V.Int64>
  AverageCorrect(xs,Aggregate.average(xs))
def checked_average_is_exact_truncating_integer_mean(xs):
  input_case(xs,Aggregate.sum(xs),Aggregate.count(xs),Sum.checked_sum_is_right_fold_integer_addition(xs),C.count_is_exact_positive_integer_length(xs))
