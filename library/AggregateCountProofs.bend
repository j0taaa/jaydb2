# Exact checked count of arbitrary finite lists. Rejection excludes every
# signed64 representation of the independent nonnegative natural list length.
import Base
import ./AggregateModel.bend as M
import ./AggregateSumProofs.bend as Sum
import ./AggregateNonnegative.bend as N
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ./Int64IntegerAddition.bend as Add
import ./Aggregate.bend as Aggregate

def ones(xs: List<&2,V.Int64>) -> List<&2,V.Int64>:
  match xs:
    case Nil{}: Nil{}
    case Con{x,tail}: Con{V.Int64{0,1},ones(tail)}

def positive_length(xs: List<&2,V.Int64>) -> A.Integer:
  A.Integer{M.length(xs),0n}

law sum_of_ones_is_positive_length:
  for +xs: List<&2,V.Int64>
  {M.sum(ones(xs)) == positive_length(xs) : A.Integer}
def sum_of_ones_is_positive_length(xs):
  match xs:
    case Nil{}: {==}
    case Con{x,+tail}:
      Equal.cong(A.Integer,A.Integer,integer => Add.add(A.Integer{1n,0n},integer),M.sum(ones(tail)),positive_length(tail),sum_of_ones_is_positive_length(tail))

law count_is_actual_sum_of_ones:
  for +xs: List<&2,V.Int64>
  {Aggregate.count(xs) == Aggregate.sum(ones(xs)) : Maybe<&2,V.Int64>}
def count_is_actual_sum_of_ones(xs):
  match xs:
    case Nil{}: {==}
    case Con{x,+tail}:
      Equal.cong(Maybe<&2,V.Int64>,Maybe<&2,V.Int64>,result => Aggregate.plus(V.Int64{0,1},result),Aggregate.count(tail),Aggregate.sum(ones(tail)),count_is_actual_sum_of_ones(tail))

# Every shorter nonnegative length is representable whenever the full length
# is. Actual checked subtraction supplies each predecessor witness.
law representable_length_implies_all_suffix_counts_fit:
  for +xs: List<&2,V.Int64>
  for representation: M.Representable<positive_length(xs)>
  M.SuffixSumsFit(ones(xs))
def representable_length_implies_all_suffix_counts_fit(xs,representation):
  match xs representation:
    case Nil{} representation: Unit{}
    case Con{+x,+tail} M.Representable{+word,+exact}:
      M.Both{M.Representable{word,
        (%Equal.sym(A.Integer,M.sum(ones(Con{x,tail})),positive_length(Con{x,tail}),sum_of_ones_is_positive_length(Con{x,tail})) : M.EqualInteger(A.integer(word),_)
          exact)},
        representable_length_implies_all_suffix_counts_fit(tail,M.Representable{I.wrapping_sub(word,V.Int64{0,1}),N.nonnegative_predecessor_is_represented_by_actual_subtraction(word,M.length(tail),exact)})}

def CountCorrect(+xs: List<&2,V.Int64>,result: Maybe<&2,V.Int64>) -> Type:
  match result:
    case Some{r}: M.Both<{I.negative(r) == False{} : Bool},{A.unsigned(r) == M.length(xs) : Nat}>
    case None{}: M.Representable<positive_length(xs)> -> Empty

def mapped_sum_result_is_count(+xs: List<&2,V.Int64>,result: Maybe<&2,V.Int64>,
  correct: Sum.SumCorrect(ones(xs),result)) -> CountCorrect(xs,result):
  match result:
    case Some{+word}:
      match correct:
        case M.Both{exact,suffixes}:
          +natural_exact = {(%sum_of_ones_is_positive_length(xs) : M.EqualInteger(A.integer(word),_) exact) : M.EqualInteger(A.integer(word),positive_length(xs))}
          M.Both{N.nonnegative_word_has_clear_sign(word,M.length(xs),natural_exact),N.nonnegative_word_has_exact_unsigned_value(word,M.length(xs),natural_exact)}
    case None{}:
      representation => correct(representable_length_implies_all_suffix_counts_fit(xs,representation))

# No output, suffix-fit, sign, overflow, or loop invariant is an input premise.
law checked_count_is_exact_representable_length:
  for +xs: List<&2,V.Int64>
  CountCorrect(xs,Aggregate.count(xs))
def checked_count_is_exact_representable_length(xs):
  %Equal.sym(Maybe<&2,V.Int64>,Aggregate.count(xs),Aggregate.sum(ones(xs)),count_is_actual_sum_of_ones(xs)) : CountCorrect(xs,_)
  mapped_sum_result_is_count(xs,Aggregate.sum(ones(xs)),Sum.checked_sum_is_right_fold_integer_addition(ones(xs)))
