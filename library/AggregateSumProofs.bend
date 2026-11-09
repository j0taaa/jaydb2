# Complete correctness of the actual documented right-fold checked sum.
# Rejection means the independent representability of every right suffix is
# impossible. It does not assert that the final mathematical sum is out of range.
import Base
import ./AggregateModel.bend as M
import ./AggregateAddition.bend as Bridge
import ./Value.bend as V
import ./Aggregate.bend as Aggregate
import ./Int64.bend as I
import ./Int64Proofs.bend as A

def SumCorrect(+xs: List<&2,V.Int64>,result: Maybe<&2,V.Int64>) -> Type:
  match result:
    case Some{r}: M.Both<M.EqualInteger(A.integer(r),M.sum(xs)),M.SuffixSumsFit(xs)>
    case None{}: M.SuffixSumsFit(xs) -> Empty

def unfit_tail_excludes_fitted_whole(+x: V.Int64,+xs: List<&2,V.Int64>,
  impossible: M.SuffixSumsFit(xs) -> Empty,fit: M.SuffixSumsFit(Con{x,xs})) -> Empty:
  match fit:
    case M.Both{whole,tail}: impossible(tail)

def rejected_addition_excludes_fitted_whole(+x: V.Int64,+xs: List<&2,V.Int64>,+tail: V.Int64,
  tail_exact: M.EqualInteger(A.integer(tail),M.sum(xs)),
  impossible: @r: V.Int64 -> A.IntegerSum(A.integer(x),A.integer(tail),A.integer(r)) -> Empty,
  fit: M.SuffixSumsFit(Con{x,xs})) -> Empty:
  match fit:
    case M.Both{M.Representable{+candidate,exact},tail_fit}:
      impossible(candidate,Bridge.mathematical_sum_candidate_is_scalar_addition_candidate(x,tail,M.sum(xs),candidate,tail_exact,exact))

def addition_case(+x: V.Int64,+xs: List<&2,V.Int64>,+tail: V.Int64,
  tail_exact: M.EqualInteger(A.integer(tail),M.sum(xs)),tail_fit: M.SuffixSumsFit(xs),
  result: Maybe<&2,V.Int64>,correct: A.AdditionCorrect(x,tail,result)) -> SumCorrect(Con{x,xs},result):
  match result:
    case Some{+r}:
      +exact = Bridge.added_word_has_exact_mathematical_sum(x,tail,M.sum(xs),r,tail_exact,correct)
      M.Both{exact,M.Both{M.Representable{r,exact},tail_fit}}
    case None{}:
      fit => rejected_addition_excludes_fitted_whole(x,xs,tail,tail_exact,correct,fit)

def tail_case(+x: V.Int64,+xs: List<&2,V.Int64>,tail_result: Maybe<&2,V.Int64>,
  correct: SumCorrect(xs,tail_result)) -> SumCorrect(Con{x,xs},Aggregate.plus(x,tail_result)):
  match tail_result:
    case None{}:
      fit => unfit_tail_excludes_fitted_whole(x,xs,correct,fit)
    case Some{+tail}:
      match correct:
        case M.Both{tail_exact,tail_fit}:
          addition_case(x,xs,tail,tail_exact,tail_fit,I.add(x,tail),A.checked_add_is_integer_addition(x,tail))

# Only the input list is quantified; scalar correctness and every suffix
# representability witness are derived, with no output/invariant premise.
law checked_sum_is_right_fold_integer_addition:
  for +xs: List<&2,V.Int64>
  SumCorrect(xs,Aggregate.sum(xs))
def checked_sum_is_right_fold_integer_addition(xs):
  match xs:
    case Nil{}: M.Both{{==},Unit{}}
    case Con{+x,+tail}:
      tail_case(x,tail,Aggregate.sum(tail),checked_sum_is_right_fold_integer_addition(tail))
