# Publication theorem is CONDITIONAL IN ITS RESULT, with no assumed success:
# actual technical finalization either publishes the corresponding working pair
# on Success or preserves the entire initial state on every other status.
# This makes no liveness or guaranteed-resource-success assertion.
import Base
import ../Voucher.bend as V
import ./VoucherPairProofs.bend as P
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../contract/Requirements.bend as R
import ../../../src/Termination.bend as T

def Correct(+owner: String,+request: String,+input: String,+cancel: Bool,+initial: D.State,+working: D.State,response: S.Response) -> Type:
  match response:
    case S.Response{S.Success{},value}: P.PairState(owner,request,input,cancel,S.publish(S.Response{S.Success{},value},initial,working))
    case S.Response{S.Input{},value}: {S.publish(S.Response{S.Input{},value},initial,working) == initial : D.State}
    case S.Response{S.Authentication{},value}: {S.publish(S.Response{S.Authentication{},value},initial,working) == initial : D.State}
    case S.Response{S.Certificate{},value}: {S.publish(S.Response{S.Certificate{},value},initial,working) == initial : D.State}
    case S.Response{S.DataError{},value}: {S.publish(S.Response{S.DataError{},value},initial,working) == initial : D.State}
    case S.Response{S.Limit{},value}: {S.publish(S.Response{S.Limit{},value},initial,working) == initial : D.State}
    case S.Response{S.Failure{},value}: {S.publish(S.Response{S.Failure{},value},initial,working) == initial : D.State}
    case S.Response{S.Refusal{},value}: {S.publish(S.Response{S.Refusal{},value},initial,working) == initial : D.State}

def response_case(response: S.Response,+owner: String,+request: String,+input: String,+cancel: Bool,+initial: D.State,+working: D.State,pair: P.PairState(owner,request,input,cancel,working)) -> Correct(owner,request,input,cancel,initial,working,response):
  match response:
    case S.Response{S.Success{},value}: pair
    case S.Response{S.Input{},value}: {==}
    case S.Response{S.Authentication{},value}: {==}
    case S.Response{S.Certificate{},value}: {==}
    case S.Response{S.DataError{},value}: {==}
    case S.Response{S.Limit{},value}: {==}
    case S.Response{S.Failure{},value}: {==}
    case S.Response{S.Refusal{},value}: {==}

law technical_finalization_keeps_initial_or_publishes_the_complete_computed_pair:
  for configuration: S.Configuration
  for +owner: String
  for +request: String
  for +input: String
  for +cancel: Bool
  for +initial: D.State
  for +old: List<&2,D.Row>
  for +response: S.Response
  for found: {D.rows_collection(D.Application{owner},initial) == Some{old} : Maybe<&2,List<&2,D.Row>>}
  Correct(owner,request,input,cancel,initial,P.state(owner,initial,old,request,input,cancel),R.finalize(response,configuration,P.state(owner,initial,old,request,input,cancel)))
def technical_finalization_keeps_initial_or_publishes_the_complete_computed_pair(configuration,owner,request,input,cancel,initial,old,response,found):
  response_case(R.finalize(response,configuration,P.state(owner,initial,old,request,input,cancel)),owner,request,input,cancel,initial,P.state(owner,initial,old,request,input,cancel),P.the_computed_replacement_state_contains_both_exact_corresponding_rows(owner,initial,old,request,input,cancel,found))
