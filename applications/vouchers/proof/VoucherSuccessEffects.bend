# Independent finite state-effect witness for a COMPLETED raw Success:
# unchanged state, or one of the three concrete proved table transformations.
# The witness carries real input-view evidence and literal resulting-state
# equality, never an invariant function or an assumed desired postcondition.
import Base
import ./VoucherLifetimeState.bend as State
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/ValueScalarProofs.bend as Pair
import ../../../library/ReceiptLaws.bend as RL
import ../../../library/MutationPublicationProofs.bend as Boundary
import ../../../contract/Requirements.bend as R

type Change is Data:
  StateUnchanged{}
  TableTransformed{update: State.Update,owner: String,rows: List<&2,D.Row>}
def result(change: Change,before: D.State) -> D.State:
  match change:
    case StateUnchanged{}: before
    case TableTransformed{update,owner,rows}: State.transformed_state(update,owner,before,rows)
def Valid(+before: D.State,change: Change) -> Data:
  match change:
    case StateUnchanged{}: Unit
    case TableTransformed{update,owner,rows}: {D.rows_collection(D.Application{owner},before) == Some{rows} : Maybe<&2,List<&2,D.Row>>}

def SuccessResult(+before: D.State,+working: D.State,response: S.Response) -> Data:
  match response:
    case S.Response{S.Success{},value}: Sigma<&2,&2,Change,change => Pair.Both<Valid(before,change),{working == result(change,before) : D.State}>>
    case _: Unit

def Success(+before: D.State,trace: S.Trace) -> Data:
  match trace:
    case S.Prefix{working,events}: Unit
    case S.Final{working,events,response}: SuccessResult(before,working,response)

def change_preserves_global(+change: Change,+before: D.State,valid: Valid(before,change),previous: State.Global(before)) -> State.Global(result(change,before)):
  match change:
    case StateUnchanged{}: previous
    case TableTransformed{update,owner,rows}: State.the_three_proved_concrete_replacement_transforms_preserve_every_principal_lifetime(update,owner,before,rows,valid,previous)

def finalized_success_case(response: S.Response,+schema: D.Schema,+limits: S.Limits,+before: D.State,+working: D.State,+change: Change,valid: Valid(before,change),same: {working == result(change,before) : D.State},previous: State.Global(before)) -> State.Global(S.publish(response,before,working)):
  match response:
    case S.Response{S.Success{},value}:
      %Equal.sym(D.State,working,result(change,before),same) : State.Global(_)
      change_preserves_global(change,before,valid,previous)
    case S.Response{S.Input{},value}: previous
    case S.Response{S.Authentication{},value}: previous
    case S.Response{S.Certificate{},value}: previous
    case S.Response{S.DataError{},value}: previous
    case S.Response{S.Limit{},value}: previous
    case S.Response{S.Failure{},value}: previous
    case S.Response{S.Refusal{},value}: previous

def raw_success(+schema: D.Schema,+limits: S.Limits,+before: D.State,+working: D.State,+value: D.Value,effect: SuccessResult(before,working,S.Response{S.Success{},value}),previous: State.Global(before)) -> State.Global(S.publish(R.finalize(S.Response{S.Success{},value},RL.technical(schema,limits),working),before,working)):
  match effect:
    case (change,Pair.Both{valid,same}): finalized_success_case(R.finalize(S.Response{S.Success{},value},RL.technical(schema,limits),working),schema,limits,before,working,change,valid,same,previous)

def response_case(response: S.Response,+schema: D.Schema,+limits: S.Limits,+before: D.State,+working: D.State,effect: SuccessResult(before,working,response),previous: State.Global(before)) -> State.Global(S.publish(R.finalize(response,RL.technical(schema,limits),working),before,working)):
  match response:
    case S.Response{S.Success{},value}: raw_success(schema,limits,before,working,value,effect,previous)
    case S.Response{S.Refusal{},value}:
      %Equal.sym(D.State,S.publish(R.finalize(S.Response{S.Refusal{},value},RL.technical(schema,limits),working),before,working),before,Boundary.actual_refusal_finalization_cannot_publish_earlier_working_writes(RL.technical(schema,limits),value,before,working)) : State.Global(_)
      previous
    case S.Response{S.DataError{},value}:
      %Equal.sym(D.State,S.publish(R.finalize(S.Response{S.DataError{},value},RL.technical(schema,limits),working),before,working),before,Boundary.actual_data_error_finalization_cannot_publish_earlier_working_writes(RL.technical(schema,limits),value,before,working)) : State.Global(_)
      previous
    case S.Response{S.Input{},value}: previous
    case S.Response{S.Authentication{},value}: previous
    case S.Response{S.Certificate{},value}: previous
    case S.Response{S.Limit{},value}: previous
    case S.Response{S.Failure{},value}: previous

# Internal composition only. The final public actual-program/replay theorem
# must DERIVE this effect witness from inputs, never accept it as a premise.
def advance_preserves(+trace: S.Trace,+schema: D.Schema,+limits: S.Limits,+before: D.State,effect: Success(before,trace),previous: State.Global(before)) -> State.Global(RL.advance(trace,schema,limits,before)):
  match trace:
    case S.Prefix{working,events}: previous
    case S.Final{working,events,response}: response_case(response,schema,limits,before,working,effect,previous)
