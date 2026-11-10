# Rollback belongs to the existing publication boundary: the actual engine
# keeps earlier writes in its working state/event path. Core.conclude alone
# decides which state is published. No administrator laws or tools are changed.
import Base
import ./MutationWritePlan.bend as M
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ../src/Core.bend as Core

def StopsRollback(plan: M.Plan,+initial: D.State) -> Data:
  match plan:
    case M.WriteHandoff{working,events}: Unit
    case M.WriteHalt{working,events,response}: {S.publish(response,initial,working) == initial : D.State}

def prefix_preserves_rollback(+plan: M.Plan,+event: S.OperationEvent,+initial: D.State,rollback: StopsRollback(plan,initial)) -> StopsRollback(M.prepend(event,plan),initial):
  match plan:
    case M.WriteHandoff{working,events}: Unit{}
    case M.WriteHalt{working,events,response}: rollback

def result_preserves_rollback(+result: D.ResultOp,+before: D.State,+op: D.Operation,+tail: M.Plan,+initial: D.State,rollback: StopsRollback(tail,initial)) -> StopsRollback(M.combine(result,before,op,tail),initial):
  match result:
    case D.FailureData{}: {==}
    case D.Observed{observation}: {==}
    case D.Changed{working}: prefix_preserves_rollback(tail,S.OperationEvent{op,S.Write{}},initial,rollback)

law every_stopped_actual_write_plan_discards_all_working_writes_at_publication:
  for +operations: List<&2,D.Operation>
  for +schema: D.Schema
  for +before: D.State
  for +initial: D.State
  StopsRollback(M.plan(operations,schema,before),initial)
def every_stopped_actual_write_plan_discards_all_working_writes_at_publication(operations,schema,before,initial):
  match operations:
    case Nil{}: Unit{}
    case Con{+op,+tail}: result_preserves_rollback(D.operate(schema,before,op),before,op,M.plan(tail,schema,M.after(D.operate(schema,before,op),before)),initial,every_stopped_actual_write_plan_discards_all_working_writes_at_publication(tail,schema,M.after(D.operate(schema,before,op),before),initial))

law existing_core_conclusion_publishes_exactly_success_and_rolls_back_every_other_status:
  for +status: S.Status
  for -value: D.Value
  for -working: D.State
  for -events: List<&2,S.OperationEvent>
  for -bytes: List<&2,U32>
  for -initial: D.State
  {Core.conclude(Core.Prepared{working,events,S.Response{status,value},bytes},initial) == Core.Conclusion{Bool.pick(D.State,S.is_success(status),working,initial),S.Response{status,value},bytes} : Core.Conclusion}
def existing_core_conclusion_publishes_exactly_success_and_rolls_back_every_other_status(status,value,working,events,bytes,initial):
  match status:
    case S.Input{}: {==}
    case S.Authentication{}: {==}
    case S.Certificate{}: {==}
    case S.DataError{}: {==}
    case S.Limit{}: {==}
    case S.Failure{}: {==}
    case S.Refusal{}: {==}
    case S.Success{}: {==}

# Refusal may be normalized to DataError/Limit during finalization; all retain
# rollback, even for invalid payloads/resources and arbitrary working states.
def finalized_refusal_technique(ok: Bool,fits: Bool,+value: D.Value,+initial: D.State,+working: D.State) -> {S.publish(R.response_technique_cases(ok,fits,S.Response{S.Refusal{},value}),initial,working) == initial : D.State}:
  match ok fits:
    case False{} False{}: {==}
    case False{} True{}: {==}
    case True{} False{}: {==}
    case True{} True{}: {==}

law actual_refusal_finalization_cannot_publish_earlier_working_writes:
  for configuration: S.Configuration
  for +value: D.Value
  for +initial: D.State
  for +working: D.State
  {S.publish(R.finalize(S.Response{S.Refusal{},value},configuration,working),initial,working) == initial : D.State}
def actual_refusal_finalization_cannot_publish_earlier_working_writes(configuration,value,initial,working):
  match configuration:
    case S.Configuration{schema,laws,+limits,environment}: finalized_refusal_technique(D.value_valid(value),R.fits(R.limit_response(limits),S.response_value(S.Response{S.Refusal{},value})),value,initial,working)

law actual_data_error_finalization_cannot_publish_earlier_working_writes:
  for configuration: S.Configuration
  for -value: D.Value
  for -initial: D.State
  for -working: D.State
  {S.publish(R.finalize(S.Response{S.DataError{},value},configuration,working),initial,working) == initial : D.State}
def actual_data_error_finalization_cannot_publish_earlier_working_writes(configuration,value,initial,working):
  match configuration:
    case S.Configuration{schema,laws,limits,environment}: {==}
