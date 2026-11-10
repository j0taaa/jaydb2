# Total exact interpreter theorem, including the changing working state,
# retained first-stop event, and caller handoff. No output/result/invariant
# premise at the public boundary; arbitrary done may itself read/write/refuse.
import Base
import ./MutationWriteSequence.bend as W
import ./MutationWritePlan.bend as M
import ./QueryReadTrace.bend as H
import ./ReadOperationProofs.bend as Failure
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Action.bend as A
import ./Proofs.bend as Event
import ../src/Termination.bend as T

def finish(plan: M.Plan,+remaining: Nat,+schema: D.Schema,done: S.Action,history: List<&2,S.OperationEvent>) -> S.Trace:
  match plan:
    case M.WriteHandoff{working,events}: T.observe(remaining,done,schema,working,H.append_events(events,history))
    case M.WriteHalt{working,events,response}: S.Final{working,H.append_events(events,history),response}

law real_changed_primitive_retains_the_write_and_continues_in_its_actual_new_state:
  for +remaining: Nat
  for +schema: D.Schema
  for +before: D.State
  for +working: D.State
  for +op: D.Operation
  for -resume: S.Return -> S.Action
  for +history: List<&2,S.OperationEvent>
  for actual: {D.operate(schema,before,op) == D.Changed{working} : D.ResultOp}
  {S.resume_execution_trace(remaining,S.step(S.Access{op,resume},schema,before),schema,history) == T.observe(remaining,resume(S.UnitValue{}),schema,working,S.append(history,S.OperationEvent{op,S.Write{}})) : S.Trace}
def real_changed_primitive_retains_the_write_and_continues_in_its_actual_new_state(remaining,schema,before,working,op,resume,history,actual):
  %Equal.sym(D.ResultOp,D.operate(schema,before,op),D.Changed{working},actual) :
    {S.resume_execution_trace(remaining,S.apply(_,before,op,resume),schema,history) == T.observe(remaining,resume(S.UnitValue{}),schema,working,S.append(history,S.OperationEvent{op,S.Write{}})) : S.Trace}
  T.continuation(remaining,working,resume(S.UnitValue{}),S.OperationEvent{op,S.Write{}},schema,history)

law malformed_write_return_refusal_finishes_for_any_remaining_owned_sequence_budget:
  for operations: List<&2,D.Operation>
  for +remaining: Nat
  for -schema: D.Schema
  for -state: D.State
  for -history: List<&2,S.OperationEvent>
  {T.observe(M.depth(operations,1n+remaining),S.Refuse{D.VText{"unexpected write return"}},schema,state,history) == S.Final{state,history,S.Response{S.Refusal{},D.VText{"unexpected write return"}}} : S.Trace}
def malformed_write_return_refusal_finishes_for_any_remaining_owned_sequence_budget(operations,remaining,schema,state,history):
  match operations:
    case Nil{}: T.stopped(remaining,state,S.Response{S.Refusal{},D.VText{"unexpected write return"}},schema,history)
    case Con{op,tail}: T.stopped(M.depth(tail,1n+remaining),state,S.Response{S.Refusal{},D.VText{"unexpected write return"}},schema,history)

law an_actual_earlier_write_stays_before_all_later_source_events:
  for +plan: M.Plan
  for +event: S.OperationEvent
  for +remaining: Nat
  for +schema: D.Schema
  for -done: S.Action
  for +history: List<&2,S.OperationEvent>
  {finish(plan,remaining,schema,done,S.append(history,event)) == finish(M.prepend(event,plan),remaining,schema,done,history) : S.Trace}
def an_actual_earlier_write_stays_before_all_later_source_events(plan,event,remaining,schema,done,history):
  match plan:
    case M.WriteHandoff{working,events}: {==}
    case M.WriteHalt{working,events,response}: {==}

def result_case(+result: D.ResultOp,+tail: List<&2,D.Operation>,+schema: D.Schema,+before: D.State,+op: D.Operation,+remaining: Nat,-done: S.Action,+history: List<&2,S.OperationEvent>,actual: {D.operate(schema,before,op) == result : D.ResultOp},recursive: @+earlier: List<&2,S.OperationEvent> -> {T.observe(M.depth(tail,1n+remaining),W.perform(tail,done),schema,M.after(result,before),earlier) == finish(M.plan(tail,schema,M.after(result,before)),1n+remaining,schema,done,earlier) : S.Trace}) ->
  {T.observe(M.depth(Con{op,tail},1n+remaining),W.perform(Con{op,tail},done),schema,before,history) == finish(M.combine(result,before,op,M.plan(tail,schema,M.after(result,before))),1n+remaining,schema,done,history) : S.Trace}:
  match result:
    case D.FailureData{}: Failure.actual_data_failure_retains_its_event_and_finishes_without_a_return_callback(M.depth(tail,1n+remaining),schema,before,op,r => A.written(W.perform(tail,done),r),history,actual)
    case D.Observed{+observation}:
      Equal.trans(S.Trace,T.observe(M.depth(Con{op,tail},1n+remaining),W.perform(Con{op,tail},done),schema,before,history),T.observe(M.depth(tail,1n+remaining),S.Refuse{D.VText{"unexpected write return"}},schema,before,S.append(history,S.OperationEvent{op,S.Reading{observation}})),S.Final{before,S.append(history,S.OperationEvent{op,S.Reading{observation}}),S.Response{S.Refusal{},D.VText{"unexpected write return"}}},Event.read_continuation(M.depth(tail,1n+remaining),schema,before,op,observation,r => A.written(W.perform(tail,done),r),history,actual),malformed_write_return_refusal_finishes_for_any_remaining_owned_sequence_budget(tail,remaining,schema,before,S.append(history,S.OperationEvent{op,S.Reading{observation}})))
    case D.Changed{+working}:
      Equal.trans(S.Trace,T.observe(M.depth(Con{op,tail},1n+remaining),W.perform(Con{op,tail},done),schema,before,history),T.observe(M.depth(tail,1n+remaining),W.perform(tail,done),schema,working,S.append(history,S.OperationEvent{op,S.Write{}})),finish(M.prepend(S.OperationEvent{op,S.Write{}},M.plan(tail,schema,working)),1n+remaining,schema,done,history),real_changed_primitive_retains_the_write_and_continues_in_its_actual_new_state(M.depth(tail,1n+remaining),schema,before,working,op,r => A.written(W.perform(tail,done),r),history,actual),
        Equal.trans(S.Trace,T.observe(M.depth(tail,1n+remaining),W.perform(tail,done),schema,working,S.append(history,S.OperationEvent{op,S.Write{}})),finish(M.plan(tail,schema,working),1n+remaining,schema,done,S.append(history,S.OperationEvent{op,S.Write{}})),finish(M.prepend(S.OperationEvent{op,S.Write{}},M.plan(tail,schema,working)),1n+remaining,schema,done,history),recursive(S.append(history,S.OperationEvent{op,S.Write{}})),an_actual_earlier_write_stays_before_all_later_source_events(M.plan(tail,schema,working),S.OperationEvent{op,S.Write{}},1n+remaining,schema,done,history)))

law actual_ordered_write_sequence_has_total_exact_evolving_state_behavior:
  for +operations: List<&2,D.Operation>
  for +schema: D.Schema
  for +before: D.State
  for +remaining: Nat
  for -done: S.Action
  for +history: List<&2,S.OperationEvent>
  {T.observe(M.depth(operations,1n+remaining),W.perform(operations,done),schema,before,history) == finish(M.plan(operations,schema,before),1n+remaining,schema,done,history) : S.Trace}
def actual_ordered_write_sequence_has_total_exact_evolving_state_behavior(operations,schema,before,remaining,done,history):
  match operations:
    case Nil{}: {==}
    case Con{+op,+tail}:
      result_case(D.operate(schema,before,op),tail,schema,before,op,remaining,done,history,{==},earlier => actual_ordered_write_sequence_has_total_exact_evolving_state_behavior(tail,schema,M.after(D.operate(schema,before,op),before),remaining,done,earlier))
