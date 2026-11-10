# One primitive followed by a LOCAL DATA mutation decision. Decoder equality
# is a necessary component refinement for an arbitrary CPS handler, consumed
# once. Public helper theorems discharge it for ALL Return variants themselves.
import Base
import ./MutationDecision.bend as B
import ./MutationWritePlan.bend as M
import ./MutationWriteTrace.bend as Write
import ./ReadOperationProofs.bend as Failure
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Proofs.bend as Event
import ../src/Termination.bend as T

def trace(~Out: Data,decision: B.Decision<Out>,+remaining: Nat,+schema: D.Schema,+state: D.State,done: Out -> S.Action,history: List<&2,S.OperationEvent>) -> S.Trace:
  match decision:
    case B.MutationReturn{result}: T.observe(2n+remaining,done(result),schema,state,history)
    case B.MutationWrite{operation,result}: Write.finish(M.plan([operation],schema,state),1n+remaining,schema,done(result),history)
    case B.MutationRefuse{reason}: S.Final{state,history,S.Response{S.Refusal{},reason}}

law executing_a_local_mutation_decision_has_exact_primitive_result_and_handoff:
  for ~Out: Data
  for +decision: B.Decision<Out>
  for +remaining: Nat
  for +schema: D.Schema
  for +state: D.State
  for -done: Out -> S.Action
  for +history: List<&2,S.OperationEvent>
  {T.observe(2n+remaining,B.action(~Out,decision,done),schema,state,history) == trace(~Out,decision,remaining,schema,state,done,history) : S.Trace}
def executing_a_local_mutation_decision_has_exact_primitive_result_and_handoff(Out,decision,remaining,schema,state,done,history):
  match decision:
    case B.MutationReturn{result}: {==}
    case B.MutationWrite{operation,result}: Write.actual_ordered_write_sequence_has_total_exact_evolving_state_behavior([operation],schema,state,remaining,done(result),history)
    case B.MutationRefuse{reason}: T.stopped(1n+remaining,state,S.Response{S.Refusal{},reason},schema,history)

def result_trace(~Out: Data,~Env: Data,~decode: Env -> S.Return -> B.Decision<Out>,+env: Env,result: D.ResultOp,+remaining: Nat,+schema: D.Schema,+before: D.State,+op: D.Operation,done: Out -> S.Action,history: List<&2,S.OperationEvent>) -> S.Trace:
  match result:
    case D.FailureData{}: S.Final{before,S.append(history,S.OperationEvent{op,S.ErrorOfData{}}),S.Response{S.DataError{},D.VAbsent{}}}
    case D.Observed{+observation}: trace(~Out,decode(env,S.Datum{observation}),remaining,schema,before,done,S.append(history,S.OperationEvent{op,S.Reading{observation}}))
    case D.Changed{working}: trace(~Out,decode(env,S.UnitValue{}),remaining,schema,working,done,S.append(history,S.OperationEvent{op,S.Write{}}))

def result_case(~Out: Data,~Env: Data,~decode: Env -> S.Return -> B.Decision<Out>,+env: Env,+result: D.ResultOp,+remaining: Nat,+schema: D.Schema,+before: D.State,+op: D.Operation,-resume: S.Return -> S.Action,-done: Out -> S.Action,+history: List<&2,S.OperationEvent>,actual: {D.operate(schema,before,op) == result : D.ResultOp},handler: @+r: S.Return -> {resume(r) == B.action(~Out,decode(env,r),done) : S.Action}) ->
  {T.observe(3n+remaining,S.Access{op,resume},schema,before,history) == result_trace(~Out,~Env,~decode,env,result,remaining,schema,before,op,done,history) : S.Trace}:
  match result:
    case D.FailureData{}: Failure.actual_data_failure_retains_its_event_and_finishes_without_a_return_callback(2n+remaining,schema,before,op,resume,history,actual)
    case D.Observed{+observation}:
      Equal.trans(S.Trace,T.observe(3n+remaining,S.Access{op,resume},schema,before,history),T.observe(2n+remaining,resume(S.Datum{observation}),schema,before,S.append(history,S.OperationEvent{op,S.Reading{observation}})),trace(~Out,decode(env,S.Datum{observation}),remaining,schema,before,done,S.append(history,S.OperationEvent{op,S.Reading{observation}})),Event.read_continuation(2n+remaining,schema,before,op,observation,resume,history,actual),
        Equal.trans(S.Trace,T.observe(2n+remaining,resume(S.Datum{observation}),schema,before,S.append(history,S.OperationEvent{op,S.Reading{observation}})),T.observe(2n+remaining,B.action(~Out,decode(env,S.Datum{observation}),done),schema,before,S.append(history,S.OperationEvent{op,S.Reading{observation}})),trace(~Out,decode(env,S.Datum{observation}),remaining,schema,before,done,S.append(history,S.OperationEvent{op,S.Reading{observation}})),Equal.cong(S.Action,S.Trace,action => T.observe(2n+remaining,action,schema,before,S.append(history,S.OperationEvent{op,S.Reading{observation}})),resume(S.Datum{observation}),B.action(~Out,decode(env,S.Datum{observation}),done),handler(S.Datum{observation})),executing_a_local_mutation_decision_has_exact_primitive_result_and_handoff(~Out,decode(env,S.Datum{observation}),remaining,schema,before,done,S.append(history,S.OperationEvent{op,S.Reading{observation}}))))
    case D.Changed{+working}:
      Equal.trans(S.Trace,T.observe(3n+remaining,S.Access{op,resume},schema,before,history),T.observe(2n+remaining,resume(S.UnitValue{}),schema,working,S.append(history,S.OperationEvent{op,S.Write{}})),trace(~Out,decode(env,S.UnitValue{}),remaining,schema,working,done,S.append(history,S.OperationEvent{op,S.Write{}})),Write.real_changed_primitive_retains_the_write_and_continues_in_its_actual_new_state(2n+remaining,schema,before,working,op,resume,history,actual),
        Equal.trans(S.Trace,T.observe(2n+remaining,resume(S.UnitValue{}),schema,working,S.append(history,S.OperationEvent{op,S.Write{}})),T.observe(2n+remaining,B.action(~Out,decode(env,S.UnitValue{}),done),schema,working,S.append(history,S.OperationEvent{op,S.Write{}})),trace(~Out,decode(env,S.UnitValue{}),remaining,schema,working,done,S.append(history,S.OperationEvent{op,S.Write{}})),Equal.cong(S.Action,S.Trace,action => T.observe(2n+remaining,action,schema,working,S.append(history,S.OperationEvent{op,S.Write{}})),resume(S.UnitValue{}),B.action(~Out,decode(env,S.UnitValue{}),done),handler(S.UnitValue{})),executing_a_local_mutation_decision_has_exact_primitive_result_and_handoff(~Out,decode(env,S.UnitValue{}),remaining,schema,working,done,S.append(history,S.OperationEvent{op,S.Write{}}))))

law an_actual_primitive_and_its_locally_refined_decoder_have_total_exact_behavior:
  for ~Out: Data
  for ~Env: Data
  for ~decode: Env -> S.Return -> B.Decision<Out>
  for +env: Env
  for +remaining: Nat
  for +schema: D.Schema
  for +before: D.State
  for +op: D.Operation
  for -resume: S.Return -> S.Action
  for -done: Out -> S.Action
  for +history: List<&2,S.OperationEvent>
  for handler: @+r: S.Return -> {resume(r) == B.action(~Out,decode(env,r),done) : S.Action}
  {T.observe(3n+remaining,S.Access{op,resume},schema,before,history) == result_trace(~Out,~Env,~decode,env,D.operate(schema,before,op),remaining,schema,before,op,done,history) : S.Trace}
def an_actual_primitive_and_its_locally_refined_decoder_have_total_exact_behavior(Out,Env,decode,env,remaining,schema,before,op,resume,done,history,handler):
  result_case(~Out,~Env,~decode,env,D.operate(schema,before,op),remaining,schema,before,op,resume,done,history,{==},handler)
