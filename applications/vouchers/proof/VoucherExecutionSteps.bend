# Internal one-step proof composition. Callback certificates concern exactly
# one actual return/state/event handoff; final public Voucher heads must derive
# them from fixed source, never take a completed action/outcome as a premise.
import Base
import ./VoucherSuccessEffects.bend as E
import ../../../library/MutationStateShapeProofs.bend as Shape
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/ReadOperationProofs.bend as Read
import ../../../library/MutationWriteTrace.bend as Write
import ../../../library/Proofs.bend as Event
import ../../../library/ValueScalarProofs.bend as Pair
import ../../../proof/Foundations.bend as F
import ../../../src/Termination.bend as T

def refusal(fuel: Nat,+initial: D.State,+working: D.State,+schema: D.Schema,+history: List<&2,S.OperationEvent>,+reason: D.Value) -> E.Success(initial,T.observe(fuel,S.Refuse{reason},schema,working,history)):
  match fuel:
    case 0n: Unit{}
    case 1n+n:
      %Equal.sym(S.Trace,T.observe(1n+n,S.Refuse{reason},schema,working,history),S.Final{working,history,S.Response{S.Refusal{},reason}},T.stopped(n,working,S.Response{S.Refusal{},reason},schema,history)) : E.Success(initial,_)
      Unit{}

def identity_finish(fuel: Nat,+initial: D.State,+schema: D.Schema,+history: List<&2,S.OperationEvent>,+value: D.Value) -> E.Success(initial,T.observe(fuel,S.Finish{value},schema,initial,history)):
  match fuel:
    case 0n: Unit{}
    case 1n+n:
      %Equal.sym(S.Trace,T.observe(1n+n,S.Finish{value},schema,initial,history),S.Final{initial,history,S.Response{S.Success{},value}},T.stopped(n,initial,S.Response{S.Success{},value},schema,history)) : E.Success(initial,_)
      (E.StateUnchanged{},Pair.Both{Unit{},{==}})

def changed_finish(fuel: Nat,+initial: D.State,+working: D.State,+schema: D.Schema,+history: List<&2,S.OperationEvent>,+value: D.Value,+change: E.Change,valid: E.Valid(initial,change),same: {working == E.result(change,initial) : D.State}) -> E.Success(initial,T.observe(fuel,S.Finish{value},schema,working,history)):
  match fuel:
    case 0n: Unit{}
    case 1n+n:
      %Equal.sym(S.Trace,T.observe(1n+n,S.Finish{value},schema,working,history),S.Final{working,history,S.Response{S.Success{},value}},T.stopped(n,working,S.Response{S.Success{},value},schema,history)) : E.Success(initial,_)
      (change,Pair.Both{valid,same})

def read_case(+result: D.ResultOp,+remaining: Nat,+initial: D.State,+working: D.State,+schema: D.Schema,+collection: D.Collection,+key: String,+name: String,-resume: S.Return -> S.Action,+history: List<&2,S.OperationEvent>,actual: {D.operate(schema,working,D.ReadCell{collection,key,name}) == result : D.ResultOp},kind: Read.ResultKind(Read.Cell{},result),handler: @+observation: D.Observation -> E.Success(initial,T.observe(remaining,resume(S.Datum{observation}),schema,working,S.append(history,S.OperationEvent{D.ReadCell{collection,key,name},S.Reading{observation}})))) -> E.Success(initial,T.observe(1n+remaining,S.Access{D.ReadCell{collection,key,name},resume},schema,working,history)):
  match result:
    case D.FailureData{}:
      %Equal.sym(S.Trace,T.observe(1n+remaining,S.Access{D.ReadCell{collection,key,name},resume},schema,working,history),S.Final{working,S.append(history,S.OperationEvent{D.ReadCell{collection,key,name},S.ErrorOfData{}}),S.Response{S.DataError{},D.VAbsent{}}},Read.actual_data_failure_retains_its_event_and_finishes_without_a_return_callback(remaining,schema,working,D.ReadCell{collection,key,name},resume,history,actual)) : E.Success(initial,_)
      Unit{}
    case D.Observed{+observation}:
      %Equal.sym(S.Trace,T.observe(1n+remaining,S.Access{D.ReadCell{collection,key,name},resume},schema,working,history),T.observe(remaining,resume(S.Datum{observation}),schema,working,S.append(history,S.OperationEvent{D.ReadCell{collection,key,name},S.Reading{observation}})),Event.read_continuation(remaining,schema,working,D.ReadCell{collection,key,name},observation,resume,history,actual)) : E.Success(initial,_)
      handler(observation)
    case D.Changed{w}: F.absurd_boolean(E.Success(initial,T.observe(1n+remaining,S.Access{D.ReadCell{collection,key,name},resume},schema,working,history)),kind)

def cell_read(+remaining: Nat,+initial: D.State,+working: D.State,+schema: D.Schema,+collection: D.Collection,+key: String,+name: String,-resume: S.Return -> S.Action,+history: List<&2,S.OperationEvent>,handler: @+observation: D.Observation -> E.Success(initial,T.observe(remaining,resume(S.Datum{observation}),schema,working,S.append(history,S.OperationEvent{D.ReadCell{collection,key,name},S.Reading{observation}})))) -> E.Success(initial,T.observe(1n+remaining,S.Access{D.ReadCell{collection,key,name},resume},schema,working,history)):
  read_case(D.operate(schema,working,D.ReadCell{collection,key,name}),remaining,initial,working,schema,collection,key,name,resume,history,{==},Read.real_named_read_operations_have_only_the_expected_observation_or_data_failure(Read.Cell{},schema,working,collection,key,name),handler)

def changed_case(+next: D.State,+remaining: Nat,+initial: D.State,+working: D.State,+schema: D.Schema,+collection: D.Collection,+transform: Shape.Transform,shape: Shape.Shape(working,collection,transform,D.Changed{next}),-resume: S.Return -> S.Action,+history: List<&2,S.OperationEvent>,actual: {D.operate(schema,working,Shape.operation(collection,transform)) == D.Changed{next} : D.ResultOp},handler: @+next: D.State -> @+rows: List<&2,D.Row> -> @found: {D.rows_collection(collection,working) == Some{rows} : Maybe<&2,List<&2,D.Row>>} -> @same: {next == D.swap_collection(collection,working,Shape.apply(transform,rows)) : D.State} -> E.Success(initial,T.observe(remaining,resume(S.UnitValue{}),schema,next,S.append(history,S.OperationEvent{Shape.operation(collection,transform),S.Write{}})))) -> E.Success(initial,T.observe(1n+remaining,S.Access{Shape.operation(collection,transform),resume},schema,working,history)):
  match shape:
    case (rows,Pair.Both{found,same}):
      %Equal.sym(S.Trace,T.observe(1n+remaining,S.Access{Shape.operation(collection,transform),resume},schema,working,history),T.observe(remaining,resume(S.UnitValue{}),schema,next,S.append(history,S.OperationEvent{Shape.operation(collection,transform),S.Write{}})),Write.real_changed_primitive_retains_the_write_and_continues_in_its_actual_new_state(remaining,schema,working,next,Shape.operation(collection,transform),resume,history,actual)) : E.Success(initial,_)
      handler(next,rows,found,same)

def write_case(+result: D.ResultOp,+remaining: Nat,+initial: D.State,+working: D.State,+schema: D.Schema,+collection: D.Collection,+transform: Shape.Transform,-resume: S.Return -> S.Action,+history: List<&2,S.OperationEvent>,actual: {D.operate(schema,working,Shape.operation(collection,transform)) == result : D.ResultOp},shape: Shape.Shape(working,collection,transform,result),handler: @+next: D.State -> @+rows: List<&2,D.Row> -> @found: {D.rows_collection(collection,working) == Some{rows} : Maybe<&2,List<&2,D.Row>>} -> @same: {next == D.swap_collection(collection,working,Shape.apply(transform,rows)) : D.State} -> E.Success(initial,T.observe(remaining,resume(S.UnitValue{}),schema,next,S.append(history,S.OperationEvent{Shape.operation(collection,transform),S.Write{}})))) -> E.Success(initial,T.observe(1n+remaining,S.Access{Shape.operation(collection,transform),resume},schema,working,history)):
  match result:
    case D.FailureData{}:
      %Equal.sym(S.Trace,T.observe(1n+remaining,S.Access{Shape.operation(collection,transform),resume},schema,working,history),S.Final{working,S.append(history,S.OperationEvent{Shape.operation(collection,transform),S.ErrorOfData{}}),S.Response{S.DataError{},D.VAbsent{}}},Read.actual_data_failure_retains_its_event_and_finishes_without_a_return_callback(remaining,schema,working,Shape.operation(collection,transform),resume,history,actual)) : E.Success(initial,_)
      Unit{}
    case D.Observed{observation}: F.absurd_boolean(E.Success(initial,T.observe(1n+remaining,S.Access{Shape.operation(collection,transform),resume},schema,working,history)),shape)
    case D.Changed{+next}: changed_case(next,remaining,initial,working,schema,collection,transform,shape,resume,history,actual,handler)

def row_write(+remaining: Nat,+initial: D.State,+working: D.State,+schema: D.Schema,+collection: D.Collection,+transform: Shape.Transform,-resume: S.Return -> S.Action,+history: List<&2,S.OperationEvent>,handler: @+next: D.State -> @+rows: List<&2,D.Row> -> @found: {D.rows_collection(collection,working) == Some{rows} : Maybe<&2,List<&2,D.Row>>} -> @same: {next == D.swap_collection(collection,working,Shape.apply(transform,rows)) : D.State} -> E.Success(initial,T.observe(remaining,resume(S.UnitValue{}),schema,next,S.append(history,S.OperationEvent{Shape.operation(collection,transform),S.Write{}})))) -> E.Success(initial,T.observe(1n+remaining,S.Access{Shape.operation(collection,transform),resume},schema,working,history)):
  write_case(D.operate(schema,working,Shape.operation(collection,transform)),remaining,initial,working,schema,collection,transform,resume,history,{==},Shape.actual_ordinary_row_transform_has_complete_input_state_shape_for_every_input(schema,working,collection,transform),handler)
