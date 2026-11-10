# Total actual read/add/write engine behavior. Numeric correctness and exact
# overflow rejection are supplied by CounterDecisions' independent integer
# meaning, rather than assuming an overflow flag, output word, or write result.
import Base
import ./MutationCounterDecisions.bend as C
import ./MutationDecisionTrace.bend as Trace
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Mutation.bend as M
import ./Value.bend as V
import ../src/Termination.bend as T

law actual_counter_add_has_total_exact_read_checked_sum_write_and_handoff:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +key: String
  for +column: String
  for +delta: V.Int64
  for +remaining: Nat
  for -done: V.Int64 -> S.Action
  for +history: List<&2,S.OperationEvent>
  {T.observe(3n+remaining,M.counter_add(collection,key,column,delta,done),schema,state,history) == Trace.result_trace(~V.Int64,~C.CounterContext,~C.decode,C.CounterContext{collection,key,column,delta},D.operate(schema,state,D.ReadCell{collection,key,column}),remaining,schema,state,D.ReadCell{collection,key,column},done,history) : S.Trace}
def actual_counter_add_has_total_exact_read_checked_sum_write_and_handoff(schema,state,collection,key,column,delta,remaining,done,history):
  Trace.an_actual_primitive_and_its_locally_refined_decoder_have_total_exact_behavior(~V.Int64,~C.CounterContext,~C.decode,C.CounterContext{collection,key,column,delta},remaining,schema,state,D.ReadCell{collection,key,column},M.counter_read(collection,key,column,delta,done),done,history,r => C.actual_counter_decoder_has_the_exact_decision_for_every_return(collection,key,column,delta,done,r))

law actual_next_is_the_same_total_checked_counter_with_delta_one:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +key: String
  for +column: String
  for +remaining: Nat
  for -done: V.Int64 -> S.Action
  for +history: List<&2,S.OperationEvent>
  {T.observe(3n+remaining,M.next(collection,key,column,done),schema,state,history) == Trace.result_trace(~V.Int64,~C.CounterContext,~C.decode,C.CounterContext{collection,key,column,V.Int64{0,1}},D.operate(schema,state,D.ReadCell{collection,key,column}),remaining,schema,state,D.ReadCell{collection,key,column},done,history) : S.Trace}
def actual_next_is_the_same_total_checked_counter_with_delta_one(schema,state,collection,key,column,remaining,done,history):
  actual_counter_add_has_total_exact_read_checked_sum_write_and_handoff(schema,state,collection,key,column,V.Int64{0,1},remaining,done,history)
