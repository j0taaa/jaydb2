# Public total functional heads. Only input DATA is supplied: no successful
# operation/output/trace premise. Done is arbitrary affine Action; its behavior
# is observed from the actual final working state after the owned write prefix.
import Base
import ./MutationWriteSequence.bend as W
import ./MutationWritePlan.bend as M
import ./MutationWriteTrace.bend as R
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Action.bend as A
import ./Mutation.bend as Mutation
import ../src/Termination.bend as T

law actual_define_rows_has_total_exact_state_events_short_circuit_and_handoff:
  for +schema: D.Schema
  for +before: D.State
  for +collection: D.Collection
  for +xs: List<&2,D.Row>
  for +remaining: Nat
  for -done: S.Action
  for +history: List<&2,S.OperationEvent>
  {T.observe(M.depth(W.rows(collection,xs),1n+remaining),A.define_rows(collection,xs,done),schema,before,history) == R.finish(M.plan(W.rows(collection,xs),schema,before),1n+remaining,schema,done,history) : S.Trace}
def actual_define_rows_has_total_exact_state_events_short_circuit_and_handoff(schema,before,collection,xs,remaining,done,history):
  Equal.trans(S.Trace,T.observe(M.depth(W.rows(collection,xs),1n+remaining),A.define_rows(collection,xs,done),schema,before,history),T.observe(M.depth(W.rows(collection,xs),1n+remaining),W.perform(W.rows(collection,xs),done),schema,before,history),R.finish(M.plan(W.rows(collection,xs),schema,before),1n+remaining,schema,done,history),Equal.cong(S.Action,S.Trace,action => T.observe(M.depth(W.rows(collection,xs),1n+remaining),action,schema,before,history),A.define_rows(collection,xs,done),W.perform(W.rows(collection,xs),done),W.actual_define_rows_is_exactly_the_ordered_named_write_sequence(collection,xs,done)),R.actual_ordered_write_sequence_has_total_exact_evolving_state_behavior(W.rows(collection,xs),schema,before,remaining,done,history))

law actual_remove_rows_has_total_exact_state_events_short_circuit_and_handoff:
  for +schema: D.Schema
  for +before: D.State
  for +collection: D.Collection
  for +xs: List<&2,String>
  for +remaining: Nat
  for -done: S.Action
  for +history: List<&2,S.OperationEvent>
  {T.observe(M.depth(W.removals(collection,xs),1n+remaining),Mutation.remove_rows(collection,xs,done),schema,before,history) == R.finish(M.plan(W.removals(collection,xs),schema,before),1n+remaining,schema,done,history) : S.Trace}
def actual_remove_rows_has_total_exact_state_events_short_circuit_and_handoff(schema,before,collection,xs,remaining,done,history):
  Equal.trans(S.Trace,T.observe(M.depth(W.removals(collection,xs),1n+remaining),Mutation.remove_rows(collection,xs,done),schema,before,history),T.observe(M.depth(W.removals(collection,xs),1n+remaining),W.perform(W.removals(collection,xs),done),schema,before,history),R.finish(M.plan(W.removals(collection,xs),schema,before),1n+remaining,schema,done,history),Equal.cong(S.Action,S.Trace,action => T.observe(M.depth(W.removals(collection,xs),1n+remaining),action,schema,before,history),Mutation.remove_rows(collection,xs,done),W.perform(W.removals(collection,xs),done),W.actual_remove_rows_is_exactly_the_ordered_named_write_sequence(collection,xs,done)),R.actual_ordered_write_sequence_has_total_exact_evolving_state_behavior(W.removals(collection,xs),schema,before,remaining,done,history))

law actual_columns_has_total_exact_state_events_short_circuit_and_handoff:
  for +schema: D.Schema
  for +before: D.State
  for +collection: D.Collection
  for +key: String
  for +xs: List<&2,D.Field>
  for +remaining: Nat
  for -done: S.Action
  for +history: List<&2,S.OperationEvent>
  {T.observe(M.depth(W.columns(collection,key,xs),1n+remaining),Mutation.columns(collection,key,xs,done),schema,before,history) == R.finish(M.plan(W.columns(collection,key,xs),schema,before),1n+remaining,schema,done,history) : S.Trace}
def actual_columns_has_total_exact_state_events_short_circuit_and_handoff(schema,before,collection,key,xs,remaining,done,history):
  Equal.trans(S.Trace,T.observe(M.depth(W.columns(collection,key,xs),1n+remaining),Mutation.columns(collection,key,xs,done),schema,before,history),T.observe(M.depth(W.columns(collection,key,xs),1n+remaining),W.perform(W.columns(collection,key,xs),done),schema,before,history),R.finish(M.plan(W.columns(collection,key,xs),schema,before),1n+remaining,schema,done,history),Equal.cong(S.Action,S.Trace,action => T.observe(M.depth(W.columns(collection,key,xs),1n+remaining),action,schema,before,history),Mutation.columns(collection,key,xs,done),W.perform(W.columns(collection,key,xs),done),W.actual_columns_is_exactly_the_ordered_named_write_sequence(collection,key,xs,done)),R.actual_ordered_write_sequence_has_total_exact_evolving_state_behavior(W.columns(collection,key,xs),schema,before,remaining,done,history))
