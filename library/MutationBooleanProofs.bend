# Public total conditional-mutation heads: input DATA only. Every local
# decoder certificate is discharged here, not assumed. The initial real read
# always remains in the history, including a rejected predicate or comparison.
import Base
import ./MutationBooleanDecisions.bend as B
import ./MutationDecisionTrace.bend as Trace
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Mutation.bend as M
import ../src/Termination.bend as T

law actual_insert_if_absent_has_total_exact_read_decision_write_and_handoff:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +row: D.Row
  for +remaining: Nat
  for -done: Bool -> S.Action
  for +history: List<&2,S.OperationEvent>
  {T.observe(3n+remaining,M.insert_if_absent(collection,row,done),schema,state,history) == Trace.result_trace(~Bool,~B.RowContext,~B.insertion,B.RowContext{collection,row},D.operate(schema,state,D.ViewExistence{collection,D.row_key(row)}),remaining,schema,state,D.ViewExistence{collection,D.row_key(row)},done,history) : S.Trace}
def actual_insert_if_absent_has_total_exact_read_decision_write_and_handoff(schema,state,collection,row,remaining,done,history):
  match row:
    case D.Row{+key,+fields}:
      Trace.an_actual_primitive_and_its_locally_refined_decoder_have_total_exact_behavior(~Bool,~B.RowContext,~B.insertion,B.RowContext{collection,D.Row{key,fields}},remaining,schema,state,D.ViewExistence{collection,key},M.inserted(collection,D.Row{key,fields},done),done,history,r => B.actual_insert_decoder_has_the_exact_decision_for_every_return(collection,D.Row{key,fields},done,r))

law actual_replace_if_has_total_exact_observation_predicate_full_row_write_and_handoff:
  for ~accept: D.Observation -> Bool
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +row: D.Row
  for +column: String
  for +remaining: Nat
  for -done: Bool -> S.Action
  for +history: List<&2,S.OperationEvent>
  {T.observe(3n+remaining,M.replace_if(~accept,collection,row,column,done),schema,state,history) == Trace.result_trace(~Bool,~B.RowContext,~B.replacement(~accept),B.RowContext{collection,row},D.operate(schema,state,D.ReadCell{collection,D.row_key(row),column}),remaining,schema,state,D.ReadCell{collection,D.row_key(row),column},done,history) : S.Trace}
def actual_replace_if_has_total_exact_observation_predicate_full_row_write_and_handoff(accept,schema,state,collection,row,column,remaining,done,history):
  match row:
    case D.Row{+key,+fields}:
      Trace.an_actual_primitive_and_its_locally_refined_decoder_have_total_exact_behavior(~Bool,~B.RowContext,~B.replacement(~accept),B.RowContext{collection,D.Row{key,fields}},remaining,schema,state,D.ReadCell{collection,key,column},M.replace_received(~accept,collection,D.Row{key,fields},done),done,history,r => B.actual_predicate_replacement_decoder_has_the_exact_decision_for_every_return(~accept,collection,D.Row{key,fields},done,r))

law actual_compare_exchange_has_total_exact_read_literal_comparison_full_row_write_and_handoff:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +row: D.Row
  for +column: String
  for +expected: D.Value
  for +remaining: Nat
  for -done: Bool -> S.Action
  for +history: List<&2,S.OperationEvent>
  {T.observe(3n+remaining,M.compare_exchange(collection,row,column,expected,done),schema,state,history) == Trace.result_trace(~Bool,~B.CompareContext,~B.comparison,B.CompareContext{collection,row,expected},D.operate(schema,state,D.ReadCell{collection,D.row_key(row),column}),remaining,schema,state,D.ReadCell{collection,D.row_key(row),column},done,history) : S.Trace}
def actual_compare_exchange_has_total_exact_read_literal_comparison_full_row_write_and_handoff(schema,state,collection,row,column,expected,remaining,done,history):
  match row:
    case D.Row{+key,+fields}:
      Trace.an_actual_primitive_and_its_locally_refined_decoder_have_total_exact_behavior(~Bool,~B.CompareContext,~B.comparison,B.CompareContext{collection,D.Row{key,fields},expected},remaining,schema,state,D.ReadCell{collection,key,column},M.cas_received(collection,D.Row{key,fields},expected,done),done,history,r => B.actual_compare_exchange_decoder_has_the_exact_decision_for_every_return(collection,D.Row{key,fields},expected,done,r))
