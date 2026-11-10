# Complete Summary.store binding to the independent checked count/suffix-sum
# proof and the actual evolving-state one-row write interpreter. No successful
# compute/write or completed trace is assumed. Failure does not invoke done.
import Base
import ./MutationOrderedProofs.bend as Writes
import ./MutationWritePlan.bend as Plan
import ./MutationWriteTrace.bend as Trace
import ./MutationWriteSequence.bend as Ops
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Logic.bend as L
import ./Summary.bend as Summary
import ./SummaryProofs.bend as Math
import ./Value.bend as V
import ../src/Termination.bend as T

def expected(result: Maybe<&2,Summary.Stats>,+schema: D.Schema,+state: D.State,+collection: D.Collection,+key: String,+remaining: Nat,done: S.Action,history: List<&2,S.OperationEvent>) -> S.Trace:
  match result:
    case None{}: S.Final{state,history,S.Response{S.Refusal{},D.VText{"summary overflow"}}}
    case Some{stats}: Trace.finish(Plan.plan(Ops.rows(collection,[Summary.row(key,stats)]),schema,state),1n+remaining,schema,done,history)

law actual_summary_store_result_refuses_or_performs_exactly_its_one_complete_row_write:
  for +result: Maybe<&2,Summary.Stats>
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +key: String
  for +remaining: Nat
  for -done: S.Action
  for +history: List<&2,S.OperationEvent>
  {T.observe(2n+remaining,Summary.store_result(collection,key,result,done),schema,state,history) == expected(result,schema,state,collection,key,remaining,done,history) : S.Trace}
def actual_summary_store_result_refuses_or_performs_exactly_its_one_complete_row_write(result,schema,state,collection,key,remaining,done,history):
  match result:
    case None{}: T.stopped(1n+remaining,state,S.Response{S.Refusal{},D.VText{"summary overflow"}},schema,history)
    case Some{Summary.Stats{+count,+total}}: Writes.actual_define_rows_has_total_exact_state_events_short_circuit_and_handoff(schema,state,collection,[Summary.row(key,Summary.Stats{count,total})],remaining,done,history)

law actual_summary_store_has_exact_checked_math_write_trace_and_handoff:
  for +values: List<&2,V.Int64>
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +key: String
  for +remaining: Nat
  for -done: S.Action
  for +history: List<&2,S.OperationEvent>
  L.E<{T.observe(2n+remaining,Summary.store(collection,key,values,done),schema,state,history) == expected(Summary.compute(values),schema,state,collection,key,remaining,done,history) : S.Trace},Math.SummaryCorrect(values,Summary.compute(values))>
def actual_summary_store_has_exact_checked_math_write_trace_and_handoff(values,schema,state,collection,key,remaining,done,history):
  L.Both{actual_summary_store_result_refuses_or_performs_exactly_its_one_complete_row_write(Summary.compute(values),schema,state,collection,key,remaining,done,history),Math.checked_summary_is_exact_count_and_right_fold_sum(values)}

law summary_row_has_exact_named_count_key_and_total_payloads:
  for +key: String
  for +count: V.Int64
  for +total: V.Int64
  L.E<{D.row_key(Summary.row(key,Summary.Stats{count,total})) == key : String},L.E<{D.find_field(fields(Summary.row(key,Summary.Stats{count,total})),"count") == Some{V.int_value(count)} : Maybe<&2,D.Value>},L.E<{D.find_field(fields(Summary.row(key,Summary.Stats{count,total})),"id") == Some{D.VText{key}} : Maybe<&2,D.Value>},{D.find_field(fields(Summary.row(key,Summary.Stats{count,total})),"total") == Some{V.int_value(total)} : Maybe<&2,D.Value>}>>>

def fields(row: D.Row) -> List<&2,D.Field>:
  match row:
    case D.Row{key,fields}: fields

def summary_row_has_exact_named_count_key_and_total_payloads(key,count,total): L.Both{{==},L.Both{{==},L.Both{{==},{==}}}}
