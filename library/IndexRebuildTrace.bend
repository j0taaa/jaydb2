# Total actual Index.rebuild: enumerate original keys, remove in that order,
# upsert complete new rows in supplied order, then hand off in the evolved
# working state. Mathematical depth is derived from input DATA, not a quota.
import Base
import ./IndexActionProofs.bend as I
import ./MutationWritePlan.bend as Plan
import ./MutationWriteTrace.bend as Writes
import ./ReadOperationProofs.bend as Reads
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Index.bend as Index
import ./Read.bend as Read
import ./Proofs.bend as Event
import ../proof/Foundations.bend as F
import ../src/Termination.bend as T

def after_depth(result: D.ResultOp,+collection: D.Collection,+rows: List<&2,D.Row>,+remaining: Nat) -> Nat:
  match result:
    case D.Observed{D.Keys{keys}}: Plan.depth(I.operations(collection,keys,rows),1n+remaining)
    case D.Observed{D.Cell{value}}: 1n+remaining
    case D.Observed{D.RowAbsent{}}: 1n+remaining
    case D.Observed{D.Count{count}}: 1n+remaining
    case D.Observed{D.Existence{exists}}: 1n+remaining
    case D.FailureData{}: 1n+remaining
    case D.Changed{working}: 1n+remaining

def expected(result: D.ResultOp,+schema: D.Schema,+state: D.State,+collection: D.Collection,+rows: List<&2,D.Row>,+remaining: Nat,done: S.Action,+history: List<&2,S.OperationEvent>) -> S.Trace:
  match result:
    case D.Observed{+observation}:
      match observation:
        case D.Keys{keys}: Writes.finish(Plan.plan(I.operations(collection,keys,rows),schema,state),1n+remaining,schema,done,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.Keys{keys}}}))
        case D.Cell{value}: S.Final{state,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.Cell{value}}}),S.Response{S.Refusal{},D.VText{"unexpected keys return"}}}
        case D.RowAbsent{}: S.Final{state,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.RowAbsent{}}}),S.Response{S.Refusal{},D.VText{"unexpected keys return"}}}
        case D.Count{count}: S.Final{state,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.Count{count}}}),S.Response{S.Refusal{},D.VText{"unexpected keys return"}}}
        case D.Existence{exists}: S.Final{state,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.Existence{exists}}}),S.Response{S.Refusal{},D.VText{"unexpected keys return"}}}
    case D.FailureData{}: S.Final{state,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.ErrorOfData{}}),S.Response{S.DataError{},D.VAbsent{}}}
    case D.Changed{working}: S.Final{working,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Write{}}),S.Response{S.Refusal{},D.VText{"unexpected keys return"}}}

def result_case(+result: D.ResultOp,+schema: D.Schema,+state: D.State,+collection: D.Collection,+rows: List<&2,D.Row>,+remaining: Nat,-done: S.Action,+history: List<&2,S.OperationEvent>,actual: {D.operate(schema,state,D.EnumerateKeys{collection}) == result : D.ResultOp},kind: Reads.ResultKind(Reads.Keys{},result)) ->
  {T.observe(1n+after_depth(result,collection,rows,remaining),Index.rebuild(collection,rows,done),schema,state,history) == expected(result,schema,state,collection,rows,remaining,done,history) : S.Trace}:
  match result:
    case D.FailureData{}: Reads.actual_data_failure_retains_its_event_and_finishes_without_a_return_callback(1n+remaining,schema,state,D.EnumerateKeys{collection},Read.keys_return(keys => Index.maintain(collection,keys,rows,done)),history,actual)
    case D.Observed{D.Keys{+keys}}:
      Equal.trans(S.Trace,T.observe(1n+Plan.depth(I.operations(collection,keys,rows),1n+remaining),Index.rebuild(collection,rows,done),schema,state,history),T.observe(Plan.depth(I.operations(collection,keys,rows),1n+remaining),Index.maintain(collection,keys,rows,done),schema,state,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.Keys{keys}}})),Writes.finish(Plan.plan(I.operations(collection,keys,rows),schema,state),1n+remaining,schema,done,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.Keys{keys}}})),Event.read_continuation(Plan.depth(I.operations(collection,keys,rows),1n+remaining),schema,state,D.EnumerateKeys{collection},D.Keys{keys},Read.keys_return(items => Index.maintain(collection,items,rows,done)),history,actual),I.actual_index_maintenance_has_total_exact_state_events_errors_and_business_handoff(schema,state,collection,keys,rows,remaining,done,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.Keys{keys}}})))
    case D.Observed{D.Cell{value}}: F.absurd_boolean({T.observe(2n+remaining,Index.rebuild(collection,rows,done),schema,state,history) == expected(D.Observed{D.Cell{value}},schema,state,collection,rows,remaining,done,history) : S.Trace},kind)
    case D.Observed{D.RowAbsent{}}: F.absurd_boolean({T.observe(2n+remaining,Index.rebuild(collection,rows,done),schema,state,history) == expected(D.Observed{D.RowAbsent{}},schema,state,collection,rows,remaining,done,history) : S.Trace},kind)
    case D.Observed{D.Count{count}}: F.absurd_boolean({T.observe(2n+remaining,Index.rebuild(collection,rows,done),schema,state,history) == expected(D.Observed{D.Count{count}},schema,state,collection,rows,remaining,done,history) : S.Trace},kind)
    case D.Observed{D.Existence{exists}}: F.absurd_boolean({T.observe(2n+remaining,Index.rebuild(collection,rows,done),schema,state,history) == expected(D.Observed{D.Existence{exists}},schema,state,collection,rows,remaining,done,history) : S.Trace},kind)
    case D.Changed{working}: F.absurd_boolean({T.observe(2n+remaining,Index.rebuild(collection,rows,done),schema,state,history) == expected(D.Changed{working},schema,state,collection,rows,remaining,done,history) : S.Trace},kind)

law actual_rebuild_has_total_exact_enumeration_removal_upsert_and_handoff_behavior:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +rows: List<&2,D.Row>
  for +remaining: Nat
  for -done: S.Action
  for +history: List<&2,S.OperationEvent>
  {T.observe(1n+after_depth(D.operate(schema,state,D.EnumerateKeys{collection}),collection,rows,remaining),Index.rebuild(collection,rows,done),schema,state,history) == expected(D.operate(schema,state,D.EnumerateKeys{collection}),schema,state,collection,rows,remaining,done,history) : S.Trace}
def actual_rebuild_has_total_exact_enumeration_removal_upsert_and_handoff_behavior(schema,state,collection,rows,remaining,done,history):
  result_case(D.operate(schema,state,D.EnumerateKeys{collection}),schema,state,collection,rows,remaining,done,history,{==},Reads.real_named_read_operations_have_only_the_expected_observation_or_data_failure(Reads.Keys{},schema,state,collection,"",""))
