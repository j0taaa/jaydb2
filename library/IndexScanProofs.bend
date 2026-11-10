# Total actual public scan_equal: enumerate every source key, then the fixed
# two-cell visitor in enumeration order. Mathematical observation depth is
# derived from the actual source DATA; it does not change runtime limits.
import Base
import ./IndexScanModel.bend as M
import ./IndexScanMapProofs.bend as Map
import ./ReadOperationProofs.bend as Reads
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Index.bend as Index
import ./Key.bend as Key
import ./Read.bend as Read
import ./Query.bend as Q
import ./Proofs.bend as Event
import ../proof/Foundations.bend as F
import ../src/Termination.bend as T

def after_depth(result: D.ResultOp,+remaining: Nat) -> Nat:
  match result:
    case D.Observed{D.Keys{keys}}: M.depth(keys,remaining)
    case D.Observed{D.Cell{value}}: 1n+remaining
    case D.Observed{D.RowAbsent{}}: 1n+remaining
    case D.Observed{D.Count{count}}: 1n+remaining
    case D.Observed{D.Existence{exists}}: 1n+remaining
    case D.FailureData{}: 1n+remaining
    case D.Changed{working}: 1n+remaining

def expected(result: D.ResultOp,+schema: D.Schema,+state: D.State,+collection: D.Collection,+value: String,+remaining: Nat,done: D.Value -> S.Action,+history: List<&2,S.OperationEvent>) -> S.Trace:
  match result:
    case D.Observed{D.Keys{+keys}}: Map.finish(M.plan(keys,schema,state,collection,value),remaining,schema,state,done,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.Keys{keys}}}))
    case D.Observed{D.Cell{value}}: S.Final{state,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.Cell{value}}}),S.Response{S.Refusal{},D.VText{"unexpected keys return"}}}
    case D.Observed{D.RowAbsent{}}: S.Final{state,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.RowAbsent{}}}),S.Response{S.Refusal{},D.VText{"unexpected keys return"}}}
    case D.Observed{D.Count{count}}: S.Final{state,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.Count{count}}}),S.Response{S.Refusal{},D.VText{"unexpected keys return"}}}
    case D.Observed{D.Existence{exists}}: S.Final{state,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.Existence{exists}}}),S.Response{S.Refusal{},D.VText{"unexpected keys return"}}}
    case D.FailureData{}: S.Final{state,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.ErrorOfData{}}),S.Response{S.DataError{},D.VAbsent{}}}
    case D.Changed{working}: S.Final{working,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Write{}}),S.Response{S.Refusal{},D.VText{"unexpected keys return"}}}

def result_case(+result: D.ResultOp,+schema: D.Schema,+state: D.State,+collection: D.Collection,+parts: List<&2,String>,+remaining: Nat,-done: D.Value -> S.Action,+history: List<&2,S.OperationEvent>,actual: {D.operate(schema,state,D.EnumerateKeys{collection}) == result : D.ResultOp},kind: Reads.ResultKind(Reads.Keys{},result)) ->
  {T.observe(1n+after_depth(result,remaining),Index.scan_equal(collection,parts,done),schema,state,history) == expected(result,schema,state,collection,Key.encode(parts),remaining,done,history) : S.Trace}:
  match result:
    case D.FailureData{}: Reads.actual_data_failure_retains_its_event_and_finishes_without_a_return_callback(1n+remaining,schema,state,D.EnumerateKeys{collection},Read.keys_return(keys => Q.filter_map(~Index.Scan,~Index.visit,Index.Scan{collection,Key.encode(parts)},keys,done)),history,actual)
    case D.Observed{D.Keys{+keys}}:
      Equal.trans(S.Trace,T.observe(1n+M.depth(keys,remaining),Index.scan_equal(collection,parts,done),schema,state,history),T.observe(M.depth(keys,remaining),Q.filter_map(~Index.Scan,~Index.visit,Index.Scan{collection,Key.encode(parts)},keys,done),schema,state,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.Keys{keys}}})),Map.finish(M.plan(keys,schema,state,collection,Key.encode(parts)),remaining,schema,state,done,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.Keys{keys}}})),Event.read_continuation(M.depth(keys,remaining),schema,state,D.EnumerateKeys{collection},D.Keys{keys},Read.keys_return(items => Q.filter_map(~Index.Scan,~Index.visit,Index.Scan{collection,Key.encode(parts)},items,done)),history,actual),Map.actual_fixed_index_filter_map_has_total_exact_reads_stopping_projection_and_handoff(keys,schema,state,collection,Key.encode(parts),remaining,done,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.Keys{keys}}})))
    case D.Observed{D.Cell{value}}: F.absurd_boolean({T.observe(2n+remaining,Index.scan_equal(collection,parts,done),schema,state,history) == expected(D.Observed{D.Cell{value}},schema,state,collection,Key.encode(parts),remaining,done,history) : S.Trace},kind)
    case D.Observed{D.RowAbsent{}}: F.absurd_boolean({T.observe(2n+remaining,Index.scan_equal(collection,parts,done),schema,state,history) == expected(D.Observed{D.RowAbsent{}},schema,state,collection,Key.encode(parts),remaining,done,history) : S.Trace},kind)
    case D.Observed{D.Count{count}}: F.absurd_boolean({T.observe(2n+remaining,Index.scan_equal(collection,parts,done),schema,state,history) == expected(D.Observed{D.Count{count}},schema,state,collection,Key.encode(parts),remaining,done,history) : S.Trace},kind)
    case D.Observed{D.Existence{exists}}: F.absurd_boolean({T.observe(2n+remaining,Index.scan_equal(collection,parts,done),schema,state,history) == expected(D.Observed{D.Existence{exists}},schema,state,collection,Key.encode(parts),remaining,done,history) : S.Trace},kind)
    case D.Changed{working}: F.absurd_boolean({T.observe(2n+remaining,Index.scan_equal(collection,parts,done),schema,state,history) == expected(D.Changed{working},schema,state,collection,Key.encode(parts),remaining,done,history) : S.Trace},kind)

law actual_scan_equal_has_total_exact_enumeration_visits_projection_errors_and_handoff:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +parts: List<&2,String>
  for +remaining: Nat
  for -done: D.Value -> S.Action
  for +history: List<&2,S.OperationEvent>
  {T.observe(1n+after_depth(D.operate(schema,state,D.EnumerateKeys{collection}),remaining),Index.scan_equal(collection,parts,done),schema,state,history) == expected(D.operate(schema,state,D.EnumerateKeys{collection}),schema,state,collection,Key.encode(parts),remaining,done,history) : S.Trace}
def actual_scan_equal_has_total_exact_enumeration_visits_projection_errors_and_handoff(schema,state,collection,parts,remaining,done,history):
  result_case(D.operate(schema,state,D.EnumerateKeys{collection}),schema,state,collection,parts,remaining,done,history,{==},Reads.real_named_read_operations_have_only_the_expected_observation_or_data_failure(Reads.Keys{},schema,state,collection,"",""))
