# Total actual index visitor. Source reads stay in target/value order, including
# missing/filtered rows; primitive data failure stops before the next read.
# Projection uses the actual pure decoder; independent source-index/table
# meaning is supplied separately rather than inferred from this one visit.
import Base
import ./QueryReadPlan.bend as Read
import ./QueryReadPlanProofs.bend as Reads
import ./QuerySelectionModel.bend as Selection
import ./QueryReadTrace.bend as History
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Index.bend as Index
import ../src/Termination.bend as T

type VisitPlan is Data:
  VisitYield{item: Maybe<&2,D.Value>,events: List<&2,S.OperationEvent>}
  VisitDenied{response: S.Response,events: List<&2,S.OperationEvent>}

def from_projection(value: String,projection: Index.Projection,events: List<&2,S.OperationEvent>) -> VisitPlan:
  match projection:
    case Index.Target{target,v}: VisitYield{Bool.pick(Maybe<&2,D.Value>,String.eq(value,v),Some{D.VText{target}},None{}),events}
    case Index.Missing{}: VisitYield{None{},events}
    case Index.Invalid{}: VisitDenied{S.Response{S.Refusal{},D.VText{"invalid index entry"}},events}

def from_read_plan(value: String,plan: Read.Plan) -> VisitPlan:
  match plan:
    case Read.ReadsReady{problem,record,events}: from_projection(value,Index.projection(Selection.render(problem,record)),events)
    case Read.ReadsFailed{events}: VisitDenied{S.Response{S.DataError{},D.VAbsent{}},events}

def plan(+schema: D.Schema,+state: D.State,+collection: D.Collection,key: String,value: String) -> VisitPlan:
  from_read_plan(value,Read.plan(schema,state,collection,key,["target","value"]))

def trace(plan: VisitPlan,+depth: Nat,+schema: D.Schema,+state: D.State,done: Maybe<&2,D.Value> -> S.Action,history: List<&2,S.OperationEvent>) -> S.Trace:
  match plan:
    case VisitYield{item,events}: T.observe(depth,done(item),schema,state,History.append_events(events,history))
    case VisitDenied{response,events}: S.Final{state,History.append_events(events,history),response}

law actual_projected_callback_has_exact_target_filter_missing_or_invalid_behavior:
  for +value: String
  for +projection: Index.Projection
  for +events: List<&2,S.OperationEvent>
  for +remaining: Nat
  for +schema: D.Schema
  for +state: D.State
  for -done: Maybe<&2,D.Value> -> S.Action
  for +history: List<&2,S.OperationEvent>
  {T.observe(1n+remaining,Index.projected(value,done,projection),schema,state,History.append_events(events,history)) == trace(from_projection(value,projection,events),1n+remaining,schema,state,done,history) : S.Trace}
def actual_projected_callback_has_exact_target_filter_missing_or_invalid_behavior(value,projection,events,remaining,schema,state,done,history):
  match projection:
    case Index.Target{target,v}: {==}
    case Index.Missing{}: {==}
    case Index.Invalid{}: T.stopped(remaining,state,S.Response{S.Refusal{},D.VText{"invalid index entry"}},schema,History.append_events(events,history))

law completing_actual_source_reads_has_exact_index_visitor_decoding:
  for +value: String
  for +plan: Read.Plan
  for +remaining: Nat
  for +schema: D.Schema
  for +state: D.State
  for -done: Maybe<&2,D.Value> -> S.Action
  for +history: List<&2,S.OperationEvent>
  {Reads.finish(plan,1n+remaining,schema,state,Index.selected(value,done),history) == trace(from_read_plan(value,plan),1n+remaining,schema,state,done,history) : S.Trace}
def completing_actual_source_reads_has_exact_index_visitor_decoding(value,plan,remaining,schema,state,done,history):
  match plan:
    case Read.ReadsReady{problem,record,events}: actual_projected_callback_has_exact_target_filter_missing_or_invalid_behavior(value,Index.projection(Selection.render(problem,record)),events,remaining,schema,state,done,history)
    case Read.ReadsFailed{events}: {==}

law actual_index_visitor_has_total_exact_two_field_reads_projection_errors_and_handoff:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +key: String
  for +value: String
  for +remaining: Nat
  for -done: Maybe<&2,D.Value> -> S.Action
  for +history: List<&2,S.OperationEvent>
  {T.observe(3n+remaining,Index.visit(Index.Scan{collection,value},key,done),schema,state,history) == trace(plan(schema,state,collection,key,value),1n+remaining,schema,state,done,history) : S.Trace}
def actual_index_visitor_has_total_exact_two_field_reads_projection_errors_and_handoff(schema,state,collection,key,value,remaining,done,history):
  Equal.trans(S.Trace,T.observe(3n+remaining,Index.visit(Index.Scan{collection,value},key,done),schema,state,history),Reads.finish(Read.plan(schema,state,collection,key,["target","value"]),1n+remaining,schema,state,Index.selected(value,done),history),trace(plan(schema,state,collection,key,value),1n+remaining,schema,state,done,history),Reads.actual_read_fields_has_total_exact_source_state_behavior(schema,state,collection,key,["target","value"],1n+remaining,Index.selected(value,done),history),completing_actual_source_reads_has_exact_index_visitor_decoding(value,Read.plan(schema,state,collection,key,["target","value"]),remaining,schema,state,done,history))
