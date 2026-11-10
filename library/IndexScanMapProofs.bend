# TOTAL fixed index filter_map execution: both actual reads for every visited
# key; retained filtered reads; first error/refusal stops; exact output order and
# handoff. No assumed visitor progress, successful prefix, or completed output.
import Base
import ./IndexVisitProofs.bend as Visit
import ./IndexScanModel.bend as M
import ./QueryReadTrace.bend as H
import ./QueryFilterMapModel.bend as Projection
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Index.bend as Index
import ./Query.bend as Q
import ./Sequence.bend as Sequence
import ../src/Termination.bend as T

def finish(plan: M.MapPlan,+remaining: Nat,+schema: D.Schema,+state: D.State,done: D.Value -> S.Action,history: List<&2,S.OperationEvent>) -> S.Trace:
  match plan:
    case M.ScanYield{items,events}: T.observe(1n+remaining,done(Sequence.values(items)),schema,state,H.append_events(events,history))
    case M.ScanDenied{response,events}: S.Final{state,H.append_events(events,history),response}

law source_event_concatenation_is_exact_history_composition:
  for +first: List<&2,S.OperationEvent>
  for +later: List<&2,S.OperationEvent>
  for +history: List<&2,S.OperationEvent>
  {H.append_events(M.events(first,later),history) == H.append_events(later,H.append_events(first,history)) : List<&2,S.OperationEvent>}
def source_event_concatenation_is_exact_history_composition(first,later,history):
  match first:
    case Nil{}: {==}
    case Con{+event,+tail}: source_event_concatenation_is_exact_history_composition(tail,later,S.append(history,event))

law source_item_projection_and_events_preserve_exact_tail_handoff:
  for +tail: M.MapPlan
  for +item: Maybe<&2,D.Value>
  for +seen: List<&2,S.OperationEvent>
  for +remaining: Nat
  for +schema: D.Schema
  for +state: D.State
  for -done: D.Value -> S.Action
  for +history: List<&2,S.OperationEvent>
  {finish(tail,remaining,schema,state,value => done(Q.include(item,value)),H.append_events(seen,history)) == finish(M.combine(Visit.VisitYield{item,seen},tail),remaining,schema,state,done,history) : S.Trace}
def source_item_projection_and_events_preserve_exact_tail_handoff(tail,item,seen,remaining,schema,state,done,history):
  match tail:
    case M.ScanDenied{+response,+later}: Equal.cong(List<&2,S.OperationEvent>,S.Trace,events => S.Final{state,events,response},H.append_events(later,H.append_events(seen,history)),H.append_events(M.events(seen,later),history),Equal.sym(List<&2,S.OperationEvent>,H.append_events(M.events(seen,later),history),H.append_events(later,H.append_events(seen,history)),source_event_concatenation_is_exact_history_composition(seen,later,history)))
    case M.ScanYield{+items,+later}:
      Equal.trans(S.Trace,T.observe(1n+remaining,done(Q.include(item,Sequence.values(items))),schema,state,H.append_events(later,H.append_events(seen,history))),T.observe(1n+remaining,done(Sequence.values(Projection.push(item,items))),schema,state,H.append_events(later,H.append_events(seen,history))),T.observe(1n+remaining,done(Sequence.values(Projection.push(item,items))),schema,state,H.append_events(M.events(seen,later),history)),Equal.cong(D.Value,S.Trace,value => T.observe(1n+remaining,done(value),schema,state,H.append_events(later,H.append_events(seen,history))),Q.include(item,Sequence.values(items)),Sequence.values(Projection.push(item,items)),Equal.sym(D.Value,Sequence.values(Projection.push(item,items)),Q.include(item,Sequence.values(items)),Projection.projected_items_encode_exactly_the_query_include_operation(item,items))),Equal.cong(List<&2,S.OperationEvent>,S.Trace,events => T.observe(1n+remaining,done(Sequence.values(Projection.push(item,items))),schema,state,events),H.append_events(later,H.append_events(seen,history)),H.append_events(M.events(seen,later),history),Equal.sym(List<&2,S.OperationEvent>,H.append_events(M.events(seen,later),history),H.append_events(later,H.append_events(seen,history)),source_event_concatenation_is_exact_history_composition(seen,later,history))))

def visit_case(+head: Visit.VisitPlan,+keys: List<&2,String>,+schema: D.Schema,+state: D.State,+collection: D.Collection,+value: String,+remaining: Nat,-done: D.Value -> S.Action,+history: List<&2,S.OperationEvent>,recursive: @+item: Maybe<&2,D.Value> -> @+seen: List<&2,S.OperationEvent> -> {T.observe(M.depth(keys,remaining),Q.filter_map(~Index.Scan,~Index.visit,Index.Scan{collection,value},keys,result => done(Q.include(item,result))),schema,state,H.append_events(seen,history)) == finish(M.plan(keys,schema,state,collection,value),remaining,schema,state,result => done(Q.include(item,result)),H.append_events(seen,history)) : S.Trace}) ->
  {Visit.trace(head,M.depth(keys,remaining),schema,state,item => Q.filter_map(~Index.Scan,~Index.visit,Index.Scan{collection,value},keys,result => done(Q.include(item,result))),history) == finish(M.combine(head,M.plan(keys,schema,state,collection,value)),remaining,schema,state,done,history) : S.Trace}:
  match head:
    case Visit.VisitDenied{response,seen}: {==}
    case Visit.VisitYield{+item,+seen}:
      Equal.trans(S.Trace,T.observe(M.depth(keys,remaining),Q.filter_map(~Index.Scan,~Index.visit,Index.Scan{collection,value},keys,result => done(Q.include(item,result))),schema,state,H.append_events(seen,history)),finish(M.plan(keys,schema,state,collection,value),remaining,schema,state,result => done(Q.include(item,result)),H.append_events(seen,history)),finish(M.combine(Visit.VisitYield{item,seen},M.plan(keys,schema,state,collection,value)),remaining,schema,state,done,history),recursive(item,seen),source_item_projection_and_events_preserve_exact_tail_handoff(M.plan(keys,schema,state,collection,value),item,seen,remaining,schema,state,done,history))

law actual_fixed_index_filter_map_has_total_exact_reads_stopping_projection_and_handoff:
  for +keys: List<&2,String>
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +value: String
  for +remaining: Nat
  for -done: D.Value -> S.Action
  for +history: List<&2,S.OperationEvent>
  {T.observe(M.depth(keys,remaining),Q.filter_map(~Index.Scan,~Index.visit,Index.Scan{collection,value},keys,done),schema,state,history) == finish(M.plan(keys,schema,state,collection,value),remaining,schema,state,done,history) : S.Trace}
def actual_fixed_index_filter_map_has_total_exact_reads_stopping_projection_and_handoff(keys,schema,state,collection,value,remaining,done,history):
  match keys:
    case Nil{}: {==}
    case Con{+key,+tail}:
      Equal.trans(S.Trace,T.observe(M.depth(Con{key,tail},remaining),Q.filter_map(~Index.Scan,~Index.visit,Index.Scan{collection,value},Con{key,tail},done),schema,state,history),Visit.trace(Visit.plan(schema,state,collection,key,value),M.depth(tail,remaining),schema,state,item => Q.filter_map(~Index.Scan,~Index.visit,Index.Scan{collection,value},tail,result => done(Q.include(item,result))),history),finish(M.plan(Con{key,tail},schema,state,collection,value),remaining,schema,state,done,history),Visit.actual_index_visitor_has_total_exact_two_field_reads_projection_errors_and_handoff(schema,state,collection,key,value,Nat.add(M.owned(tail),remaining),item => Q.filter_map(~Index.Scan,~Index.visit,Index.Scan{collection,value},tail,result => done(Q.include(item,result))),history),visit_case(Visit.plan(schema,state,collection,key,value),tail,schema,state,collection,value,remaining,done,history,item => seen => actual_fixed_index_filter_map_has_total_exact_reads_stopping_projection_and_handoff(tail,schema,state,collection,value,remaining,result => done(Q.include(item,result)),H.append_events(seen,history))))
