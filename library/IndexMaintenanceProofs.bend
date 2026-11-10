# Actual maintenance plus ONE concrete business upsert establishes unchanged
# ExactIndex under an explicit PURE INPUT delta correspondence. An arbitrary
# business callback is only given exact handoff behavior, never assumed to
# preserve the desired whole invariant. Permission/admission remains separate.
import Base
import ./IndexMaintenancePlan.bend as M
import ./CollectionFrameProofs.bend as Frame
import ./IndexValidatedWrites.bend as Batch
import ./IndexRebuildProofs.bend as Rebuild
import ./IndexActionProofs.bend as Runtime
import ./MutationWritePlan.bend as Plan
import ./MutationWriteTrace.bend as Writes
import ./MutationPrimitiveProofs.bend as Primitive
import ./QueryReadTrace.bend as History
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Logic.bend as L
import ./Action.bend as A
import ./Index.bend as Index
import ./TableLaws.bend as Table
import ./ValueScalarProofs.bend as Pair
import ../src/Termination.bend as T

def history(+collection: D.Collection,old: List<&2,String>,new: List<&2,D.Row>,before: List<&2,S.OperationEvent>) -> List<&2,S.OperationEvent>:
  History.append_events(M.events(collection,old,new),before)

def from_effect(+schema: D.Schema,+before: D.State,+collection: D.Collection,+old: List<&2,String>,+new: List<&2,D.Row>,+current: List<&2,D.Row>,+remaining: Nat,-business: S.Action,+events: List<&2,S.OperationEvent>,effect: M.Effect(schema,before,collection,old,new,current)) -> L.E<{T.observe(Plan.depth(Runtime.operations(collection,old,new),1n+remaining),Index.maintain(collection,old,new,business),schema,before,events) == T.observe(1n+remaining,business,schema,M.state(collection,before,old,new,current),history(collection,old,new,events)) : S.Trace},{D.rows_collection(collection,M.state(collection,before,old,new,current)) == Some{M.rows(old,new,current)} : Maybe<&2,List<&2,D.Row>>}>:
  match effect:
    case Pair.Both{plan,view}: L.Both{Equal.trans(S.Trace,T.observe(Plan.depth(Runtime.operations(collection,old,new),1n+remaining),Index.maintain(collection,old,new,business),schema,before,events),Writes.finish(Plan.plan(Runtime.operations(collection,old,new),schema,before),1n+remaining,schema,business,events),T.observe(1n+remaining,business,schema,M.state(collection,before,old,new,current),history(collection,old,new,events)),Runtime.actual_index_maintenance_has_total_exact_state_events_errors_and_business_handoff(schema,before,collection,old,new,remaining,business,events),Equal.cong(Plan.Plan,S.Trace,p => Writes.finish(p,1n+remaining,schema,business,events),Plan.plan(Runtime.operations(collection,old,new),schema,before),Plan.WriteHandoff{M.state(collection,before,old,new,current),M.events(collection,old,new)},plan)),view}

law actual_maintenance_has_exact_validated_input_delta_and_business_handoff:
  for +schema: D.Schema
  for +before: D.State
  for +collection: D.Collection
  for +table: D.SchemaTable
  for +old: List<&2,String>
  for +new: List<&2,D.Row>
  for +current: List<&2,D.Row>
  for +remaining: Nat
  for -business: S.Action
  for +events: List<&2,S.OperationEvent>
  for +schema_found: {D.schema_collection(collection,schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(collection,before) == Some{current} : Maybe<&2,List<&2,D.Row>>}
  for +addresses: {Batch.unicode_keys(old) == True{} : Bool}
  for valid: Batch.ValidRows(table,new)
  L.E<{T.observe(Plan.depth(Runtime.operations(collection,old,new),1n+remaining),Index.maintain(collection,old,new,business),schema,before,events) == T.observe(1n+remaining,business,schema,M.state(collection,before,old,new,current),history(collection,old,new,events)) : S.Trace},{D.rows_collection(collection,M.state(collection,before,old,new,current)) == Some{M.rows(old,new,current)} : Maybe<&2,List<&2,D.Row>>}>
def actual_maintenance_has_exact_validated_input_delta_and_business_handoff(schema,before,collection,table,old,new,current,remaining,business,events,schema_found,rows_found,addresses,valid):
  from_effect(schema,before,collection,old,new,current,remaining,business,events,M.actual_maintenance_plan_has_exact_independent_input_delta_state_events_and_rows(schema,before,collection,table,old,new,current,schema_found,rows_found,addresses,valid))

def operation(collection: D.Collection,row: D.Row) -> D.Operation:
  match row:
    case D.Row{key,fields}: D.DefineRow{collection,key,fields}

def business(collection: D.Collection,row: D.Row,value: D.Value) -> S.Action:
  A.define_rows(collection,[row],S.Finish{value})

def final_state(+index: D.Collection,base: D.Collection,before: D.State,old: List<&2,String>,new: List<&2,D.Row>,current: List<&2,D.Row>,base_rows: List<&2,D.Row>,row: D.Row) -> D.State:
  D.swap_collection(base,M.state(index,before,old,new,current),D.insert_row(base_rows,row))

def final_events(+index: D.Collection,base: D.Collection,old: List<&2,String>,new: List<&2,D.Row>,row: D.Row,events: List<&2,S.OperationEvent>) -> List<&2,S.OperationEvent>:
  S.append(history(index,old,new,events),S.OperationEvent{operation(base,row),S.Write{}})

law an_actual_valid_business_upsert_has_exact_new_state_write_and_closed_value:
  for +schema: D.Schema
  for +before: D.State
  for +base: D.Collection
  for +table: D.SchemaTable
  for +base_rows: List<&2,D.Row>
  for +row: D.Row
  for +value: D.Value
  for +events: List<&2,S.OperationEvent>
  for schema_found: {D.schema_collection(base,schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for rows_found: {D.rows_collection(base,before) == Some{base_rows} : Maybe<&2,List<&2,D.Row>>}
  for valid: {D.row_is_valid(table,row) == True{} : Bool}
  {T.observe(2n,business(base,row,value),schema,before,events) == S.Final{D.swap_collection(base,before,D.insert_row(base_rows,row)),S.append(events,S.OperationEvent{operation(base,row),S.Write{}}),S.Response{S.Success{},value}} : S.Trace}
def an_actual_valid_business_upsert_has_exact_new_state_write_and_closed_value(schema,before,base,table,base_rows,row,value,events,schema_found,rows_found,valid):
  match row:
    case D.Row{+key,+fields}: Writes.real_changed_primitive_retains_the_write_and_continues_in_its_actual_new_state(1n,schema,before,D.swap_collection(base,before,D.insert_row(base_rows,D.Row{key,fields})),D.DefineRow{base,key,fields},r => A.written(S.Finish{value},r),events,Primitive.defining_a_valid_row_in_an_existing_collection_performs_the_exact_upsert(schema,before,base,table,base_rows,key,fields,schema_found,rows_found,valid))

def after_handoff(~build: List<&2,D.Row> -> List<&2,D.Row>,+schema: D.Schema,+before: D.State,+index: D.Collection,+base: D.Collection,+base_table: D.SchemaTable,+old: List<&2,String>,+new: List<&2,D.Row>,+current: List<&2,D.Row>,+base_rows: List<&2,D.Row>,+row: D.Row,+value: D.Value,+events: List<&2,S.OperationEvent>,+separate: Frame.Separate(index,base),base_schema: {D.schema_collection(base,schema) == Some{base_table} : Maybe<&2,D.SchemaTable>},base_found: {D.rows_collection(base,before) == Some{base_rows} : Maybe<&2,List<&2,D.Row>>},valid_business: {D.row_is_valid(base_table,row) == True{} : Bool},input_delta: {M.rows(old,new,current) == build(D.insert_row(base_rows,row)) : List<&2,D.Row>},handoff: L.E<{T.observe(Plan.depth(Runtime.operations(index,old,new),2n),Index.maintain(index,old,new,business(base,row,value)),schema,before,events) == T.observe(2n,business(base,row,value),schema,M.state(index,before,old,new,current),history(index,old,new,events)) : S.Trace},{D.rows_collection(index,M.state(index,before,old,new,current)) == Some{M.rows(old,new,current)} : Maybe<&2,List<&2,D.Row>>}>) -> L.E<{T.observe(Plan.depth(Runtime.operations(index,old,new),2n),Index.maintain(index,old,new,business(base,row,value)),schema,before,events) == S.Final{final_state(index,base,before,old,new,current,base_rows,row),final_events(index,base,old,new,row,events),S.Response{S.Success{},value}} : S.Trace},Table.ExactIndex(~build,base,index,final_state(index,base,before,old,new,current,base_rows,row))>:
  match handoff:
    case L.Both{trace,index_view}:
      +base_view = Equal.trans(Maybe<&2,List<&2,D.Row>>,D.rows_collection(base,M.state(index,before,old,new,current)),D.rows_collection(base,before),Some{base_rows},M.actual_maintenance_prefix_preserves_every_separate_business_collection_view(index,base,before,old,new,current,separate),base_found)
      L.Both{Equal.trans(S.Trace,T.observe(Plan.depth(Runtime.operations(index,old,new),2n),Index.maintain(index,old,new,business(base,row,value)),schema,before,events),T.observe(2n,business(base,row,value),schema,M.state(index,before,old,new,current),history(index,old,new,events)),S.Final{final_state(index,base,before,old,new,current,base_rows,row),final_events(index,base,old,new,row,events),S.Response{S.Success{},value}},trace,an_actual_valid_business_upsert_has_exact_new_state_write_and_closed_value(schema,M.state(index,before,old,new,current),base,base_table,base_rows,row,value,history(index,old,new,events),base_schema,base_view,valid_business)),Rebuild.views_establish_exact_index(~build,final_state(index,base,before,old,new,current,base_rows,row),base,index,D.insert_row(base_rows,row),M.rows(old,new,current),Frame.replacing_an_existing_collection_has_the_exact_new_row_view(base,M.state(index,before,old,new,current),base_rows,D.insert_row(base_rows,row),base_view),Equal.trans(Maybe<&2,List<&2,D.Row>>,D.rows_collection(index,final_state(index,base,before,old,new,current,base_rows,row)),D.rows_collection(index,M.state(index,before,old,new,current)),Some{M.rows(old,new,current)},Frame.replacing_a_collection_preserves_every_separate_collection_view(base,index,M.state(index,before,old,new,current),D.insert_row(base_rows,row),Frame.separate_collection_domains_are_symmetric(index,base,separate)),index_view),input_delta)}

law actual_maintenance_and_business_upsert_establish_exact_index_from_independent_input_delta:
  for ~build: List<&2,D.Row> -> List<&2,D.Row>
  for +schema: D.Schema
  for +before: D.State
  for +index: D.Collection
  for +base: D.Collection
  for +index_table: D.SchemaTable
  for +base_table: D.SchemaTable
  for +old: List<&2,String>
  for +new: List<&2,D.Row>
  for +current: List<&2,D.Row>
  for +base_rows: List<&2,D.Row>
  for +row: D.Row
  for +value: D.Value
  for +events: List<&2,S.OperationEvent>
  for +separate: Frame.Separate(index,base)
  for +index_schema: {D.schema_collection(index,schema) == Some{index_table} : Maybe<&2,D.SchemaTable>}
  for +index_found: {D.rows_collection(index,before) == Some{current} : Maybe<&2,List<&2,D.Row>>}
  for +base_schema: {D.schema_collection(base,schema) == Some{base_table} : Maybe<&2,D.SchemaTable>}
  for +base_found: {D.rows_collection(base,before) == Some{base_rows} : Maybe<&2,List<&2,D.Row>>}
  for +addresses: {Batch.unicode_keys(old) == True{} : Bool}
  for valid_new: Batch.ValidRows(index_table,new)
  for valid_business: {D.row_is_valid(base_table,row) == True{} : Bool}
  for input_delta: {M.rows(old,new,current) == build(D.insert_row(base_rows,row)) : List<&2,D.Row>}
  L.E<{T.observe(Plan.depth(Runtime.operations(index,old,new),2n),Index.maintain(index,old,new,business(base,row,value)),schema,before,events) == S.Final{final_state(index,base,before,old,new,current,base_rows,row),final_events(index,base,old,new,row,events),S.Response{S.Success{},value}} : S.Trace},Table.ExactIndex(~build,base,index,final_state(index,base,before,old,new,current,base_rows,row))>
def actual_maintenance_and_business_upsert_establish_exact_index_from_independent_input_delta(build,schema,before,index,base,index_table,base_table,old,new,current,base_rows,row,value,events,separate,index_schema,index_found,base_schema,base_found,addresses,valid_new,valid_business,input_delta):
  after_handoff(~build,schema,before,index,base,base_table,old,new,current,base_rows,row,value,events,separate,base_schema,base_found,valid_business,input_delta,actual_maintenance_has_exact_validated_input_delta_and_business_handoff(schema,before,index,index_table,old,new,current,1n,business(base,row,value),events,index_schema,index_found,addresses,valid_new))
