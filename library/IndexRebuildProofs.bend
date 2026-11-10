# Actual rebuild establishes exact complete rows, then the UNCHANGED
# TableLaws.ExactIndex when the provided INPUT replacement equals a pure build
# of the INPUT base rows. No final invariant/trace or primitive success is a
# premise. Separate base collection views are proved preserved by actual writes.
import Base
import ./IndexReplacementProofs.bend as Rebuilt
import ./CollectionFrameProofs.bend as Frame
import ./IndexRebuildTrace.bend as Runtime
import ./IndexActionProofs.bend as Ops
import ./MutationWritePlan.bend as Plan
import ./MutationWriteTrace.bend as Writes
import ./QueryReadTrace.bend as History
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Logic.bend as L
import ./Index.bend as Index
import ./TableLaws.bend as Table
import ./ValueScalarProofs.bend as Pair
import ../src/Termination.bend as T

def events(+collection: D.Collection,+old: List<&2,D.Row>,new: List<&2,D.Row>,history: List<&2,S.OperationEvent>) -> List<&2,S.OperationEvent>:
  History.append_events(Rebuilt.events(collection,old,new),S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.Keys{D.keys_rows(old)}}}))

law actual_existing_collection_enumeration_yields_exactly_its_input_row_keys:
  for +schema: D.Schema
  for +before: D.State
  for +collection: D.Collection
  for +table: D.SchemaTable
  for +old: List<&2,D.Row>
  for schema_found: {D.schema_collection(collection,schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for rows_found: {D.rows_collection(collection,before) == Some{old} : Maybe<&2,List<&2,D.Row>>}
  {D.operate(schema,before,D.EnumerateKeys{collection}) == D.Observed{D.Keys{D.keys_rows(old)}} : D.ResultOp}
def actual_existing_collection_enumeration_yields_exactly_its_input_row_keys(schema,before,collection,table,old,schema_found,rows_found):
  %Equal.sym(Maybe<&2,D.SchemaTable>,D.schema_collection(collection,schema),Some{table},schema_found) : {D.operate_resolved(D.EnumerateKeys{collection},D.resolve_parts(_,D.rows_collection(collection,before)),before) == D.Observed{D.Keys{D.keys_rows(old)}} : D.ResultOp}
  %Equal.sym(Maybe<&2,List<&2,D.Row>>,D.rows_collection(collection,before),Some{old},rows_found) : {D.operate_resolved(D.EnumerateKeys{collection},D.resolve_parts(Some{table},_),before) == D.Observed{D.Keys{D.keys_rows(old)}} : D.ResultOp}
  {==}

def from_replacement(+schema: D.Schema,+before: D.State,+collection: D.Collection,+table: D.SchemaTable,+old: List<&2,D.Row>,+new: List<&2,D.Row>,+remaining: Nat,-done: S.Action,+history: List<&2,S.OperationEvent>,schema_found: {D.schema_collection(collection,schema) == Some{table} : Maybe<&2,D.SchemaTable>},rows_found: {D.rows_collection(collection,before) == Some{old} : Maybe<&2,List<&2,D.Row>>},replacement: Rebuilt.Replacement(schema,before,collection,old,new)) ->
  L.E<{T.observe(1n+Plan.depth(Ops.operations(collection,D.keys_rows(old),new),1n+remaining),Index.rebuild(collection,new,done),schema,before,history) == T.observe(1n+remaining,done,schema,Rebuilt.state(collection,before,old,new),events(collection,old,new,history)) : S.Trace},{D.rows_collection(collection,Rebuilt.state(collection,before,old,new)) == Some{new} : Maybe<&2,List<&2,D.Row>>}>:
  match replacement:
    case Pair.Both{plan,view}:
      L.Both{Equal.trans(S.Trace,T.observe(1n+Plan.depth(Ops.operations(collection,D.keys_rows(old),new),1n+remaining),Index.rebuild(collection,new,done),schema,before,history),Writes.finish(Plan.plan(Ops.operations(collection,D.keys_rows(old),new),schema,before),1n+remaining,schema,done,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.Keys{D.keys_rows(old)}}})),T.observe(1n+remaining,done,schema,Rebuilt.state(collection,before,old,new),events(collection,old,new,history)),Runtime.result_case(D.Observed{D.Keys{D.keys_rows(old)}},schema,before,collection,new,remaining,done,history,actual_existing_collection_enumeration_yields_exactly_its_input_row_keys(schema,before,collection,table,old,schema_found,rows_found),Unit{}),Equal.cong(Plan.Plan,S.Trace,p => Writes.finish(p,1n+remaining,schema,done,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.Keys{D.keys_rows(old)}}})),Plan.plan(Ops.operations(collection,D.keys_rows(old),new),schema,before),Plan.WriteHandoff{Rebuilt.state(collection,before,old,new),Rebuilt.events(collection,old,new)},plan)),view}

law actual_rebuild_has_exact_complete_replacement_history_and_caller_handoff:
  for +schema: D.Schema
  for +before: D.State
  for +collection: D.Collection
  for +table: D.SchemaTable
  for +old: List<&2,D.Row>
  for +new: List<&2,D.Row>
  for +remaining: Nat
  for -done: S.Action
  for +history: List<&2,S.OperationEvent>
  for +schema_found: {D.schema_collection(collection,schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(collection,before) == Some{old} : Maybe<&2,List<&2,D.Row>>}
  for +valid_old: {D.rows_valid_cases(old,table) == True{} : Bool}
  for +valid_new: {D.rows_valid_cases(new,table) == True{} : Bool}
  L.E<{T.observe(1n+Plan.depth(Ops.operations(collection,D.keys_rows(old),new),1n+remaining),Index.rebuild(collection,new,done),schema,before,history) == T.observe(1n+remaining,done,schema,Rebuilt.state(collection,before,old,new),events(collection,old,new,history)) : S.Trace},{D.rows_collection(collection,Rebuilt.state(collection,before,old,new)) == Some{new} : Maybe<&2,List<&2,D.Row>>}>
def actual_rebuild_has_exact_complete_replacement_history_and_caller_handoff(schema,before,collection,table,old,new,remaining,done,history,schema_found,rows_found,valid_old,valid_new):
  from_replacement(schema,before,collection,table,old,new,remaining,done,history,schema_found,rows_found,Rebuilt.actual_rebuild_write_plan_establishes_exact_complete_replacement_from_valid_input_rows(schema,before,collection,table,old,new,schema_found,rows_found,valid_old,valid_new))

# Input build correspondence is unavoidable: rebuild receives caller rows and
# neither reads business data nor proves an arbitrary caller build automatically.
def views_establish_exact_index(~build: List<&2,D.Row> -> List<&2,D.Row>,+state: D.State,+base: D.Collection,+index: D.Collection,+base_rows: List<&2,D.Row>,+replacement: List<&2,D.Row>,base_view: {D.rows_collection(base,state) == Some{base_rows} : Maybe<&2,List<&2,D.Row>>},index_view: {D.rows_collection(index,state) == Some{replacement} : Maybe<&2,List<&2,D.Row>>},input_correspondence: {replacement == build(base_rows) : List<&2,D.Row>}) -> Table.ExactIndex(~build,base,index,state):
  %Equal.sym(Maybe<&2,List<&2,D.Row>>,D.rows_collection(base,state),Some{base_rows},base_view) : Table.ExactRows(~build,_,D.rows_collection(index,state))
  %Equal.sym(Maybe<&2,List<&2,D.Row>>,D.rows_collection(index,state),Some{replacement},index_view) : Table.ExactRows(~build,Some{base_rows},_)
  input_correspondence

def closed_index(~build: List<&2,D.Row> -> List<&2,D.Row>,+schema: D.Schema,+before: D.State,+index: D.Collection,+base: D.Collection,+table: D.SchemaTable,+old: List<&2,D.Row>,+new: List<&2,D.Row>,+base_rows: List<&2,D.Row>,+value: D.Value,+history: List<&2,S.OperationEvent>,+separate: Frame.Separate(index,base),base_found: {D.rows_collection(base,before) == Some{base_rows} : Maybe<&2,List<&2,D.Row>>},input_correspondence: {new == build(base_rows) : List<&2,D.Row>},closed: L.E<{T.observe(1n+Plan.depth(Ops.operations(index,D.keys_rows(old),new),1n),Index.rebuild(index,new,S.Finish{value}),schema,before,history) == S.Final{Rebuilt.state(index,before,old,new),events(index,old,new,history),S.Response{S.Success{},value}} : S.Trace},{D.rows_collection(index,Rebuilt.state(index,before,old,new)) == Some{new} : Maybe<&2,List<&2,D.Row>>}>) -> L.E<{T.observe(1n+Plan.depth(Ops.operations(index,D.keys_rows(old),new),1n),Index.rebuild(index,new,S.Finish{value}),schema,before,history) == S.Final{Rebuilt.state(index,before,old,new),events(index,old,new,history),S.Response{S.Success{},value}} : S.Trace},Table.ExactIndex(~build,base,index,Rebuilt.state(index,before,old,new))>:
  match closed:
    case L.Both{trace,index_view}: L.Both{trace,views_establish_exact_index(~build,Rebuilt.state(index,before,old,new),base,index,base_rows,new,Equal.trans(Maybe<&2,List<&2,D.Row>>,D.rows_collection(base,Rebuilt.state(index,before,old,new)),D.rows_collection(base,before),Some{base_rows},Rebuilt.the_exact_rebuilt_state_preserves_every_separate_source_collection_view(index,base,before,old,new,separate),base_found),index_view,input_correspondence)}

law actual_closed_rebuild_establishes_the_unchanged_exact_index_law_from_input_build_correspondence:
  for ~build: List<&2,D.Row> -> List<&2,D.Row>
  for +schema: D.Schema
  for +before: D.State
  for +index: D.Collection
  for +base: D.Collection
  for +table: D.SchemaTable
  for +old: List<&2,D.Row>
  for +new: List<&2,D.Row>
  for +base_rows: List<&2,D.Row>
  for +value: D.Value
  for +history: List<&2,S.OperationEvent>
  for +separate: Frame.Separate(index,base)
  for +schema_found: {D.schema_collection(index,schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for +index_found: {D.rows_collection(index,before) == Some{old} : Maybe<&2,List<&2,D.Row>>}
  for +base_found: {D.rows_collection(base,before) == Some{base_rows} : Maybe<&2,List<&2,D.Row>>}
  for +valid_old: {D.rows_valid_cases(old,table) == True{} : Bool}
  for +valid_new: {D.rows_valid_cases(new,table) == True{} : Bool}
  for input_correspondence: {new == build(base_rows) : List<&2,D.Row>}
  L.E<{T.observe(1n+Plan.depth(Ops.operations(index,D.keys_rows(old),new),1n),Index.rebuild(index,new,S.Finish{value}),schema,before,history) == S.Final{Rebuilt.state(index,before,old,new),events(index,old,new,history),S.Response{S.Success{},value}} : S.Trace},Table.ExactIndex(~build,base,index,Rebuilt.state(index,before,old,new))>
def actual_closed_rebuild_establishes_the_unchanged_exact_index_law_from_input_build_correspondence(build,schema,before,index,base,table,old,new,base_rows,value,history,separate,schema_found,index_found,base_found,valid_old,valid_new,input_correspondence):
  closed_index(~build,schema,before,index,base,table,old,new,base_rows,value,history,separate,base_found,input_correspondence,actual_rebuild_has_exact_complete_replacement_history_and_caller_handoff(schema,before,index,table,old,new,0n,S.Finish{value},history,schema_found,index_found,valid_old,valid_new))
