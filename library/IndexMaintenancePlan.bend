# Independent explicit index delta: remove supplied old keys, then sequential
# full-row upserts (including last-write-wins duplicates). All primitive success
# is derived from INPUT schema/views/Unicode/new-row validity. Business handoff
# is not assumed to preserve this result; that needs separate actual behavior.
import Base
import ./CollectionFrameProofs.bend as Frame
import ./RowRemovalProofs.bend as Remove
import ./RowInsertionProofs.bend as Insert
import ./IndexValidatedWrites.bend as Batch
import ./MutationPlanComposition.bend as Compose
import ./IndexReplacementProofs.bend as Rebuilt
import ./IndexActionProofs.bend as Index
import ./IndexScanModel.bend as Events
import ./MutationWriteSequence.bend as W
import ./MutationWritePlan.bend as M
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./ValueScalarProofs.bend as Pair

def rows(old: List<&2,String>,new: List<&2,D.Row>,current: List<&2,D.Row>) -> List<&2,D.Row>:
  Insert.all(new,Remove.all(old,current))

def removed_state(+collection: D.Collection,+before: D.State,+old: List<&2,String>,current: List<&2,D.Row>) -> D.State:
  Batch.working(W.removals(collection,old),collection,before,Remove.all(old,current))

def state(+collection: D.Collection,+before: D.State,+old: List<&2,String>,+new: List<&2,D.Row>,+current: List<&2,D.Row>) -> D.State:
  Batch.working(W.rows(collection,new),collection,removed_state(collection,before,old,current),rows(old,new,current))

def events(+collection: D.Collection,old: List<&2,String>,new: List<&2,D.Row>) -> List<&2,S.OperationEvent>:
  Events.events(Batch.recorded(W.removals(collection,old)),Batch.recorded(W.rows(collection,new)))

def Effect(+schema: D.Schema,+before: D.State,+collection: D.Collection,+old: List<&2,String>,+new: List<&2,D.Row>,+current: List<&2,D.Row>) -> Data:
  Pair.Both<{M.plan(Index.operations(collection,old,new),schema,before) == M.WriteHandoff{state(collection,before,old,new,current),events(collection,old,new)} : M.Plan},{D.rows_collection(collection,state(collection,before,old,new,current)) == Some{rows(old,new,current)} : Maybe<&2,List<&2,D.Row>>}>

def after_insert(+schema: D.Schema,+before: D.State,+collection: D.Collection,+old: List<&2,String>,+new: List<&2,D.Row>,+current: List<&2,D.Row>,removed: {M.plan(W.removals(collection,old),schema,before) == M.WriteHandoff{removed_state(collection,before,old,current),Batch.recorded(W.removals(collection,old))} : M.Plan},inserted: Batch.Success(W.rows(collection,new),schema,removed_state(collection,before,old,current),collection,rows(old,new,current))) -> Effect(schema,before,collection,old,new,current):
  match inserted:
    case Pair.Both{plan,view}:
      Pair.Both{Equal.trans(M.Plan,M.plan(Index.operations(collection,old,new),schema,before),Compose.follow(M.plan(W.removals(collection,old),schema,before),W.rows(collection,new),schema),M.WriteHandoff{state(collection,before,old,new,current),events(collection,old,new)},Compose.actual_data_plan_for_concatenated_operations_is_exact_stage_composition(W.removals(collection,old),W.rows(collection,new),schema,before),Equal.trans(M.Plan,Compose.follow(M.plan(W.removals(collection,old),schema,before),W.rows(collection,new),schema),Compose.prefix(Batch.recorded(W.removals(collection,old)),M.plan(W.rows(collection,new),schema,removed_state(collection,before,old,current))),M.WriteHandoff{state(collection,before,old,new,current),events(collection,old,new)},Equal.cong(M.Plan,M.Plan,p => Compose.follow(p,W.rows(collection,new),schema),M.plan(W.removals(collection,old),schema,before),M.WriteHandoff{removed_state(collection,before,old,current),Batch.recorded(W.removals(collection,old))},removed),Equal.cong(M.Plan,M.Plan,p => Compose.prefix(Batch.recorded(W.removals(collection,old)),p),M.plan(W.rows(collection,new),schema,removed_state(collection,before,old,current)),M.WriteHandoff{state(collection,before,old,new,current),Batch.recorded(W.rows(collection,new))},plan))),view}

def after_remove(+schema: D.Schema,+before: D.State,+collection: D.Collection,+table: D.SchemaTable,+old: List<&2,String>,+new: List<&2,D.Row>,+current: List<&2,D.Row>,+schema_found: {D.schema_collection(collection,schema) == Some{table} : Maybe<&2,D.SchemaTable>},valid: Batch.ValidRows(table,new),removed: Batch.Success(W.removals(collection,old),schema,before,collection,Remove.all(old,current))) -> Effect(schema,before,collection,old,new,current):
  match removed:
    case Pair.Both{plan,view}: after_insert(schema,before,collection,old,new,current,plan,Batch.every_schema_valid_upsert_batch_has_exact_state_events_and_transformed_rows(new,schema,removed_state(collection,before,old,current),collection,table,Remove.all(old,current),schema_found,view,valid))

law actual_maintenance_plan_has_exact_independent_input_delta_state_events_and_rows:
  for +schema: D.Schema
  for +before: D.State
  for +collection: D.Collection
  for +table: D.SchemaTable
  for +old: List<&2,String>
  for +new: List<&2,D.Row>
  for +current: List<&2,D.Row>
  for +schema_found: {D.schema_collection(collection,schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(collection,before) == Some{current} : Maybe<&2,List<&2,D.Row>>}
  for +addresses: {Batch.unicode_keys(old) == True{} : Bool}
  for valid: Batch.ValidRows(table,new)
  Effect(schema,before,collection,old,new,current)
def actual_maintenance_plan_has_exact_independent_input_delta_state_events_and_rows(schema,before,collection,table,old,new,current,schema_found,rows_found,addresses,valid):
  after_remove(schema,before,collection,table,old,new,current,schema_found,valid,Batch.every_valid_addressed_removal_batch_has_exact_state_events_and_transformed_rows(old,schema,before,collection,table,current,schema_found,rows_found,addresses))

law actual_maintenance_prefix_preserves_every_separate_business_collection_view:
  for +collection: D.Collection
  for +watched: D.Collection
  for +before: D.State
  for +old: List<&2,String>
  for +new: List<&2,D.Row>
  for +current: List<&2,D.Row>
  for +separate: Frame.Separate(collection,watched)
  {D.rows_collection(watched,state(collection,before,old,new,current)) == D.rows_collection(watched,before) : Maybe<&2,List<&2,D.Row>>}
def actual_maintenance_prefix_preserves_every_separate_business_collection_view(collection,watched,before,old,new,current,separate):
  Equal.trans(Maybe<&2,List<&2,D.Row>>,D.rows_collection(watched,state(collection,before,old,new,current)),D.rows_collection(watched,removed_state(collection,before,old,current)),D.rows_collection(watched,before),Rebuilt.an_empty_or_nonempty_known_update_preserves_separate_collection_views(W.rows(collection,new),collection,watched,removed_state(collection,before,old,current),rows(old,new,current),separate),Rebuilt.an_empty_or_nonempty_known_update_preserves_separate_collection_views(W.removals(collection,old),collection,watched,before,Remove.all(old,current),separate))
