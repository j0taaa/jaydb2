# Independent rebuild postcondition: ALL original rows are erased and the
# supplied canonical schema-valid replacement rows are obtained EXACTLY.
# Preconditions concern only initial collection views and input row validity.
# No successful primitive/output plan or completed invariant is assumed.
import Base
import ./CollectionFrameProofs.bend as Frame
import ./RowRemovalProofs.bend as Remove
import ./RowInsertionProofs.bend as Insert
import ./IndexValidatedWrites.bend as Batch
import ./MutationPlanComposition.bend as Compose
import ./IndexActionProofs.bend as Index
import ./IndexScanModel.bend as Events
import ./MutationWriteSequence.bend as W
import ./MutationWritePlan.bend as M
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./ValueScalarProofs.bend as Pair

def removals(+collection: D.Collection,old: List<&2,D.Row>) -> List<&2,D.Operation>:
  W.removals(collection,D.keys_rows(old))

def removed_state(+collection: D.Collection,+state: D.State,old: List<&2,D.Row>) -> D.State:
  Batch.working(removals(collection,old),collection,state,Nil{})

def state(+collection: D.Collection,+before: D.State,old: List<&2,D.Row>,+new: List<&2,D.Row>) -> D.State:
  Batch.working(W.rows(collection,new),collection,removed_state(collection,before,old),new)

def events(+collection: D.Collection,old: List<&2,D.Row>,new: List<&2,D.Row>) -> List<&2,S.OperationEvent>:
  Events.events(Batch.recorded(removals(collection,old)),Batch.recorded(W.rows(collection,new)))

def Replacement(+schema: D.Schema,+before: D.State,+collection: D.Collection,+old: List<&2,D.Row>,+new: List<&2,D.Row>) -> Data:
  Pair.Both<{M.plan(Index.operations(collection,D.keys_rows(old),new),schema,before) == M.WriteHandoff{state(collection,before,old,new),events(collection,old,new)} : M.Plan},{D.rows_collection(collection,state(collection,before,old,new)) == Some{new} : Maybe<&2,List<&2,D.Row>>}>

law every_valid_original_table_is_completely_erased_by_its_enumerated_keys:
  for +schema: D.Schema
  for +before: D.State
  for +collection: D.Collection
  for +table: D.SchemaTable
  for +old: List<&2,D.Row>
  for +schema_found: {D.schema_collection(collection,schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(collection,before) == Some{old} : Maybe<&2,List<&2,D.Row>>}
  for +valid: {D.rows_valid_cases(old,table) == True{} : Bool}
  Batch.Success(removals(collection,old),schema,before,collection,Nil{})
def every_valid_original_table_is_completely_erased_by_its_enumerated_keys(schema,before,collection,table,old,schema_found,rows_found,valid):
  %Remove.removing_every_enumerated_original_key_empties_every_finite_source_table(old) : Batch.Success(removals(collection,old),schema,before,collection,_)
  Batch.every_valid_addressed_removal_batch_has_exact_state_events_and_transformed_rows(D.keys_rows(old),schema,before,collection,table,old,schema_found,rows_found,Batch.actual_contract_valid_rows_have_only_unicode_enumerated_addresses(old,table,valid))

law every_valid_canonical_replacement_is_written_exactly_into_empty_storage:
  for +schema: D.Schema
  for +before: D.State
  for +collection: D.Collection
  for +table: D.SchemaTable
  for +new: List<&2,D.Row>
  for +schema_found: {D.schema_collection(collection,schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(collection,before) == Some{Nil{}} : Maybe<&2,List<&2,D.Row>>}
  for +valid: {D.rows_valid_cases(new,table) == True{} : Bool}
  Batch.Success(W.rows(collection,new),schema,before,collection,new)
def every_valid_canonical_replacement_is_written_exactly_into_empty_storage(schema,before,collection,table,new,schema_found,rows_found,valid):
  %Insert.upserting_canonical_unique_replacement_rows_into_empty_storage_is_exact_replacement(new,Insert.actual_valid_rows_have_independent_canonical_unique_keys(new,table,valid)) : Batch.Success(W.rows(collection,new),schema,before,collection,_)
  Batch.every_schema_valid_upsert_batch_has_exact_state_events_and_transformed_rows(new,schema,before,collection,table,Nil{},schema_found,rows_found,Batch.actual_contract_valid_rows_give_each_independent_row_validation(new,table,valid))

def after_insertion(+schema: D.Schema,+before: D.State,+collection: D.Collection,+old: List<&2,D.Row>,+new: List<&2,D.Row>,removed: {M.plan(removals(collection,old),schema,before) == M.WriteHandoff{removed_state(collection,before,old),Batch.recorded(removals(collection,old))} : M.Plan},inserted: Batch.Success(W.rows(collection,new),schema,removed_state(collection,before,old),collection,new)) -> Replacement(schema,before,collection,old,new):
  match inserted:
    case Pair.Both{plan,view}:
      Pair.Both{Equal.trans(M.Plan,M.plan(Index.operations(collection,D.keys_rows(old),new),schema,before),Compose.follow(M.plan(removals(collection,old),schema,before),W.rows(collection,new),schema),M.WriteHandoff{state(collection,before,old,new),events(collection,old,new)},Compose.actual_data_plan_for_concatenated_operations_is_exact_stage_composition(removals(collection,old),W.rows(collection,new),schema,before),Equal.trans(M.Plan,Compose.follow(M.plan(removals(collection,old),schema,before),W.rows(collection,new),schema),Compose.prefix(Batch.recorded(removals(collection,old)),M.plan(W.rows(collection,new),schema,removed_state(collection,before,old))),M.WriteHandoff{state(collection,before,old,new),events(collection,old,new)},Equal.cong(M.Plan,M.Plan,p => Compose.follow(p,W.rows(collection,new),schema),M.plan(removals(collection,old),schema,before),M.WriteHandoff{removed_state(collection,before,old),Batch.recorded(removals(collection,old))},removed),Equal.cong(M.Plan,M.Plan,p => Compose.prefix(Batch.recorded(removals(collection,old)),p),M.plan(W.rows(collection,new),schema,removed_state(collection,before,old)),M.WriteHandoff{state(collection,before,old,new),Batch.recorded(W.rows(collection,new))},plan))),view}

def after_removal(+schema: D.Schema,+before: D.State,+collection: D.Collection,+table: D.SchemaTable,+old: List<&2,D.Row>,+new: List<&2,D.Row>,+schema_found: {D.schema_collection(collection,schema) == Some{table} : Maybe<&2,D.SchemaTable>},+valid_new: {D.rows_valid_cases(new,table) == True{} : Bool},removed: Batch.Success(removals(collection,old),schema,before,collection,Nil{})) -> Replacement(schema,before,collection,old,new):
  match removed:
    case Pair.Both{plan,view}: after_insertion(schema,before,collection,old,new,plan,every_valid_canonical_replacement_is_written_exactly_into_empty_storage(schema,removed_state(collection,before,old),collection,table,new,schema_found,view,valid_new))

law actual_rebuild_write_plan_establishes_exact_complete_replacement_from_valid_input_rows:
  for +schema: D.Schema
  for +before: D.State
  for +collection: D.Collection
  for +table: D.SchemaTable
  for +old: List<&2,D.Row>
  for +new: List<&2,D.Row>
  for +schema_found: {D.schema_collection(collection,schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(collection,before) == Some{old} : Maybe<&2,List<&2,D.Row>>}
  for +valid_old: {D.rows_valid_cases(old,table) == True{} : Bool}
  for +valid_new: {D.rows_valid_cases(new,table) == True{} : Bool}
  Replacement(schema,before,collection,old,new)
def actual_rebuild_write_plan_establishes_exact_complete_replacement_from_valid_input_rows(schema,before,collection,table,old,new,schema_found,rows_found,valid_old,valid_new):
  after_removal(schema,before,collection,table,old,new,schema_found,valid_new,every_valid_original_table_is_completely_erased_by_its_enumerated_keys(schema,before,collection,table,old,schema_found,rows_found,valid_old))

law an_empty_or_nonempty_known_update_preserves_separate_collection_views:
  for +operations: List<&2,D.Operation>
  for +collection: D.Collection
  for +watched: D.Collection
  for +before: D.State
  for +new: List<&2,D.Row>
  for separate: Frame.Separate(collection,watched)
  {D.rows_collection(watched,Batch.working(operations,collection,before,new)) == D.rows_collection(watched,before) : Maybe<&2,List<&2,D.Row>>}
def an_empty_or_nonempty_known_update_preserves_separate_collection_views(operations,collection,watched,before,new,separate):
  match operations:
    case Nil{}: {==}
    case Con{op,tail}: Frame.replacing_a_collection_preserves_every_separate_collection_view(collection,watched,before,new,separate)

law the_exact_rebuilt_state_preserves_every_separate_source_collection_view:
  for +collection: D.Collection
  for +watched: D.Collection
  for +before: D.State
  for +old: List<&2,D.Row>
  for +new: List<&2,D.Row>
  for +separate: Frame.Separate(collection,watched)
  {D.rows_collection(watched,state(collection,before,old,new)) == D.rows_collection(watched,before) : Maybe<&2,List<&2,D.Row>>}
def the_exact_rebuilt_state_preserves_every_separate_source_collection_view(collection,watched,before,old,new,separate):
  Equal.trans(Maybe<&2,List<&2,D.Row>>,D.rows_collection(watched,state(collection,before,old,new)),D.rows_collection(watched,removed_state(collection,before,old)),D.rows_collection(watched,before),an_empty_or_nonempty_known_update_preserves_separate_collection_views(W.rows(collection,new),collection,watched,removed_state(collection,before,old),new,separate),an_empty_or_nonempty_known_update_preserves_separate_collection_views(removals(collection,old),collection,watched,before,Nil{},separate))
